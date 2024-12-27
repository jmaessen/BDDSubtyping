{-# LANGUAGE PatternSynonyms, ViewPatterns #-}
module BDDSubtyping.BDD(
  BDD, TR, Base, BDDPat(..), pattern Bot, pattern Top,
  toGraph, fromGraph,
  select, base,
  root, size, rightmost, bdd, FV(..),
  bddBases, model, modelDiff,
  basicUnion, basicIntersect, basicDifference, complement,
  basicImplies, basicEqv, trToBDD,
  eraseSubtypes, eraseDisjoints,
  common, commonOrErase,
  canonS, isCanon,
  isBottom, relate, relateNaive, isDisjoint,
  commute, rightComplement, leftComplement, Relation(..),
  eraseDisjointsC, eraseSubtypesC, commonC,
  intersect
) where
import Control.Monad(liftM2)
import qualified Data.IntMap.Strict as M
import Data.IntMap((!))
import qualified Data.Map.Strict as DM
import System.IO.Unsafe(unsafePerformIO) -- For memo tables

import Data.NaiveMemo(MemoTable, mkMemo, memoize, memoizeIdem1, ConsId, getId)
import BDDSubtyping.DAG(DAG, Relatedness(..), tr, unMkDag)
import BDDSubtyping.BDDInternal

import Debug.Trace(traceShow)

-- Take the complement of a BDD. O(1).
complement :: BDD -> BDD
complement (BDD Pos t) = BDD Not t
complement (BDD Not t) = BDD Pos t

data BDDPat r = BotP | Select Base r r | TopP deriving (Eq, Ord, Show)

type BDDGraph = M.IntMap (BDDPat Int)

toGraph :: BDD -> BDDGraph
toGraph b0 = gf where
  (_, gf, _) = loop b0 mempty mempty
  loop b gr hc = loop' (bdd b) gr hc
  loop' (Select i t e) gr hc =
    let (e', gre, hce) = loop e gr hc
        (t', grt, hct) = loop t gre hce
        v = Select i t' e'
    in node v grt hct
  loop' TopP gr hc = node TopP gr hc
  loop' BotP gr hc = node BotP gr hc
  node p gr hc
    | Just n <- DM.lookup p hc = (n, gr, hc)
    | otherwise = (s, M.insert s p gr, DM.insert p s hc)
    where s = M.size gr

fromGraph :: BDDGraph -> BDD
fromGraph g = g'!(M.size g - 1) where
  g' = fmap convert g
  convert BotP = Bot
  convert TopP = Top
  convert (Select i t e) = select i (g'!t) (g'!e)

-- A pattern matcher for BDDs that abstracts away RNBDD.
bdd :: BDD -> BDDPat BDD
bdd (BDD Pos (Sel v t e)) = Select v t (BDD Pos e)
bdd (BDD Not (Sel v (BDD Not t) e)) = Select v (BDD Pos t) (BDD Not e)
bdd (BDD Not (Sel v (BDD Pos t) e)) = Select v (BDD Not t) (BDD Not e)
bdd (BDD Pos _{-None-}) = BotP
bdd (BDD Not _{-None-}) = TopP

-- Smart constructor that handles elimination.
sel :: Base -> BDD -> RNBDD -> RNBDD
sel _ (BDD Pos t) e | t == e = e
sel i t e = Sel i t e

-- Fundamental select smart constructor that just deals with BDD / RNBDD conversion.
select0 :: Base -> BDD -> BDD -> BDD
select0 i t (BDD Pos e) = BDD Pos $ Sel i t e
select0 i (BDD Pos t) (BDD Not e) = BDD Not (Sel i (BDD Not t) e)
select0 i (BDD Not t) (BDD Not e) = BDD Not (Sel i (BDD Pos t) e)

-- Select smart constructor that handles elimination and BDD / RNBDD conversion.
select :: Base -> BDD -> BDD -> BDD
select i t (BDD Pos e) = BDD Pos (sel i t e)
select i (BDD Pos t) (BDD Not e) = BDD Not (sel i (BDD Not t) e)
select i (BDD Not t) (BDD Not e) = BDD Not (sel i (BDD Pos t) e)

-- A singleton BDD representing base type i
base :: Base -> BDD
base i = select0 i Top Bot

type TR = DAG

-- By convention Top/Bot have a root of (-1) which is otherwise invalid.
root :: BDD -> Base
root (BDD _ rn) = rootRN rn

rootRN :: RNBDD -> Base
rootRN (Sel i _ _) = i
rootRN _ = -1

-- Metric for ordering that respects root order
metricRN :: RNBDD -> (Base, ConsId)
metricRN b@(Sel i _ _) = (i, getId b)
metricRN _ = (-1, -1)

metric :: BDD -> (Base, ConsId)
metric (BDD _ rn) = metricRN rn

-- Given base type relation TR, does bdd type t *fully* contain base type b?
bddBases :: TR -> BDD -> (Base -> Bool)
bddBases r (BDD Pos t) = rnbddBases r t
bddBases r (BDD Not t) = not . rnbddBases r t

rnbddBases :: TR -> RNBDD -> (Base -> Bool)
rnbddBases r (Sel n t e) =
  let tBases = bddBases r t
      eBases = rnbddBases r e
  in \ i ->
      if n >= i && tr r n i == Subtype
        then tBases i
        else eBases i
rnbddBases _ _{-None-} = const False

-- By convention, the rightmost leaf of a RNBDD is None/Bot (False).
-- We read the value of the rightmost leaf of a BDD from its root Sense.
rightmost :: BDD -> Bool
rightmost (BDD Pos _) = False
rightmost (BDD Not _) = True

-- An RNBDD will contain only Bases <= its root.
-- Its complement (Not) will contain all Bases > its root
-- and the complement of Bases in its RNBDD.
-- So we can find a BDD's behavior on all types by enumerating
-- its behavior on types up to (root bdd + 1), with the last
-- type standing in for its behavior on all larger Bases.
model :: TR -> BDD -> [Base]
model r b = filter (bddBases r b) [0..root b + 1]

-- Model difference.  We want to use the model for the highest root.
-- This is designed to compare models for non-canonical types.
-- Returns a list of bases at which the models differ.
-- This will be empty if the models match.
modelDiff :: TR -> BDD -> BDD -> [Base]
modelDiff r a b = filter (\i -> ab i /= bb i) [0..(root a `max` root b) + 1]
  where ab = bddBases r a
        bb = bddBases r b

{-# NOINLINE basicIntersectMemoTable #-}
basicIntersectMemoTable :: MemoTable (BDD, BDD) BDD
basicIntersectMemoTable = unsafePerformIO $ mkMemo

-- There's one interesting binary operation on BDDs, basic intersect (we
-- can derive union and difference using complement).  O(mn).
-- Note that basic intersect is oblivious to type relation, and
-- thus results with the same model can differ!
basicIntersect :: BDD -> BDD -> BDD
basicIntersect a0 b0 = loop a0 b0 where
  loop Bot _ = Bot
  loop Top b = b
  loop _ Bot = Bot
  loop a Top = a
  loop r@(BDD sa a) (BDD sb b) | a == b = if sa == sb then r else Bot
  loop a b
    | metric a >= metric b = loop' (a,b)
    | otherwise = loop' (b,a)
  loop' = memoize basicIntersectMemoTable loop''
  loop'' (bdd -> Select va ta ea, bdd -> Select vb tb eb)
    | va == vb = select va (ta `loop` tb) (ea `loop` eb)
  loop'' (bdd -> Select va ta ea, b) =
    select va (loop ta b)  (loop ea b)
  loop'' _ = error "basicIntersect: unreachable"

basicUnion :: BDD -> BDD -> BDD
basicUnion a b = complement $ basicIntersect (complement a) (complement b)

basicDifference :: BDD -> BDD -> BDD
basicDifference a b = basicIntersect a (complement b)

basicImplies :: BDD -> BDD -> BDD
basicImplies a b = complement (basicDifference a b)

basicEqv :: BDD -> BDD -> BDD
basicEqv a b = basicImplies a b `basicIntersect` basicImplies b a

-- Convert TR to equivalent BDD.
trToBDD :: TR -> BDD
trToBDD r =
  foldr basicIntersect Top $
    [ b | (sup, subs) <- unMkDag r,
          let sb = map base subs,
          b <- [basicUnion (base sup) (complement (foldr basicUnion Bot sb))] -- subtyping
    ]

{-# NOINLINE eraseSubtypesTable #-}
eraseSubtypesTable :: MemoTable (RNBDD, (Base, TR)) RNBDD
eraseSubtypesTable = unsafePerformIO mkMemo

{-# NOINLINE eraseDisjointsTable #-}
eraseDisjointsTable :: MemoTable (RNBDD, (Base, TR)) RNBDD
eraseDisjointsTable = unsafePerformIO mkMemo

-- Erase all strict subtypes of base i in bdd b to their else branch.
eraseSubtypes :: TR -> Base -> BDD -> BDD
eraseSubtypes r i b0 = loop b0 where
  loop (BDD p None) = BDD p None
  loop (BDD p e) = BDD p $ loopRN (e, (i, r))
  loopRN = memoizeIdem1 eraseSubtypesTable loopRN'
  loopRN' (Sel j t e, p@(i',r'))
    | j < i' && tr r' j i' == Subtype = loopRN (e,p)
    | otherwise = sel j (loop t) (loopRN (e,p))
  loopRN' _{-None-} = None

-- Erase all types disjoint from base i in bdd b to their else branch.
eraseDisjoints :: TR -> Base -> BDD -> BDD
eraseDisjoints r i b0 = loop b0 where
  loop (BDD p None) = BDD p None
  loop (BDD p e) = BDD p $ loopRN (e, (i, r))
  loopRN = memoizeIdem1 eraseDisjointsTable loopRN'
  loopRN' (Sel j t e, p@(i',r'))
    | j < i' && tr r' j i' == Disjoint = loopRN (e,p)
    | otherwise = sel j (loop t) (loopRN (e,p))
  loopRN' _{-None-} = None

selectM :: Base -> Maybe BDD -> Maybe BDD -> Maybe BDD
selectM i = liftM2 (select i)

selM :: Base -> Maybe BDD -> Maybe RNBDD -> Maybe RNBDD
selM i = liftM2 (sel i)

{-# NOINLINE commonMemoTable #-}
commonMemoTable :: MemoTable (BDD, RNBDD, (Base, TR)) (Maybe RNBDD)
commonMemoTable = unsafePerformIO mkMemo

common :: TR -> Base -> BDD -> BDD -> Maybe BDD
common r c t0 e0 = loop0 t0 e0 where
  loop0 t (BDD Pos e) = BDD Pos <$> loop t e
  loop0 t (BDD Not e) = BDD Not <$> loop (complement t) e
  loop Top None = Nothing
  loop Bot None = Just None
  loop a   b   = loop' (a, b, (c, r))
  loop' = memoize commonMemoTable loop''
  loop'' (t@(bdd -> Select it tt et), e@(Sel ie te ee), _) =
    case compare it ie of
      GT -> thenHigh it tt et e
      EQ -> selM it (loop0 tt te) (loop et ee)
      LT -> elseHigh t ie te ee
  loop'' (bdd -> Select it tt et, e, _) = thenHigh it tt et e
  loop'' (t, Sel ie te ee, _) = elseHigh t ie te ee
  loop'' _ = error "common: unreachable"
  thenHigh it tt et e
    | tr r it c == Subtype = sel it tt <$> loop et e
    | otherwise = selM it (BDD Pos <$> loop tt e) (loop et e)
  elseHigh t ie te ee
    | tr r ie c == Disjoint = sel ie te <$> loop t ee
    | otherwise = selM ie (loop0 t te) (loop t ee)

{-# NOINLINE coeMemoTable #-}
coeMemoTable :: MemoTable (BDD, BDD, (Base, TR)) (BDD, BDD, Maybe BDD)
coeMemoTable = unsafePerformIO mkMemo

-- Fused common and erase: should equal:
-- (eraseDisjoints r c t, eraseSubtypes r c e,
--  common r c (eraseDisjoints r c t) (eraseSubtypes r c e))
commonOrErase :: TR -> Base -> BDD -> BDD -> (BDD, BDD, Maybe BDD)
commonOrErase r c t0 e0 = loop t0 e0 where
  loop Top Bot = (Top, Bot, Nothing)
  loop Bot Top = (Bot, Top, Nothing)
  loop Top Top = (Top, Top, Just Top)
  loop Bot Bot = (Bot, Bot, Just Bot)
  loop t e = loop' (t,e,(c,r))
  loop' = memoize coeMemoTable loop''
  loop'' (t@(bdd -> Select it tt et), e@(bdd -> Select ie te ee), _) =
    case (compare it ie, tr r it c) of
      (GT, cmp) -> thenHigh cmp it tt et e
      (EQ, cmp) -> same cmp it tt et te ee
      (LT, _) ->   elseHigh (tr r ie c) t ie te ee
  loop'' (bdd -> Select it tt et, e, _) = thenHigh (tr r it c) it tt et e
  loop'' (t, bdd -> Select ie te ee, _) = elseHigh (tr r ie c) t ie te ee
  loop'' _ = error "commonOrErase: unreachable"
  both i tt et te ee = (select i tt' et', select i te' ee', selectM i t' e')
    where (tt', te', t') = loop tt te
          (et', ee', e') = loop et ee
  same Subtype i tt et _ ee = thenHigh Subtype i tt et ee
  same Disjoint i _ et te ee = elseHigh Disjoint et i te ee
  same MayIntersect i tt et te ee = both i tt et te ee
  thenHigh Disjoint _ _ et e = loop et e
  thenHigh Subtype it tt et e
    | tt' == et' = f
    | otherwise = (select it tt' et', ee', select it tt' <$> e')
    where tt' = eraseDisjoints r c tt
          f@(et', ee', e') = loop et e
  thenHigh MayIntersect it tt et e = both it tt et e e
  elseHigh Subtype t _ _ ee = loop t ee
  elseHigh Disjoint t ie te ee
    | te' == ee' = f
    | otherwise = (et', select ie te' ee', select ie te' <$> e')
    where te' = eraseSubtypes r c te
          f@(et', ee', e') = loop t ee
  elseHigh MayIntersect t ie te ee = both ie t t te ee

{-# NOINLINE canonSTable #-}
canonSTable :: MemoTable (BDD, TR) BDD
canonSTable = unsafePerformIO mkMemo

canonS :: TR -> BDD -> BDD
canonS r b0 = loop b0 where
  loop Top = Top
  loop Bot = Bot
  loop b = loop' (b, r)
  loop' = memoizeIdem1 canonSTable loop''
  loop'' (bdd -> Select i t e, _) = loopS i t e
  loop'' _ = error "canonS: unreachable"
  loopS i t e = loopS' i (loop t) (loop e)
  loopS' _ t e | t == e = t
  loopS' i t e =
    case commonOrErase r i t e of
      (t', e', Nothing)
        | t' == t && e' == e -> select i t' e'
        | t' == t -> loopS' i t' (loop e')
        | e' == e -> loopS' i (loop t') e'
        | otherwise -> loopS i t' e'
      (_, _, Just s) -> loop s

isCanon :: TR -> BDD -> Bool
isCanon r b = canonS r b == b

size :: BDD -> Int
size b = sizeb b where
  sizeb (BDD _ rnb) = sizernb rnb
  sizernb (Sel _ t e) = 1 + sizeb t + sizernb e
  sizernb _ = 0

data Relation =
  Relation { isSubtype :: Bool, isSupertype :: Bool,
             isSubtypeComp :: Bool, isSupertypeComp :: Bool }
  deriving (Eq, Show)

instance Semigroup Relation where
  ~(Relation sub1 sup1 subc1 supc1) <> ~(Relation sub2 sup2 subc2 supc2) =
    Relation (sub1 && sub2) (sup1 && sup2) (subc1 && subc2) (supc1 && supc2)

commute :: Relation -> Relation
commute ~(Relation sub sup subc supc) = Relation sup sub subc supc

rightComplement :: Relation -> Relation
rightComplement ~(Relation sub sup subc supc) = Relation subc supc sub sup

leftComplement :: Relation -> Relation
leftComplement ~(Relation sub sup subc supc) = Relation supc subc sup sub

isDisjoint :: Relation -> Bool
isDisjoint (Relation False False subc _) = subc
isDisjoint _ = False

-- Does a type denote bottom with respect to the given type relation?
isBottom :: TR -> BDD -> Bool
isBottom r b0 = loop b0 where
  loop (BDD Pos (Sel i t e)) =
    loop (eraseDisjoints r i t) && loop (eraseSubtypes r i (BDD Pos e))
  loop (BDD Not _) = False
  loop _ {- Bot -} = True

-- Relate two types naively with respect to base type relation.
-- a is disjoint from b if their intersection is empty (Bot).
-- a is a subtype of b if their intersection is a, and vice versa.
relateNaive :: TR -> BDD -> BDD -> Relation
relateNaive r a0 b0 = Relation
  { isSubtype = a == c
  , isSupertype = b == c
  , isSubtypeComp = a == d
  , isSupertypeComp = b' == d
  }
  where a = canonS r a0
        b = canonS r b0
        b' = complement b
        c = canonS r $ basicIntersect a b
        d = canonS r $ basicIntersect a b'

{-# NOINLINE relateTable #-}
relateTable :: MemoTable (RNBDD, RNBDD, TR) Relation
relateTable = unsafePerformIO mkMemo

-- Relate two types with respect to base type relation.
-- a is disjoint from b if their intersection is empty (Bot).
-- a is a subtype of b if their intersection is a, and vice versa.
relate :: TR -> BDD -> BDD -> Relation
relate r a0 b0 = loop (canonS r a0) (canonS r b0) where
  loop a (BDD Pos b) = loop1 a b
  loop a (BDD Not b) = rightComplement $ loop1 a b
  loop1 (BDD Pos a) b = loopRN a b
  loop1 (BDD Not a) b = leftComplement $ loopRN a b
  loopRN None None = Relation True True True False
  loopRN None _    = Relation True False True False
  loopRN _    None = Relation False True True False
  loopRN a b
    | a == b = Relation True True False False
    | metricRN a >= metricRN b = loopRN' (a, b, r)
    | otherwise = commute $ loopRN' (b, a, r)
  loopRN' = memoize relateTable loopRN''
  loopRN'' (Sel ia ta ea, Sel ib tb eb, _)
    | ia == ib = loop ta tb <> loopRN ea eb
  loopRN'' (Sel ia ta ea, b, _) =
    loop ta (canonS r (eraseDisjoints r ia (BDD Pos b))) <>
    commute (loop1 (canonS r (eraseSubtypes r ia (BDD Pos b))) ea)
  loopRN'' _ = error "Unreachable in loopRN''"

selectC :: TR -> Base -> BDD -> BDD -> BDD
selectC r i t (BDD Pos e) = BDD Pos $ selC r i t e
selectC r i t (BDD Not e) = BDD Not $ selC r i (complement t) e

selC :: TR -> Base -> BDD -> RNBDD -> RNBDD
selC r i t e =
  case commonCRN r i t e of
    Just s -> s
    Nothing -> sel i t e

selMC :: TR -> Base -> Maybe BDD -> Maybe RNBDD -> Maybe RNBDD
selMC r i = liftM2 (selC r i)

{-# NOINLINE eraseSubtypesCTable #-}
eraseSubtypesCTable :: MemoTable (RNBDD, (Base, TR)) RNBDD
eraseSubtypesCTable = unsafePerformIO mkMemo

{-# NOINLINE eraseDisjointsCTable #-}
eraseDisjointsCTable :: MemoTable (RNBDD, (Base, TR)) RNBDD
eraseDisjointsCTable = unsafePerformIO mkMemo

-- Erase all strict subtypes of base i in bdd b to their else branch.
eraseSubtypesC :: TR -> Base -> BDD -> BDD
eraseSubtypesC r i b0 = loop b0 where
  loop (BDD p None) = BDD p None
  loop (BDD p e) = BDD p $ loopRN (e, (i, r))
  loopRN = memoizeIdem1 eraseSubtypesCTable loopRN'
  loopRN' (Sel j t e, p@(i',r'))
    | j < i' && tr r' j i' == Subtype = loopRN (e,p)
    | otherwise = selC r j (loop t) (loopRN (e,p))
  loopRN' _{-None-} = None

-- Erase all types disjoint from base i in bdd b to their else branch.
eraseDisjointsC :: TR -> Base -> BDD -> BDD
eraseDisjointsC r i b0 = loop b0 where
  loop (BDD p None) = BDD p None
  loop (BDD p e) = BDD p $ loopRN (e, (i, r))
  loopRN = memoizeIdem1 eraseDisjointsCTable loopRN'
  loopRN' (Sel j t e, p@(i',r'))
    | j < i' && tr r' j i' == Disjoint = loopRN (e,p)
    | otherwise = selC r j (loop t) (loopRN (e,p))
  loopRN' _{-None-} = None

commonC :: TR -> Base -> BDD -> BDD -> Maybe BDD
commonC r i t (BDD Pos e) = BDD Pos <$> commonCRN r i t e
commonC r i t (BDD Not e) = BDD Not <$> commonCRN r i (complement t) e

{-# NOINLINE commonCMemoTable #-}
commonCMemoTable :: MemoTable (BDD, RNBDD, (Base, TR)) (Maybe RNBDD)
commonCMemoTable = unsafePerformIO mkMemo

commonCRN :: TR -> Base -> BDD -> RNBDD -> Maybe RNBDD
commonCRN r c t0 e0 = loop t0 e0 where
  loop0 t (BDD Pos e) = BDD Pos <$> loop t e
  loop0 t (BDD Not e) = BDD Not <$> loop (complement t) e
  loop Top None = Nothing
  loop Bot None = Just None
  loop (BDD Pos t) e | t == e = Just e
  loop t   e   = loop' (t, e, (c, r))
  loop' = memoize commonCMemoTable loop''
  loop'' (t@(bdd -> Select it tt et), e@(Sel ie te ee), _) =
    case compare it ie of
      GT -> thenHigh it tt et e
      EQ -> selMC r it (loop0 tt te) (loop et ee)
      LT -> elseHigh t ie te ee
  loop'' (bdd -> Select it tt et, e, _) = thenHigh it tt et e
  loop'' (t, Sel ie te ee, _) = elseHigh t ie te ee
  loop'' _ = error "common: unreachable"
  thenHigh it tt et e
    | tr r it c == Subtype = selC r it tt <$> e'
    | otherwise = selMC r it (loop0 tt (eraseDisjointsC r it (BDD Pos e))) e'
    where e' = loop et es
          BDD Pos es = eraseSubtypesC r it (BDD Pos e)
  elseHigh t ie te ee
    | tr r ie c == Disjoint = selC r ie te <$> e'
    | otherwise = selMC r ie (loop0 (eraseDisjointsC r ie t) te) e'
    where e' = loop (eraseSubtypesC r ie t) ee

{-# NOINLINE intersectTable #-}
intersectTable :: MemoTable (BDD, BDD, TR) BDD
intersectTable = unsafePerformIO mkMemo

-- Intersect two types already in canonical form,
-- returning a canonical form with respect to the given type relation.
intersect :: TR -> BDD -> BDD -> BDD
intersect r a0 b0 = loop a0 b0 where
  loop a b | traceShow ("i",a,b,isCanon r a, isCanon r b) False = undefined
  loop a b = traceShow ("r",a,b,res,isCanon r res) res
    where res = loop1 a b
  loop1 Bot _ = Bot
  loop1 Top b = b
  loop1 _ Bot = Bot
  loop1 a Top = a
  loop1 a@(BDD sa ar) (BDD sb br)
    | ar == br = if sa == sb then a else Bot
  loop1 a b
    | metric a >= metric b = loop' (a,b,r)
    | otherwise = loop' (b,a,r)
  loop' = memoize intersectTable loop''
  loop'' (a,b,_) | traceShow ("j",a,b) False = undefined
  loop'' (bdd -> Select va ta ea, bdd -> Select vb tb eb, _)
    | va == vb = selectC r va (ta `loop` tb) (ea `loop` eb)
  loop'' (bdd -> Select va ta ea, b, _) =
    selectC r va (loop ta (eraseDisjointsC r va b)) (loop ea (eraseSubtypesC r va b))
  loop'' _ = error "basicIntersect: unreachable"
