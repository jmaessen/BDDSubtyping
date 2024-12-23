{-# LANGUAGE PatternSynonyms, ViewPatterns #-}
module BDDSubtyping.BDD(
  BDD, TR, Base, BDDPat(..), pattern Bot, pattern Top,
  toGraph, fromGraph,
  select, base, exact, exactly,
  root, size, rightmost, bdd, FV(..),
  bddBases, model, modelDiff,
  basicUnion, basicIntersect, basicDifference, complement,
  basicImplies, basicEqv, trToBDD,
  eraseSubtypes, eraseDisjoints,
  common, commonOrErase,
  canonS, isCanon,
  isBottom, relate, relateNaive, isDisjoint,
  commute, rightComplement, leftComplement, Relation(..),
  sel, mergeEq, Sense(..) -- For Debug
) where
import Control.Monad(liftM2)
import qualified Data.IntMap.Strict as M
import Data.IntMap((!))
import qualified Data.Map.Strict as DM
import System.IO.Unsafe(unsafePerformIO) -- For memo tables

import Data.NaiveMemo(ConsId, getId, MemoTable, mkMemo, memoize, memoizeIdem1)
import BDDSubtyping.DAG(DAG, Relatedness(..), tr, unMkDag)
import BDDSubtyping.BDDInternal

import Debug.Trace(trace, traceShow)

-- Take the complement of a BDD. O(1).
complement :: BDD -> BDD
complement (BDD Pos t) = BDD Not t
complement (BDD Not t) = BDD Pos t

data BDDPat r = BotP | Select Base r r | Exact Base Bool r | TopP deriving (Eq, Ord, Show)

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
  loop' (Exact i m e) gr hc =
    let (e', gre, hce) = loop e gr hc
        v = Exact i m e'
    in node v gre hce
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
  convert (Exact i m e) = exact i m (g'!e)

-- A pattern matcher for BDDs that abstracts away RNBDD.
bdd :: BDD -> BDDPat BDD
bdd (BDD Pos (Sel v t e)) = Select v t (BDD Pos e)
bdd (BDD Not (Sel v (BDD Not t) e)) = Select v (BDD Pos t) (BDD Not e)
bdd (BDD Not (Sel v (BDD Pos t) e)) = Select v (BDD Not t) (BDD Not e)
bdd (BDD Pos (Eq v e)) = Exact v True (BDD Pos e)
bdd (BDD Not (Eq v e)) = Exact v False (BDD Not e)
bdd (BDD Pos _{-None-}) = BotP
bdd (BDD Not _{-None-}) = TopP

-- Smart constructor that handles elimination.
sel :: Base -> BDD -> RNBDD -> RNBDD
sel _ (BDD Pos t) e | t == e = e
sel i t (Eq i' e) | i == i' = sel i t e
sel _ (BDD Pos t0@(Eq _ et0)) e0
  | allEq et0, Just r <- mergeEq Pos t0 e0 = r
  where
    allEq None = True
    allEq (Eq _ e) = allEq e
    allEq _ = False
sel i t e = Sel i t e

mergeEq :: Sense -> RNBDD -> RNBDD -> Maybe RNBDD
mergeEq _   None e = Just e
mergeEq Pos t None = Just t
mergeEq Not _ None = Just None
mergeEq pn  t@(Eq it et) (Sel ie te ee)
  | it < ie = sel ie <$> mergeEq' pn t te <*> mergeEq pn t ee
  | it == ie = sel ie <$> mergeEq' pn t te <*> mergeEq pn et ee
mergeEq pn  t@(Eq it _) (Eq ie ee)
  | it < ie = Eq ie <$> mergeEq pn t ee
mergeEq Pos (Eq it et) (Eq ie ee)
  | it == ie = Eq ie <$> mergeEq Pos et ee
mergeEq Not (Eq it _) (Eq ie _)
  | it == ie = Nothing
mergeEq Pos (Eq it et) e = Eq it <$> mergeEq Pos et e
mergeEq Not (Eq _ et) e = mergeEq Not et e
mergeEq _ _ _ = error "mergeEq: unreachable"
mergeEq' :: Sense -> RNBDD -> BDD -> Maybe BDD
mergeEq' pn t (BDD pn' e) = BDD s <$> mergeEq s t e
  where s = if pn == pn' then Pos else Not

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

-- A singleton BDD representing exactly the type i
exactly :: Base -> BDD
exactly i = BDD Pos $ Eq i None

-- A singleton BDD representing base type i
base :: Base -> BDD
base i = select0 i Top Bot

-- Basic exact smart constructor that handles elimination and RNBDD conversion
exact :: Base -> Bool -> BDD -> BDD
exact v True (BDD Pos b) = BDD Pos $ Eq v b -- b union v
exact v False (BDD Not b) = BDD Not $ Eq v b -- (not b) minus v == not (b union v)
exact _ _ b = b

type TR = DAG

-- By convention Top/Bot have a root of (-1) which is otherwise invalid.
root :: BDD -> Base
root (BDD _ rn) = rootRN rn

rootRN :: RNBDD -> Base
rootRN (Sel i _ _) = i
rootRN (Eq i _) = i
rootRN _ = -1

-- The height is (-1) for Top/Bot, and twice the root for other nodes, plus one for Sel.
height :: BDD -> (Base, ConsId)
height (BDD _ rn) = heightRN rn

heightRN :: RNBDD -> (Base, ConsId)
heightRN a@(Sel i _ _) = (i + i + 1, getId a)
heightRN a@(Eq i _) = (i + i, getId a)
heightRN _ = (-1,0)

-- Given base type relation TR, does bdd type t *fully* contain base type b?
bddBases :: TR -> BDD -> (Base -> Bool)
bddBases r (BDD Pos t) = rnbddBases r t
bddBases r (BDD Not t) = not . rnbddBases r t

rnbddBases :: TR -> RNBDD -> (Base -> Bool)
rnbddBases r (Eq v e) =
  let eBases = rnbddBases r e
  in \i -> v == i || eBases i
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

{-# NOINLINE intersectMemoTable #-}
intersectMemoTable :: MemoTable (BDD, BDD) BDD
intersectMemoTable = unsafePerformIO $ mkMemo

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
    | height a >= height b = loop' (a,b)
    | otherwise = loop' (b,a)
  loop' = memoize intersectMemoTable loop''
  loop'' (bdd -> Select va ta ea, bdd -> Select vb tb eb)
    | va == vb = select va (ta `loop` tb) (ea `loop` eb)
  loop'' (bdd -> Select va ta ea, b@(bdd -> Exact vb _ eb))
    | va == vb = select va (loop ta b) (loop ea eb)
  loop'' (bdd -> Select va ta ea, b) =
    select va (loop ta b)  (loop ea b)
  loop'' (bdd -> Exact va ma ea, bdd -> Exact vb mb eb)
    | va == vb = exact va (ma && mb) (loop ea eb)
  loop'' (bdd -> Exact va ma ea, b) =
    exact' va ma (loop ea b) b
  loop'' _ = error "basicIntersect: unreachable"
  exact' v True e b
    | rightmost b = exact v True e
    | otherwise = e
  exact' v False e _ = exact v False e

basicUnion :: BDD -> BDD -> BDD
basicUnion a b = complement $ basicIntersect (complement a) (complement b)

basicDifference :: BDD -> BDD -> BDD
basicDifference a b = basicIntersect a (complement b)

basicImplies :: BDD -> BDD -> BDD
basicImplies a b = complement (basicDifference a b)

basicEqv :: BDD -> BDD -> BDD
basicEqv a b = basicImplies a b `basicIntersect` basicImplies b a

-- Convert TR to equivalent BDD.
-- Type exclusion requires us to explicitly include the notion of exact types!
-- Ex: Brown ∩ Dog cannot be exactly Brown or Dog, it must be *strictly* less.
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
  loopRN' (Eq j e, p@(i',r'))
    | j <= i' && tr r' j i' == Subtype = loopRN (e,p)
    | otherwise = Eq j (loopRN (e,p))
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
  loopRN' (Eq j e, p@(i',r'))
    | j <= i' && tr r' j i' /= Subtype = loopRN (e,p)
    | otherwise = Eq j (loopRN (e,p))
  loopRN' _{-None-} = None

selectM :: Base -> Maybe BDD -> Maybe BDD -> Maybe BDD
selectM i = liftM2 (select i)

{-# NOINLINE commonMemoTable #-}
commonMemoTable :: MemoTable (BDD, BDD, (Base, TR)) (Maybe BDD)
commonMemoTable = unsafePerformIO mkMemo

common :: TR -> Base -> BDD -> BDD -> Maybe BDD
common r c t0 e0 = loop t0 e0 where
  loop Top Bot = Nothing
  loop Bot Top = Nothing
  loop Top Top = Just Top
  loop Bot Bot = Just Bot -- Bot Bot
  loop a   b   = loop' (a, b, (c, r))
  loop' = memoize commonMemoTable loop''
  loop'' (t@(bdd -> Select it tt et), e@(bdd -> Select ie te ee), _) =
    case compare it ie of
      GT -> thenHigh it tt et e
      EQ -> selectM it (loop tt te) (loop et ee)
      LT -> elseHigh t ie te ee
  loop'' (bdd -> Select it tt et, e@(bdd -> Exact ie _ _), _)
    | it >= ie = thenHigh it tt et e
  loop'' (t@(bdd -> Exact it _ _), bdd -> Select ie te ee, _)
    | ie >= it = elseHigh t ie te ee
  loop'' (t@(bdd -> Exact it mt et), e@(bdd -> Exact ie me ee), _) =
    case compare it ie of
      GT -> exact it mt <$> loop et e
      -- The EQ case shouldn't happen in properly-erased BDDs.
      EQ | mt /= me -> Nothing
         | otherwise -> exact it mt <$> loop et ee
      LT -> exact ie me <$> loop t ee
  loop'' (bdd -> Exact it mt et, e, _) = exact it mt <$> loop et e
  loop'' (t, bdd -> Exact ie me ee, _) = exact ie me <$> loop t ee
  loop'' (bdd -> Select it tt et, e, _) = thenHigh it tt et e
  loop'' (t, bdd -> Select ie te ee, _) = elseHigh t ie te ee
  loop'' _ = error "common: unreachable"
  thenHigh it tt et e
    | tr r it c == Subtype = select it tt <$> loop et e
    | otherwise = selectM it (loop tt e) (loop et e)
  elseHigh t ie te ee
    | tr r ie c == Disjoint = select ie te <$> loop t ee
    | otherwise = selectM ie (loop t te) (loop t ee)

{-# NOINLINE coeMemoTable #-}
coeMemoTable :: MemoTable (BDD, BDD, (Base, TR)) (BDD, BDD, Maybe BDD)
coeMemoTable = unsafePerformIO mkMemo

-- Fused common and erase: should equal:
-- (eraseDisjoints r c t, eraseSubtypes r c e,
--  common r c (eraseDisjoints r c t) (eraseSubtypes r c e))
commonOrErase :: TR -> Base -> BDD -> BDD -> (BDD, BDD, Maybe BDD)
commonOrErase r c t0 e0 = loop t0 e0 where
  loop Top Bot | trace "TB" True = (Top, Bot, Nothing)
  loop Bot Top | trace "BT" True = (Bot, Top, Nothing)
  loop Top Top | trace "TT" True = (Top, Top, Just Top)
  loop Bot Bot | trace "BB" True = (Bot, Bot, Just Bot)
  loop t e = loop' (t,e,(c,r))
  loop' = memoize coeMemoTable loop''
  loop'' (t@(bdd -> Select it tt et), e@(bdd -> Select ie te ee), _) =
    case (compare it ie, tr r it c) of
      (GT, cmp) -> trace "SSG" $ thenHigh cmp it tt et e
      (EQ, cmp) -> trace "SSE" $ same cmp it tt et te ee
      (LT, _) -> trace "SSE" elseHigh (tr r ie c) t ie te ee
  loop'' (bdd -> Select it tt et, e@(bdd -> Exact ie _ _), _)
    | it >= ie = trace "SE" $ thenHigh (tr r it c) it tt et e
  loop'' (t@(bdd -> Exact it _ _), bdd -> Select ie te ee, _)
    | ie >= it = trace "ES" $ elseHigh (tr r ie c) t ie te ee
  loop'' (t@(bdd -> Exact it mt et), e@(bdd -> Exact ie me ee), _) =
    case compare it ie of
      GT -> trace "EEG" $ thenExact it mt et e
      EQ | tr r it c == Subtype -> trace "EEES" (exact it mt et', ee', exact it mt <$> e')
         | otherwise -> trace "EEE" (et', exact ie me ee', exact ie me <$> e')
         where (et', ee', e') = loop et ee
      LT -> trace "EEL" $ elseExact t ie me ee
  loop'' (bdd -> Exact it mt et, e, _) = trace "E_" $ thenExact it mt et e
  loop'' (t, bdd -> Exact ie me ee, _) = trace "_E" $ elseExact t ie me ee
  loop'' (bdd -> Select it tt et, e, _) = trace "S_" $ thenHigh (tr r it c) it tt et e
  loop'' (t, bdd -> Select ie te ee, _) = trace "_S" $ elseHigh (tr r ie c) t ie te ee
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
  thenExact :: Base -> Bool -> BDD -> BDD -> (BDD, BDD, Maybe BDD)
  thenExact it mt et e
    | tr r it c /= Subtype = f
    | otherwise = (exact it mt et', ee', exact it mt <$> e')
    where f@(et', ee', e') = loop et e
  elseExact :: BDD -> Base -> Bool -> BDD -> (BDD, BDD, Maybe BDD)
  elseExact t ie me ee
    | tr r ie c == Subtype = f
    | otherwise = (et', exact ie me ee', exact ie me <$> e')
    where f@(et', ee', e') = loop t ee

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
  loop'' (bdd -> Exact i m e, _) = exact i m $ loop e
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
  loop (BDD _ (Eq _ _)) = False
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
    | heightRN a >= heightRN b = loopRN' (a, b, r)
    | otherwise = commute $ loopRN' (b, a, r)
  loopRN' = loopRN''
  loopRN'' (Sel ia ta ea, Sel ib tb eb, _)
    | ia == ib = loop ta tb <> loopRN ea eb
  loopRN'' (Sel ia ta ea, b, _) =
    loop ta (canonS r (eraseDisjoints r ia (BDD Pos b))) <>
    commute (loop1 (canonS r (eraseSubtypes r ia (BDD Pos b))) ea)
  loopRN'' (Eq ia ea, Eq ib eb, _)
    | ia == ib =
      Relation True True False True <> loopRN ea eb
  loopRN'' (Eq _ ea, b, _) =
    Relation False True True True <> loopRN ea b
  loopRN'' _ = error "Unreachable in loopRN''"
