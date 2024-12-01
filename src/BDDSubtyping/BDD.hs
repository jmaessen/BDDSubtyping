{-# LANGUAGE PatternSynonyms, ViewPatterns #-}
module BDDSubtyping.BDD(
  BDD, TR, Base, BDDPat(..), pattern Bot, pattern Top,
  toGraph, fromGraph,
  select, base, exact, exactly,
  root, size, rightmost, bdd, FV(..),
  bddBases, model, modelDiff,
  basicUnion, basicIntersect, basicDifference, complement,
  basicImplies, basicEqv, trToBDD,
  eraseSubtypes, eraseDisjoints, fullyErase,
  common, commonOrErase,
  canonTD, canonBU, canonS, canonW,
  isBottom, relate, commute, Relation(..)
) where
import BDDSubtyping.DAG(DAG, Relatedness(..), tr, unMkDag)
import Control.Monad(liftM2)
import qualified Data.IntSet as S
import qualified Data.IntMap.Strict as M
import qualified Data.Map.Strict as DM
import Data.IntMap((!))

type Base = Int

-- We use right-negative ROBDDs with higher Bases
-- at the top (descending variable order), with
-- supertypes having higher numbers than subtypes
-- (consistent with topological ordering).

data Sense = Not | Pos deriving (Eq, Ord, Show)

data BDD = BDD Sense RNBDD deriving (Eq, Ord)

data RNBDD
  = None
  | Eq Base RNBDD
  | Sel Base {-# UNPACK #-}!BDD RNBDD
  deriving (Eq, Ord)

instance Show BDD where
  showsPrec _ Bot = ("Bot"++)
  showsPrec _ Top = ("Top"++)
  showsPrec p (BDD Pos b) = showsPrec p b
  showsPrec _ (BDD Not b) = showParen True (("complement "++) . shows b)

instance Show RNBDD where
  showsPrec _ None = ("Bot"++)
  showsPrec _ (Sel i Top None) = showParen True (("base "++) . shows i)
  showsPrec _ (Eq i e) = showParen True (("exact "++) . shows i . (" True "++) . shows e)
  showsPrec _ (Sel i t e) =
    showParen True
      (("select "++) . shows i . (' ':) . shows t . (' ':) . shows e)

class Show a => FV a where
  fv :: a -> S.IntSet
  rename :: M.IntMap Base -> a -> a
  showIt :: a -> ShowS
  showIt = shows

instance FV BDD where
  fv (BDD _ b) = fv b
  rename r (BDD p b) = BDD p (rename r b)

instance FV RNBDD where
  fv None = mempty
  fv (Sel i t e) = S.insert i (fv t <> fv e)
  fv (Eq i e) = S.insert i (fv e)
  rename _ None = None
  rename r (Sel i t e) = sel (r!i) (rename r t) (rename r e)
  rename r (Eq i e) = Eq (r!i) $ rename r e

-- Take the complement of a BDD. O(1).
complement :: BDD -> BDD
complement (BDD Pos t) = BDD Not t
complement (BDD Not t) = BDD Pos t

pattern Bot :: BDD
pattern Bot = BDD Pos None

pattern Top :: BDD
pattern Top = BDD Not None

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
bdd (BDD Pos None) = BotP
bdd (BDD Not None) = TopP
bdd (BDD Pos (Sel v t e)) = Select v t (BDD Pos e)
bdd (BDD Not (Sel v (BDD Not t) e)) = Select v (BDD Pos t) (BDD Not e)
bdd (BDD Not (Sel v (BDD Pos t) e)) = Select v (BDD Not t) (BDD Not e)
bdd (BDD Pos (Eq v e)) = Exact v True (BDD Pos e)
bdd (BDD Not (Eq v e)) = Exact v False (BDD Not e)

-- Basic sel smart constructor that handles elimination.
sel :: Base -> BDD -> RNBDD -> RNBDD
sel _ (BDD Pos t) e | t == e = e
sel i t e = Sel i t e

-- Fundamental select smart constructor that just deals with BDD / RNBDD conversion.
select0 :: Base -> BDD -> BDD -> BDD
select0 i t (BDD Pos e) = BDD Pos (Sel i t e)
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
root (BDD _ (Sel i _ _)) = i
root (BDD _ (Eq i _)) = i
root _ = -1

-- Given base type relation TR, does bdd type t *fully* contain base type b?
bddBases :: TR -> BDD -> (Base -> Bool)
bddBases r (BDD Pos t) = rnbddBases r t
bddBases r (BDD Not t) = not . rnbddBases r t

rnbddBases :: TR -> RNBDD -> (Base -> Bool)
rnbddBases _ None = const False
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
  loop a@(bdd -> Select va ta ea) b@(bdd -> Select vb tb eb) =
    case compare va vb of
      GT -> select va (ta `loop` b)  (ea `loop` b)
      EQ -> select va (ta `loop` tb) (ea `loop` eb)
      LT -> select vb (a  `loop` tb) (a  `loop` eb)
  loop a@(bdd -> Exact va ma ea) b@(bdd -> Exact vb mb eb) =
    case compare va vb of
      GT -> exact va ma (loop ea b)
      EQ -> exact va (ma && mb) (loop ea eb)
      LT -> exact vb mb (loop a eb)
  loop a@(bdd -> Select va ta ea) b@(bdd -> Exact vb mb eb) =
    case compare va vb of
      GT -> select va (loop ta b) (loop ea b)
      EQ -> select va (loop ta b) (loop ea eb)
      LT -> exact vb mb (loop a eb)
  loop a{- Exact _ _ _ -} b{- Select _ _ _ -} = loop b a

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

-- Erase all strict subtypes of base i in bdd b to their else branch.
eraseSubtypes :: TR -> Base -> BDD -> BDD
eraseSubtypes r i b0 = loop b0 where
  loop (BDD p e) = BDD p $ loopRN e
  loopRN (Sel j t e)
    | j < i && tr r j i == Subtype = loopRN e
    | otherwise = sel j (loop t) (loopRN e)
  loopRN (Eq j e)
    | j <= i && tr r j i == Subtype = loopRN e
    | otherwise = Eq j (loopRN e)
  loopRN None = None

-- Erase all types disjoint from base i in bdd b to their else branch.
eraseDisjoints :: TR -> Base -> BDD -> BDD
eraseDisjoints r i b0 = loop b0 where
  loop (BDD p e) = BDD p $ loopRN e
  loopRN (Sel j t e)
    | j < i && tr r j i == Disjoint = loopRN e
    | otherwise = sel j (loop t) (loopRN e)
  loopRN (Eq j e)
    | j < i && tr r j i /= Subtype = loopRN e
    | otherwise = Eq j (loopRN e)
  loopRN None = None

-- Recursively erase disjoint types from the then-branch and
-- subtypes from the else-branch all the way down the BDD,
-- working top-down (to minimize node count).  O(n^2).
fullyErase :: TR -> BDD -> BDD
fullyErase r (bdd -> Select i t e) =
  select i
         (fullyErase r (eraseDisjoints r i t))
         (fullyErase r (eraseSubtypes  r i e))
fullyErase _ leaf = leaf

selectM :: Base -> Maybe BDD -> Maybe BDD -> Maybe BDD
selectM i = liftM2 (select i)

common :: TR -> Base -> BDD -> BDD -> Maybe BDD
common r c t0 e0 = loop t0 e0 where
  loop t@(bdd -> Select it tt et) e@(bdd -> Select ie te ee) =
    case compare it ie of
      GT -> thenHigh it tt et e
      EQ -> selectM it (loop tt te) (loop et ee)
      LT -> elseHigh t ie te ee
  loop t@(bdd -> Select it tt et) e@(bdd -> Exact ie me ee)
    | it >= ie = thenHigh it tt et e
    | otherwise = exact ie me <$> loop t ee
  loop t@(bdd -> Exact it mt et) e@(bdd -> Select ie te ee)
    | ie >= it = elseHigh t ie te ee
    | otherwise = exact it mt <$> loop et e
  loop t@(bdd -> Exact it mt et) e@(bdd -> Exact ie me ee) =
    case compare it ie of
      LT -> exact it mt <$> loop et e
      EQ | mt == me -> exact it mt <$> loop et ee
      EQ -> Nothing
      GT -> exact ie me <$> loop t ee
  loop (bdd -> Select it tt et) e = thenHigh it tt et e
  loop t (bdd -> Select ie te ee) = elseHigh t ie te ee
  loop Top Bot = Nothing
  loop Bot Top = Nothing
  loop Top Top = Just Top
  loop _   _   = Just Bot -- Bot Bot
  thenHigh it tt et e
    | tr r it c == Subtype = select it tt <$> loop et e
    | otherwise = selectM it (loop tt e) (loop et e)
  elseHigh t ie te ee
    | tr r ie c == Disjoint = select ie te <$> loop t ee
    | otherwise = selectM ie (loop t te) (loop t ee)

-- shallowCommon :: TR -> BDD -> BDD
-- shallowCommon r (bdd -> Select i t e) =
--   maybe b id $ common r i t e
-- shallowCommon r b = b

-- Fused common and erase: should equal:
-- (eraseDisjoints r c t, eraseSubtypes r c e,
--  common r c (eraseDisjoints r c t) (eraseSubtypes r c e))
commonOrErase :: TR -> Base -> BDD -> BDD -> (BDD, BDD, Maybe BDD)
commonOrErase r c t0 e0 = loop t0 e0 where
  loop t@(bdd -> Select it tt et) e@(bdd -> Select ie te ee) =
    case (compare it ie, tr r it c) of
      (GT, cmp) -> thenHigh cmp it tt et e
      (EQ, cmp) -> same cmp it tt et te ee
      (LT, _) -> elseHigh (tr r ie c) t ie te ee
  loop (bdd -> Select it tt et) e = thenHigh (tr r it c) it tt et e
  loop t (bdd -> Select ie te ee) = elseHigh (tr r ie c) t ie te ee
  loop Top Bot = (Top, Bot, Nothing)
  loop Bot Top = (Bot, Top, Nothing)
  loop Top Top = (Top, Top, Just Top)
  loop Bot Bot = (Bot, Bot, Just Bot)
  both i tt et te ee = (select i tt' et', select i te' ee', selectM i t' e')
    where (tt', te', t') = loop tt te
          (et', ee', e') = loop et ee
  same Subtype i tt et _ ee = thenHigh Subtype i tt et ee
  same Disjoint i _ et te ee = elseHigh Disjoint et i te ee
  same MayIntersect i tt et te ee = both i tt et te ee
  thenHigh Disjoint _ _ et e = loop et e
  thenHigh Subtype it tt et e
    | tt' == et' = (et', ee', e')
    | otherwise = (select it tt' et', ee', select it tt' <$> e')
    where tt' = eraseDisjoints r c tt
          (et', ee', e') = loop et e
  thenHigh MayIntersect it tt et e = both it tt et e e
  elseHigh Subtype t _ _ ee = loop t ee
  elseHigh Disjoint t ie te ee
    | te' == ee' = (et', ee', e')
    | otherwise = (et', select ie te' ee', select ie te' <$> e')
    where te' = eraseSubtypes r c te
          (et', ee', e') = loop t ee
  elseHigh MayIntersect t ie te ee = both ie t t te ee

shallowCE :: TR -> BDD -> BDD
shallowCE r (bdd -> Select i t e) =
  case commonOrErase r i t e of
    (t', e', Nothing) -> select i t' e'
    (_, _, Just s) -> s
shallowCE _ b = b

canonTD :: TR -> BDD -> BDD
canonTD r (bdd -> Select i t e) =
  case commonOrErase r i t e of
    (t', e', Nothing) -> select i (canonTD r t') (canonTD r e')
    (_, _, Just s) -> canonTD r s
canonTD _ b = b

canonBU :: TR -> BDD -> BDD
canonBU r (bdd -> Select i t e) =
  let t' = canonBU r t
      e' = canonBU r e
  in if t' == e' then t' else shallowCE r (select0 i t' e')
canonBU _ b = b

canonS :: TR -> BDD -> BDD
canonS r (bdd -> Select i t e) =
  let t' = canonS r t
      e' = canonS r e
  in case (t' == e', commonOrErase r i t e) of
    (True, _) -> t'
    (_, (_, _, Just s)) -> canonS r s
    (_, (t'', e'', Nothing)) -> select0 i t'' e''
canonS _ b = b

canonW :: TR -> BDD -> BDD
canonW r (bdd -> Select i t e) =
  let t' = canonW r t
      e' = canonW r e
  in case (t' == e', commonOrErase r i t e) of
    (True, _) -> t'
    (_, (_, _, Just s)) -> fullyErase r s
    (_, (t'', e'', Nothing)) -> select0 i t'' e''
canonW _ b = b

size :: BDD -> Int
size b = sizeb b where
  sizeb (BDD _ rnb) = sizernb rnb
  sizernb (Sel _ t e) = 1 + sizeb t + sizernb e
  sizernb _ = 0

data Relation = Relation { isSubtype :: Bool, isSupertype :: Bool, isDisjoint :: Bool }
  deriving (Eq, Show)

instance Semigroup Relation where
  Relation sub1 sup1 dis1 <> Relation sub2 sup2 dis2 =
    Relation (sub1 && sub2) (sup1 && sup2) (dis1 && dis2)

commute :: Relation -> Relation
commute (Relation sub sup dis) = Relation sup sub dis

-- Does a type denote bottom with respect to the given type relation?
isBottom :: TR -> BDD -> Bool
isBottom r b0 = loop b0 where
  loop (BDD Pos (Sel i t e)) =
    loop (eraseDisjoints r i t) && loop (eraseSubtypes r i (BDD Pos e))
  loop (BDD Not _) = False
  loop _ {- Bot -} = True

-- Relate two types with respect to base type relation.
-- a is disjoint from b if their intersection is empty (Bot).
-- a is a subtype of b if their intersection is a, and vice versa.
relate :: TR -> BDD -> BDD -> Relation
relate r a0 b0 = loop a0 b0 where
  loop a b = const undefined (a,b,r)
