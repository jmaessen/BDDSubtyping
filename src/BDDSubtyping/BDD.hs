{-# LANGUAGE PatternSynonyms, ViewPatterns #-}
module BDDSubtyping.BDD(
  BDD, TR, Base, BDDPat(..), pattern Bot, pattern Top,
  select, base, root, size, rightmost, bdd,
  bddBases, model, modelDiff,
  basicUnion, basicIntersect, basicDifference, complement,
  eraseSubtypes, eraseDisjoints, fullyErase,
  common
) where
import BDDSubtyping.DAG(DAG, Relatedness(..), tr)
import Control.Monad(liftM2)

type Base = Int

-- We use right-negative ROBDDs with higher Bases
-- at the top (descending variable order), with
-- supertypes having higher numbers than subtypes
-- (consistent with topological ordering).

data Sense = Not | Pos deriving (Eq, Ord, Show)

data BDD = BDD Sense RNBDD deriving (Eq, Ord, Show)

data RNBDD = None | Sel Base BDD RNBDD
  deriving (Eq, Ord, Show)

-- Take the complement of a BDD. O(1).
complement :: BDD -> BDD
complement (BDD Pos t) = BDD Not t
complement (BDD Not t) = BDD Pos t

pattern Bot :: BDD
pattern Bot = BDD Pos None

pattern Top :: BDD
pattern Top = BDD Not None

data BDDPat = BotP | Select Base BDD BDD | TopP deriving (Show)

-- A pattern matcher for BDDs that abstracts away RNBDD.
bdd :: BDD -> BDDPat
bdd (BDD Pos None) = BotP
bdd (BDD Not None) = TopP
bdd (BDD Pos (Sel v t e)) = Select v t (BDD Pos e)
bdd (BDD Not (Sel v (BDD Not t) e)) = Select v (BDD Pos t) (BDD Not e)
bdd (BDD Not (Sel v (BDD Pos t) e)) = Select v (BDD Not t) (BDD Not e)

-- Fundamental select smart constructor that just deals with BDD / RNBDD conversion.
sel :: Base -> BDD -> BDD -> BDD
sel i t (BDD Pos e) = BDD Pos (Sel i t e)
sel i (BDD Pos t) (BDD Not e) = BDD Not (Sel i (BDD Not t) e)
sel i (BDD Not t) (BDD Not e) = BDD Not (Sel i (BDD Pos t) e)

-- A singleton BDD representing base type i
base :: Base -> BDD
base i = sel i Top Bot

-- Basic select smart constructor that handles elimination.
select :: Base -> BDD -> BDD -> BDD
select i t e
  | t == e = e
  | otherwise = sel i t e

type TR = DAG

-- By convention Top/Bot have a root of (-1) which is otherwise invalid.
root :: BDD -> Base
root (BDD _ (Sel i _ _)) = i
root _ = -1

-- Given base type relation TR, does bdd type t *fully* contain base type b?
bddBases :: TR -> BDD -> (Base -> Bool)
bddBases r (BDD Pos t) = rnbddBases r t
bddBases r (BDD Not t) = not . rnbddBases r t

rnbddBases :: TR -> RNBDD -> (Base -> Bool)
rnbddBases _ None = const False
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
-- and the complement of Bases less than its RNBDD.
-- So we can find a BDD's behavior on all types by enumerating
-- its behavior on types up to (root bdd + 1), with the last
-- type standing in for its behavior on all larger Bases.
model :: TR -> BDD -> [Bool]
model r b = map (bddBases r b) [0..root b + 1]

-- Model difference.  We want to use the model for the highest root.
-- This is designed to compare models for non-canonical types.
-- Returns a list of bases at which the models differ.
-- This will be empty if the models match.
modelDiff :: TR -> BDD -> BDD -> [Base]
modelDiff r a b = filter (\i -> ab i /= bb i) [0..(root a `max` root b) + 1]
  where ab = bddBases r a
        bb = bddBases r b

-- There's one interesting binary operation on BDDs, basic union (we
-- can derive intersection and different using complement).  O(mn).
-- Note that basic union is oblivious to type relation, and
-- thus results with the same model can differ!
basicUnion :: BDD -> BDD -> BDD
basicUnion a@(bdd -> TopP) _ = a
basicUnion (bdd -> BotP) b = b
basicUnion a@(bdd -> Select va ta ea) b@(bdd -> Select vb tb eb) =
  case compare va vb of
    GT -> select va (ta `basicUnion` b)  (ea `basicUnion` b)
    EQ -> select va (ta `basicUnion` tb) (ea `basicUnion` eb)
    LT -> select vb (a  `basicUnion` tb) (a  `basicUnion` eb)
basicUnion _ b@(bdd -> TopP) = b
basicUnion a _ {- @(bdd -> BotP) -} = a

basicIntersect :: BDD -> BDD -> BDD
basicIntersect a b = complement $ basicUnion (complement a) (complement b)

basicDifference :: BDD -> BDD -> BDD
basicDifference a b = complement $ basicUnion (complement a) b

-- Erase all strict subtypes of base i in bdd b to their else branch.
eraseSubtypes :: TR -> Base -> BDD -> BDD
eraseSubtypes trd i (bdd -> Select j t e)
  | j <= i && tr trd j i == Subtype = e
  | otherwise = select j (eraseSubtypes trd i t) (eraseSubtypes trd i e)
eraseSubtypes _ _ leaf = leaf

-- Erase all types disjoint from base i in bdd b to their else branch.
eraseDisjoints :: TR -> Base -> BDD -> BDD
eraseDisjoints r i (bdd -> Select j t e)
  | tr r j i == Disjoint = e
  | otherwise = select j (eraseDisjoints r i t) (eraseDisjoints r i e)
eraseDisjoints _ _ leaf = leaf

-- Recursively erase disjoint types from the then-branch and
-- subtypes from the else-branch all the way down the BDD,
-- working top-down (to minimize node count).  O(n^2).
fullyErase :: TR -> BDD -> BDD
fullyErase r (bdd -> Select i t e) =
  select i
         (fullyErase r (eraseDisjoints r i t))
         (fullyErase r (eraseSubtypes  r i e))
fullyErase _ leaf = leaf

select' :: Base -> Maybe BDD -> Maybe BDD -> Maybe BDD
select' i = liftM2 (select i)

common :: TR -> Base -> BDD -> BDD -> Maybe BDD
common r c t@(bdd -> Select it tt et) e@(bdd -> Select ie te ee) =
  case compare it ie of
    GT -> commonThenHigh r c it tt et e
    EQ -> select' it (common r c tt te) (common r c et ee)
    LT -> commonElseHigh r c t ie te ee
common r c (bdd -> Select it tt et) e = commonThenHigh r c it tt et e
common r c t (bdd -> Select ie te ee) = commonElseHigh r c t ie te ee
common _   _ Top Bot = Nothing
common _   _ Bot Top = Nothing
common _   _ Top Top = Just Top
common _   _ _   _   = Just Bot -- Bot Bot

commonThenHigh :: TR -> Base -> Base -> BDD -> BDD -> BDD -> Maybe BDD
commonThenHigh r c it tt et e
  | tr r it c == Subtype = select' it (Just tt) (common r c et e)
  | otherwise = select' it (common r c tt e) (common r c et e)

commonElseHigh :: TR -> Base -> BDD -> Base -> BDD -> BDD -> Maybe BDD
commonElseHigh r c t ie te ee
  | tr r ie c == Disjoint = select' ie (Just te) (common r c t ee)
  | otherwise = select' ie (common r c t te) (common r c t ee)

size :: BDD -> Int
size b = sizeb b where
  sizeb (BDD _ rnb) = sizernb rnb
  sizernb (Sel _ t e) = 1 + sizeb t + sizernb e
  sizernb _ = 0
