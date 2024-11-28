{-# LANGUAGE PatternSynonyms, ViewPatterns #-}
module BDDSubtyping.BDD(
  BDD, TR, Base, BDDPat(..), pattern Bot, pattern Top,
  select, base, root, size, rightmost, bdd,
  bddBases, model, modelDiff,
  basicUnion, basicIntersect, basicDifference, complement,
  eraseSubtypes, eraseDisjoints, fullyErase,
  common, commonOrErase
) where
import BDDSubtyping.DAG(DAG, Relatedness(..), tr)
import Control.Monad(liftM2)

type Base = Int

-- We use right-negative ROBDDs with higher Bases
-- at the top (descending variable order), with
-- supertypes having higher numbers than subtypes
-- (consistent with topological ordering).

data Sense = Not | Pos deriving (Eq, Ord, Show)

data BDD = BDD Sense RNBDD deriving (Eq, Ord)

data RNBDD = None | Sel Base {-# UNPACK #-}!BDD RNBDD
  deriving (Eq, Ord)

instance Show BDD where
  showsPrec _ Bot = ("Bot"++)
  showsPrec _ Top = ("Top"++)
  showsPrec p (BDD Pos b) = showsPrec p b
  showsPrec _ (BDD Not b) = showParen True (("complement "++) . shows b)

instance Show RNBDD where
  showsPrec _ None = ("Bot"++)
  showsPrec _ (Sel i Top None) = showParen True (("base "++) . shows i)
  showsPrec _ (Sel i t e) =
    showParen True
      (("select "++) . shows i . (' ':) . shows t . (' ':) . shows e)

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
eraseSubtypes r i (bdd -> Select j t e)
  | j <= i && tr r j i == Subtype = eraseSubtypes r i e
  | otherwise = select j (eraseSubtypes r i t) (eraseSubtypes r i e)
eraseSubtypes _ _ leaf = leaf

-- Erase all types disjoint from base i in bdd b to their else branch.
eraseDisjoints :: TR -> Base -> BDD -> BDD
eraseDisjoints r i (bdd -> Select j t e)
  | tr r j i == Disjoint = eraseDisjoints r i e
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
common r c t0 e0 = loop t0 e0 where
  loop t@(bdd -> Select it tt et) e@(bdd -> Select ie te ee) =
    case compare it ie of
      GT -> thenHigh it tt et e
      EQ -> select' it (loop tt te) (loop et ee)
      LT -> elseHigh t ie te ee
  loop (bdd -> Select it tt et) e = thenHigh it tt et e
  loop t (bdd -> Select ie te ee) = elseHigh t ie te ee
  loop Top Bot = Nothing
  loop Bot Top = Nothing
  loop Top Top = Just Top
  loop _   _   = Just Bot -- Bot Bot
  thenHigh it tt et e
    | tr r it c == Subtype = select' it (Just tt) (loop et e)
    | otherwise = select' it (loop tt e) (loop et e)
  elseHigh t ie te ee
    | tr r ie c == Disjoint = select' ie (Just te) (loop t ee)
    | otherwise = select' ie (loop t te) (loop t ee)

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
  loop _   _   = (Bot, Bot, Just Bot)
  both i tt et te ee = (select i tt' et', select i te' ee', select' i t' e')
    where (tt', te', t') = loop tt te
          (et', ee', e') = loop et ee
  same Subtype i tt et _ ee = both i tt et ee ee
  same Disjoint i _ et te ee = both i et et te ee
  same MayIntersect i tt et te ee = both i tt et te ee
  thenHigh Disjoint _ _ et e = loop et e
  thenHigh Subtype it tt et e = (select it tt' et', ee', select' it (Just tt') e')
    where tt' = eraseDisjoints r c tt
          (et', ee', e') = loop et e
  thenHigh MayIntersect it tt et e = both it tt et e e
  elseHigh Subtype t _ _ ee = loop t ee
  elseHigh Disjoint t ie te ee = (et', select ie te' ee', select' ie (Just te') e')
    where te' = eraseSubtypes r c te
          (et', ee', e') = loop t ee
  elseHigh MayIntersect t ie te ee = both ie t t te ee

size :: BDD -> Int
size b = sizeb b where
  sizeb (BDD _ rnb) = sizernb rnb
  sizernb (Sel _ t e) = 1 + sizeb t + sizernb e
  sizernb _ = 0
