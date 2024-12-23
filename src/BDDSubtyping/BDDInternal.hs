{-# LANGUAGE PatternSynonyms, TypeFamilies #-}
module BDDSubtyping.BDDInternal(
  BDD(..), RNBDD, Sense(..), Base,
  pattern None, pattern Sel, pattern Eq,
  pattern Bot, pattern Top,
  FV(fv, rename, showIt),
  commuteBDD -- but not MemoKey.
) where
import Data.Hashable(Hashable(hashWithSalt))
import qualified Data.DescSet as S
import Data.IntMap((!))
import qualified Data.IntMap.Strict as M
import System.IO.Unsafe(unsafePerformIO)

import Data.NaiveMemo

type Base = Int

-- We use right-negative ROBDDs with higher Bases
-- at the top (descending variable order), with
-- supertypes having higher numbers than subtypes
-- (consistent with topological ordering).

data Sense = Not | Pos deriving (Eq, Ord, Show)

instance Hashable Sense where
  hashWithSalt s Not = s + 1
  hashWithSalt s Pos = s + 2

data BDD = BDD !Sense !RNBDD deriving (Eq)

instance Hashable BDD where
  hashWithSalt s (BDD d r) = (s `hashWithSalt` d) `hashWithSalt` r

-- The constuctors are hidden (C = concrete) and replaced with patterns
-- that enforce hash-consing.
data RNBDD
  = NoneC
  | EqC !ConsId !Base !RNBDD
  | SelC !ConsId !Base {-# UNPACK #-}!BDD !RNBDD

commuteBDD :: (BDD, BDD) -> (BDD, BDD)
commuteBDD t@(ab@(BDD sa a), bb@(BDD sb b))
  | (getId a, sa) <= (getId b, sb) = t
  | otherwise = (bb, ab)

instance Eq RNBDD where
  (==) = hcEq

instance Hashable RNBDD where
  hashWithSalt = hcHashWithSalt

instance HashConsable RNBDD where
  getId NoneC = 0
  getId (EqC i _ _) = i
  getId (SelC i _ _ _) = i

  setId i (EqC _ b e) = EqC i b e
  setId i (SelC _ b t e) = SelC i b t e
  setId _ _{-NoneC-} = NoneC

  EqC _ ba ea `contentEq` EqC _ bb eb =
    ba == bb && ea == eb
  SelC _ ba ta ea `contentEq` SelC _ bb tb eb =
    ba == bb && ta == tb && ea == eb
  NoneC `contentEq` NoneC = True
  _ `contentEq` _ = False

  contentHashWithSalt s (EqC _ b r) =
    (s `hashWithSalt` b) `hashWithSalt` r
  contentHashWithSalt s (SelC _ b t e) =
    ((s `hashWithSalt` b) `hashWithSalt` e) `hashWithSalt` t
  contentHashWithSalt s _{-None-} = s + 1

{-# NOINLINE hashConsTable #-}
hashConsTable :: ConsTable RNBDD
hashConsTable = unsafePerformIO $ mkCons

rnbdd :: RNBDD -> RNBDD
rnbdd = hashCons hashConsTable

instance Show BDD where
  showsPrec _ Bot = ("Bot"++)
  showsPrec _ Top = ("Top"++)
  showsPrec p (BDD Pos b) = showsPrec p b
  showsPrec _ (BDD Not b) = showParen True (("complement "++) . shows b)

instance Show RNBDD where
  showsPrec _ (Sel i Top None) = showParen True (("base "++) . shows i)
  showsPrec _ (Eq i None) = showParen True (("exactly "++) . shows i)
  showsPrec _ (Eq i e) = showParen True (("exact "++) . shows i . (" True "++) . shows e)
  showsPrec _ (Sel i t e) =
    showParen True
      (("select "++) . shows i . (' ':) . shows t . (' ':) . shows e)
  showsPrec _ _{-None-} = ("Bot"++)

none :: RNBDD
none = rnbdd NoneC

pattern None :: RNBDD
pattern None <- NoneC where
  None = none

pattern Sel :: Base -> BDD -> RNBDD -> RNBDD
pattern Sel i t e <- (SelC _ i t e) where
  Sel i t e = rnbdd (SelC 0 i t e)

pattern Eq :: Base -> RNBDD -> RNBDD
pattern Eq i e <- (EqC _ i e) where
  Eq i e = rnbdd (EqC 0 i e)

pattern Bot :: BDD
pattern Bot <- BDD Pos None where
  Bot = BDD Pos none

pattern Top :: BDD
pattern Top <- BDD Not None where
  Top = BDD Not none

class Show a => FV a where
  fv :: a -> S.Set Base
  rename :: M.IntMap Base -> a -> a
  showIt :: a -> ShowS
  showIt = shows

instance FV BDD where
  fv (BDD _ b) = fv b
  rename r (BDD p b) = BDD p (rename r b)

instance FV RNBDD where
  fv (Sel i t e)
    | S.getMax r == Just i = r
    | otherwise = S.insertLarger i r
    where r = fv t <> fv e
  fv (Eq i e) = S.insertLarger i (fv e)
  fv _{-None-} = mempty
  rename r (Sel i t e) = Sel (r!i) (rename r t) (rename r e)
  rename r (Eq i e) = Eq (r!i) $ rename r e
  rename _ _{-None-} = None

instance MemoKey RNBDD where
  type MK RNBDD = Int
  toMemoKey = getId

instance MemoKey BDD where
  type MK BDD = Int
  toMemoKey (BDD Pos r) = toMemoKey r
  toMemoKey (BDD Not r) = negate (toMemoKey r) - 1
