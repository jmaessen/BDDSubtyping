module Data.DescSet(
  Set, singleton, insertLarger, difference, intersection, toDescList, fromDescList,
  fromAscList, fromList, findMax,
  null, size, isSubsetOf, disjoint
) where
import Prelude hiding (null)
import qualified Prelude as P
import Data.Hashable(Hashable)
import Data.List(sort, group)
import Data.List.NonEmpty(NonEmpty(..))
import Data.Semigroup

newtype Set a = S { toDescList :: [a] } deriving (Eq, Ord, Hashable)

instance Show a => Show (Set a) where
  showsPrec _ (S as) = showParen True (("fromDescList "++) . showList as)

dEBUG :: Bool
dEBUG = True

fromDescList :: Ord a => [a] -> Set a
fromDescList as@(_:at)
  | dEBUG && or (zipWith (<=) as at) = error "fromDescList: not descending"
fromDescList as = S as

singleton :: Ord a => a -> Set a
singleton a = S [a]

-- Insert element larger than any element currently in set.
insertLarger :: Ord a => a -> Set a -> Set a
insertLarger a (S (a':_))
  | dEBUG && a <= a' = error "insertLarger: smaller"
insertLarger a (S as) = S (a:as)

instance (Ord a) => Semigroup (Set a) where
  S as0 <> S bs0 = S $ loop as0 bs0 where
    loop [] b = b
    loop a [] = a
    loop as@(a:at) bs@(b:bt) =
      case compare a b of
        GT -> a : loop at bs
        EQ -> a : loop at bt
        LT -> b : loop as bt
  sconcat (a :| b) = mconcat (a:b)

instance (Ord a) => Monoid (Set a) where
  mempty = S []
  mconcat [] = S []
  mconcat [s] = s
  mconcat [a,b] = a <> b
  mconcat ss = fromList $ concat $ map (reverse . toDescList) ss

difference :: Ord a => Set a -> Set a -> Set a
difference (S as0) (S bs0) = S $ loop as0 bs0 where
  loop [] _ = []
  loop a [] = a
  loop as@(a:at) bs@(b:bt) =
    case compare a b of
      GT -> a : loop at bs
      EQ -> loop at bt
      LT -> loop as bt

intersection :: Ord a => Set a -> Set a -> Set a
intersection (S as0) (S bs0) = S $ loop as0 bs0 where
  loop [] _ = []
  loop _ [] = []
  loop as@(a:at) bs@(b:bt) =
    case compare a b of
      GT -> loop at bs
      EQ -> a : loop at bt
      LT -> loop as bt

findMax :: Set a -> a
findMax = head . toDescList

fromAscList :: Ord a => [a] -> Set a
fromAscList = fromDescList . reverse

fromList :: Ord a => [a] -> Set a
fromList = S . reverse . map head . group . sort

null :: Set a -> Bool
null = P.null . toDescList

size :: Set a -> Int
size = length . toDescList

isSubsetOf :: Ord a => Set a -> Set a -> Bool
isSubsetOf (S as0) (S bs0) = loop as0 bs0 where
  loop [] _ = True
  loop _ [] = False
  loop as@(a:at) (b:bt) =
    case compare a b of
      GT -> False
      EQ -> loop at bt
      LT -> loop as bt

disjoint :: Ord a => Set a -> Set a -> Bool
disjoint (S as0) (S bs0) = loop as0 bs0 where
  loop [] _ = True
  loop _ [] = True
  loop as@(a:at) bs@(b:bt) =
    case compare a b of
      GT -> loop at bs
      EQ -> False
      LT -> loop as bt
