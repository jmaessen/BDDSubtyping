{-# LANGUAGE TypeFamilies #-}
module Data.NaiveMemo(
  MemoKey(..),
  MemoTable, mkMemo, memoize, memoizeIdem1,
  HashConsable(..), ConsId,
  ConsTable, mkCons, hcEq, hcHashWithSalt, hashCons,
  HashConsed, hashConsed, underlying
) where
import Control.Concurrent.MVar(MVar, newMVar, modifyMVar)
import Data.Hashable(Hashable(hashWithSalt))
import qualified Data.HashMap.Lazy as HM
import System.IO.Unsafe(unsafeDupablePerformIO)

-- Naive-ish memoization.  NOT purely functional,
-- but space-leaky nonetheless.

class MemoKey a where
  type MK a
  toMemoKey :: a -> MK a

instance MemoKey Int where
  type MK Int = Int
  toMemoKey = id

instance (MemoKey a, MemoKey b) => MemoKey (a,b) where
  type MK (a,b) = (MK a, MK b)
  toMemoKey (a,b) = (toMemoKey a, toMemoKey b)

instance (MemoKey a, MemoKey b, MemoKey c) => MemoKey (a,b,c) where
  type MK (a,b,c) = (MK a, MK b, MK c)
  toMemoKey (a,b,c) = (toMemoKey a, toMemoKey b, toMemoKey c)

newtype MemoTable a b = MT (MVar (HM.HashMap (MK a) b))

mkMemo :: (MemoKey a, Hashable (MK a)) => IO (MemoTable a b)
mkMemo = MT <$> newMVar mempty

memoize ::
  (MemoKey a, Hashable (MK a)) =>
  MemoTable a b -> (a -> b) -> (a -> b)
memoize (MT table) f = go where
  go a = do
    let k = toMemoKey a
    unsafeDupablePerformIO $
      modifyMVar table $ \t ->
        pure $
        case HM.lookup k t of
          Just r -> (t, r)
          Nothing -> (HM.insert k r t, r)
            where r = f a

-- Like memoize, but also records that the result when passed in
-- as the first element of the pair yields itself.
memoizeIdem1 ::
  (MemoKey a, MemoKey b, Hashable (MK a), Hashable (MK b)) =>
  MemoTable (a,b) a -> ((a,b) -> a) -> ((a,b) -> a)
memoizeIdem1 (MT table) f = go where
  go ab@(~(_, b)) = do
    let k = toMemoKey ab
    unsafeDupablePerformIO $ do
      r <-
        modifyMVar table $ \t ->
          pure $
          case HM.lookup k t of
            Just r -> (t, r)
            Nothing -> (HM.insert k r t, r)
              where r = f ab
      -- To avoid deadlock when forcing r (which is still a thunk),
      -- we must drop the MVar and re-take it.
      let k' = toMemoKey (r, b)
      if k /= k' then
        modifyMVar table $ \t -> pure (HM.insert k' r t, r)
      else pure r

type ConsId = Int

newtype ConsTable a = HC (MVar (ConsId, HM.HashMap (ByContent a) a))

mkCons :: HashConsable a => IO (ConsTable a)
mkCons = HC <$> newMVar (1, mempty)

class HashConsable a where
  -- requires:
  --   contentHashWithSalt k a == contentHashWithSalt k (setId j a)
  --   contentEq a (setId j a)
  --   contentEq a b => contentHashWithSalt k a == contentHashWithSalt k b
  -- for all a, b, j, k
  contentHashWithSalt :: Int -> a -> Int
  contentEq :: a -> a -> Bool
  getId :: a -> ConsId
  setId :: ConsId -> a -> a

newtype ByContent a = BC a

instance HashConsable a => Hashable (ByContent a) where
  hashWithSalt s (BC a) = contentHashWithSalt s a

instance HashConsable a => Eq (ByContent a) where
  (BC a) == (BC b) = contentEq a b

-- equality for hash consable things
hcEq :: HashConsable a => a -> a -> Bool
hcEq a b = getId a == getId b

-- Hashable for hash consable things
hcHashWithSalt :: HashConsable a => Int -> a -> Int
hcHashWithSalt s a = hashWithSalt s (getId a)

hashCons :: HashConsable a => ConsTable a -> a -> a
hashCons (HC table) = go where
  go !a = do
    unsafeDupablePerformIO $
      modifyMVar table $ \(i, t) ->
        pure $
        case HM.lookup (BC a) t of
          Just r -> ((i, t), r)
          Nothing -> ((i+1, HM.insert (BC r) r t), r)
            where r = setId i a

-- Hash cons wrapper type that takes the place of a newtype
data HashConsed a = Cons !ConsId !a

hashConsed :: (Eq a, Hashable a) => ConsTable (HashConsed a) -> a -> HashConsed a
hashConsed t = hashCons t . Cons 0

underlying :: HashConsed a -> a
underlying (Cons _ a) = a

instance (Eq a, Hashable a) => HashConsable (HashConsed a) where
  contentEq (Cons _ a) (Cons _ b) = a == b
  contentHashWithSalt s (Cons _ a) = hashWithSalt s a
  getId = toMemoKey
  setId i (Cons _ a) = Cons i a

instance (Eq a, Hashable a) => Eq (HashConsed a) where
  (==) = hcEq

instance (Eq a, Hashable a) => Hashable (HashConsed a) where
  hashWithSalt = hcHashWithSalt

instance MemoKey (HashConsed a) where
  type MK (HashConsed a) = ConsId
  toMemoKey (Cons i _) = i
