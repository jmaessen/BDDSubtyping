{-# LANGUAGE TemplateHaskell #-}
module BDD where
import Test.QuickCheck

import BDDSubtyping.BDD
import BDDSubtyping.DAG(mkDag)
import DAG() -- for Arbitrary DAG


instance Arbitrary BDD where
  arbitrary = sized bdd where
    bdd :: Int -> Gen BDD
    bdd n | n <= 0 = oneof [return Bot, return Top]
    bdd n = do
      t <- chooseInt (-2, n-1) >>= bdd
      e <- chooseInt (-2, n-1) >>= bdd
      return (select (n-1) t e)

prop_bdd_exact :: TR -> BDD -> NonNegative Int -> Bool
prop_bdd_exact trd bdd (NonNegative i) = bdd_contains_exact trd bdd i == bdd_exacts trd bdd i

prop_bdd_big :: TR -> BDD -> NonNegative Int -> Bool
prop_bdd_big tr bdd (NonNegative i) = bdd_contains_exact tr bdd (root bdd + i + 1) == rightmost bdd

prop_union :: TR -> BDD -> BDD -> Bool
prop_union tr a b = and $ zipWith (\i v -> (bdd_exacts tr a i || bdd_exacts tr b i) == v) [0..] (model tr (union a b))

prop_intersect :: TR -> BDD -> BDD -> Bool
prop_intersect tr a b = and $ zipWith (\i v -> (bdd_exacts tr a i && bdd_exacts tr b i) == v) [0..] (model tr (intersect a b))

prop_erase_subtypes_root :: TR -> BDD -> Property
prop_erase_subtypes_root trd (Select i t e) = property $ model_eq trd (Select i t e) (select i t (erase_subtypes trd i e))
prop_erase_subtypes_root _ _ = property Discard

prop_erase_disjoints_root :: TR -> BDD -> Property
prop_erase_disjoints_root trd (Select i t e) = property $ model_eq trd (Select i t e) (select i (erase_disjoints trd i t) e)
prop_erase_disjoints_root _ _ = property Discard

prop_fully_erase :: TR -> BDD -> Bool
prop_fully_erase tr bdd = model_eq tr bdd (fully_erase tr bdd)

prop_common_refl :: TR -> BDD -> Bool
prop_common_refl tr bdd =
  case common tr (1 + root bdd) bdd bdd of
    Just bdd2 -> model_eq tr bdd bdd2
    Nothing -> False

prop_common :: TR -> BDD -> Property
prop_common tr (Select i t e) =
  case common tr i t e of
    Just r -> property $ model_eq tr (Select i t e) r
    Nothing -> property Discard
prop_common _ _ = property Discard

prop_common_complete :: TR -> BDD -> Bool
prop_common_complete tr s =
  common tr c (erase_disjoints tr c s) (erase_subtypes tr c s) /= Nothing
  where c = root s + 1

prop_common_correct1 :: TR -> BDD -> BDD -> Property
prop_common_correct1 tr t e =
  let c = max (root t) (root e) + 1
  in case common tr c t e of
        Nothing -> property Discard
        Just s -> property $ model_eq tr (Select c t e) s

prop_common_correct2 :: TR -> BDD -> Bool
prop_common_correct2 tr s =
  let c = max (root t) (root e) + 1
      t = erase_disjoints tr c s
      e = erase_subtypes tr c s
      Just k = common tr c t e
  in model_eq tr (Select c t e) k

prop_common_size :: TR -> BDD -> BDD -> Property
prop_common_size tr t e =
  let c = max (root t) (root e) + 1
  in case common tr c t e of
        Nothing -> property Discard
        Just s -> property $ size s <= size t + size e

------------------------------------------------------------

ttr :: TR
ttr = mkDag [(0, [0]), (1, [1]), (2, [0, 1, 2]), (3, [1, 3])]


qc :: (Testable t) => t -> IO ()
qc = qcs 12

qcs :: (Testable t) => Int -> t -> IO ()
qcs s = quickCheckWith (stdArgs{ maxSuccess = 1000, maxSize = s, maxDiscardRatio = 3 })

return []

bddTestAll :: IO Bool
bddTestAll = $quickCheckAll
