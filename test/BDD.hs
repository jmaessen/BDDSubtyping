{-# LANGUAGE TemplateHaskell, ViewPatterns #-}
module BDD where
import Test.QuickCheck

import BDDSubtyping.BDD
import BDDSubtyping.DAG(mkDag)
import DAG() -- for Arbitrary DAG


instance Arbitrary BDD where
  arbitrary = sized mkBdd where
    mkBdd :: Int -> Gen BDD
    mkBdd n | n <= 0 = oneof [return Bot, return Top]
    mkBdd n = do
      t <- chooseInt (-2, n-1) >>= mkBdd
      e <- chooseInt (-2, n-1) >>= mkBdd
      return (select (n-1) t e)

prop_bdd_big :: TR -> BDD -> NonNegative Base -> Property
prop_bdd_big r b (NonNegative i) =
  bddBases r b (root b + i + 1) === rightmost b

prop_base_empty :: NonNegative Base -> Property
prop_base_empty (NonNegative i) =
  model (mkDag []) (base i) === (replicate i False ++ [True, False])


prop_base :: TR -> NonNegative Base -> Property
prop_base r (NonNegative i) =
  drop i (model r (base i)) === [True, False]

prop_complement :: TR -> BDD -> Property
prop_complement r a = model r a === fmap not (model r (complement a))

prop_union :: TR -> BDD -> BDD -> Bool
prop_union r a b =
  and $ zipWith (\i v -> (bddBases r a i || bddBases r b i) == v)
                [0..] (model r (basicUnion a b))

prop_eraseSubtypes_root :: TR -> BDD -> Property
prop_eraseSubtypes_root r b@(bdd -> Select i t e) =
  modelDiff r b (select i t (eraseSubtypes r i e)) === []
prop_eraseSubtypes_root _ _ = property Discard

mkPos :: BDD -> BDD
mkPos b
  | rightmost b = complement b
  | otherwise = b

prop_eraseDisjoints_root :: TR -> BDD -> Property
prop_eraseDisjoints_root r b@(bdd -> Select i t e) =
  modelDiff r b (select i (eraseDisjoints r i t) e) === []
prop_eraseDisjoints_root _ _ = property Discard

prop_erase_root :: TR -> BDD -> Property
prop_erase_root r b@(bdd -> Select i t e) =
  modelDiff r b (select i (eraseDisjoints r i t) (eraseSubtypes r i e)) === []
prop_erase_root _ _ = property Discard

prop_fullyErase :: TR -> BDD -> Property
prop_fullyErase r b = modelDiff r b (fullyErase r b) === []

prop_common_refl :: TR -> BDD -> Property
prop_common_refl r b =
  case common r (1 + root b) b b of
    Just b2 -> modelDiff r b b2 === []
    Nothing -> property False

prop_common :: TR -> BDD -> Property
prop_common r b@(bdd -> Select i t e) =
  case common r i t e of
    Just c -> modelDiff r b c === []
    Nothing -> property Discard
prop_common _ _ = property Discard

prop_common_complete :: TR -> BDD -> Bool
prop_common_complete r s =
  common r c (eraseDisjoints r c s) (eraseSubtypes r c s) /= Nothing
  where c = root s + 1

prop_common_correct1 :: TR -> BDD -> BDD -> Property
prop_common_correct1 r t e =
  let c = max (root t) (root e) + 1
  in case common r c t e of
        Just s -> modelDiff r (select c t e) s === []
        Nothing -> property Discard

prop_common_correct2 :: TR -> BDD -> Property
prop_common_correct2 r s =
  let c = root s + 1
      t = eraseDisjoints r c s
      e = eraseSubtypes r c s
      Just k = common r c t e
  in modelDiff r (select c t e) k === []

prop_common_size :: TR -> BDD -> BDD -> Property
prop_common_size r t e =
  let c = max (root t) (root e) + 1
      t' = fullyErase r t
      e' = fullyErase r e
  in case common r c t' e' of
        Just s -> property $ size s <= size t' + size e'
        Nothing -> property Discard

prop_size_counter :: Property
prop_size_counter = prop_common_size r t e where
  r = mkDag [(2,[1]),(3,[1,2]),(8,[1,2,5,6,7]),(9,[1,2,4,5,6]),(10,[0,1,2,4,5,6,9]),(11,[1,2,3,4,5,6,7,9])]
  t = complement (select 10 (complement (select 4 Top (base 1))) Bot)
  e = complement (select 10 (complement (select 5 (base 0) Bot)) Bot)

------------------------------------------------------------

ttr :: TR
ttr = mkDag [(0, [0]), (1, [1]), (2, [0, 1, 2]), (3, [1, 3])]


qc :: (Testable t) => t -> IO ()
qc = qcs 12

qcs :: (Testable t) => Int -> t -> IO ()
qcs s = quickCheckWith (stdArgs{ maxSuccess = 1000, maxSize = s, maxDiscardRatio = 3 })

return []

bddTestAll :: IO Bool
bddTestAll = $forAllProperties (quickCheckWithResult (stdArgs{maxSuccess=1000, maxDiscardRatio=1000}))
