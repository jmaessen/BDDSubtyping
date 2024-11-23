{-# LANGUAGE TemplateHaskell #-}
module DAG where
import Control.Monad(replicateM)
import Data.List(sort)
import Test.QuickCheck

import BDDSubtyping.DAG

instance Arbitrary DAG where
  arbitrary = mkDag <$> sized dag where
    dag :: Int -> Gen [(Int,[Int])]
    dag 0 = return [(0,[])]
    dag n = do
      d <- dag (n - 1)
      n_edges <- chooseInt (0, n-1)
      edges <- replicateM n_edges (choose (0, n-1))
      return ((n,edges):d)

prop_dag_refl :: DAG -> Int -> Bool
prop_dag_refl d n = tr d n n == Subtype

prop_dag_symm :: DAG -> Int -> Int -> Bool
prop_dag_symm d a b = tr d a b == tr d b a

prop_dag_trans :: DAG -> NonNegative Int -> NonNegative Int -> NonNegative Int -> Bool
prop_dag_trans dag (NonNegative a) (NonNegative b) (NonNegative c) =
  let [aa, bb, cc] = sort [a, b, c] in
  case (tr dag aa bb, tr dag bb cc, tr dag aa cc) of
    (Subtype, Subtype, d) -> d == Subtype
    (MayIntersect, MayIntersect, _) -> True
    (Subtype, MayIntersect, _) -> True
    (MayIntersect, Subtype, d) -> d /= Disjoint
    (Disjoint, Subtype, _) -> True
    (Subtype, Disjoint, d) -> d == Disjoint
    (Disjoint, MayIntersect, _) -> True
    (MayIntersect, Disjoint, d) -> d == Disjoint || d == MayIntersect
    (Disjoint, Disjoint, _) -> True

return []

dagTestAll :: IO Bool
dagTestAll = $quickCheckAll
