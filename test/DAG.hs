{-# LANGUAGE TemplateHaskell #-}
module DAG where
import Control.Monad(replicateM)
import Test.QuickCheck
import qualified Data.IntSet as S

import BDDSubtyping.DAG

instance Arbitrary DAG where
  arbitrary = mkDag <$> sized dag where
    dag :: Int -> Gen [(Int,[Int])]
    dag 0 = return []
    dag n = do
      d <- dag (n - 1)
      n_edges <- chooseInt (0, n-1)
      edges <- replicateM n_edges (choose (0, n-1))
      return ((n,edges):d)
  shrink dag = mkDag <$> (deletions um ++ elims)
    where
      um = unMkDag dag
      -- Delete single list elements
      deletions :: [a] -> [[a]]
      deletions [] = []
      deletions (x:xs) = xs : ((x:) <$> deletions xs)
      -- Delete mentioned variables that are not lhses
      elims =
        [ [(a, filter (/= e) vs) | (a,vs) <- um ] |
          e <- S.toList (used `S.difference` incls)]
        where
          (incls, used) = mconcat $
            [(S.singleton a, S.fromAscList bs) |
              (a,bs) <- um]

type TNode = NonNegative Node

prop_dag_valid :: DAG -> Property
prop_dag_valid d = invalidEdges d === []

prop_dag_refl :: DAG -> TNode -> Bool
prop_dag_refl d (NonNegative n) = tr d n n == Subtype

prop_dag_symm :: DAG -> TNode -> TNode -> Bool
prop_dag_symm d (NonNegative a) (NonNegative b) = tr d a b == tr d b a

prop_dag_trans :: DAG -> TNode -> TNode -> TNode -> Property
prop_dag_trans dag (NonNegative a) (NonNegative b) (NonNegative c) =
  let [aa, bb, cc] = [a, a + b + 1, a + b + c + 2] in
  case (tr dag aa bb, tr dag bb cc, tr dag aa cc) of
    (Subtype, Subtype, Subtype) -> property True
    (Subtype, MayIntersect, _) -> property True
    (Subtype, Disjoint, Disjoint) -> property True
    (MayIntersect, MayIntersect, _) -> property True
    (MayIntersect, Subtype, d) -> d =/= Disjoint
    (MayIntersect, Disjoint, d) -> d === Disjoint .||. d === MayIntersect
    (Disjoint, _, _) -> property True
    d -> counterexample (show d) False

prop_dagMax_exists :: DAG -> Property
prop_dagMax_exists d
  | m == -1 = property Discard
  | otherwise = subs d m =/= mempty
  where m = dagMax d

prop_dagMax_max :: DAG -> TNode -> Property
prop_dagMax_max d (NonNegative a)
  | subs d a /= mempty = property (a <= dagMax d)
  | otherwise = property Discard

return []

dagTestAll :: IO Bool
dagTestAll = $forAllProperties (quickCheckWithResult (stdArgs{maxSuccess=1000, maxDiscardRatio=1000}))
