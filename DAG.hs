module BDDSubtyping.DAG(DAG, Relatedness(..), mkDag, tr, isValid)
import Data.IntMap.Strict(IntMap, (!?))
import qualified Data.IntSet as S
import Data.IntSet(IntSet)

-- DAGs represented as a transitively closed
-- relation between Int pairs.  Node values
-- must be topologically ordered.  We use this
-- DAG to represent the supertype relation.

newtype DAG = DAG (IntMap IntSet)
  deriving (Eq)

instance Arbitrary DAG where
  arbitrary = fmap tc $ sized dag where
    dag :: Int -> Gen (IntMap IntSet)
    dag 0 = return (M.singleton 0 S.empty)
    dag n = do
      d <- dag (n - 1)
      n_edges <- chooseInt (0, n-1)
      edges <- fmap S.fromList $ replicateM n_edges (choose (0, n-1))
      return (M.insert n edges d)

instance Show DAG where
  show (DAG d) = "mkDag " ++ show [(i, S.toList es) | (i, es) <- M.toList d]

isValid :: DAG -> Bool
isValid
-- Contructor
mkDag :: [(Int, [Int])] -> DAG
mkDag ns = tc (M.fromList [(i, S.fromList es) | (i, es) <- ns])

-- Transitive closure (input is reflexively closed)
tc :: IntMap IntSet -> DAG
tc is = DAG (foldl' tcn M.empty (M.toAscList is)) where
  tcn :: IntMap IntSet -> (Int, IntSet) -> IntMap IntSet
  tcn acc (i, i_edges) =
    M.insert i (S.insert i (S.unions (i_edges : [ tcs | c <- S.toList i_edges, Just tcs <- [acc!?c]]))) acc

data Relatedness = Subtype | Disjoint | MayIntersect
  deriving (Eq, Show)

-- Relate
tr :: DAG -> Int -> Int -> Relatedness
tr d a b | a > b = tr d b a
tr d a b | a == b = Subtype
tr (DAG d) a b =
  case (d!?a, d!?b) of
    (_, Nothing) -> Disjoint
    (_, Just bs) | S.member a bs -> Subtype
    (Just as, Just bs)
        | S.disjoint as bs -> Disjoint
        | otherwise -> MayIntersect
    _ -> Disjoint
