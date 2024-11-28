module BDDSubtyping.DAG(DAG, Node, tr, mkDag, invalidEdges, subs, Relatedness(..)) where
import Data.IntMap.Strict(IntMap, (!?))
import qualified Data.IntMap.Strict as M
import qualified Data.IntSet as S
import Data.IntSet(IntSet)
import Data.List(foldl')

type Node = Int

newtype DAG = DAG (IntMap IntSet)
  deriving (Eq)

instance Show DAG where
  showsPrec _ (DAG d) = ("mkDag " ++) . showgr d
    where showgr g = shows [(i, S.toList es) | (i, es) <- M.toList g]

mkDag :: [(Node, [Node])] -> DAG
mkDag ns =
  DAG $ tc (M.fromList [(i, S.fromList es) | (i, es) <- ns, not (null es)])

-- Given a DAG, return a list of invalid edges.  This should be empty.
invalidEdges :: DAG -> [(Node, Node)]
invalidEdges (DAG d) =
  [(a,b) | (a,bs) <- M.toList d, b <- S.toList bs, a < b]

-- Transitive closure.  Assumes topologically sorted node numbering.
tc :: IntMap IntSet -> IntMap IntSet
tc is = foldl' tcn M.empty (M.toAscList is) where
  tcn :: IntMap IntSet -> (Node, IntSet) -> IntMap IntSet
  tcn acc (i, i_edges) =
    M.insert i (S.unions (i_edges : [ tcs | c <- S.toList i_edges, Just tcs <- [acc!?c]])) acc

data Relatedness = Subtype | Disjoint | MayIntersect
  deriving (Eq, Show)

-- Relate
tr :: DAG -> Node -> Node -> Relatedness
tr d a b | a > b = tr d b a
tr _ a b | a == b = Subtype
tr (DAG d) a b =
  case (d!?a, d!?b) of
    (_, Just bSubs) | S.member a bSubs -> Subtype
    (Just aSubs, Just bSubs) | not (S.disjoint aSubs bSubs) -> MayIntersect
    _ -> Disjoint

-- Subtypes
subs :: DAG -> Node -> [Node]
subs (DAG d) a = S.toList $ M.findWithDefault mempty a d
