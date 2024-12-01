module BDDSubtyping.DAG(
  DAG, Node,
  tr, Relatedness(..),
  mkDag, unMkDag, tt,
  invalidEdges, subs, dagMax) where
import Data.IntMap.Strict(IntMap, (!?))
import qualified Data.IntMap.Strict as M
import Data.IntSet(IntSet)
import qualified Data.IntSet as S
import Data.Foldable

type Node = Int

newtype DAG = DAG (IntMap IntSet)
  deriving (Eq)

instance Show DAG where
  showsPrec _ d = ("mkDag " ++) . shows (tt d)

mkDag :: [(Node, [Node])] -> DAG
mkDag ns =
  DAG $ tc (M.fromList [(i, S.fromList es) | (i, es) <- ns, not (null es)])

unMkDag :: DAG -> [(Node, [Node])]
unMkDag (DAG d) = [(n, S.toList es) | (n, es) <- M.toList d]

-- Given a DAG, return a list of invalid edges.  This should be empty.
invalidEdges :: DAG -> [(Node, Node)]
invalidEdges (DAG d) =
  [(a,b) | (a,bs) <- M.toList d, b <- S.toList bs, a < b]

-- Transitive trim.  Reduces DAG to minimal dependencies and unmakes it.
tt :: DAG -> [(Node, [Node])]
tt (DAG d) =
  [(v, S.toList (as `S.difference` ts)) |
    (v, as) <- M.toList d,
    let ts = foldMap (\a -> M.findWithDefault mempty a d) (S.toList as)]

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
subs :: DAG -> Node -> IntSet
subs (DAG d) a = M.findWithDefault mempty a d

-- Maximum value in DAG, or (-1) if none.
dagMax :: DAG -> Node
dagMax (DAG d) = maybe (-1) fst $ M.lookupMax d
