{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE TypeFamilies #-}
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
import Data.NaiveMemo
import System.IO.Unsafe(unsafePerformIO)

type Node = Int

type DAG = HashConsed (IntMap IntSet)

instance Show DAG where
  showsPrec _ d = ("mkDag " ++) . shows (tt d)

{-# NOINLINE dagCons #-}
dagCons :: ConsTable DAG
dagCons = unsafePerformIO mkCons

mkDag :: [(Node, [Node])] -> DAG
mkDag ns =
  hashConsed dagCons $ tc (M.fromList [(i, S.fromList es) | (i, es) <- ns, not (null es)])

unMkDag :: DAG -> [(Node, [Node])]
unMkDag d = [(n, S.toList es) | (n, es) <- M.toList (underlying d)]

-- Given a DAG, return a list of invalid edges.  This should be empty.
invalidEdges :: DAG -> [(Node, Node)]
invalidEdges d =
  [(a,b) | (a,bs) <- M.toList (underlying d), b <- S.toList bs, a < b]

-- Transitive trim.  Reduces DAG to minimal dependencies and unmakes it.
tt :: DAG -> [(Node, [Node])]
tt d =
  [(v, S.toList (as `S.difference` ts)) |
    (v, as) <- M.toList (underlying d),
    let ts = foldMap (\a -> M.findWithDefault mempty a (underlying d)) (S.toList as)]

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
tr d a b =
  case (underlying d!?a, underlying d!?b) of
    (_, Just bSubs) | S.member a bSubs -> Subtype
    (Just aSubs, Just bSubs) | not (S.disjoint aSubs bSubs) -> MayIntersect
    _ -> Disjoint

-- Subtypes
subs :: DAG -> Node -> IntSet
subs d a = M.findWithDefault mempty a (underlying d)

-- Maximum value in DAG, or (-1) if none.
dagMax :: DAG -> Node
dagMax d = maybe (-1) fst $ M.lookupMax $ underlying d
