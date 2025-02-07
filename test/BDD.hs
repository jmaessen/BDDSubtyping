{-# LANGUAGE TemplateHaskell, ViewPatterns #-}
module BDD where
import Test.QuickCheck
import qualified Data.DescSet as DS
import qualified Data.IntSet as S
import qualified Data.IntMap as M
import Data.IntMap((!))

import BDDSubtyping.BDD
import BDDSubtyping.DAG(mkDag, unMkDag, subs, tr, Relatedness(..))
import DAG(Dot(..)) -- + Arbitrary DAG

type BaseInc = Positive Base
p :: Positive i -> i
p (Positive i) = i

type NBase = NonNegative Base
nn :: NonNegative i -> i
nn (NonNegative i) = i

instance Arbitrary BDD where
  arbitrary = sized mkBdd where
    mkBdd :: Int -> Gen BDD
    mkBdd n | n <= 0 = oneof [return Bot, return Top]
    mkBdd n = do
      let i = n - 1
      t <- chooseInt (0, i) >>= mkBdd
      e <- chooseInt (0, i) >>= mkBdd
      return (select i t e)
  shrink b | rightmost b =
    complement b : (complement <$> shrink (complement b))
  shrink (bdd -> Select i t e) =
    e:t:(select i t <$> shrink e)++(select i <$> shrink t <*> pure e)
  shrink _ = []

-- Test fixture type.
data TF a b = TF a b

instance (FV r, FV a) => FV (TF r a) where
  fv (TF r a) = fv r <> fv a
  rename rn (TF r a) = TF (rename rn r) (rename rn a)
  showIt (TF r a) = ("(TF\n  r = "++) . shows r . ("\n  a = "++) . showIt a . ("\n)"++)

instance (Arbitrary a, FV a, Arbitrary b, FV b) => Arbitrary (TF a b) where
  arbitrary = TF <$> arbitrary <*> arbitrary
  shrink (TF a b) =
    (TF a <$> shrink b) ++
    ((`TF` b) <$> shrink a) ++
    shrinkFV
    where
      fvb = fv (TF a b)
      shrinkFV
        | DS.null fvb || DS.size fvb == 1 + DS.findMax fvb = []
        | otherwise =
          [rename (M.fromList (zip (reverse (DS.toDescList fvb)) [0..])) (TF a b)]

instance (FV a, FV b) => Show (TF a b) where
  showsPrec _ = showIt

-- Some helpers for test fixtures
instance FV () where
  fv () = mempty
  rename _ () = ()

instance (FV a, FV b) => FV (a,b) where
  fv (a,b) = fv a <> fv b
  rename r (a,b) = (rename r a, rename r b)
  showIt (a,b) = shows a . ("\n  b = "++) . shows b

instance (FV a, FV b, FV c) => FV (a,b,c) where
  fv (a,b,c) = fv a <> fv b <> fv c
  rename r (a,b,c) = (rename r a, rename r b, rename r c)
  showIt (a,b,c) =
    shows a . ("\n  b = "++) . shows b . ("\n  c = "++) . shows c

instance FV NBase where
  fv (nn -> b) = DS.singleton b
  rename r (nn -> b) = NonNegative (r!b)

instance FV BaseInc where
  fv _ = mempty
  rename _ _ = Positive 1

instance FV TR where
  fv r = DS.fromList [ v | (a, vs) <- unMkDag r, v <- a : vs ]
  rename rn r =
    mkDag [(a', bs')
          | (a, bs) <- unMkDag r
          , Just a' <- [M.lookup a rn]
          , let bs' = [ b' | b <- bs, Just b' <- [M.lookup b rn]]
          , not (null bs')
          ]

-- Draw BDD as DAG
instance Dot BDD where
  toDot b0 = [ l | (n, b) <- M.toList g, l <- node n b ]
    where
      g = toGraph b0
      node n (Select i t e) =
        let (tid, tl) = ref n t
            (eid, el) = ref n e
            sn = show n
        in ["  N"++sn++" [label=\""++show i++"\"];",
            "  N"++sn++":sw -> "++tid++";",
            "  N"++sn++":se -> "++eid++" [style=dashed];"]
           ++ tl ++ el
      -- node n (Exact i m e) =
      --   let (eid, el) = ref n e
      --       mm | m = "="
      --          | otherwise = "!"
      --       sn = show n
      --   in ["  N"++sn++" [label=\""++mm++show i++"\", shape=box];",
      --       "  N"++sn++":s -> "++eid++" [style=dashed];"]
      --      ++ el
      node _ _ = []
      ref i e = ref' i e (g!e)
      ref' i _ TopP =
        let si = show i
        in ("NT"++si, [ "  NT"++si++" [label=\"T\",shape=none]"])
      ref' i _ BotP =
        let si = show i
        in ("NB"++si, [ "  NB"++si++" [label=\"⟂\",shape=none]"])
      ref' _ n _ = ("N"++show n, [])

prop_hc_base :: TF () BDD -> Property
prop_hc_base (TF () a) = a === mkEq a where
  mkEq (bdd -> Select i Top Bot) = base i
  mkEq b@(bdd -> Select _ _ Top) = complement (mkEq (complement b))
  mkEq (bdd -> Select i t e) = select i t e
  mkEq Top = Top
  mkEq _{-Bot-} = Bot

prop_graph_id :: TF () BDD -> Property
prop_graph_id (TF () b) =
  fromGraph (toGraph b) === b

prop_bdd_big :: TF TR (BDD, BaseInc) -> Property
prop_bdd_big (TF r (b, p -> i)) =
  bddBases r b (root b + i + 1) === rightmost b

prop_base_empty :: NBase -> Property
prop_base_empty (nn -> i) =
  model (mkDag []) (base i) === [i]

prop_base :: TF TR NBase -> Property
prop_base (TF r (nn -> i)) =
  model r (base i) === S.toAscList (S.insert i (subs r i))

prop_fv_base :: NBase -> Property
prop_fv_base (nn -> i) =
  fv (base i) === DS.singleton i

prop_bases_bot :: TF TR NBase -> Property
prop_bases_bot (TF r (nn -> i)) =
  bddBases r Bot i === False

prop_fv_bot :: Property
prop_fv_bot = fv Bot === mempty

prop_bases_top :: TF TR NBase -> Property
prop_bases_top (TF r (nn -> i)) = bddBases r Top i === True

prop_fv_top :: Property
prop_fv_top = fv Top === mempty

prop_bases_base :: TF TR NBase -> Property
prop_bases_base (TF r (nn -> i)) = bddBases r (base i) i === True

prop_complement :: TF TR BDD -> Property
prop_complement (TF r a) = modelDiff r a (complement a) === [0..root a + 1]

prop_fv_complement :: TF () BDD -> Property
prop_fv_complement (TF _ a) = fv a === fv (complement a)

prop_union :: TF TR (BDD, BDD) -> Property
prop_union (TF r (a, b)) =
  let u = basicUnion a b
  in filter
       (\i -> (bddBases r a i || bddBases r b i) /= bddBases r u i)
       [0..1+maximum[root a, root b, root u]] === []

-- This is only true of *basic* union!
prop_fv_union :: TF () (BDD, BDD) -> Bool
prop_fv_union (TF _ (a, b)) = fv (a `basicUnion` b) `DS.isSubsetOf` (fv a <> fv b)

prop_union_idem :: TF () BDD -> Property
prop_union_idem (TF () a) = (a `basicUnion` a) === a

prop_union_comm :: TF () (BDD, BDD) -> Property
prop_union_comm (TF () (a, b)) = (a `basicUnion` b) === (b `basicUnion` a)

prop_union_assoc :: TF () (BDD, BDD, BDD) -> Property
prop_union_assoc (TF () (a, b, c)) =
  (a `basicUnion` (b `basicUnion` c)) === ((a `basicUnion` b) `basicUnion` c)

prop_union_ident :: TF () BDD -> Property
prop_union_ident (TF () a) = (a `basicUnion` Bot) === a

prop_univ_zero :: TF () BDD -> Property
prop_univ_zero (TF () a) = (a `basicUnion` Top) === Top

prop_excl_mid :: TF () BDD -> Property
prop_excl_mid (TF () a) = (a `basicUnion` complement a) === Top

prop_complex_excl_mid :: TF () (BDD, BDD) -> Property
prop_complex_excl_mid (TF () (a, b)) =
  ((a `basicUnion` b) `basicUnion` complement a) === Top

prop_neg_univ1 :: Property
prop_neg_univ1 = complement Bot === Top

prop_neg_univ2 :: Property
prop_neg_univ2 = Bot === complement Top

prop_double_complement :: TF () BDD -> Property
prop_double_complement (TF () b) = complement (complement b) === b

prop_robbins :: TF () (BDD, BDD) -> Property
prop_robbins (TF () (a, b)) =
  complement (complement (a `basicUnion` b) `basicUnion` complement (a `basicUnion` complement b)) === a

prop_robbins2 :: TF () (BDD, BDD) -> Property
prop_robbins2 (TF () (a, b)) =
  ((a `basicUnion` b) `basicIntersect` (a `basicUnion` complement b)) === a

prop_eraseSubtypes_root :: TF TR BDD -> Property
prop_eraseSubtypes_root (TF r b@(bdd -> Select i t e)) =
  modelDiff r b (select i t (eraseSubtypes r i e)) === []
prop_eraseSubtypes_root _ = property Discard

prop_eraseSubtypes_fv :: TF TR (BaseInc, BDD) -> Property
prop_eraseSubtypes_fv (TF r (p -> ii, e))
  | iSubs `DS.disjoint` fve = erased === e
  | otherwise = property (fv erased `DS.isSubsetOf` (fve `DS.difference` iSubs))
  where iSubs = DS.fromAscList $ S.toAscList $ subs r i
        fve = fv e
        erased = eraseSubtypes r i e
        i = root e + ii

prop_eraseSubtypes_complement :: TF TR (BaseInc, BDD) -> Property
prop_eraseSubtypes_complement (TF r (p -> i, b)) =
  complement (eraseSubtypes r c b) === eraseSubtypes r c (complement b)
  where c = root b + i

prop_eraseSubtypes_idem :: TF TR (BaseInc, BDD) -> Property
prop_eraseSubtypes_idem (TF r (p -> i, b)) =
  eraseSubtypes r c (eraseSubtypes r c b) === eraseSubtypes r c b
  where c = root b + i

prop_eraseSubtypes_union :: TF TR (BaseInc, BDD, BDD) -> Property
prop_eraseSubtypes_union (TF r (p -> i, a, b)) =
  eraseSubtypes r c (a `basicUnion` b) === (eraseSubtypes r c a `basicUnion` eraseSubtypes r c b)
  where c = (root a `max` root b) + i

prop_eraseDisjoints_root :: TF TR BDD -> Property
prop_eraseDisjoints_root (TF r b@(bdd -> Select i t e)) =
  modelDiff r b (select i (eraseDisjoints r i t) e) === []
prop_eraseDisjoints_root _ = property Discard

prop_eraseDisjoints_fv :: TF TR (BaseInc, BDD) -> Property
prop_eraseDisjoints_fv (TF r (p -> ii, e))
  -- | iDisjs `S.disjoint` fve = erased === e -- Not true for Eq
  | otherwise = property (fv erased `DS.isSubsetOf` (fve `DS.difference` iDisjs))
  where iDisjs = DS.fromAscList (filter ((Disjoint==). tr r i) [0..i-1])
        fve = fv e
        erased = eraseDisjoints r i e
        i = root e + ii

prop_eraseDisjoints_complement :: TF TR (BaseInc, BDD) -> Property
prop_eraseDisjoints_complement (TF r (p -> i, b)) =
  complement (eraseDisjoints r c b) === eraseDisjoints r c (complement b)
  where c = root b + i

prop_eraseDisjoints_idem :: TF TR (BaseInc, BDD) -> Property
prop_eraseDisjoints_idem (TF r (p -> i, b)) =
  eraseDisjoints r c (eraseDisjoints r c b) === eraseDisjoints r c b
  where c = root b + i

prop_eraseDisjoints_union :: TF TR (BaseInc, BDD, BDD) -> Property
prop_eraseDisjoints_union (TF r (p -> i, a, b)) =
  eraseDisjoints r c (a `basicUnion` b) === (eraseDisjoints r c a `basicUnion` eraseDisjoints r c b)
  where c = (root a `max` root b) + i

prop_erase_root :: TF TR BDD -> Property
prop_erase_root (TF r b@(bdd -> Select i t e)) =
  modelDiff r b (select i (eraseDisjoints r i t) (eraseSubtypes r i e)) === []
prop_erase_root _ = property Discard

-- common always succeeds when handed two equal BDDs
prop_common_refl :: TF TR (BaseInc, BDD) -> Property
prop_common_refl (TF r (p -> i, b)) =
  case common r (root b + i) b b of
    Just b2 -> modelDiff r b b2 === []
    Nothing -> property False

prop_common :: TF TR BDD -> Property
prop_common (TF r b@(bdd -> Select i t e)) =
  let t' = eraseDisjoints r i t
      e' = eraseSubtypes r i e
  in case common r i t' e' of
    Just c -> modelDiff r b c === []
    Nothing -> t =/= e .&&. t' =/= e'
prop_common _ = property Discard

prop_common_fv :: TF TR BDD -> Property
prop_common_fv (TF r (bdd -> Select i t e)) =
  let t' = eraseDisjoints r i t
      e' = eraseSubtypes r i e
  in case common r i t' e' of
    Just c -> property (fv c `DS.isSubsetOf` (fv t' <> fv e'))
    Nothing -> t =/= e .&&. t' =/= e'
prop_common_fv _ = property Discard

prop_common_complete :: TF TR (BaseInc, BDD) -> Property
prop_common_complete (TF r (p -> i, s)) =
  case (eraseDisjoints r c s, eraseSubtypes r c s) of
    (a,b) | a /= b -> common r c a b =/= Nothing
    _ -> property Discard
  where c = root s + i

prop_common_eq :: TF TR (BaseInc, BDD) -> Property
prop_common_eq (TF r (p -> i, s)) =
  let c = root s + i
  in common r c s s === Just s

prop_common_correct2 :: TF TR (BaseInc, BDD) -> Property
prop_common_correct2 (TF r (p -> i, s)) =
  let c = root s + i
      t = eraseDisjoints r c s
      e = eraseSubtypes r c s
      Just k = common r c t e
  in modelDiff r (select c t e) k === []

prop_common_complement :: TF TR BDD -> Property
prop_common_complement (TF r (bdd -> Select c t e)) =
  let t' = eraseDisjoints r c t
      e' = eraseSubtypes r c e
  in case common r c t' e' of
    Just s -> common r c (complement t') (complement e') === Just (complement s)
    Nothing -> property Discard
prop_common_complement _ = property Discard

prop_commonOrErase_refl :: TF TR (BaseInc, BDD) -> Property
prop_commonOrErase_refl (TF r (p -> i, b)) =
  let c = root b + i
      t = eraseDisjoints r c b
      e = eraseSubtypes r c b
      Just s = common r c t e
  in commonOrErase r c b b === (t, e, Just s)

prop_commonOrErase :: TF TR BDD -> Property
prop_commonOrErase (TF r (bdd -> Select c t e)) =
  let t' = eraseDisjoints r c t
      e' = eraseSubtypes r c e
  in commonOrErase r c t e === (t', e', common r c t' e')
prop_commonOrErase _ = property Discard

prop_canonS_idem :: TF TR BDD -> Property
prop_canonS_idem (TF r b) = c === canonS r c
  where c = canonS r b

prop_canonS_complement :: TF TR BDD -> Property
prop_canonS_complement (TF r b) =
  canonS r (complement b) === complement (canonS r b)

prop_canonS_base :: TF TR NBase -> Property
prop_canonS_base (TF r (nn -> b)) =
  canonS r (base b) === base b

prop_canonS_bot :: TF TR () -> Property
prop_canonS_bot (TF r _) =
  canonS r Bot === Bot

prop_canonS_top :: TF TR () -> Property
prop_canonS_top (TF r _) =
  canonS r Top === Top

prop_isBottom :: TF TR BDD -> Property
prop_isBottom (TF r b)
 | isBottom r b = counterexample "bottom" (model r b === [])
 | model r b /= [] = counterexample "nonempty" (not (isBottom r b))
 | otherwise = property Discard

prop_relateNaiveBase :: TF TR (NBase, NBase) -> Property
prop_relateNaiveBase (TF r (nn -> a, nn -> b)) =
  let rel = relateNaive r (base a) (base b)
      rel' = tr r a b
  in counterexample (show rel')
       (rel ===
         case rel' of
           Subtype -> Relation (a <= b) (b <= a) False False
           MayIntersect -> Relation False False False False
           Disjoint -> Relation False False True False)

prop_relateNaiveBot :: TF TR BDD -> Property
prop_relateNaiveBot (TF r b) =
  let rel = relateNaive r Bot b
      bot = isBottom r b
      top = isBottom r (complement b)
  in rel === Relation True bot True top

prop_relateNaiveTop :: TF TR BDD -> Property
prop_relateNaiveTop (TF r b) =
  let rel = relateNaive r Top b
      bot = isBottom r b
      top = isBottom r (complement b)
  in rel === Relation top True bot True

prop_relateNaive_comm :: TF TR (BDD, BDD) -> Property
prop_relateNaive_comm (TF r (a,b)) =
  relateNaive r a b === commute (relateNaive r b a)

prop_relateNaive_rcomp :: TF TR (BDD, BDD) -> Property
prop_relateNaive_rcomp (TF r (a,b)) =
  relateNaive r a (complement b) === rightComplement (relateNaive r a b)

prop_relateNaive_lcomp :: TF TR (BDD, BDD) -> Property
prop_relateNaive_lcomp (TF r (a,b)) =
  relateNaive r (complement a) b === leftComplement (relateNaive r a b)

prop_relateNaive_lcomp_counter :: Property
prop_relateNaive_lcomp_counter = prop_relateNaive_lcomp (TF r (a,b)) where
  r = mkDag [(1,[0]),(2,[0]),(3,[2]),(4,[1])]
  a = (select 4 Top (base 3))
  b = (select 3 (base 2) (base 1))

-- Test join
prop_relateNaive_semigroup :: TF TR ((BaseInc, BDD, BDD), BDD) -> Property
prop_relateNaive_semigroup (TF r ((p -> i, a, b), c)) =
  let v = (root a `max` root b `max` root c) + i
      at = eraseDisjoints r v a
      ct = eraseDisjoints r v c
      be = eraseSubtypes r v b
      ce = eraseSubtypes r v c
  in relateNaive r (select v a b) c ===
       (relateNaive r at ct <> relateNaive r be ce)

prop_relateNaive_relate :: TF TR (BDD, BDD) -> Property
prop_relateNaive_relate (TF r (a,b)) =
  relateNaive r a b === relate r a b

prop_canon_common_refl :: TF TR (BaseInc, BDD) -> Property
prop_canon_common_refl (TF r (p -> i, b)) =
    common r (root b' + i) b' b' === Just b'
  where b' = canonS r b

prop_eraseDisjointsC :: TF TR (BaseInc, BDD) -> Property
prop_eraseDisjointsC (TF r (p -> i, b)) =
  let v = root b + i
      bc = canonS r b
  in eraseDisjointsC r v bc === canonS r (eraseDisjoints r v b)

prop_eraseSubtypesC :: TF TR (BaseInc, BDD) -> Property
prop_eraseSubtypesC (TF r (p -> i, b)) =
  let v = root b + i
      bc = canonS r b
  in eraseSubtypesC r v bc === canonS r (eraseSubtypes r v b)

prop_commonC :: TF TR BDD -> Property
prop_commonC (TF r (bdd -> Select i t e)) =
  let tc = canonS r (eraseDisjoints r i t)
      ec = canonS r (eraseSubtypes r i e)
  in case (commonC r i tc ec, canonS r <$> common r i tc ec) of
    (Nothing, Nothing) -> property Discard
    (Just Bot, Just Bot) -> property Discard
    (Just Top, Just Top) -> property Discard
    (a, b) -> counterexample (show (tc,ec)) (a === b)
prop_commonC _ = property Discard

prop_commonC_canon :: TF TR BDD -> Property
prop_commonC_canon (TF r (bdd -> Select i t e)) =
  let tc = canonS r (eraseDisjoints r i t)
      ec = canonS r (eraseSubtypes r i e)
  in case commonC r i tc ec of
    Nothing -> property Discard
    Just Bot -> property Discard
    Just Top -> property Discard
    Just res -> res === canonS r res
prop_commonC_canon _ = property Discard

prop_intersect_canon :: TF TR (BDD, BDD) -> Property
prop_intersect_canon (TF r (a,b)) =
    counterexample (show (a', b'))
      (intersect r a' b' === canonS r (basicIntersect a b))
  where a' = canonS r a
        b' = canonS r b

-- Last because high rejection rates.

prop_relateNaive_sub :: TF TR (BDD, BDD) -> Property
prop_relateNaive_sub (TF r (a,b))
  | isSubtype rel && isSupertype rel =
    counterexample "equiv" (modelDiff r a b === [])
  | isSubtype rel =
    counterexample "subtype" (modelDiff r a i === [])
  | isSupertype rel =
    counterexample "supertype" (modelDiff r b i === [])
  | otherwise = property Discard
  where rel = relateNaive r a b
        i = basicIntersect a b

prop_relateNaive_subc :: TF TR (BDD, BDD) -> Property
prop_relateNaive_subc (TF r (a,b))
  | isSubtypeComp rel && isSupertypeComp rel =
    counterexample "equiv" (modelDiff r a b' === [])
  | isSubtypeComp rel =
    counterexample "subtype" (modelDiff r a i === [])
  | isSupertypeComp rel =
    counterexample "supertype" (modelDiff r b' i === [])
  | otherwise = property Discard
  where rel = relateNaive r a b
        b' = complement b
        i = basicIntersect a b'

prop_relateNaive_disj :: TF TR (BDD, BDD) -> Property
prop_relateNaive_disj (TF r (a,b))
  | isDisjoint rel = model r (basicIntersect a b) === []
  | isDisjoint (rightComplement rel) = model r (basicIntersect a (complement b)) === []
  | otherwise = property Discard
  where rel = relateNaive r a b

prop_common_correct1 :: TF TR BDD -> Property
prop_common_correct1 (TF r b@(bdd -> Select c t e)) =
  let t' = eraseDisjoints r c t
      e' = eraseSubtypes r c e
  in case common r c t' e' of
    Just s -> modelDiff r b s === []
    Nothing -> property Discard
prop_common_correct1 _ = property Discard

-- This just takes ages.
prop_trToBDD_top :: TR -> Property
prop_trToBDD_top r =
  modelDiff r Top (trToBDD r) === []

------------------------------------------------------------

qc :: (Testable t) => t -> IO ()
qc = qcs 12

qcs :: (Testable t) => Int -> t -> IO ()
qcs s = quickCheckWith (stdArgs{ maxSuccess = 10000, maxSize = s, maxDiscardRatio = 10 })

return []

bddTestAll :: IO Bool
bddTestAll = $forAllProperties (quickCheckWithResult (stdArgs{maxSuccess=10000, maxDiscardRatio=10}))
