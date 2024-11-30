{-# LANGUAGE TemplateHaskell, ViewPatterns #-}
module BDD where
import Test.QuickCheck
import qualified Data.IntSet as S

import BDDSubtyping.BDD
import BDDSubtyping.DAG(mkDag, subs, tr, Relatedness(..))
import DAG() -- for Arbitrary DAG

type NBase = NonNegative Base
nn :: NonNegative i -> i
nn (NonNegative i) = i

instance Arbitrary BDD where
  arbitrary = sized mkBdd where
    mkBdd :: Int -> Gen BDD
    mkBdd n | n <= 0 = oneof [return Bot, return Top]
    mkBdd n = do
      t <- chooseInt (-2, n-1) >>= mkBdd
      e <- chooseInt (-2, n-1) >>= mkBdd
      return (select (n-1) t e)

prop_bdd_big :: TR -> BDD -> NBase -> Property
prop_bdd_big r b (nn -> i) =
  bddBases r b (root b + i + 1) === rightmost b

prop_base_empty :: NBase -> Property
prop_base_empty (nn -> i) =
  model (mkDag []) (base i) === [i]

prop_base :: TR -> NBase -> Property
prop_base r (nn -> i) =
  model r (base i) === S.toAscList (S.insert i (subs r i))

prop_fv_base :: NBase -> Property
prop_fv_base (nn -> i) =
  fv (base i) === S.singleton i

prop_exactly :: TR -> NBase -> Property
prop_exactly r (nn -> i) =
  model r (exactly i) === [i]

prop_fv_exactly :: NBase -> Property
prop_fv_exactly (nn -> i) =
  fv (exactly i) === S.singleton i

prop_bases_bot :: TR -> NBase -> Property
prop_bases_bot r (nn -> i) = bddBases r Bot i === False

prop_fv_bot :: Property
prop_fv_bot = fv Bot === mempty

prop_bases_top :: TR -> NBase -> Property
prop_bases_top r (nn -> i) = bddBases r Top i === True

prop_fv_top :: Property
prop_fv_top = fv Top === mempty

prop_bases_base :: TR -> NBase -> Property
prop_bases_base r (nn -> i) = bddBases r (base i) i === True

prop_complement :: TR -> BDD -> Property
prop_complement r a = modelDiff r a (complement a) === [0..root a + 1]

prop_fv_complement :: BDD -> Property
prop_fv_complement a = fv a === fv (complement a)

prop_union :: TR -> BDD -> BDD -> Property
prop_union r a b =
  let u = basicUnion a b
  in filter
       (\i -> (bddBases r a i || bddBases r b i) /= bddBases r u i)
       [0..1+maximum[root a, root b, root u]] === []

-- This is only true of *basic* union!
prop_fv_union :: BDD -> BDD -> Bool
prop_fv_union a b = fv (a `basicUnion` b) `S.isSubsetOf` (fv a <> fv b)

prop_union_idem :: BDD -> Property
prop_union_idem a = (a `basicUnion` a) === a

prop_union_comm :: BDD -> BDD -> Property
prop_union_comm a b = (a `basicUnion` b) === (b `basicUnion` a)

prop_union_assoc :: BDD -> BDD -> BDD -> Property
prop_union_assoc a b c = (a `basicUnion` (b `basicUnion` c)) === ((a `basicUnion` b) `basicUnion` c)

prop_union_ident :: BDD -> Property
prop_union_ident a = (a `basicUnion` Bot) === a

prop_univ_zero :: BDD -> Property
prop_univ_zero a = (a `basicUnion` Top) === Top

prop_excl_mid :: BDD -> Property
prop_excl_mid a = (a `basicUnion` complement a) === Top

prop_complex_excl_mid :: BDD -> BDD -> Property
prop_complex_excl_mid a b = ((a `basicUnion` b) `basicUnion` complement a) === Top

prop_neg_univ1 :: Property
prop_neg_univ1 = complement Bot === Top

prop_neg_univ2 :: Property
prop_neg_univ2 = Bot === complement Top

prop_double_complement :: BDD -> Property
prop_double_complement b = complement (complement b) === b

prop_robbins :: BDD -> BDD -> Property
prop_robbins a b = complement (complement (a `basicUnion` b) `basicUnion` complement (a `basicUnion` complement b)) === a

prop_robbins2 :: BDD -> BDD -> Property
prop_robbins2 a b = ((a `basicUnion` b) `basicIntersect` (a `basicUnion` complement b)) === a

prop_eraseSubtypes_root :: TR -> BDD -> Property
prop_eraseSubtypes_root r b@(bdd -> Select i t e) =
  modelDiff r b (select i t (eraseSubtypes r i e)) === []
prop_eraseSubtypes_root _ _ = property Discard

prop_eraseSubtypes_fv :: TR -> NBase -> BDD -> Property
prop_eraseSubtypes_fv r (nn -> ii) e
  | iSubs `S.disjoint` fve = erased === e
  | otherwise = property (fv erased `S.isSubsetOf` (fve `S.difference` iSubs))
  where iSubs = subs r i
        fve = fv e
        erased = eraseSubtypes r i e
        i = root e + ii + 1

prop_eraseSubtypes_complement :: TR -> NBase -> BDD -> Property
prop_eraseSubtypes_complement r (nn -> i) b =
  complement (eraseSubtypes r c b) === eraseSubtypes r c (complement b)
  where c = root b + i + 1

prop_eraseSubtypes_idem :: TR -> NBase -> BDD -> Property
prop_eraseSubtypes_idem r (nn -> i) b =
  eraseSubtypes r c (eraseSubtypes r c b) === eraseSubtypes r c b
  where c = root b + i + 1

prop_eraseSubtypes_union :: TR -> NBase -> BDD -> BDD -> Property
prop_eraseSubtypes_union r (nn -> i) a b =
  eraseSubtypes r c (a `basicUnion` b) === (eraseSubtypes r c a `basicUnion` eraseSubtypes r c b)
  where c = (root a `max` root b) + i + 1

prop_eraseDisjoints_root :: TR -> BDD -> Property
prop_eraseDisjoints_root r b@(bdd -> Select i t e) =
  modelDiff r b (select i (eraseDisjoints r i t) e) === []
prop_eraseDisjoints_root _ _ = property Discard

prop_eraseDisjoints_fv :: TR -> NBase -> BDD -> Property
prop_eraseDisjoints_fv r (nn -> ii) e
  | iDisjs `S.disjoint` fve = erased === e
  | otherwise = property (fv erased `S.isSubsetOf` (fve `S.difference` iDisjs))
  where iDisjs = S.fromList (filter ((Disjoint==). tr r i) [0..i-1])
        fve = fv e
        erased = eraseDisjoints r i e
        i = root e + ii + 1

prop_eraseDisjoints_complement :: TR -> NBase -> BDD -> Property
prop_eraseDisjoints_complement r (nn -> i) b =
  complement (eraseDisjoints r c b) === eraseDisjoints r c (complement b)
  where c = root b + i + 1

prop_eraseDisjoints_idem :: TR -> NBase -> BDD -> Property
prop_eraseDisjoints_idem r (nn -> i) b =
  eraseDisjoints r c (eraseDisjoints r c b) === eraseDisjoints r c b
  where c = root b + i + 1

prop_eraseDisjoints_union :: TR -> NBase -> BDD -> BDD -> Property
prop_eraseDisjoints_union r (nn -> i) a b =
  eraseDisjoints r c (a `basicUnion` b) === (eraseDisjoints r c a `basicUnion` eraseDisjoints r c b)
  where c = (root a `max` root b) + i + 1

prop_erase_root :: TR -> BDD -> Property
prop_erase_root r b@(bdd -> Select i t e) =
  modelDiff r b (select i (eraseDisjoints r i t) (eraseSubtypes r i e)) === []
prop_erase_root _ _ = property Discard

prop_fullyErase :: TR -> BDD -> Property
prop_fullyErase r b = modelDiff r b (fullyErase r b) === []

prop_fullyErase_idem :: TR -> BDD -> Property
prop_fullyErase_idem r b =
  c === fullyErase r c
  where c = fullyErase r b

-- common always succeeds when handed two equal BDDs
prop_common_refl :: TR -> BDD -> Property
prop_common_refl r b =
  case common r (1 + root b) b b of
    Just b2 -> modelDiff r b b2 === []
    Nothing -> property False

prop_common :: TR -> BDD -> Property
prop_common r b@(bdd -> Select i t e) =
  let t' = eraseDisjoints r i t
      e' = eraseSubtypes r i e
  in case common r i t' e' of
    Just c -> modelDiff r b c === []
    Nothing -> t =/= e .&&. t' =/= e'
prop_common _ _ = property Discard

prop_common_fv :: TR -> BDD -> Property
prop_common_fv r (bdd -> Select i t e) =
  let t' = eraseDisjoints r i t
      e' = eraseSubtypes r i e
  in case common r i t' e' of
    Just c -> property (fv c `S.isSubsetOf` (fv t' <> fv e'))
    Nothing -> t =/= e .&&. t' =/= e'
prop_common_fv _ _ = property Discard

prop_common_complete :: TR -> BDD -> Property
prop_common_complete r s =
  case (eraseDisjoints r c s, eraseSubtypes r c s) of
    (a,b) | a /= b -> common r c a b =/= Nothing
    _ -> property Discard
  where c = root s + 1

prop_common_eq :: TR -> BDD -> Property
prop_common_eq r s =
  let c = root s + 1
  in common r c s s === Just s

prop_common_correct2 :: TR -> BDD -> Property
prop_common_correct2 r s =
  let c = root s + 1
      t = eraseDisjoints r c s
      e = eraseSubtypes r c s
      Just k = common r c t e
  in modelDiff r (select c t e) k === []

prop_common_complement :: TR -> BDD -> Property
prop_common_complement r (bdd -> Select c t e) =
  let t' = eraseDisjoints r c t
      e' = eraseSubtypes r c e
  in case common r c t' e' of
    Just s -> common r c (complement t') (complement e') === Just (complement s)
    Nothing -> property Discard
prop_common_complement _ _ = property Discard

prop_commonOrErase_refl :: TR -> BDD -> Property
prop_commonOrErase_refl r b =
  let c = root b + 1
      t = eraseDisjoints r c b
      e = eraseSubtypes r c b
      Just s = common r c t e
  in commonOrErase r c b b === (t, e, Just s)

prop_commonOrErase :: TR -> BDD -> Property
prop_commonOrErase r (bdd -> Select c t e) =
  let t' = eraseDisjoints r c t
      e' = eraseSubtypes r c e
  in commonOrErase r c t e === (t', e', common r c t' e')
prop_commonOrErase _ _ = property Discard

canon_idem :: (TR -> BDD -> BDD) -> TR -> BDD -> Property
canon_idem canon r b =
  counterexample (unlines $ map show cs) (c == canon r c)
  where
    c = canon r b
    cc name can = let c' = can r b in (name, c', can r c')
    cs = [ ct | ct@(_,c1,c2) <- [cc "canonTD" canonTD, cc "canonBU" canonBU, cc "canonS" canonS, cc "canonW" canonW], c1 /= c2]

-- Believed false
prop_canonTD_idem :: TR -> BDD -> Property
prop_canonTD_idem = canon_idem canonTD

-- Believed false
prop_canonBU_idem :: TR -> BDD -> Property
prop_canonBU_idem = canon_idem canonBU

-- True?
prop_canonS_idem :: TR -> BDD -> Property
prop_canonS_idem = canon_idem canonS

-- True????
prop_canonW_idem :: TR -> BDD -> Property
prop_canonW_idem = canon_idem canonW

prop_isBottom :: TR -> BDD -> Property
prop_isBottom r b
 | isBottom r b = counterexample "bottom" (model r b === [])
 | otherwise = counterexample "nonbottom" (model r b =/= [])

-- Last because high rejection rates.
prop_common_correct1 :: TR -> BDD -> Property
prop_common_correct1 r b@(bdd -> Select c t e) =
  let t' = eraseDisjoints r c t
      e' = eraseSubtypes r c e
  in case common r c t' e' of
        Just s -> modelDiff r b s === []
        Nothing -> property Discard
prop_common_correct1 _ _ = property Discard

-- This just takes ages.
prop_trToBDD_top :: TR -> Property
prop_trToBDD_top r =
  modelDiff r Top (trToBDD r) === []

------------------------------------------------------------

ttr :: TR
ttr = mkDag [(0, [0]), (1, [1]), (2, [0, 1, 2]), (3, [1, 3])]


qc :: (Testable t) => t -> IO ()
qc = qcs 12

qcs :: (Testable t) => Int -> t -> IO ()
qcs s = quickCheckWith (stdArgs{ maxSuccess = 10000, maxSize = s, maxDiscardRatio = 3 })

return []

bddTestAll :: IO Bool
bddTestAll = $forAllProperties (quickCheckWithResult (stdArgs{maxSuccess=10000, maxDiscardRatio=1000}))
