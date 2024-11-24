module BDDSubtyping.BDD(
  BDD(..), TR,
  select, root, size, rightmost,
  bdd_contains_exact, bdd_exacts, model, model_eq,
  union, intersect,
  erase_subtypes, erase_disjoints, fully_erase,
  common
) where
import BDDSubtyping.DAG(DAG, Relatedness(..), tr)
import Control.Monad(liftM2)

type Name = Int

data BDD = Bot | Select Name BDD BDD | Top
  deriving (Eq, Show)

select :: Name -> BDD -> BDD -> BDD
select i t e
  | t == e = e
  | otherwise = Select i t e

type TR = DAG

root :: BDD -> Name
root (Select i _ _) = i
root _ = 0

bdd_contains_exact :: TR -> BDD -> Name -> Bool
bdd_contains_exact _ Top _ = True
bdd_contains_exact _ Bot _ = False
bdd_contains_exact trd (Select n t e) i =
  case tr trd n i of
    Subtype | n >= i -> bdd_contains_exact trd t i
    _ -> bdd_contains_exact trd e i

bdd_exacts :: TR -> BDD -> (Name -> Bool)
bdd_exacts trd bdd = bdde bdd where
  bdde :: BDD -> (Name -> Bool)
  bdde Top = const True
  bdde Bot = const False
  bdde (Select i t e) = (\j -> if j <= i && tr trd j i == Subtype then bdd_t j else bdd_e j)
    where bdd_e = bdde e
          bdd_t = bdde t

rightmost :: BDD -> Bool
rightmost (Select _ _ e) = rightmost e
rightmost Top = True
rightmost Bot = False

model :: TR -> BDD -> [Bool]
model trd bdd = map (bdd_exacts trd bdd) [0..root bdd + 1]

model_eq :: TR -> BDD -> BDD -> Bool
model_eq trd a0 b0 = meq (model trd a0) (model trd b0) where
  meq [a] bs = all (a==) bs
  meq as [b] = all (==b) as
  meq (a:as) (b:bs) = a == b && meq as bs
  meq _ _ = error "Null model?"

union :: BDD -> BDD -> BDD
union Top _ = Top
union Bot b = b
union _ Top = Top
union a Bot = a
union a@(Select i1 t1 e1) b@(Select i2 t2 e2)
  | i1 > i2 = select i1 (union t1 b) (union e1 b)
  | i1 == i2 = select i1 (union t1 t2) (union e1 e2)
  | otherwise = select i2 (union a t2) (union a e2)

intersect :: BDD -> BDD -> BDD
intersect Top a = a
intersect Bot _ = Bot
intersect b Top = b
intersect _ Bot = Bot
intersect a@(Select i1 t1 e1) b@(Select i2 t2 e2)
  | i1 > i2 = select i1 (intersect t1 b) (intersect e1 b)
  | i1 == i2 = select i1 (intersect t1 t2) (intersect e1 e2)
  | otherwise = select i2 (intersect a t2) (intersect a e2)

erase_subtypes :: TR -> Int -> BDD -> BDD
erase_subtypes trd i (Select j t e)
  | j < i && tr trd j i == Subtype = e
  | otherwise = select j (erase_subtypes trd i t) (erase_subtypes trd i e)
erase_subtypes _ _ leaf = leaf

erase_disjoints :: TR -> Int -> BDD -> BDD
erase_disjoints trd i (Select j t e)
  | tr trd j i == Disjoint = e
  | otherwise = select j (erase_disjoints trd i t) (erase_disjoints trd i e)
erase_disjoints _ _ leaf = leaf

fully_erase :: TR -> BDD -> BDD
fully_erase trd (Select i t e) = select i (fully_erase trd (erase_disjoints trd i t)) (fully_erase trd (erase_subtypes trd i e))
fully_erase _ leaf = leaf

select' :: Int -> Maybe BDD -> Maybe BDD -> Maybe BDD
select' i = liftM2 (select i)

common :: TR -> Int -> BDD -> BDD -> Maybe BDD
common _   _ Top Bot = Nothing
common _   _ Bot Top = Nothing
common _   _ Top Top = Just Top
common _   _ Bot Bot = Just Bot
common trd c t@(Select it tt et) e@(Select ie te ee)
  | it > ie && tr trd it c == Subtype = select' it (Just tt) (common trd c et e)
  | it > ie = select' it (common trd c tt e) (common trd c et e)
  | it == ie = select' it (common trd c tt te) (common trd c et ee)
  | it < ie && tr trd ie c == Disjoint = select' ie (Just te) (common trd c t ee)
  | it < ie = select' ie (common trd c t te) (common trd c t ee)
common trd c (Select it tt et) e
  | tr trd it c == Subtype = select' it (Just tt) (common trd c et e)
  | otherwise = select' it (common trd c tt e) (common trd c et e)
common trd c t (Select ie te ee)
  | tr trd ie c == Disjoint = select' ie (Just te) (common trd c t ee)
  | otherwise = select' ie (common trd c t te) (common trd c t ee)

size :: BDD -> Int
size (Select _ t e) = 1 + size t + size e
size _ = 0
