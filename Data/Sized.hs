{-# LANGUAGE ConstraintKinds, DataKinds, DeriveDataTypeable, DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor, DeriveTraversable, FlexibleContexts             #-}
{-# LANGUAGE FlexibleInstances, GADTs, GeneralizedNewtypeDeriving           #-}
{-# LANGUAGE KindSignatures, LambdaCase, LiberalTypeSynonyms                #-}
{-# LANGUAGE MultiParamTypeClasses, NoMonomorphismRestriction               #-}
{-# LANGUAGE PatternSynonyms, PolyKinds, ScopedTypeVariables                #-}
{-# LANGUAGE StandaloneDeriving, TypeFamilies, TypeOperators, ViewPatterns  #-}
{-# OPTIONS_GHC -fno-warn-type-defaults -fno-warn-orphans #-}
module Data.Sized
       (Sized, empty, toList, toContainer, replicate, replicate',
        singleton, uncons,
        unsafeFromList, unsafeFromList', fromList, fromList',
        unsafeFromContainer, unsafeFromContainer',
        fromContainer, fromContainer',
        append, head, last, tail, init, null,
        length, sLength, map, reverse, intersperse,
        take, takeAtMost, drop, splitAt, splitAtMost, elem, notElem,
        find, (!!), (%!!), index, sIndex, elemIndex, sElemIndex,
        findIndex, sFindIndex, findIndices, sFindIndices,
        elemIndices, sElemIndices, zip, zipSame, zipWith, zipWithSame, unzip,
        ConsView (..), viewCons, SnocView(..), viewSnoc,
        pattern (:<), pattern NilL, pattern (:>), pattern NilR)
       where
import           Data.Constraint
import           Data.Constraint.Forall
import           Data.Foldable          (Foldable)
import           Data.ListLike          (FoldableLL, ListLike)
import qualified Data.ListLike          as LL
import qualified Data.Sequence          as Seq
import           Data.Traversable       (Traversable)
import           Data.Type.Equality     hiding (trans)
import           Data.Type.Natural
import           Data.Type.Ordinal      (Ordinal, ordToInt)
import           Data.Typeable          (Typeable)
import qualified Data.Vector            as V
import           Prelude                hiding (drop, elem, head, init, last,
                                         length, map, notElem, null, replicate,
                                         reverse, splitAt, tail, take, unzip,
                                         zip, zipWith, (!!))
import qualified Prelude                as P

newtype Sized f n a =
  Sized { runSized :: f a
        } deriving (Read, Show, Eq, Ord, Typeable,
                    Functor, Foldable, Traversable)

toContainer :: Sized f n a -> f a
toContainer = runSized
{-# INLINE toContainer #-}

empty :: ListLike (f a) a => Sized f Z a
empty = Sized LL.empty
{-# INLINE empty #-}

wrap0 :: (f a -> b) -> Sized f n a -> b
wrap0 f (Sized xs) = f xs
{-# INLINE wrap0 #-}

instance Class (FoldableLL f a) (ListLike f a) where
  cls = Sub Dict

instance ListLike f a :=> FoldableLL f a where
  ins = Sub Dict

instance FoldableLL (f a) a => FoldableLL (Sized f n a) a where
  {-# SPECIALISE instance LL.FoldableLL (Sized [] n a) a #-}
  {-# SPECIALISE instance LL.FoldableLL (Sized V.Vector n a) a #-}
  {-# SPECIALISE instance LL.FoldableLL (Sized Seq.Seq n a) a #-}
  foldl f a (Sized xs) = LL.foldl f a xs
  {-# INLINE foldl #-}
  foldl' f a (Sized xs) = LL.foldl' f a xs
  {-# INLINE foldl' #-}
  foldl1 f (Sized xs) = LL.foldl1 f xs
  {-# INLINE foldl1 #-}
  foldr f a (Sized xs) = LL.foldr f a xs
  {-# INLINE foldr #-}
  foldr' f a (Sized xs) = LL.foldr' f a xs
  {-# INLINE foldr' #-}
  foldr1 f (Sized xs) = LL.foldr1 f xs
  {-# INLINE foldr1 #-}

replicate :: ListLike (f a) a => SNat n -> a -> Sized f n a
replicate sn a = Sized $ LL.replicate (sNatToInt sn) a
{-# INLINE replicate #-}

replicate' :: (SingI (n :: Nat), ListLike (f a) a) => a -> Sized f n a
replicate' = withSing replicate
{-# INLINE replicate' #-}

singleton :: ListLike (f a) a => a -> Sized f One a
singleton = Sized . LL.singleton
{-# INLINE singleton #-}

uncons :: ListLike (f a) a => Sized f (S n) a -> (a, Sized f n a)
uncons (Sized xs) = (LL.head xs, Sized $ LL.tail xs)
{-# INLINE uncons #-}

-- | Unsafe version of 'fromList'. If a given list is shorter than
--   the length @n@, then something unusual happens.
unsafeFromList :: ListLike (f a) a => SNat n -> [a] -> Sized f n a
unsafeFromList sn xs = Sized $ LL.fromList $ P.take (sNatToInt sn) $ xs
{-# INLINE [2] unsafeFromList #-}

{-# RULES
"unsafeFromList/Zero" forall (sz :: SNat Z) xs.
  unsafeFromList sz xs = unsafeFromContainer sz xs
"unsafeFromList/List" forall sn (xs :: [a]).
  unsafeFromList sn xs = Sized (P.take (sNatToInt sn) xs)
 #-}

fromList :: ListLike (f a) a => SNat n -> [a] -> Maybe (Sized f n a)
fromList sn xs =
  if P.length xs < sNatToInt sn
  then Nothing
  else Just $ unsafeFromList sn xs
{-# INLINABLE [2] fromList #-}

{-# RULES
"fromList/Zero" forall (sn :: SNat Z) xs.
  fromList sn xs = Just $ Sized $ LL.empty
"fromList/List" forall sn (xs :: [a]).
  fromList sn xs = fromContainer sn xs
  #-}

fromList' :: (ListLike (f a) a, SingI (n :: Nat)) => [a] -> Maybe (Sized f n a)
fromList' = withSing fromList
{-# INLINE fromList' #-}

unsafeFromList' :: (SingI (n :: Nat), ListLike (f a) a) => [a] -> Sized f n a
unsafeFromList' = withSing unsafeFromList
{-# INLINE unsafeFromList' #-}

unsafeFromContainer :: ListLike (f a) a => SNat n -> f a -> Sized f n a
unsafeFromContainer sn xs = Sized $ LL.take (sNatToInt sn) xs
{-# INLINE [2] unsafeFromContainer #-}

{-# RULES
"unsafeFromContainer/Zero" forall (sn :: SNat Z) xs.
  unsafeFromContainer sn xs = Sized $ LL.empty
  #-}

fromContainer :: ListLike (f a) a => SNat n -> f a -> Maybe (Sized f n a)
fromContainer sn xs =
  if LL.length xs < sNatToInt sn
  then Nothing
  else Just $ unsafeFromContainer sn xs
{-# INLINE [2] fromContainer #-}

{-# RULES
"fromContainer/Zero" forall (sn :: SNat Z) xs.
  fromContainer sn xs = Just $ Sized LL.empty
  #-}

fromContainer' :: (ListLike (f a) a, SingI (n :: Nat)) => f a -> Maybe (Sized f n a)
fromContainer' = withSing fromContainer
{-# INLINE fromContainer' #-}

unsafeFromContainer' :: (SingI (n :: Nat), ListLike (f a) a) => f a -> Sized f n a
unsafeFromContainer' = withSing unsafeFromContainer
{-# INLINE unsafeFromContainer' #-}

toList :: ListLike (f a) a => Sized f n a -> [a]
toList = LL.toList . runSized
{-# INLINE [2] toList #-}

{-# RULES
"toList/" forall (xs :: Sized [] a n).
  toList xs = runSized xs
  #-}

append :: ListLike (f a) a => Sized f n a -> Sized f m a -> Sized f (n :+ m) a
append (Sized xs) (Sized ys) = Sized $ LL.append xs ys
{-# INLINE append #-}

head :: ListLike (f a) a => Sized f (S n) a -> a
head = LL.head . runSized
{-# INLINE head #-}

last ::  ListLike (f a) a => Sized f (S n) a -> a
last = LL.last . runSized
{-# INLINE last #-}

tail :: ListLike (f a) a => Sized f (S n) a -> Sized f n a
tail = Sized . LL.tail . runSized
{-# INLINE tail #-}

init :: ListLike (f a) a => Sized f (S n) a -> Sized f n a
init = Sized . LL.init . runSized
{-# INLINE init #-}

null :: ListLike (f a) a => Sized f n a -> Bool
null = LL.null . runSized
{-# INLINE [2] null #-}
{-# RULES
"null/Zero" forall (xs :: Sized f Z a).
  null xs = True
"null/Succ" forall (xs :: Sized f (S n) a).
  null xs = False
  #-}

length :: ListLike (f a) a => Sized f n a -> Int
length = LL.length . runSized
{-# INLINE length #-}

sLength :: SingI n => Sized f n a -> SNat n
sLength _ = sing
{-# INLINE sLength #-}

map :: Functor f => (a -> b) -> Sized f n a -> Sized f n b
map f = Sized . fmap f . runSized
{-# INLINE map #-}

reverse :: ListLike (f a) a => Sized f n a -> Sized f n a
reverse = Sized . LL.reverse . runSized
{-# INLINE reverse #-}

intersperse :: ListLike (f a) a => a -> Sized f n a -> Sized f ((Two :* n) :-: One) a
intersperse a = Sized . LL.intersperse a . runSized
{-# INLINE intersperse #-}

take :: (ListLike (f a) a, (n :<<= m) ~ True)
     => SNat n -> Sized f m a -> Sized f n a
take sn (Sized xs) = Sized $ LL.take (sNatToInt sn) xs
{-# INLINE take #-}

takeAtMost :: (ListLike (f a) a)
           => SNat n -> Sized f m a -> Sized f (Min n m) a
takeAtMost sn (Sized xs) = Sized $ LL.take (sNatToInt sn) xs
{-# INLINE takeAtMost #-}

drop :: (ListLike (f a) a, (n :<<= m) ~ True)
     => SNat n -> Sized f m a -> Sized f (m :-: n) a
drop sn = Sized . LL.drop (sNatToInt sn) . runSized
{-# INLINE drop #-}

splitAt :: (LL.ListLike (f a) a, (n :<<= m) ~ True)
        => SNat n -> Sized f m a -> (Sized f n a, Sized f (m :-: n) a)
splitAt n xs =
  let (as, bs) = LL.splitAt (sNatToInt n) (runSized xs)
  in (Sized as, Sized bs)
{-# INLINE splitAt #-}

splitAtMost :: LL.ListLike (f a) a
            => SNat n -> Sized f m a -> (Sized f (Min n m) a, Sized f (m :-: n) a)
splitAtMost n xs =
  let (as, bs) = LL.splitAt (sNatToInt n) (runSized xs)
  in (Sized as, Sized bs)
{-# INLINE splitAtMost #-}

elem :: (ListLike (f a) a, Eq a) => a -> Sized f n a -> Bool
elem a = LL.elem a . runSized
{-# INLINE elem #-}

notElem :: (ListLike (f a) a, Eq a) => a -> Sized f n a -> Bool
notElem a = LL.notElem a . runSized
{-# INLINE notElem #-}

find :: ListLike (f a) a => (a -> Bool) -> Sized f n a -> Maybe a
find p = wrap0 (LL.find p)
{-# INLINE find #-}

(!!) :: (ListLike (f a) a, (n :<<= m) ~ True) => Sized f (S m) a -> SNat n -> a
Sized xs !! n = LL.index xs (sNatToInt n)
{-# INLINE (!!) #-}

(%!!) :: ListLike (f a) a => Sized f n a -> Ordinal n -> a
Sized xs %!! n = LL.index xs (ordToInt n)
{-# INLINE (%!!) #-}

index :: (ListLike (f c) c, (n :<<= m) ~ 'True) => SNat n -> Sized f (S m) c -> c
index = flip (!!)
{-# INLINE index #-}

sIndex :: ListLike (f c) c => Ordinal n -> Sized f n c -> c
sIndex = flip (%!!)
{-# INLINE sIndex #-}

elemIndex :: (Eq a, ListLike (f a) a) => a -> Sized f n a -> Maybe Int
elemIndex a = findIndex (== a)
{-# INLINE elemIndex #-}

sElemIndex :: (SingI n, ListLike (f a) a, Eq a)
           => a -> Sized f n a -> Maybe (Ordinal n)
sElemIndex a = sFindIndex (== a)
{-# INLINE sElemIndex #-}

sFindIndex :: (SingI n, ListLike (f a) a) => (a -> Bool) -> Sized f n a -> Maybe (Ordinal n)
sFindIndex p = fmap toEnum . findIndex p
{-# INLINE sFindIndex #-}

findIndex :: ListLike (f a) a => (a -> Bool) -> Sized f n a -> Maybe Int
findIndex p = LL.findIndex p . runSized
{-# INLINE findIndex #-}

findIndices :: ListLike (f a) a => (a -> Bool) -> Sized f n a -> [Int]
findIndices p = LL.findIndices p . runSized
{-# INLINE findIndices #-}

sFindIndices :: (SingI n, ListLike (f a) a) => (a -> Bool) -> Sized f n a -> [Ordinal n]
sFindIndices p = fmap toEnum . findIndices p
{-# INLINE sFindIndices #-}

elemIndices :: (ListLike (f a) a, Eq a) => a -> Sized f n a -> [Int]
elemIndices a = LL.elemIndices a . runSized
{-# INLINE elemIndices #-}


sElemIndices :: (SingI n, ListLike (f a) a, Eq a) => a -> Sized f n a -> [Ordinal n]
sElemIndices p = fmap toEnum . elemIndices p
{-# INLINE sElemIndices #-}

zip :: (LL.ListLike (f a) a, LL.ListLike (f b) b, LL.ListLike (f (a, b)) (a, b))
    => Sized f n a -> Sized f m b -> Sized f (Min n m) (a, b)
zip (Sized xs) (Sized ys) = Sized $ LL.zip xs ys
{-# INLINE zip #-}

zipSame :: (ListLike (f (a, b)) (a, b), ListLike (f b) b, ListLike (f a) a)
        => Sized f n a -> Sized f n b -> Sized f n (a, b)
zipSame (Sized xs) (Sized ys) = Sized $ LL.zip xs ys
{-# INLINE zipSame #-}

zipWith :: (LL.ListLike (f a) a, LL.ListLike (f b) b, LL.ListLike (f c) c)
    => (a -> b -> c) -> Sized f n a -> Sized f m b -> Sized f (Min n m) c
zipWith f (Sized xs) (Sized ys) = Sized $ LL.zipWith f xs ys
{-# INLINE zipWith #-}

zipWithSame :: (LL.ListLike (f a) a, LL.ListLike (f b) b, LL.ListLike (f c) c)
    => (a -> b -> c) -> Sized f n a -> Sized f n b -> Sized f n c
zipWithSame f (Sized xs) (Sized ys) = Sized $ LL.zipWith f xs ys
{-# INLINE zipWithSame #-}

unzip :: (ListLike (f b) b, ListLike (f a) a, ListLike (f (a, b)) (a, b))
      => Sized f n (a, b) -> (Sized f n a, Sized f n b)
unzip (Sized xys) =
  let (xs, ys) = LL.unzip xys
  in (Sized xs, Sized ys)
{-# INLINE unzip #-}

data ConsView f n a where
  NilCV :: ConsView f Z a
  (::-) :: SingI n => a -> Sized f n a -> ConsView f (S n) a

infixr 5 ::-

viewCons :: forall f a n. (SingI n, ListLike (f a) a)
         => Sized f n a
         -> ConsView f n a
viewCons sz = case sing :: SNat n of
  SZ    -> NilCV
  SS n' -> withSingI n' $ head sz ::- tail sz

infixr 5 :<
pattern a :< b <- (viewCons -> a ::- b)
pattern NilL   <- (viewCons -> NilCV)

data SnocView f n a where
  NilSV :: SnocView f Z a
  (:-:) :: SingI n => Sized f n a -> a -> SnocView f (S n) a


viewSnoc :: forall f n a. (SingI n, ListLike (f a) a)
         => Sized f n a
         -> SnocView f n a
viewSnoc sz = case sing :: SNat n of
  SZ   -> NilSV
  SS n -> withSingI n $ init sz :-: last sz

infixl 5 :>
pattern a :> b <- (viewSnoc -> a :-: b)
pattern NilR   <- (viewSnoc -> NilSV)
