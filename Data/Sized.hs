{-# LANGUAGE ConstraintKinds, DataKinds, DeriveDataTypeable, DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor, DeriveTraversable, FlexibleContexts             #-}
{-# LANGUAGE FlexibleInstances, GADTs, GeneralizedNewtypeDeriving           #-}
{-# LANGUAGE KindSignatures, LambdaCase, LiberalTypeSynonyms                #-}
{-# LANGUAGE MultiParamTypeClasses, NoMonomorphismRestriction               #-}
{-# LANGUAGE PatternSynonyms, PolyKinds, ScopedTypeVariables                #-}
{-# LANGUAGE StandaloneDeriving, TypeFamilies, TypeOperators, ViewPatterns  #-}
{-# OPTIONS_GHC -fno-warn-type-defaults -fno-warn-orphans #-}
-- | This module provides the functionality to make length-parametrized types
--   from existing 'ListLike' and 'Functor' sequential types.
-- 
--   Most of the complexity of operations for @Sized f n a@ are the same as
--   original operations for @f@. For example, '!!' is O(1) for
--   @Sized Vector n a@ but O(i) for @Sized [] n a@.
--
--  This module also provides powerful view types and pattern synonyms to
--  inspect the sized sequence. See <#patterns Views and Patterns> for more detail.
module Data.Sized
       ( -- * Main Data-types
         Sized(), ListLikeF, SomeSized(..),
         -- * Accessors
         -- ** Length information
         length, sLength, null,
         -- ** Indexing
         (!!), (%!!), index, sIndex, head, last, uncons, unsnoc,
         -- ** Slicing
         tail, init, take, takeAtMost, drop, splitAt, splitAtMost,
         -- * Construction
         -- ** Initialisation
         empty, singleton, toSomeSized, replicate, replicate',
         -- ** Concatenation
         cons, snoc, (<|), (|>), append, (++), concat,
         -- ** Others
         zip, zipSame, zipWith, zipWithSame, unzip,
         -- * Transformation
         map, reverse, intersperse, nub, sort, sortBy, insert, insertBy,
         -- * Conversion
         -- ** List
         toList, fromList, fromList', unsafeFromList, unsafeFromList',
         fromListWithDefault, fromListWithDefault',
         -- ** Base container
         unsized,
         toSized, toSized', unsafeToSized, unsafeToSized',
         toSizedWithDefault, toSizedWithDefault',
         -- * Querying
         -- ** Partitioning
         Partitioned(..),
         takeWhile, dropWhile, span, break, partition,
         -- ** Searching
         elem, notElem, find, findIndex, sFindIndex, findIndices, sFindIndices,
         elemIndex, sElemIndex, elemIndices, sElemIndices,
         -- * Views and Patterns
         -- $views
         pattern (:<), pattern NilL , pattern (:>), pattern NilR,
         ConsView (..), viewCons, SnocView(..), viewSnoc
       ) where

import Data.Sized.Internal

import           Data.ListLike         (FoldableLL)
import qualified Data.ListLike         as LL
import           Data.Proxy            (Proxy (..))
import qualified Data.Sequence         as Seq
import           Data.Type.Monomorphic
import           Data.Type.Natural
import           Data.Type.Ordinal     (Ordinal, ordToInt)
import           Data.Typeable         (Typeable)
import qualified Data.Vector           as V
import           Prelude               (Bool (..), Enum (..), Eq (..),
                                        Functor (..), Int, Maybe (..), Num (..),
                                        Ord (..), Ordering, Show (..), flip,
                                        undefined, ($), (.))
import qualified Prelude               as P
import           Unsafe.Coerce         (unsafeCoerce)

-- | 'Sized' vector with the length is existentially quantified.
--   This type is used mostly when the return type's length cannot
--   be statically determined beforehand.
--
-- @SomeSized sn xs :: SomeSized f a@ stands for the 'Sized' sequence
-- @xs@ of element type @a@ and length @sn@.
data SomeSized f a where
  SomeSized :: (ListLikeF f, SingI n)
            => SNat n
            -> Sized f (n :: Nat) a
            -> SomeSized f a

-- | The type @Partitioned f n a@ represents partitioned sequence of length @n@.
--   Value @Partitioned lenL ls lenR rs@ stands for:
-- 
--   * Entire sequence is divided into @ls@ and @rs@, and their length
--     are @lenL@ and @lenR@ resp.
-- 
--   * @lenL + lenR = n@
data Partitioned f n a where
  Partitioned :: (ListLikeF f, SingI n, SingI m)
              => SNat n
              -> Sized f (n :: Nat) a
              -> SNat m
              -> Sized f (m :: Nat) a
              -> Partitioned f (n :+ m) a

deriving instance Typeable SomeSized

deriving instance Show (f a) => Show (SomeSized f a)
instance Eq (f a) => Eq (SomeSized f a) where
  (SomeSized _ (Sized xs)) == (SomeSized _ (Sized ys)) = xs == ys

-- | Consruct the 'Sized' sequence from base type, but
--   the length parameter is dynamically determined and
--   existentially quantified; see also 'SomeSized'.
toSomeSized :: forall f a. ListLikeF f => f a -> SomeSized f a
toSomeSized = givenListLikeF $ \xs ->
  case promote $ LL.length xs of
    Monomorphic sn -> withSingI sn $ SomeSized sn $ unsafeToSized sn xs

-- | Forget the length and obtain the wrapped base container.
unsized :: Sized f n a -> f a
unsized = runSized
{-# INLINE unsized #-}

-- | Empty sequence.
empty :: forall f a. ListLikeF f => Sized f Z a
empty = withListLikeF (Proxy :: Proxy (f a)) $ Sized LL.empty
{-# INLINE empty #-}

instance ListLikeF f => FoldableLL (Sized f n a) a where
  {-# SPECIALISE instance LL.FoldableLL (Sized [] n a) a #-}
  {-# SPECIALISE instance LL.FoldableLL (Sized V.Vector n a) a #-}
  {-# SPECIALISE instance LL.FoldableLL (Sized Seq.Seq n a) a #-}
  foldl  f a = givenListLikeF' $ LL.foldl f a
  {-# INLINE foldl #-}
  foldl' f a = givenListLikeF' $ LL.foldl' f a
  {-# INLINE foldl' #-}
  foldl1 f   = givenListLikeF' $ LL.foldl1 f
  {-# INLINE foldl1 #-}
  foldr  f a = givenListLikeF' $ LL.foldr f a
  {-# INLINE foldr #-}
  foldr' f a = givenListLikeF' $ LL.foldr' f a
  {-# INLINE foldr' #-}
  foldr1 f   = givenListLikeF' $ LL.foldr1 f
  {-# INLINE foldr1 #-}

-- | Append an element to the head of sequence.
cons :: (ListLikeF f) => a -> Sized f n a -> Sized f (S n) a
cons a = givenListLikeF' $ Sized . LL.cons a
{-# INLINE cons #-}

-- | Infix version of 'cons'.
(<|) :: (ListLikeF f) => a -> Sized f n a -> Sized f (S n) a
(<|) = cons
{-# INLINE (<|) #-}
infixr 5 <|

-- | Infix version of 'snoc'.
(|>) :: (ListLikeF f) => Sized f n a -> a -> Sized f (S n) a
(|>) = snoc
{-# INLINE (|>) #-}
infixl 5 |>

-- | Concatenates multiple sequences into one.
concat :: forall f f' m n a. (ListLikeF f, ListLikeF f')
       => Sized f' m (Sized f n a) -> Sized f (m :* n) a
concat =
  givenListLikeF' $ withListLikeF (Proxy :: Proxy (f' (f a))) $
  withListLikeF (Proxy :: Proxy (f a)) $
  Sized . LL.concat . fmap runSized

-- | Append an element to the tail of sequence.
snoc :: (ListLikeF f) => Sized f n a -> a -> Sized f (S n) a
snoc (Sized xs) a = withListLikeF' xs $ Sized $ LL.snoc xs a
{-# INLINE snoc #-}

-- | Replicates the same value.
replicate :: forall f n a. ListLikeF f => SNat n -> a -> Sized f n a
replicate sn a = withListLikeF (Proxy :: Proxy (f a)) $
                 Sized $ LL.replicate (sNatToInt sn) a
{-# INLINE replicate #-}

-- | 'replicate' with the length inferred.
replicate' :: (SingI (n :: Nat), ListLikeF f) => a -> Sized f n a
replicate' = withSing replicate
{-# INLINE replicate' #-}

-- | Sequence with one element.
singleton :: forall f a. ListLikeF f => a -> Sized f One a
singleton = withListLikeF (Proxy :: Proxy (f a)) $ Sized . LL.singleton
{-# INLINE singleton #-}

-- | Take the 'head' and 'tail' of non-empty sequence.
--   If you want to make case-analysis for general sequence,
--   see  <#patterns Views and Patterns> section.
uncons :: ListLikeF f => Sized f (S n) a -> (a, Sized f n a)
uncons = givenListLikeF (\xs -> (LL.head xs, Sized $ LL.tail xs)) . runSized
{-# INLINE uncons #-}

unsnoc :: ListLikeF f => Sized f (S n) a -> (Sized f n a, a)
unsnoc = givenListLikeF (\xs -> (Sized $ LL.init xs, LL.last xs)) . runSized
{-# INLINE unsnoc #-}

-- | Unsafe version of 'fromList'. If the length of the given list does not 
--   equal to @n@, then something unusual happens.
unsafeFromList :: forall f n a. ListLikeF f => SNat n -> [a] -> Sized f n a
unsafeFromList _ xs =
  withListLikeF (Proxy :: Proxy (f a)) $
  Sized $ LL.fromList xs
{-# INLINE [2] unsafeFromList #-}

{-# RULES
"unsafeFromList/List" forall sn (xs :: [a]).
  unsafeFromList sn xs = Sized (P.take (sNatToInt sn) xs)
 #-}

-- | Construct a @Sized f n a@ by padding default value if the given list is short.
fromListWithDefault :: forall f n a. ListLikeF f => SNat n -> a -> [a] -> Sized f n a
fromListWithDefault sn def xs =
  let len = sNatToInt sn
  in withListLikeF (Proxy :: Proxy (f a)) $
     Sized $ LL.fromList (P.take len xs) `LL.append` LL.replicate (len - P.length xs) def
{-# INLINABLE fromListWithDefault #-}


-- | 'fromListWithDefault' with the result length inferred.
fromListWithDefault' :: (SingI (n :: Nat), ListLikeF f) => a -> [a] -> Sized f n a
fromListWithDefault' = withSing fromListWithDefault
{-# INLINE fromListWithDefault' #-}

-- | If the given list is shorter than @n@, then returns @Nothing@
--   Otherwise returns @Sized f n a@ consisting of initial @n@ element
--   of given list.
fromList :: forall f n a. ListLikeF f => SNat n -> [a] -> Maybe (Sized f n a)
fromList SZ _ = withListLikeF (Proxy :: Proxy (f a)) $
                Just $ Sized (LL.empty :: f a)
fromList sn xs =
  let len = sNatToInt sn
  in if P.length xs < len
     then Nothing
     else Just $ unsafeFromList sn $ P.take len xs
{-# INLINABLE [2] fromList #-}

{-# RULES
"fromList/List" forall sn (xs :: [a]).
  fromList sn xs = toSized sn xs
  #-}

-- | 'fromList' with the result length inferred.
fromList' :: (ListLikeF f, SingI (n :: Nat)) => [a] -> Maybe (Sized f n a)
fromList' = withSing fromList
{-# INLINE fromList' #-}

-- | 'unsafeFromList' with the result length inferred.
unsafeFromList' :: (SingI (n :: Nat), ListLikeF f) => [a] -> Sized f n a
unsafeFromList' = withSing unsafeFromList
{-# INLINE unsafeFromList' #-}

-- | Unsafe version of 'toSized'. If the length of the given list does not 
--   equal to @n@, then something unusual happens.
unsafeToSized :: SNat n -> f a -> Sized f n a
unsafeToSized _ = Sized
{-# INLINE [2] unsafeToSized #-}

-- | If the length of the input is shorter than @n@, then returns @Nothing@.
--   Otherwise returns @Sized f n a@ consisting of initial @n@ element
--   of the input.
toSized :: ListLikeF f => SNat n -> f a -> Maybe (Sized f n a)
toSized sn = givenListLikeF $ \xs ->
  let len = sNatToInt sn
  in if LL.length xs < len
     then Nothing
     else Just $ unsafeToSized sn $ LL.take len xs
{-# INLINABLE [2] toSized #-}

-- | Construct a @Sized f n a@ by padding default value if the given list is short.
toSizedWithDefault :: ListLikeF f => SNat n -> a -> f a -> Sized f n a
toSizedWithDefault sn def = givenListLikeF $ \xs ->
  let len = sNatToInt sn
  in Sized $ LL.take len xs `LL.append` LL.replicate (len - LL.length xs) def
{-# INLINABLE toSizedWithDefault #-}

-- | 'toSizedWithDefault' with the result length inferred.
toSizedWithDefault' :: (SingI (n :: Nat), ListLikeF f) => a -> f a -> Sized f n a
toSizedWithDefault' = withSing toSizedWithDefault
{-# INLINE toSizedWithDefault' #-}

-- | 'toSized' with the result length inferred.
toSized' :: (ListLikeF f, SingI (n :: Nat)) => f a -> Maybe (Sized f n a)
toSized' = withSing toSized
{-# INLINE toSized' #-}

-- | 'unsafeToSized' with the result length inferred.
unsafeToSized' :: (SingI (n :: Nat), ListLikeF f) => f a -> Sized f n a
unsafeToSized' = withSing unsafeToSized
{-# INLINE unsafeToSized' #-}

-- | Convert to list.
toList :: ListLikeF f => Sized f n a -> [a]
toList = givenListLikeF LL.toList . runSized
{-# INLINE [2] toList #-}

{-# RULES
"toList/" forall (xs :: Sized [] a n).
  toList xs = runSized xs
  #-}

-- | Append two lists.
append :: ListLikeF f => Sized f n a -> Sized f m a -> Sized f (n :+ m) a
append (Sized xs) (Sized ys) = withListLikeF' xs $ Sized $ LL.append xs ys
{-# INLINE append #-}

-- | Infix version of 'append'.
(++) :: (ListLikeF f) => Sized f n a -> Sized f m a -> Sized f (n :+ m) a
(++) = append
infixr 5 ++

-- | Take the first element of non-empty sequence.
--   If you want to make case-analysis for general sequence,
--   see  <#patterns Views and Patterns> section.
head :: ListLikeF f => Sized f (S n) a -> a
head = givenListLikeF LL.head . runSized
{-# INLINE head #-}

-- | Take the last element of non-empty sequence.
--   If you want to make case-analysis for general sequence,
--   see  <#patterns Views and Patterns> section.
last ::  ListLikeF f => Sized f (S n) a -> a
last = givenListLikeF LL.last . runSized
{-# INLINE last #-}

-- | Take the tail of non-empty sequence.
--   If you want to make case-analysis for general sequence,
--   see  <#patterns Views and Patterns> section.
tail :: ListLikeF f => Sized f (S n) a -> Sized f n a
tail = givenListLikeF (Sized . LL.tail) . runSized
{-# INLINE tail #-}

-- | Take the initial segment of non-empty sequence.
--   If you want to make case-analysis for general sequence,
--   see  <#patterns Views and Patterns> section.
init :: ListLikeF f => Sized f (S n) a -> Sized f n a
init = Sized . givenListLikeF LL.init . runSized
{-# INLINE init #-}

-- | Test if the sequence is empty or not.
null :: ListLikeF f => Sized f n a -> Bool
null = givenListLikeF' LL.null
{-# INLINE [2] null #-}
{-# RULES
"null/Zero" forall (xs :: Sized f Z a).
  null xs = True
"null/Succ" forall (xs :: Sized f (S n) a).
  null xs = False
  #-}

-- | Returns the length of wrapped containers.
--   If you use @unsafeFromList@ or similar unsafe functions,
--   this function may return different value from type-parameterized length.
length :: ListLikeF f => Sized f n a -> Int
length = givenListLikeF LL.length . runSized
{-# INLINE length #-}

-- | @SNat@ version of 'length'.
sLength :: SingI n => Sized f n a -> SNat n
sLength _ = sing
{-# INLINE sLength #-}

-- | Map function.
map :: Functor f => (a -> b) -> Sized f n a -> Sized f n b
map f = Sized . fmap f . runSized
{-# INLINE map #-}

-- | Reverse function.
reverse :: ListLikeF f => Sized f n a -> Sized f n a
reverse = Sized . givenListLikeF LL.reverse . runSized
{-# INLINE reverse #-}

-- | Intersperces.
intersperse :: ListLikeF f => a -> Sized f n a -> Sized f ((Two :* n) :-: One) a
intersperse a = Sized . givenListLikeF' (LL.intersperse a)
{-# INLINE intersperse #-}

-- | @take k xs@ takes first @k@ element of @xs@ where
-- the length of @xs@ should be larger than @k@.
-- It is really sad, that this function
-- takes at least O(k) regardless of base container.
take :: (ListLikeF f, (n :<<= m) ~ True)
     => SNat n -> Sized f m a -> Sized f n a
take sn = Sized . givenListLikeF' (LL.take (sNatToInt sn))
{-# INLINE take #-}

-- | @take k xs@ takes first @k@ element of @xs@ at most.
-- It is really sad, that this function
-- takes at least O(k) regardless of base container.
takeAtMost :: (ListLikeF f)
           => SNat n -> Sized f m a -> Sized f (Min n m) a
takeAtMost sn = givenListLikeF' $ Sized . LL.take (sNatToInt sn)
{-# INLINE takeAtMost #-}

-- | @drop k xs@ drops first @k@ element of @xs@ and returns
-- the rest of sequence, where the length of @xs@ should be larger than @k@.
-- It is really sad, that this function
-- takes at least O(k) regardless of base container.
drop :: (ListLikeF f, (n :<<= m) ~ True)
     => SNat n -> Sized f m a -> Sized f (m :-: n) a
drop sn = givenListLikeF' $ Sized . LL.drop (sNatToInt sn)
{-# INLINE drop #-}

-- | @splitAt k xs@ split @xs@ at @k@, where
-- the length of @xs@ should be less than or equal to @k@.
-- It is really sad, that this function
-- takes at least O(k) regardless of base container.
splitAt :: (ListLikeF f , (n :<<= m) ~ True)
        => SNat n -> Sized f m a -> (Sized f n a, Sized f (m :-: n) a)
splitAt n = givenListLikeF' $ \xs ->
  let (as, bs) = LL.splitAt (sNatToInt n) xs
  in (Sized as, Sized bs)
{-# INLINE splitAt #-}

-- | @splitAtMost k xs@ split @xs@ at @k@.
--   If @k@ exceeds the length of @xs@, then the second result value become empty.
-- It is really sad, that this function
-- takes at least O(k) regardless of base container.
splitAtMost :: ListLikeF f
            => SNat n -> Sized f m a -> (Sized f (Min n m) a, Sized f (m :-: n) a)
splitAtMost n = givenListLikeF' $ \xs ->
  let (as, bs) = LL.splitAt (sNatToInt n) xs
  in (Sized as, Sized bs)
{-# INLINE splitAtMost #-}

-- | Take the initial segment as long as elements satisfys the predicate.
takeWhile :: ListLikeF f
          => (a -> Bool) -> Sized f n a -> SomeSized f a
takeWhile p = givenListLikeF' $ toSomeSized . LL.takeWhile p
{-# INLINE takeWhile #-}

-- | Drop the initial segment as long as elements satisfys the predicate.
dropWhile :: ListLikeF f
          => (a -> Bool) -> Sized f n a -> SomeSized f a
dropWhile p = givenListLikeF' $ toSomeSized . LL.dropWhile p
{-# INLINE dropWhile #-}

-- | Invariant: @'ListLike' (f a) a@ instance must be implemented
-- to satisfy the following property:
-- @length (fst (span p xs)) + length (snd (span p xs)) == length xs@
-- Otherwise, this function introduces severe contradiction.
span :: ListLikeF f
     => (a -> Bool) -> Sized f n a -> Partitioned f n a
span p = givenListLikeF' $ \xs ->
         let (as, bs) = LL.span p xs
         in case (toSomeSized as, toSomeSized bs) of
           (SomeSized lenL ls, SomeSized lenR rs) ->
             unsafeCoerce $ Partitioned lenL ls lenR rs
{-# INLINE span #-}

-- | Invariant: @'ListLike' (f a) a@ instance must be implemented
-- to satisfy the following property:
-- @length (fst (break p xs)) + length (snd (break p xs)) == length xs@
-- Otherwise, this function introduces severe contradiction.
break :: ListLikeF f
     => (a -> Bool) -> Sized f n a -> Partitioned f n a
break p = givenListLikeF' $ \xs ->
         let (as, bs) = LL.break p xs
         in case (toSomeSized as, toSomeSized bs) of
           (SomeSized lenL ls, SomeSized lenR rs) ->
             unsafeCoerce $ Partitioned lenL ls lenR rs
{-# INLINE break #-}

-- | Invariant: @'ListLike' (f a) a@ instance must be implemented
-- to satisfy the following property:
-- @length (fst (partition p xs)) + length (snd (partition p xs)) == length xs@
-- Otherwise, this function introduces severe contradiction.
partition :: ListLikeF f
     => (a -> Bool) -> Sized f n a -> Partitioned f n a
partition p = givenListLikeF' $ \xs ->
         let (as, bs) = LL.partition p xs
         in case (toSomeSized as, toSomeSized bs) of
           (SomeSized lenL ls, SomeSized lenR rs) ->
             unsafeCoerce $ Partitioned lenL ls lenR rs
{-# INLINE partition #-}

-- | Remove all duplicates.
nub :: (ListLikeF f, Eq a) => Sized f n a -> SomeSized f a
nub = givenListLikeF' $ toSomeSized . LL.nub

-- | Membership test; see also 'notElem'.
elem :: (ListLikeF f, Eq a) => a -> Sized f n a -> Bool
elem a = givenListLikeF' $ LL.elem a
{-# INLINE elem #-}

-- | Negation of 'elem'.
notElem :: (ListLikeF f, Eq a) => a -> Sized f n a -> Bool
notElem a = givenListLikeF' $ LL.notElem a
{-# INLINE notElem #-}

-- | Find the element satisfying the predicate.
find :: ListLikeF f => (a -> Bool) -> Sized f n a -> Maybe a
find p = givenListLikeF' $ LL.find p
{-# INLINE find #-}

-- | (Unsafe) indexing with @Int@s.
--   If you want to check boundary statically, use '%!!' or 'sIndex'.
(!!) :: (ListLikeF f) => Sized f (S m) a -> Int -> a
Sized xs !! n = withListLikeF' xs $ LL.index xs n
{-# INLINE (!!) #-}

-- | Safe indexing with 'Ordinal's.
(%!!) :: ListLikeF f => Sized f n a -> Ordinal n -> a
Sized xs %!! n = withListLikeF' xs $ LL.index xs (ordToInt n)
{-# INLINE (%!!) #-}

-- | Flipped version of '!!'.
index :: (ListLikeF f) => Int -> Sized f (S m) c -> c
index = flip (!!)
{-# INLINE index #-}

-- | Flipped version of '%!!'.
sIndex :: ListLikeF f => Ordinal n -> Sized f n c -> c
sIndex = flip (%!!)
{-# INLINE sIndex #-}

-- | Returns the index of the given element in the list, if exists.
elemIndex :: (Eq a, ListLikeF f) => a -> Sized f n a -> Maybe Int
elemIndex a = findIndex (== a)
{-# INLINE elemIndex #-}

-- | Ordinal version of 'elemIndex'
sElemIndex :: (SingI n, ListLikeF f, Eq a)
           => a -> Sized f n a -> Maybe (Ordinal n)
sElemIndex a = sFindIndex (== a)
{-# INLINE sElemIndex #-}

-- | 'Ordinal' version of 'findIndex'.
sFindIndex :: (SingI n, ListLikeF f) => (a -> Bool) -> Sized f n a -> Maybe (Ordinal n)
sFindIndex p = fmap toEnum . findIndex p
{-# INLINE sFindIndex #-}

-- | @'findIndex' p xs@ find the element satisfying @p@ and returns its index if exists.
findIndex :: ListLikeF f => (a -> Bool) -> Sized f n a -> Maybe Int
findIndex p = givenListLikeF' $ LL.findIndex p
{-# INLINE findIndex #-}


-- | @'findIndices' p xs@ find all elements satisfying @p@ and returns their indices.
findIndices :: ListLikeF f => (a -> Bool) -> Sized f n a -> [Int]
findIndices p = givenListLikeF' $ LL.findIndices p
{-# INLINE findIndices #-}

-- | 'Ordinal' version of 'findIndices'.
sFindIndices :: (SingI n, ListLikeF f) => (a -> Bool) -> Sized f n a -> [Ordinal n]
sFindIndices p = fmap toEnum . findIndices p
{-# INLINE sFindIndices #-}

-- | Returns all indices of the given element in the list.
elemIndices :: (ListLikeF f, Eq a) => a -> Sized f n a -> [Int]
elemIndices a = givenListLikeF' $ LL.elemIndices a
{-# INLINE elemIndices #-}

-- | Ordinal version of 'elemIndices'
sElemIndices :: (SingI n, ListLikeF f, Eq a) => a -> Sized f n a -> [Ordinal n]
sElemIndices p = fmap toEnum . elemIndices p
{-# INLINE sElemIndices #-}

-- | Zipping two sequences. Length is adjusted to shorter one.
zip :: forall f a b n m. (ListLikeF f)
    => Sized f n a -> Sized f m b -> Sized f (Min n m) (a, b)
zip (Sized xs) (Sized ys) =
  withListLikeF' ys $ withListLikeF' xs $
  withListLikeF (Proxy :: Proxy (f (a,b))) $ Sized $
  LL.zip xs ys
{-# INLINE zip #-}

-- | 'zip' for the sequences of the same length.
zipSame :: forall f n a b. (ListLikeF f)
        => Sized f n a -> Sized f n b -> Sized f n (a, b)
zipSame (Sized xs) (Sized ys) =
  withListLikeF' xs $ withListLikeF' ys $
  withListLikeF (Proxy :: Proxy (f (a, b))) $
  Sized $ LL.zip xs ys
{-# INLINE zipSame #-}

-- | Zipping two sequences with funtion. Length is adjusted to shorter one.
zipWith :: forall f a b c m n. (ListLikeF f)
    => (a -> b -> c) -> Sized f n a -> Sized f m b -> Sized f (Min n m) c
zipWith f (Sized xs) (Sized ys) =
  withListLikeF' xs $ withListLikeF' ys $
  withListLikeF (Proxy :: Proxy (f c)) $
  Sized $ LL.zipWith f xs ys
{-# INLINE zipWith #-}

-- | 'zipWith' for the sequences of the same length.
zipWithSame :: forall f a b c n. ListLikeF f
            => (a -> b -> c) -> Sized f n a -> Sized f n b -> Sized f n c
zipWithSame f (Sized xs) (Sized ys) =
  withListLikeF' xs $ withListLikeF' ys $
  withListLikeF (Proxy :: Proxy (f c)) $
  Sized $ LL.zipWith f xs ys
{-# INLINE zipWithSame #-}

-- | Unzipping the sequence of tuples.
unzip :: forall f n a b. (ListLikeF f)
      => Sized f n (a, b) -> (Sized f n a, Sized f n b)
unzip (Sized xys) = withListLikeF' xys $
  withListLikeF (Proxy :: Proxy (f b)) $
  withListLikeF (Proxy :: Proxy (f a)) $
  let (xs, ys) = LL.unzip xys
  in (Sized xs, Sized ys)
{-# INLINE unzip #-}

-- | Sorting sequence by ascending order.
sort :: (ListLikeF f, Ord a)
     => Sized f n a -> Sized f n a
sort = givenListLikeF' $ Sized . LL.sort

-- | Generalized version of 'sort'.
sortBy :: (ListLikeF  f) => (a -> a -> Ordering) -> Sized f n a -> Sized f n a
sortBy cmp = givenListLikeF' $ Sized . LL.sortBy cmp

-- | Insert new element into the presorted sequence.
insert :: (ListLikeF f, Ord a) => a -> Sized f n a -> Sized f (S n) a
insert a = givenListLikeF' $ Sized . LL.insert a

-- | Generalized version of 'insert'.
insertBy :: (ListLikeF f) => (a -> a -> Ordering) -> a -> Sized f n a -> Sized f (S n) a
insertBy cmp a = givenListLikeF' $ Sized . LL.insertBy cmp a


-- $views #patterns#
-- These patterns and views are especially useful!

data ConsView f n a where
  NilCV :: ConsView f Z a
  (::-) :: a -> Sized f n a -> ConsView f (S n) a

infixr 5 ::-

viewCons :: forall f a n. (SingI n, ListLikeF f)
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


viewSnoc :: forall f n a. (SingI n, ListLikeF f)
         => Sized f n a
         -> SnocView f n a
viewSnoc sz = case sing :: SNat n of
  SZ   -> NilSV
  SS n -> withSingI n $ init sz :-: last sz

infixl 5 :>
pattern a :> b <- (viewSnoc -> a :-: b)
pattern NilR   <- (viewSnoc -> NilSV)
