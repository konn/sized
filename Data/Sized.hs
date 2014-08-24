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
--  inspect the sized sequence. See <#ViewsAndPatterns Views and Patterns> for more detail.
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
         cons, (<|), snoc, (|>), append, (++), concat,
         -- ** Zips
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
         -- $ViewsAndPatterns

         -- ** Views
         -- $views

         -- ** Patterns
         -- $patterns

         -- ** Definitions
         viewCons, ConsView (..), viewSnoc, SnocView(..),

         pattern (:<), pattern NilL , pattern (:>), pattern NilR,
       ) where

import Data.Sized.Internal

import qualified Data.ListLike         as LL
import           Data.Proxy            (Proxy (..))
import           Data.Type.Monomorphic
import           Data.Type.Natural
import           Data.Type.Ordinal     (Ordinal, ordToInt)
import           Data.Typeable         (Typeable)
import           Prelude               (Bool (..), Enum (..), Eq (..),
                                        Functor (..), Int, Maybe (..), Num (..),
                                        Ord (..), Ordering, Show (..), flip,
                                        undefined, ($), (.))
import qualified Prelude               as P
import           Unsafe.Coerce         (unsafeCoerce)

--------------------------------------------------------------------------------
-- Main data-types
--------------------------------------------------------------------------------

-- | 'Sized' vector with the length is existentially quantified.
--   This type is used mostly when the return type's length cannot
--   be statically determined beforehand.
--
-- @SomeSized sn xs :: SomeSized f a@ stands for the 'Sized' sequence
-- @xs@ of element type @a@ and length @sn@.
--
-- Since 0.1.0.0
data SomeSized f a where
  SomeSized :: (ListLikeF f, SingI n)
            => SNat n
            -> Sized f (n :: Nat) a
            -> SomeSized f a

deriving instance Typeable SomeSized

deriving instance Show (f a) => Show (SomeSized f a)
instance Eq (f a) => Eq (SomeSized f a) where
  (SomeSized _ (Sized xs)) == (SomeSized _ (Sized ys)) = xs == ys

--------------------------------------------------------------------------------
-- Accessors
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
--- Length infromation
--------------------------------------------------------------------------------

-- | Returns the length of wrapped containers.
--   If you use @unsafeFromList@ or similar unsafe functions,
--   this function may return different value from type-parameterized length.
-- 
-- Since 0.1.0.0
length :: ListLikeF f => Sized f n a -> Int
length = givenListLikeF LL.length . runSized
{-# INLINE length #-}

-- | @SNat@ version of 'length'.
-- 
-- Since 0.1.0.0
sLength :: SingI n => Sized f n a -> SNat n
sLength _ = sing
{-# INLINE sLength #-}

-- | Test if the sequence is empty or not.
-- 
-- Since 0.1.0.0
null :: ListLikeF f => Sized f n a -> Bool
null = givenListLikeF' LL.null
{-# INLINE [2] null #-}
{-# RULES
"null/Zero" forall (xs :: Sized f Z a).
  null xs = True
"null/Succ" forall (xs :: Sized f (S n) a).
  null xs = False
  #-}

--------------------------------------------------------------------------------
--- Indexing
--------------------------------------------------------------------------------

-- | (Unsafe) indexing with @Int@s.
--   If you want to check boundary statically, use '%!!' or 'sIndex'.
-- 
-- Since 0.1.0.0
(!!) :: (ListLikeF f) => Sized f (S m) a -> Int -> a
Sized xs !! n = withListLikeF' xs $ LL.index xs n
{-# INLINE (!!) #-}

-- | Safe indexing with 'Ordinal's.
-- 
-- Since 0.1.0.0
(%!!) :: ListLikeF f => Sized f n a -> Ordinal n -> a
Sized xs %!! n = withListLikeF' xs $ LL.index xs (ordToInt n)
{-# INLINE (%!!) #-}

-- | Flipped version of '!!'.
-- 
-- Since 0.1.0.0
index :: (ListLikeF f) => Int -> Sized f (S m) c -> c
index = flip (!!)
{-# INLINE index #-}

-- | Flipped version of '%!!'.
-- 
-- Since 0.1.0.0
sIndex :: ListLikeF f => Ordinal n -> Sized f n c -> c
sIndex = flip (%!!)
{-# INLINE sIndex #-}

-- | Take the first element of non-empty sequence.
--   If you want to make case-analysis for general sequence,
--   see  <#ViewsAndPatterns Views and Patterns> section.
-- 
-- Since 0.1.0.0
head :: ListLikeF f => Sized f (S n) a -> a
head = givenListLikeF LL.head . runSized
{-# INLINE head #-}

-- | Take the last element of non-empty sequence.
--   If you want to make case-analysis for general sequence,
--   see  <#ViewsAndPatterns Views and Patterns> section.
-- 
-- Since 0.1.0.0
last ::  ListLikeF f => Sized f (S n) a -> a
last = givenListLikeF LL.last . runSized
{-# INLINE last #-}

-- | Take the 'head' and 'tail' of non-empty sequence.
--   If you want to make case-analysis for general sequence,
--   see  <#ViewsAndPatterns Views and Patterns> section.
-- 
-- Since 0.1.0.0
uncons :: ListLikeF f => Sized f (S n) a -> (a, Sized f n a)
uncons = givenListLikeF (\xs -> (LL.head xs, Sized $ LL.tail xs)) . runSized
{-# INLINE uncons #-}

-- | Take the 'init' and 'last' of non-empty sequence.
--   If you want to make case-analysis for general sequence,
--   see  <#ViewsAndPatterns Views and Patterns> section.
-- 
-- Since 0.1.0.0
unsnoc :: ListLikeF f => Sized f (S n) a -> (Sized f n a, a)
unsnoc = givenListLikeF (\xs -> (Sized $ LL.init xs, LL.last xs)) . runSized
{-# INLINE unsnoc #-}

--------------------------------------------------------------------------------
--- Slicing
--------------------------------------------------------------------------------

-- | Take the tail of non-empty sequence.
--   If you want to make case-analysis for general sequence,
--   see  <#ViewsAndPatterns Views and Patterns> section.
-- 
-- Since 0.1.0.0
tail :: ListLikeF f => Sized f (S n) a -> Sized f n a
tail = givenListLikeF (Sized . LL.tail) . runSized
{-# INLINE tail #-}

-- | Take the initial segment of non-empty sequence.
--   If you want to make case-analysis for general sequence,
--   see  <#ViewsAndPatterns Views and Patterns> section.
-- 
-- Since 0.1.0.0
init :: ListLikeF f => Sized f (S n) a -> Sized f n a
init = Sized . givenListLikeF LL.init . runSized
{-# INLINE init #-}

-- | @take k xs@ takes first @k@ element of @xs@ where
-- the length of @xs@ should be larger than @k@.
-- It is really sad, that this function
-- takes at least O(k) regardless of base container.
-- 
-- Since 0.1.0.0
take :: (ListLikeF f, (n :<<= m) ~ True)
     => SNat n -> Sized f m a -> Sized f n a
take sn = Sized . givenListLikeF' (LL.take (sNatToInt sn))
{-# INLINE take #-}

-- | @take k xs@ takes first @k@ element of @xs@ at most.
-- It is really sad, that this function
-- takes at least O(k) regardless of base container.
-- 
-- Since 0.1.0.0
takeAtMost :: (ListLikeF f)
           => SNat n -> Sized f m a -> Sized f (Min n m) a
takeAtMost sn = givenListLikeF' $ Sized . LL.take (sNatToInt sn)
{-# INLINE takeAtMost #-}

-- | @drop k xs@ drops first @k@ element of @xs@ and returns
-- the rest of sequence, where the length of @xs@ should be larger than @k@.
-- It is really sad, that this function
-- takes at least O(k) regardless of base container.
-- 
-- Since 0.1.0.0
drop :: (ListLikeF f, (n :<<= m) ~ True)
     => SNat n -> Sized f m a -> Sized f (m :-: n) a
drop sn = givenListLikeF' $ Sized . LL.drop (sNatToInt sn)
{-# INLINE drop #-}

-- | @splitAt k xs@ split @xs@ at @k@, where
-- the length of @xs@ should be less than or equal to @k@.
-- It is really sad, that this function
-- takes at least O(k) regardless of base container.
-- 
-- Since 0.1.0.0
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
-- 
-- Since 0.1.0.0
splitAtMost :: ListLikeF f
            => SNat n -> Sized f m a -> (Sized f (Min n m) a, Sized f (m :-: n) a)
splitAtMost n = givenListLikeF' $ \xs ->
  let (as, bs) = LL.splitAt (sNatToInt n) xs
  in (Sized as, Sized bs)
{-# INLINE splitAtMost #-}


--------------------------------------------------------------------------------
-- Construction
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
--- Initialisation
--------------------------------------------------------------------------------

-- | Empty sequence.
-- 
-- Since 0.1.0.0
empty :: forall f a. ListLikeF f => Sized f Z a
empty = withListLikeF (Proxy :: Proxy (f a)) $ Sized LL.empty
{-# INLINE empty #-}

-- | Sequence with one element.
-- 
-- Since 0.1.0.0
singleton :: forall f a. ListLikeF f => a -> Sized f One a
singleton = withListLikeF (Proxy :: Proxy (f a)) $ Sized . LL.singleton
{-# INLINE singleton #-}

-- | Consruct the 'Sized' sequence from base type, but
--   the length parameter is dynamically determined and
--   existentially quantified; see also 'SomeSized'.
-- 
-- Since 0.1.0.0
toSomeSized :: forall f a. ListLikeF f => f a -> SomeSized f a
toSomeSized = givenListLikeF $ \xs ->
  case promote $ LL.length xs of
    Monomorphic sn -> withSingI sn $ SomeSized sn $ unsafeToSized sn xs

-- | Replicates the same value.
-- 
-- Since 0.1.0.0
replicate :: forall f n a. ListLikeF f => SNat n -> a -> Sized f n a
replicate sn a = withListLikeF (Proxy :: Proxy (f a)) $
                 Sized $ LL.replicate (sNatToInt sn) a
{-# INLINE replicate #-}

-- | 'replicate' with the length inferred.
-- 
-- Since 0.1.0.0
replicate' :: (SingI (n :: Nat), ListLikeF f) => a -> Sized f n a
replicate' = withSing replicate
{-# INLINE replicate' #-}

--------------------------------------------------------------------------------
--- Concatenation
--------------------------------------------------------------------------------

-- | Append an element to the head of sequence.
-- 
-- Since 0.1.0.0
cons :: (ListLikeF f) => a -> Sized f n a -> Sized f (S n) a
cons a = givenListLikeF' $ Sized . LL.cons a
{-# INLINE cons #-}

-- | Infix version of 'cons'.
-- 
-- Since 0.1.0.0
(<|) :: (ListLikeF f) => a -> Sized f n a -> Sized f (S n) a
(<|) = cons
{-# INLINE (<|) #-}
infixr 5 <|

-- | Append an element to the tail of sequence.
-- 
-- Since 0.1.0.0
snoc :: (ListLikeF f) => Sized f n a -> a -> Sized f (S n) a
snoc (Sized xs) a = withListLikeF' xs $ Sized $ LL.snoc xs a
{-# INLINE snoc #-}

-- | Infix version of 'snoc'.
-- 
-- Since 0.1.0.0
(|>) :: (ListLikeF f) => Sized f n a -> a -> Sized f (S n) a
(|>) = snoc
{-# INLINE (|>) #-}
infixl 5 |>

-- | Append two lists.
-- 
-- Since 0.1.0.0
append :: ListLikeF f => Sized f n a -> Sized f m a -> Sized f (n :+ m) a
append (Sized xs) (Sized ys) = withListLikeF' xs $ Sized $ LL.append xs ys
{-# INLINE append #-}

-- | Infix version of 'append'.
-- 
-- Since 0.1.0.0
(++) :: (ListLikeF f) => Sized f n a -> Sized f m a -> Sized f (n :+ m) a
(++) = append
infixr 5 ++

-- | Concatenates multiple sequences into one.
-- 
-- Since 0.1.0.0
concat :: forall f f' m n a. (ListLikeF f, ListLikeF f')
       => Sized f' m (Sized f n a) -> Sized f (m :* n) a
concat =
  givenListLikeF' $ withListLikeF (Proxy :: Proxy (f' (f a))) $
  withListLikeF (Proxy :: Proxy (f a)) $
  Sized . LL.concat . fmap runSized

--------------------------------------------------------------------------------
--- Zips
--------------------------------------------------------------------------------

-- | Zipping two sequences. Length is adjusted to shorter one.
-- 
-- Since 0.1.0.0
zip :: forall f a b n m. (ListLikeF f)
    => Sized f n a -> Sized f m b -> Sized f (Min n m) (a, b)
zip (Sized xs) (Sized ys) =
  withListLikeF' ys $ withListLikeF' xs $
  withListLikeF (Proxy :: Proxy (f (a,b))) $ Sized $
  LL.zip xs ys
{-# INLINE zip #-}

-- | 'zip' for the sequences of the same length.
-- 
-- Since 0.1.0.0
zipSame :: forall f n a b. (ListLikeF f)
        => Sized f n a -> Sized f n b -> Sized f n (a, b)
zipSame (Sized xs) (Sized ys) =
  withListLikeF' xs $ withListLikeF' ys $
  withListLikeF (Proxy :: Proxy (f (a, b))) $
  Sized $ LL.zip xs ys
{-# INLINE zipSame #-}

-- | Zipping two sequences with funtion. Length is adjusted to shorter one.
-- 
-- Since 0.1.0.0
zipWith :: forall f a b c m n. (ListLikeF f)
    => (a -> b -> c) -> Sized f n a -> Sized f m b -> Sized f (Min n m) c
zipWith f (Sized xs) (Sized ys) =
  withListLikeF' xs $ withListLikeF' ys $
  withListLikeF (Proxy :: Proxy (f c)) $
  Sized $ LL.zipWith f xs ys
{-# INLINE zipWith #-}

-- | 'zipWith' for the sequences of the same length.
-- 
-- Since 0.1.0.0
zipWithSame :: forall f a b c n. ListLikeF f
            => (a -> b -> c) -> Sized f n a -> Sized f n b -> Sized f n c
zipWithSame f (Sized xs) (Sized ys) =
  withListLikeF' xs $ withListLikeF' ys $
  withListLikeF (Proxy :: Proxy (f c)) $
  Sized $ LL.zipWith f xs ys
{-# INLINE zipWithSame #-}

-- | Unzipping the sequence of tuples.
-- 
-- Since 0.1.0.0
unzip :: forall f n a b. (ListLikeF f)
      => Sized f n (a, b) -> (Sized f n a, Sized f n b)
unzip (Sized xys) = withListLikeF' xys $
  withListLikeF (Proxy :: Proxy (f b)) $
  withListLikeF (Proxy :: Proxy (f a)) $
  let (xs, ys) = LL.unzip xys
  in (Sized xs, Sized ys)
{-# INLINE unzip #-}


--------------------------------------------------------------------------------
-- Transformation
--------------------------------------------------------------------------------

-- | Map function.
-- 
-- Since 0.1.0.0
map :: Functor f => (a -> b) -> Sized f n a -> Sized f n b
map f = Sized . fmap f . runSized
{-# INLINE map #-}

-- | Reverse function.
-- 
-- Since 0.1.0.0
reverse :: ListLikeF f => Sized f n a -> Sized f n a
reverse = Sized . givenListLikeF LL.reverse . runSized
{-# INLINE reverse #-}

-- | Intersperces.
-- 
-- Since 0.1.0.0
intersperse :: ListLikeF f => a -> Sized f n a -> Sized f ((Two :* n) :-: One) a
intersperse a = Sized . givenListLikeF' (LL.intersperse a)
{-# INLINE intersperse #-}

-- | Remove all duplicates.
-- 
-- Since 0.1.0.0
nub :: (ListLikeF f, Eq a) => Sized f n a -> SomeSized f a
nub = givenListLikeF' $ toSomeSized . LL.nub

-- | Sorting sequence by ascending order.
-- 
-- Since 0.1.0.0
sort :: (ListLikeF f, Ord a)
     => Sized f n a -> Sized f n a
sort = givenListLikeF' $ Sized . LL.sort

-- | Generalized version of 'sort'.
-- 
-- Since 0.1.0.0
sortBy :: (ListLikeF  f) => (a -> a -> Ordering) -> Sized f n a -> Sized f n a
sortBy cmp = givenListLikeF' $ Sized . LL.sortBy cmp

-- | Insert new element into the presorted sequence.
-- 
-- Since 0.1.0.0
insert :: (ListLikeF f, Ord a) => a -> Sized f n a -> Sized f (S n) a
insert a = givenListLikeF' $ Sized . LL.insert a

-- | Generalized version of 'insert'.
-- 
-- Since 0.1.0.0
insertBy :: (ListLikeF f) => (a -> a -> Ordering) -> a -> Sized f n a -> Sized f (S n) a
insertBy cmp a = givenListLikeF' $ Sized . LL.insertBy cmp a


--------------------------------------------------------------------------------
-- Conversion
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
--- List
--------------------------------------------------------------------------------

-- | Convert to list.
-- 
-- Since 0.1.0.0
toList :: ListLikeF f => Sized f n a -> [a]
toList = givenListLikeF LL.toList . runSized
{-# INLINE [2] toList #-}

{-# RULES
"toList/" forall (xs :: Sized [] a n).
  toList xs = runSized xs
  #-}

-- | If the given list is shorter than @n@, then returns @Nothing@
--   Otherwise returns @Sized f n a@ consisting of initial @n@ element
--   of given list.
-- 
-- Since 0.1.0.0
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
-- 
-- Since 0.1.0.0
fromList' :: (ListLikeF f, SingI (n :: Nat)) => [a] -> Maybe (Sized f n a)
fromList' = withSing fromList
{-# INLINE fromList' #-}

-- | Unsafe version of 'fromList'. If the length of the given list does not 
--   equal to @n@, then something unusual happens.
-- 
-- Since 0.1.0.0
unsafeFromList :: forall f n a. ListLikeF f => SNat n -> [a] -> Sized f n a
unsafeFromList _ xs =
  withListLikeF (Proxy :: Proxy (f a)) $
  Sized $ LL.fromList xs
{-# INLINE [2] unsafeFromList #-}

{-# RULES
"unsafeFromList/List" forall sn (xs :: [a]).
  unsafeFromList sn xs = Sized (P.take (sNatToInt sn) xs)
 #-}

-- | 'unsafeFromList' with the result length inferred.
-- 
-- Since 0.1.0.0
unsafeFromList' :: (SingI (n :: Nat), ListLikeF f) => [a] -> Sized f n a
unsafeFromList' = withSing unsafeFromList
{-# INLINE unsafeFromList' #-}

-- | Construct a @Sized f n a@ by padding default value if the given list is short.
-- 
-- Since 0.1.0.0
fromListWithDefault :: forall f n a. ListLikeF f => SNat n -> a -> [a] -> Sized f n a
fromListWithDefault sn def xs =
  let len = sNatToInt sn
  in withListLikeF (Proxy :: Proxy (f a)) $
     Sized $ LL.fromList (P.take len xs) `LL.append` LL.replicate (len - P.length xs) def
{-# INLINABLE fromListWithDefault #-}

-- | 'fromListWithDefault' with the result length inferred.
-- 
-- Since 0.1.0.0
fromListWithDefault' :: (SingI (n :: Nat), ListLikeF f) => a -> [a] -> Sized f n a
fromListWithDefault' = withSing fromListWithDefault
{-# INLINE fromListWithDefault' #-}

--------------------------------------------------------------------------------
--- Base containes
--------------------------------------------------------------------------------

-- | Forget the length and obtain the wrapped base container.
-- 
-- Since 0.1.0.0
unsized :: Sized f n a -> f a
unsized = runSized
{-# INLINE unsized #-}

-- | If the length of the input is shorter than @n@, then returns @Nothing@.
--   Otherwise returns @Sized f n a@ consisting of initial @n@ element
--   of the input.
-- 
-- Since 0.1.0.0
toSized :: ListLikeF f => SNat n -> f a -> Maybe (Sized f n a)
toSized sn = givenListLikeF $ \xs ->
  let len = sNatToInt sn
  in if LL.length xs < len
     then Nothing
     else Just $ unsafeToSized sn $ LL.take len xs
{-# INLINABLE [2] toSized #-}

-- | 'toSized' with the result length inferred.
-- 
-- Since 0.1.0.0
toSized' :: (ListLikeF f, SingI (n :: Nat)) => f a -> Maybe (Sized f n a)
toSized' = withSing toSized
{-# INLINE toSized' #-}

-- | Unsafe version of 'toSized'. If the length of the given list does not 
--   equal to @n@, then something unusual happens.
-- 
-- Since 0.1.0.0
unsafeToSized :: SNat n -> f a -> Sized f n a
unsafeToSized _ = Sized
{-# INLINE [2] unsafeToSized #-}

-- | 'unsafeToSized' with the result length inferred.
-- 
-- Since 0.1.0.0
unsafeToSized' :: (SingI (n :: Nat), ListLikeF f) => f a -> Sized f n a
unsafeToSized' = withSing unsafeToSized
{-# INLINE unsafeToSized' #-}

-- | Construct a @Sized f n a@ by padding default value if the given list is short.
-- 
-- Since 0.1.0.0
toSizedWithDefault :: ListLikeF f => SNat n -> a -> f a -> Sized f n a
toSizedWithDefault sn def = givenListLikeF $ \xs ->
  let len = sNatToInt sn
  in Sized $ LL.take len xs `LL.append` LL.replicate (len - LL.length xs) def
{-# INLINABLE toSizedWithDefault #-}

-- | 'toSizedWithDefault' with the result length inferred.
-- 
-- Since 0.1.0.0
toSizedWithDefault' :: (SingI (n :: Nat), ListLikeF f) => a -> f a -> Sized f n a
toSizedWithDefault' = withSing toSizedWithDefault
{-# INLINE toSizedWithDefault' #-}


--------------------------------------------------------------------------------
-- Querying
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
--- Partitioning
--------------------------------------------------------------------------------

-- | The type @Partitioned f n a@ represents partitioned sequence of length @n@.
--   Value @Partitioned lenL ls lenR rs@ stands for:
-- 
--   * Entire sequence is divided into @ls@ and @rs@, and their length
--     are @lenL@ and @lenR@ resp.
-- 
--   * @lenL + lenR = n@
--
-- Since 0.1.0.0
data Partitioned f n a where
  Partitioned :: (ListLikeF f, SingI n, SingI m)
              => SNat n
              -> Sized f (n :: Nat) a
              -> SNat m
              -> Sized f (m :: Nat) a
              -> Partitioned f (n :+ m) a

-- | Take the initial segment as long as elements satisfys the predicate.
-- 
-- Since 0.1.0.0
takeWhile :: ListLikeF f
          => (a -> Bool) -> Sized f n a -> SomeSized f a
takeWhile p = givenListLikeF' $ toSomeSized . LL.takeWhile p
{-# INLINE takeWhile #-}

-- | Drop the initial segment as long as elements satisfys the predicate.
-- 
-- Since 0.1.0.0
dropWhile :: ListLikeF f
          => (a -> Bool) -> Sized f n a -> SomeSized f a
dropWhile p = givenListLikeF' $ toSomeSized . LL.dropWhile p
{-# INLINE dropWhile #-}

-- | Invariant: @'ListLike' (f a) a@ instance must be implemented
-- to satisfy the following property:
-- @length (fst (span p xs)) + length (snd (span p xs)) == length xs@
-- Otherwise, this function introduces severe contradiction.
-- 
-- Since 0.1.0.0
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
-- 
-- Since 0.1.0.0
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
-- 
-- Since 0.1.0.0
partition :: ListLikeF f
     => (a -> Bool) -> Sized f n a -> Partitioned f n a
partition p = givenListLikeF' $ \xs ->
         let (as, bs) = LL.partition p xs
         in case (toSomeSized as, toSomeSized bs) of
           (SomeSized lenL ls, SomeSized lenR rs) ->
             unsafeCoerce $ Partitioned lenL ls lenR rs
{-# INLINE partition #-}

--------------------------------------------------------------------------------
--- Searching
--------------------------------------------------------------------------------
-- | Membership test; see also 'notElem'.
-- 
-- Since 0.1.0.0
elem :: (ListLikeF f, Eq a) => a -> Sized f n a -> Bool
elem a = givenListLikeF' $ LL.elem a
{-# INLINE elem #-}

-- | Negation of 'elem'.
-- 
-- Since 0.1.0.0
notElem :: (ListLikeF f, Eq a) => a -> Sized f n a -> Bool
notElem a = givenListLikeF' $ LL.notElem a
{-# INLINE notElem #-}

-- | Find the element satisfying the predicate.
-- 
-- Since 0.1.0.0
find :: ListLikeF f => (a -> Bool) -> Sized f n a -> Maybe a
find p = givenListLikeF' $ LL.find p
{-# INLINE find #-}

-- | @'findIndex' p xs@ find the element satisfying @p@ and returns its index if exists.
-- 
-- Since 0.1.0.0
findIndex :: ListLikeF f => (a -> Bool) -> Sized f n a -> Maybe Int
findIndex p = givenListLikeF' $ LL.findIndex p
{-# INLINE findIndex #-}

-- | 'Ordinal' version of 'findIndex'.
-- 
-- Since 0.1.0.0
sFindIndex :: (SingI n, ListLikeF f) => (a -> Bool) -> Sized f n a -> Maybe (Ordinal n)
sFindIndex p = fmap toEnum . findIndex p
{-# INLINE sFindIndex #-}

-- | @'findIndices' p xs@ find all elements satisfying @p@ and returns their indices.
-- 
-- Since 0.1.0.0
findIndices :: ListLikeF f => (a -> Bool) -> Sized f n a -> [Int]
findIndices p = givenListLikeF' $ LL.findIndices p
{-# INLINE findIndices #-}

-- | 'Ordinal' version of 'findIndices'.
-- 
-- Since 0.1.0.0
sFindIndices :: (SingI n, ListLikeF f) => (a -> Bool) -> Sized f n a -> [Ordinal n]
sFindIndices p = fmap toEnum . findIndices p
{-# INLINE sFindIndices #-}

-- | Returns the index of the given element in the list, if exists.
-- 
-- Since 0.1.0.0
elemIndex :: (Eq a, ListLikeF f) => a -> Sized f n a -> Maybe Int
elemIndex a = findIndex (== a)
{-# INLINE elemIndex #-}

-- | Ordinal version of 'elemIndex'
-- 
-- Since 0.1.0.0
sElemIndex :: (SingI n, ListLikeF f, Eq a)
           => a -> Sized f n a -> Maybe (Ordinal n)
sElemIndex a = sFindIndex (== a)
{-# INLINE sElemIndex #-}


-- | Returns all indices of the given element in the list.
-- 
-- Since 0.1.0.0
elemIndices :: (ListLikeF f, Eq a) => a -> Sized f n a -> [Int]
elemIndices a = givenListLikeF' $ LL.elemIndices a
{-# INLINE elemIndices #-}

-- | Ordinal version of 'elemIndices'
-- 
-- Since 0.1.0.0
sElemIndices :: (SingI n, ListLikeF f, Eq a) => a -> Sized f n a -> [Ordinal n]
sElemIndices p = fmap toEnum . elemIndices p
{-# INLINE sElemIndices #-}

--------------------------------------------------------------------------------
-- Views and Patterns
--------------------------------------------------------------------------------

{-$ViewsAndPatterns #ViewsAndPatterns#

   With GHC's @ViewPatterns@ and @PatternSynonym@ extensions,
   we can pattern-match on arbitrary @Sized f n a@ if @f@ is list-like functor.
   Curretnly, there are two direction view and patterns: Cons and Snoc.
   Assuming underlying sequence type @f@ has O(1) implementation for 'LL.null', 'LL.head'
   (resp. 'LL.last') and 'LL.tail' (resp. 'LL.init'), We can view and pattern-match on
   cons (resp. snoc) of @Sized f n a@ in O(1).
-}

{-$views #views#

   With @ViewPatterns@ extension, we can pattern-match on 'Sized' value as follows:
   
@
slen :: ('SingI' n, 'ListLikeF' f) => 'Sized' f n a -> 'SNat' n
slen ('viewCons' -> 'NilCV')    = 'SZ'
slen ('viewCons' -> _ '::-' as) = 'SS' (slen as)
slen _                          = error "impossible"
@
   
   The constraint @('SingI' n, 'ListLikeF' f)@ is needed for view function.
   In the above, we have extra wildcard pattern (@_@) at the last.
   Code compiles if we removed it, but current GHC warns for incomplete pattern,
   although we know first two patterns exhausts all the case.
   
   Equivalently, we can use snoc-style pattern-matching:
   
@
slen :: ('SingI' n, 'ListLikeF' f) => 'Sized' f n a -> 'SNat' n
slen ('viewSnoc' -> 'NilSV')     = 'SZ'
slen ('viewSnoc' -> as ':-::' _) = 'SS' (slen as)
@
-}

-- | View of the left end of sequence (cons-side).
-- 
-- Since 0.1.0.0
data ConsView f n a where
  NilCV :: ConsView f Z a
  (::-) :: SingI n => a -> Sized f n a -> ConsView f (S n) a

infixr 5 ::-

-- | Case analysis for the cons-side of sequence.
-- 
-- Since 0.1.0.0
viewCons :: forall f a n. (SingI n, ListLikeF f)
         => Sized f n a
         -> ConsView f n a
viewCons sz = case sing :: SNat n of
  SZ    -> NilCV
  SS n' -> withSingI n' $ head sz ::- tail sz

-- | View of the left end of sequence (snoc-side).
-- 
-- Since 0.1.0.0
data SnocView f n a where
  NilSV :: SnocView f Z a
  (:-::) :: SingI n => Sized f n a -> a -> SnocView f (S n) a
infixl 5 :-::

-- | Case analysis for the snoc-side of sequence.
-- 
-- Since 0.1.0.0
viewSnoc :: forall f n a. (SingI n, ListLikeF f)
         => Sized f n a
         -> SnocView f n a
viewSnoc sz = case sing :: SNat n of
  SZ   -> NilSV
  SS n -> withSingI n $ init sz :-:: last sz

{-$patterns #patterns#

   So we can pattern match on both end of sequence via views, but
   it is rather clumsy to nest it. For example:

@
nextToHead :: ('ListLikeF' f, 'SingI' n) => 'Sized' f ('S' ('S' n)) a -> a
nextToHead ('viewCons' -> _ '::-' ('viewCons' -> a '::-' _)) = a
@

   In such a case, with @PatternSynonyms@ extension we can write as follows:

@
nextToHead :: ('ListLikeF' f, 'SingI' n) => 'Sized' f ('S' ('S' n)) a -> a
nextToHead (_ ':<' a ':<' _) = a
@

   Of course, we can also rewrite above @slen@ example using @PatternSynonyms@:

@
slen :: ('SingI' n, 'ListLikeF' f) => 'Sized' f n a -> 'SNat' n
slen 'NilL'      = 'SZ'
slen (_ ':<' as) = 'SS' (slen as)
slen _           = error "impossible"
@

   So, we can use @':<'@ and @'NilL'@ (resp. @':>'@ and @'NilR'@) to 
   pattern-match directly on cons-side (resp. snoc-side) as we usually do for lists.
   @':<'@, @'NilL'@, @':>'@ and @'NilR'@ are neither functions nor data constructors,
   but pattern synonyms so we cannot use them in expression contexts.
   For more detail on pattern synonyms, see
   <http://www.haskell.org/ghc/docs/latest/html/users_guide/syntax-extns.html#pattern-synonyms GHC Users Guide>
   and
   <https://ghc.haskell.org/trac/ghc/wiki/PatternSynonyms HaskellWiki>.
-}

infixr 5 :<
-- | Pattern synonym for cons-side uncons.
pattern a :< b <- (viewCons -> a ::- b)
pattern NilL   <- (viewCons -> NilCV)

infixl 5 :>
pattern a :> b <- (viewSnoc -> a :-:: b)
pattern NilR   <- (viewSnoc -> NilSV)
