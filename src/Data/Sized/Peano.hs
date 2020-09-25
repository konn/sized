{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeOperators, NoImplicitPrelude #-}
{-# LANGUAGE CPP, DataKinds, GADTs, KindSignatures, MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms, PolyKinds, RankNTypes, TypeInType           #-}
{-# LANGUAGE ViewPatterns                                                 #-}
{-# LANGUAGE NoStarIsType #-}
-- | This module exports provides the functionality to make length-parametrized types
--   from existing 'CFreeMonoid' sequential types,
--   parametrised with peano numeral 'PN.Nat' kind.
--
--   Most of the complexity of operations on @'Sized' f n a@ are the same as
--   original operations on @f@. For example, '!!' is O(1) for
--   @Sized Vector n a@ but O(i) for @Sized [] n a@.
--
--  This module also provides powerful view types and pattern synonyms to
--  inspect the sized sequence. See <#ViewsAndPatterns Views and Patterns> for more detail.
module Data.Sized.Peano
  ( -- * Main Data-types
    Sized(), SomeSized, pattern SomeSized, Ordinal,
    DomC(),
    -- * Accessors
    -- ** Length information
    length, sLength, null,
    -- ** Indexing
    (!!), (%!!), index, sIndex, head, last,
    uncons, uncons', Uncons, pattern Uncons,
    unsnoc, unsnoc', Unsnoc, pattern Unsnoc,
    -- ** Slicing
    tail, init, take, takeAtMost, drop, splitAt, splitAtMost,
    -- * Construction
    -- ** Initialisation
    empty, singleton, toSomeSized, replicate, replicate', generate, generate',
    -- ** Concatenation
    cons, (<|), snoc, (|>), append, (++), concat,
    -- ** Zips
    zip, zipSame, zipWith, zipWithSame, unzip, unzipWith,
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
    Partitioned(), pattern Partitioned,
    takeWhile, dropWhile, span, break, partition,
    -- ** Searching
    elem, notElem, find, findIndex, sFindIndex, 
    findIndices, sFindIndices,
    elemIndex, sElemIndex, sUnsafeElemIndex, elemIndices, sElemIndices,
    -- * Views and Patterns
    -- $ViewsAndPatterns

    -- ** Views
    -- $views

    -- ** Patterns
    -- $patterns

    -- ** Definitions
    viewCons, ConsView,
    pattern (:-), pattern NilCV,
    viewSnoc, SnocView,
    pattern (:-::), pattern NilSV,

    pattern (:<), pattern NilL , pattern (:>), pattern NilR,
  ) where
import qualified Data.Sized as S
import Data.Sized (DomC)

import           Control.Subcategory
import           Data.Kind                    (Type)
import           Data.Singletons.Prelude      (SingI)
import           Data.Singletons.Prelude.Enum (PEnum (..))
import qualified Data.Type.Ordinal            as O
import Prelude (Maybe, Ordering, Ord, Eq, Monoid, Bool(..), Int)
import Data.Type.Natural (Two, Nat(..), SNat)
import Data.Singletons.Prelude (POrd((<=)))
import Data.Type.Natural.Class (type (-.), type (<))
import Data.Type.Natural (Min, type (-), type (+), type (*))
import Data.Type.Natural (One)

type Ordinal = (O.Ordinal :: Nat -> Type)

-- | @Sized@ wraps a sequential type 'f' and makes length-parametrized version.
--
-- Here, 'f' must satisfy @'CFreeMonoid' f@ and @Dom f a@.
--
-- Since 0.2.0.0
type Sized = (S.Sized :: (Type -> Type) -> Nat -> Type -> Type)


-- | 'Sized' sequence with the length is existentially quantified.
--   This type is used mostly when the return type's length cannot
--   be statically determined beforehand.
--
-- @SomeSized' sn xs :: SomeSized' f a@ stands for the 'Sized' sequence
-- @xs@ of element type @a@ and length @sn@.
--
-- Since 0.7.0.0
type SomeSized f a = S.SomeSized' f Nat a

pattern SomeSized
  :: forall (f :: Type -> Type) a. ()
  => forall (n :: Nat). SNat n
  -> Sized f n a -> SomeSized f a
{-# COMPLETE SomeSized #-}
pattern SomeSized n s = S.SomeSized'  n s

-- | Returns the length of wrapped containers.
--   If you use @unsafeFromList@ or similar unsafe functions,
--   this function may return different value from type-parameterized length.
--
-- Since 0.8.0.0 (type changed)
{-# INLINE length #-}
length :: (Dom f a, SingI n) => Sized f n a -> Int
length = S.length @Nat

-- | @Sing@ version of 'length'.
--
-- Since 0.8.0.0 (type changed)
{-# INLINE sLength #-}
sLength :: (Dom f a, SingI n) => Sized f n a -> SNat n
sLength = S.sLength @Nat

-- | Test if the sequence is empty or not.
--
-- Since 0.7.0.0
{-# INLINE null #-}
null :: (Dom f a, CFoldable f) => Sized f n a -> Bool
null = S.null @Nat

--------------------------------------------------------------------------------
--- Indexing
--------------------------------------------------------------------------------

-- | (Unsafe) indexing with @Int@s.
--   If you want to check boundary statically, use '%!!' or 'sIndex'.
--
-- Since 0.7.0.0
{-# INLINE (!!) #-}
(!!) :: (Dom f a, CFoldable f, (One <= m) ~ 'True) => Sized f m a -> Int -> a
(!!) = (S.!!) @Nat

-- | Safe indexing with 'Ordinal's.
--
-- Since 0.7.0.0
{-# INLINE (%!!) #-}
(%!!) :: (Dom f c, CFoldable f) => Sized f n c -> Ordinal n -> c
(%!!) = (S.%!!) @Nat

-- | Flipped version of '!!'.
--
-- Since 0.7.0.0
{-# INLINE index #-}
index
  :: (Dom f a, CFoldable f, (One <= m) ~ 'True)
  => Int -> Sized f m a -> a
index = S.index @Nat

-- | Flipped version of '%!!'.
--
-- Since 0.7.0.0
{-# INLINE sIndex #-}
sIndex :: (Dom f c, CFoldable f) => Ordinal n -> Sized f n c -> c
sIndex = S.sIndex @Nat

-- | Take the first element of non-empty sequence.
--   If you want to make case-analysis for general sequence,
--   see  <#ViewsAndPatterns Views and Patterns> section.
--
-- Since 0.7.0.0
{-# INLINE head #-}
head :: (Dom f a, CFoldable f, ('Z < n) ~ 'True) => Sized f n a -> a
head = S.head @Nat

-- | Take the last element of non-empty sequence.
--   If you want to make case-analysis for general sequence,
--   see  <#ViewsAndPatterns Views and Patterns> section.
--
-- Since 0.7.0.0
{-# INLINE last #-}
last :: (Dom f a, CFoldable f, ('Z < n) ~ 'True) => Sized f n a -> a
last = S.last @Nat

-- | Take the 'head' and 'tail' of non-empty sequence.
--   If you want to make case-analysis for general sequence,
--   see  <#ViewsAndPatterns Views and Patterns> section.
--
-- Since 0.7.0.0
{-# INLINE uncons #-}
uncons
  :: (Dom f a, SingI n, CFreeMonoid f, ('Z < n) ~ 'True)
  => Sized f n a -> Uncons f n a
uncons = S.uncons @Nat

-- | 'uncons' with explicit specified length @n@
--
--   Since 0.7.0.0
{-# INLINE uncons' #-}
uncons'
  :: (Dom f a, SingI n, CFreeMonoid f, ('Z < n) ~ 'True)
  => Sized f n a
  -> Uncons f n a
uncons' = S.uncons @Nat

-- | Take the 'init' and 'last' of non-empty sequence.
--   If you want to make case-analysis for general sequence,
--   see  <#ViewsAndPatterns Views and Patterns> section.
--
-- Since 0.7.0.0
{-# INLINE unsnoc #-}
unsnoc
  :: (Dom f a, SingI n, CFreeMonoid f, ('Z < n) ~ 'True)
  => Sized f n a -> Unsnoc f n a
unsnoc = S.unsnoc @Nat

-- | 'unsnoc'' with explicit specified length @n@
--
--   Since 0.7.0.0
{-# INLINE unsnoc' #-}
unsnoc' :: (Dom f a, SingI n, CFreeMonoid f) => proxy n -> Sized f ('S n) a -> Unsnoc f ('S n) a
unsnoc' = S.unsnoc' @Nat

type Uncons f (n :: Nat) a = S.Uncons f n a
pattern Uncons
  :: forall (f :: Type -> Type) (n :: Nat) a. ()
  => forall (n1 :: Nat). (n ~ Succ n1, SingI n1)
  => a -> Sized f n1 a -> Uncons f n a
pattern Uncons a as = S.Uncons a as

type Unsnoc f (n :: Nat) a = S.Unsnoc f n a

pattern Unsnoc
  :: forall (f :: Type -> Type) (n :: Nat) a. ()
  => forall (n1 :: Nat). (n ~ Succ n1)
  => Sized f n1 a -> a -> Unsnoc f n a
pattern Unsnoc xs x = S.Unsnoc xs x

-- | Take the tail of non-empty sequence.
--   If you want to make case-analysis for general sequence,
--   see  <#ViewsAndPatterns Views and Patterns> section.
--
-- Since 0.7.0.0
{-# INLINE tail #-}
tail :: (Dom f a, CFreeMonoid f) => Sized f (One + n) a -> Sized f n a
tail = S.tail @Nat


-- | Take the initial segment of non-empty sequence.
--   If you want to make case-analysis for general sequence,
--   see  <#ViewsAndPatterns Views and Patterns> section.
--
-- Since 0.7.0.0
{-# INLINE init #-}
init :: (Dom f a, CFreeMonoid f) => Sized f (n + One) a -> Sized f n a
init = S.init @Nat

-- | @take k xs@ takes first @k@ element of @xs@ where
-- the length of @xs@ should be larger than @k@.
--
-- Since 0.7.0.0
{-# INLINE take #-}
take
  :: (Dom f a, CFreeMonoid f, (n <= m) ~ 'True)
  => SNat n -> Sized f m a -> Sized f n a
take = S.take @Nat

-- | @'takeAtMost' k xs@ takes first at most @k@ elements of @xs@.
--
-- Since 0.7.0.0
{-# INLINE takeAtMost #-}
takeAtMost
  :: (Dom f a, CFreeMonoid f)
  => SNat n -> Sized f m a -> Sized f (Min n m) a
takeAtMost = S.takeAtMost @Nat

-- | @drop k xs@ drops first @k@ element of @xs@ and returns
-- the rest of sequence, where the length of @xs@ should be larger than @k@.
--
-- Since 0.7.0.0
{-# INLINE drop #-}
drop
  :: (Dom f a, CFreeMonoid f, (n <= m) ~ 'True)
  => SNat n -> Sized f m a -> Sized f (m - n) a
drop = S.drop @Nat

-- | @splitAt k xs@ split @xs@ at @k@, where
-- the length of @xs@ should be less than or equal to @k@.
--
-- Since 0.7.0.0
{-# INLINE splitAt #-}
splitAt
  :: (Dom f a, CFreeMonoid f, (n <= m) ~ 'True)
  => SNat n -> Sized f m a -> (Sized f n a, Sized f (m - n) a)
splitAt = S.splitAt @Nat

-- | @splitAtMost k xs@ split @xs@ at @k@.
--   If @k@ exceeds the length of @xs@, then the second result value become empty.
--
-- Since 0.7.0.0
{-# INLINE splitAtMost #-}
splitAtMost
  :: (Dom f a, CFreeMonoid f)
  => SNat n -> Sized f m a
  -> (Sized f (Min n m) a, Sized f (m -. n) a)
splitAtMost = S.splitAtMost @Nat

--------------------------------------------------------------------------------
-- Construction
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
--- Initialisation
--------------------------------------------------------------------------------

-- | Empty sequence.
--
-- Since 0.7.0.0 (type changed)
{-# INLINE empty #-}
empty :: (Dom f a, Monoid (f a)) => Sized f 'Z a
empty = S.empty @Nat

-- | Sequence with one element.
--
-- Since 0.7.0.0
{-# INLINE singleton #-}
singleton :: (Dom f a, CFreeMonoid f) => a -> Sized f One a
singleton = S.singleton @Nat

-- | Consruct the 'Sized' sequence from base type, but
--   the length parameter is dynamically determined and
--   existentially quantified; see also 'SomeSized''.
--
-- Since 0.7.0.0
{-# INLINE toSomeSized #-}
toSomeSized :: (Dom f a, CFoldable f) => f a -> SomeSized f a
toSomeSized = S.toSomeSized @Nat

-- | Replicates the same value.
--
-- Since 0.7.0.0
{-# INLINE replicate #-}
replicate :: (Dom f a, CFreeMonoid f) => SNat n -> a -> Sized f n a
replicate = S.replicate @Nat

-- | 'replicate' with the length inferred.
--
-- Since 0.7.0.0
{-# INLINE replicate' #-}
replicate' :: (Dom f a, CFreeMonoid f, SingI n) => a -> Sized f n a
replicate' = S.replicate' @Nat

-- | Construct a sequence of the given length by applying the function to each index.
--
-- Since 0.7.0.0
{-# INLINE generate #-}
generate :: (Dom f a, CFreeMonoid f) => SNat n -> (Ordinal n -> a) -> Sized f n a
generate = S.generate @Nat

-- | 'generate' with length inferred.
--
--   Since 0.8.0.0
{-# INLINE generate' #-}
generate' :: forall f n a.
  (SingI n, Dom f a, CFreeMonoid f)
  => (Ordinal n -> a) -> Sized f n a
generate' = S.generate' @Nat

--------------------------------------------------------------------------------
--- Concatenation
--------------------------------------------------------------------------------

-- | Append an element to the head of sequence.
--
-- Since 0.7.0.0
{-# INLINE cons #-}
cons :: (Dom f a, CFreeMonoid f) => a -> Sized f n a -> Sized f ('S n) a
cons = S.cons @Nat

-- | Append an element to the tail of sequence.
--
-- Since 0.7.0.0
{-# INLINE snoc #-}
snoc :: (Dom f a, CFreeMonoid f) => Sized f n a -> a -> Sized f (n + One) a
snoc = S.snoc @Nat

-- | Infix version of 'snoc'.
--
-- Since 0.7.0.0
{-# INLINE (<|) #-}
(<|) :: (Dom f a, CFreeMonoid f) => a -> Sized f n a -> Sized f ('S n) a
(<|) = (S.<|) @Nat

-- | Append an element to the tail of sequence.
--
-- Since 0.7.0.0
{-# INLINE (|>) #-}
(|>) :: (Dom f a, CFreeMonoid f) => Sized f n a -> a -> Sized f (n + One) a
(|>) = (S.|>) @Nat

-- | Infix version of 'append'.
--
-- Since 0.7.0.0
{-# INLINE (++) #-}
(++) :: (Dom f a, CFreeMonoid f) => Sized f n a -> Sized f m a -> Sized f (n + m) a
(++) = (S.++) @Nat

-- | Append two lists.
--
-- Since 0.7.0.0
{-# INLINE append #-}
append :: (Dom f a, CFreeMonoid f) => Sized f n a -> Sized f m a -> Sized f (n + m) a
append = S.append @Nat

-- | Concatenates multiple sequences into one.
--
-- Since 0.7.0.0
{-# INLINE concat #-}
concat
  :: (Dom f a, Dom f' (f a), Dom f' (Sized f n a),
      CFreeMonoid f, CFunctor f', CFoldable f'
    ) => Sized f' m (Sized f n a) -> Sized f (m * n) a
concat = S.concat @Nat

--------------------------------------------------------------------------------
--- Zips
--------------------------------------------------------------------------------

-- | Zipping two sequences. Length is adjusted to shorter one.
--
-- Since 0.7.0.0
{-# INLINE zip #-}
zip :: (Dom f a, Dom f b, Dom f (a, b), CZip f)
  => Sized f n a -> Sized f m b -> Sized f (Min n m) (a, b)
zip = S.zip @Nat

-- | 'zip' for the sequences of the same length.
--
-- Since 0.7.0.0
{-# INLINE zipSame #-}
zipSame :: (Dom f a, Dom f b, Dom f (a, b), CZip f)
  => Sized f n a -> Sized f n b -> Sized f n (a, b)
zipSame = S.zipSame @Nat

-- | Zipping two sequences with funtion. Length is adjusted to shorter one.
--
-- Since 0.7.0.0
{-# INLINE zipWith #-}
zipWith :: (Dom f a, Dom f b, Dom f c, CZip f, CFreeMonoid f)
  => (a -> b -> c) -> Sized f n a -> Sized f m b -> Sized f (Min n m) c
zipWith = S.zipWith @Nat

-- | 'zipWith' for the sequences of the same length.
--
-- Since 0.7.0.0
{-# INLINE zipWithSame #-}
zipWithSame
  :: (Dom f a, Dom f b, Dom f c, CZip f, CFreeMonoid f)
  => (a -> b -> c) -> Sized f n a -> Sized f n b -> Sized f n c
zipWithSame = S.zipWithSame @Nat

-- | Unzipping the sequence of tuples.
--
-- Since 0.7.0.0
{-# INLINE unzip #-}
unzip
  :: (Dom f a, Dom f b, Dom f (a, b), CUnzip f)
  => Sized f n (a, b) -> (Sized f n a, Sized f n b)
unzip = S.unzip @Nat

-- | Unzipping the sequence of tuples.
--
-- Since 0.7.0.0
{-# INLINE unzipWith #-}
unzipWith
  :: (Dom f a, Dom f b, Dom f c, CUnzip f)
  => (a -> (b, c)) -> Sized f n a -> (Sized f n b, Sized f n c)
unzipWith = S.unzipWith @Nat

--------------------------------------------------------------------------------
-- Transformation
--------------------------------------------------------------------------------

-- | Map function.
--
-- Since 0.7.0.0
{-# INLINE map #-}
map
  :: (Dom f a, Dom f b, CFreeMonoid f)
  => (a -> b) -> Sized f n a -> Sized f n b
map = S.map @Nat

-- | Reverse function.
--
-- Since 0.7.0.0
{-# INLINE reverse #-}
reverse :: (Dom f a, CFreeMonoid f) => Sized f n a -> Sized f n a
reverse = S.reverse @Nat

-- | Intersperces.
--
-- Since 0.7.0.0
{-# INLINE intersperse #-}
intersperse
  :: (Dom f a, CFreeMonoid f)
  => a -> Sized f n a -> Sized f ((Two * n) -. One) a 
intersperse = S.intersperse @Nat

-- | Remove all duplicates.
--
-- Since 0.7.0.0
{-# INLINE nub #-}
nub :: (Dom f a, Eq a, CFreeMonoid f) => Sized f n a -> SomeSized f a
nub = S.nub @Nat

-- | Sorting sequence by ascending order.
--
-- Since 0.7.0.0
{-# INLINE sort #-}
sort :: (Dom f a, CFreeMonoid f, Ord a) => Sized f n a -> Sized f n a
sort = S.sort @Nat

-- | Generalized version of 'sort'.
--
-- Since 0.7.0.0
{-# INLINE sortBy #-}
sortBy
  :: (Dom f a, CFreeMonoid f)
  => (a -> a -> Ordering)
  -> Sized f n a -> Sized f n a
sortBy = S.sortBy @Nat

-- | Insert new element into the presorted sequence.
--
-- Since 0.7.0.0
{-# INLINE insert #-}
insert
  :: (Dom f a, CFreeMonoid f, Ord a)
  => a -> Sized f n a -> Sized f ('S n) a
insert = S.insert @Nat

-- | Generalized version of 'insert'.
--
-- Since 0.7.0.0
{-# INLINE insertBy #-}
insertBy
  :: (Dom f a, CFreeMonoid f)
  => (a -> a -> Ordering) -> a -> Sized f n a -> Sized f ('S n) a
insertBy = S.insertBy @Nat

--------------------------------------------------------------------------------
-- Conversion
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
--- List
--------------------------------------------------------------------------------

-- | Convert to list.
--
-- Since 0.7.0.0
{-# INLINE toList #-}
toList :: (Dom f a, CFoldable f) => Sized f n a -> [a]
toList = S.toList @Nat

-- | If the given list is shorter than @n@, then returns @Nothing@
--   Otherwise returns @Sized f n a@ consisting of initial @n@ element
--   of given list.
--
--   Since 0.7.0.0 (type changed)
{-# INLINE fromList #-}
fromList :: (Dom f a, CFreeMonoid f) => SNat n -> [a] -> Maybe (Sized f n a)
fromList = S.fromList @Nat

-- | 'fromList' with the result length inferred.
--
-- Since 0.7.0.0
{-# INLINE fromList' #-}
fromList' :: (Dom f a, CFreeMonoid f, SingI n) => [a] -> Maybe (Sized f n a)
fromList' = S.fromList' @Nat

-- | Unsafe version of 'fromList'. If the length of the given list does not
--   equal to @n@, then something unusual happens.
--
-- Since 0.7.0.0
{-# INLINE unsafeFromList #-}
unsafeFromList :: (Dom f a, CFreeMonoid f) => SNat n -> [a] -> Sized f n a
unsafeFromList = S.unsafeFromList @Nat

-- | 'unsafeFromList' with the result length inferred.
--
-- Since 0.7.0.0
{-# INLINE unsafeFromList' #-}
unsafeFromList' :: (Dom f a, SingI n, CFreeMonoid f) => [a] -> Sized f n a
unsafeFromList' = S.unsafeFromList' @Nat

-- | Construct a @Sized f n a@ by padding default value if the given list is short.
--
--   Since 0.5.0.0 (type changed)
{-# INLINE fromListWithDefault #-}
fromListWithDefault :: (Dom f a, CFreeMonoid f) => SNat n -> a -> [a] -> Sized f n a
fromListWithDefault = S.fromListWithDefault @Nat

-- | 'fromListWithDefault' with the result length inferred.
--
-- Since 0.7.0.0
{-# INLINE fromListWithDefault' #-}
fromListWithDefault' :: (Dom f a, SingI n, CFreeMonoid f)
  => a -> [a] -> Sized f n a
fromListWithDefault' = S.fromListWithDefault' @Nat

--------------------------------------------------------------------------------
--- Base containes
--------------------------------------------------------------------------------

-- | Forget the length and obtain the wrapped base container.
--
-- Since 0.7.0.0
{-# INLINE unsized #-}
unsized :: Sized f n a -> f a
unsized = S.unsized @Nat

-- | If the length of the input is shorter than @n@, then returns @Nothing@.
--   Otherwise returns @Sized f n a@ consisting of initial @n@ element
--   of the input.
--
-- Since 0.7.0.0
{-# INLINE toSized #-}
toSized :: (Dom f a, CFreeMonoid f) => SNat n -> f a -> Maybe (Sized f n a)
toSized = S.toSized @Nat

-- | 'toSized' with the result length inferred.
--
-- Since 0.7.0.0
{-# INLINE toSized' #-}
toSized' :: (Dom f a, CFreeMonoid f, SingI n) => f a -> Maybe (Sized f n a)
toSized' = S.toSized' @Nat

-- | Unsafe version of 'toSized'. If the length of the given list does not
--   equal to @n@, then something unusual happens.
--
-- Since 0.7.0.0
{-# INLINE unsafeToSized #-}
unsafeToSized :: SNat n -> f a -> Sized f n a
unsafeToSized = S.unsafeToSized @Nat

-- | 'unsafeToSized' with the result length inferred.
--
-- Since 0.7.0.0
{-# INLINE unsafeToSized' #-}
unsafeToSized' :: (Dom f a, SingI n) => f a -> Sized f n a
unsafeToSized' = S.unsafeToSized' @Nat

-- | Construct a @Sized f n a@ by padding default value if the given list is short.
--
-- Since 0.7.0.0
{-# INLINE toSizedWithDefault #-}
toSizedWithDefault :: (Dom f a, CFreeMonoid f) => SNat n -> a -> f a -> Sized f n a
toSizedWithDefault = S.toSizedWithDefault @Nat

-- | 'toSizedWithDefault' with the result length inferred.
--
-- Since 0.7.0.0
{-# INLINE toSizedWithDefault' #-}
toSizedWithDefault' :: (Dom f a, SingI n, CFreeMonoid f)
  => a -> f a -> Sized f n a
toSizedWithDefault' = S.toSizedWithDefault' @Nat

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
-- Since 0.7.0.0
type Partitioned f (n :: Nat) a = S.Partitioned f n a

pattern Partitioned
  :: forall (f :: Type -> Type) (n :: Nat) a. ()
  => forall (n1 :: Nat) (m :: Nat). (n ~ (n1 + m), Dom f a)
  => SNat n1 -> Sized f n1 a -> SNat m
  -> Sized f m a -> Partitioned f n a
{-# COMPLETE Partitioned #-}
pattern Partitioned ls l rs r = S.Partitioned ls l rs r

-- | Take the initial segment as long as elements satisfys the predicate.
--
-- Since 0.7.0.0
{-# INLINE takeWhile #-}
takeWhile :: (Dom f a, CFreeMonoid f) => (a -> Bool) -> Sized f n a -> SomeSized f a
takeWhile = S.takeWhile @Nat

-- | Drop the initial segment as long as elements satisfys the predicate.
--
-- Since 0.7.0.0
{-# INLINE dropWhile #-}
dropWhile :: (Dom f a, CFreeMonoid f) => (a -> Bool) -> Sized f n a -> SomeSized f a
dropWhile = S.dropWhile @Nat

-- | Split the sequence into the longest prefix
--   of elements that satisfy the predicate
--   and the rest.
-- 
-- Since 0.7.0.0
{-# INLINE span #-}
span :: (Dom f a, CFreeMonoid f) => (a -> Bool) -> Sized f n a -> Partitioned f n a
span = S.span @Nat


-- | Split the sequence into the longest prefix
--   of elements that do not satisfy the
--   predicate and the rest.
--
-- Since 0.7.0.0
{-# INLINE break #-}
break :: (Dom f a, CFreeMonoid f) => (a -> Bool) -> Sized f n a -> Partitioned f n a
break = S.break @Nat

-- | Split the sequence in two parts, the first one containing those elements that satisfy the predicate and the second one those that don't. 
--
-- Since 0.7.0.0
{-# INLINE partition #-}
partition :: (Dom f a, CFreeMonoid f) => (a -> Bool) -> Sized f n a -> Partitioned f n a
partition = S.partition @Nat

--------------------------------------------------------------------------------
--- Searching
--------------------------------------------------------------------------------
-- | Membership test; see also 'notElem'.
--
-- Since 0.7.0.0
{-# INLINE elem #-}
elem :: (Dom f a, CFoldable f, Eq a) => a -> Sized f n a -> Bool
elem = S.elem @Nat

-- | Negation of 'elem'.
--
-- Since 0.7.0.0
{-# INLINE notElem #-}
notElem :: (Dom f a, CFoldable f, Eq a) => a -> Sized f n a -> Bool
notElem = S.notElem @Nat

-- | Find the element satisfying the predicate.
--
-- Since 0.7.0.0
{-# INLINE find #-}
find :: (Dom f a, CFoldable f) => (a -> Bool) -> Sized f n a -> Maybe a
find = S.find @Nat

-- | @'findIndex' p xs@ find the element satisfying @p@ and returns its index if exists.
--
-- Since 0.7.0.0
{-# INLINE findIndex #-}
findIndex :: (Dom f a, CFoldable f) => (a -> Bool) -> Sized f n a -> Maybe Int
findIndex = S.findIndex @Nat

-- | 'Ordinal' version of 'findIndex'.
--
-- Since 0.7.0.0
{-# INLINE sFindIndex #-}
sFindIndex :: (Dom f a, SingI n, CFoldable f) => (a -> Bool) -> Sized f n a -> Maybe (Ordinal n)
sFindIndex = S.sFindIndex @Nat

-- | @'findIndices' p xs@ find all elements satisfying @p@ and returns their indices.
--
-- Since 0.7.0.0
{-# INLINE findIndices #-}
findIndices :: (Dom f a, CFoldable f) => (a -> Bool) -> Sized f n a -> [Int]
findIndices = S.findIndices @Nat

-- | 'Ordinal' version of 'findIndices'.
--
-- Since 0.7.0.0
{-# INLINE sFindIndices #-}
sFindIndices :: (Dom f a, CFoldable f, SingI n) => (a -> Bool) -> Sized f n a -> [Ordinal n]
sFindIndices = S.sFindIndices @Nat

-- | Returns the index of the given element in the list, if exists.
--
-- Since 0.7.0.0
{-# INLINE elemIndex #-}
elemIndex :: (Dom f a, CFoldable f, Eq a) => a -> Sized f n a -> Maybe Int
elemIndex = S.elemIndex @Nat

sElemIndex, sUnsafeElemIndex :: (Dom f a, SingI n, CFoldable f, Eq a) => a -> Sized f n a -> Maybe (Ordinal n)
{-# DEPRECATED sUnsafeElemIndex "Use sElemIndex instead" #-}

-- | Ordinal version of 'elemIndex'.
--   Since 0.7.0.0, we no longer do boundary check inside the definition. 
--
--   Since 0.7.0.0
sUnsafeElemIndex = S.sElemIndex @Nat

-- | Ordinal version of 'elemIndex'.
--   Since 0.7.0.0, we no longer do boundary check inside the definition. 
--
--   Since 0.7.0.0
sElemIndex = S.sElemIndex @Nat

-- | Returns all indices of the given element in the list.
--
-- Since 0.8.0.0
{-# INLINE elemIndices #-}
elemIndices :: (Dom f a, CFoldable f, Eq a) => a -> Sized f n a -> [Int]
elemIndices = S.elemIndices @Nat

-- | Ordinal version of 'elemIndices'
--
-- Since 0.8.0.0
{-# INLINE sElemIndices #-}
sElemIndices
  :: (Dom f a, CFoldable f, SingI n, Eq a)
  => a -> Sized f n a -> [Ordinal n]
sElemIndices = S.sElemIndices @Nat


--------------------------------------------------------------------------------
-- Views and Patterns
--------------------------------------------------------------------------------

{-$ViewsAndPatterns #ViewsAndPatterns#

   With GHC's @ViewPatterns@ and @PatternSynonym@ extensions,
   we can pattern-match on arbitrary @Sized f n a@ if @f@ is list-like functor.
   Curretnly, there are two direction view and patterns: Cons and Snoc.
   Assuming underlying sequence type @f@ has O(1) implementation for 'cnull', 'chead'
   (resp. 'clast') and 'ctail' (resp. 'cinit'), We can view and pattern-match on
   cons (resp. snoc) of @Sized f n a@ in O(1).
-}

{-$views #views#

   With @ViewPatterns@ extension, we can pattern-match on 'Sized' value as follows:

@
slen :: ('KnownNat' n, 'Dom f a' f) => 'Sized' f n a -> 'Sing' n
slen ('viewCons' -> 'NilCV')    = 'SZ'
slen ('viewCons' -> _ ':-' as) = 'SS' (slen as)
slen _                          = error "impossible"
@

   The constraint @('KnownNat' n, 'Dom f a' f)@ is needed for view function.
   In the above, we have extra wildcard pattern (@_@) at the last.
   Code compiles if we removed it, but current GHC warns for incomplete pattern,
   although we know first two patterns exhausts all the case.

   Equivalently, we can use snoc-style pattern-matching:

@
slen :: ('KnownNat' n, 'Dom f a' f) => 'Sized' f n a -> 'Sing' n
slen ('viewSnoc' -> 'NilSV')     = 'SZ'
slen ('viewSnoc' -> as '-::' _) = 'SS' (slen as)
@
-}


-- | View of the left end of sequence (cons-side).
--
-- Since 0.7.0.0
type ConsView f (n :: Nat) a = S.ConsView f n a

-- | Since 0.8.0.0
pattern NilCV
  :: forall (f :: Type -> Type) n a. ()
  => (n ~ 'Z)
  => ConsView f n a
pattern NilCV = S.NilCV

-- | Since 0.8.0.0
pattern (:-)
  :: forall (f :: Type -> Type) n a. ()
  => forall n1. (n ~ (One + n1), SingI n1)
  => a -> Sized f n1 a -> ConsView f n a
pattern l :- ls = l S.:- ls

infixr 9 :-
{-# COMPLETE NilCV, (:-) #-}

-- | Case analysis for the cons-side of sequence.
--
-- Since 0.5.0.0 (type changed)
viewCons :: (Dom f a, SingI n, CFreeMonoid f) => Sized f n a -> ConsView f n a
viewCons = S.viewCons @Nat

-- | View of the left end of sequence (snoc-side).
--
-- Since 0.7.0.0
type SnocView f (n :: Nat) a = S.SnocView f n a

-- | Since 0.8.0.0
pattern NilSV
  :: forall (f :: Type -> Type) n a. ()
  => (n ~ 'Z)
  => SnocView f n a
pattern NilSV = S.NilSV

infixl 9 :-::
-- | Since 0.8.0.0
pattern (:-::)
  :: forall (f :: Type -> Type) n a. ()
  => forall n1. (n ~ (n1 + One), SingI n1)
  => Sized f n1 a -> a -> SnocView f n a
pattern ls :-:: l = ls S.:-:: l
{-# COMPLETE NilSV, (:-::) #-}

-- | Case analysis for the snoc-side of sequence.
--
-- Since 0.8.0.0 (type changed)
viewSnoc :: (Dom f a, SingI n, CFreeMonoid f) => Sized f n a -> ConsView f n a
viewSnoc = S.viewCons @Nat


{-$patterns #patterns#

   So we can pattern match on both end of sequence via views, but
   it is rather clumsy to nest it. For example:

@
nextToHead :: ('Dom f a' f, 'SingI' n) => 'Sized' f ('S' ('S' n)) a -> a
nextToHead ('viewCons' -> _ ':-' ('viewCons' -> a ':-' _)) = a
@

   In such a case, with @PatternSynonyms@ extension we can write as follows:

@
nextToHead :: ('Dom f a' f, 'SingI' n) => 'Sized' f ('S' ('S' n)) a -> a
nextToHead (_ ':<' a ':<' _) = a
@

   Of course, we can also rewrite above @slen@ example using @PatternSynonyms@:

@
slen :: ('SingI' n, 'Dom f a' f) => 'Sized' f n a -> 'Sing' n
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

-- | Pattern synonym for cons-side uncons.
pattern (:<)
  :: forall (f :: Type -> Type) a (n :: Nat).
      (Dom f a, SingI n, CFreeMonoid f)
  => forall (n1 :: Nat). (n ~ Succ n1, SingI n1)
  => a -> Sized f n1 a -> Sized f n a
pattern a :< b = a S.:< b
infixr 5 :<

-- | Pattern synonym for cons-side nil.
pattern NilL :: forall f (n :: Nat) a.
                (SingI n, CFreeMonoid f, Dom f a)
             => n ~ 'Z => Sized f n a
pattern NilL = S.NilL

-- | Pattern synonym for snoc-side unsnoc.
pattern (:>)
  :: forall (f :: Type -> Type) a (n :: Nat). 
      (Dom f a, SingI n, CFreeMonoid f)
  => forall (n1 :: Nat). (n ~ (n1 + One), SingI n1)
  => Sized f n1 a -> a -> Sized f n a
pattern a :> b = a S.:> b
infixl 5 :>

-- | Pattern synonym for snoc-side nil.
pattern NilR :: forall f (n :: Nat) a.
                (CFreeMonoid f, Dom f a,  SingI n)
             => n ~ 'Z => Sized f n a
pattern NilR = S.NilR
{-# COMPLETE (:<), NilL #-}
{-# COMPLETE (:<), NilR #-}
{-# COMPLETE (:>), NilL #-}
{-# COMPLETE (:>), NilR #-}
