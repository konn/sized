{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE NoStarIsType #-}
{-# OPTIONS_GHC -fenable-rewrite-rules #-}
{-# OPTIONS_GHC -fno-warn-type-defaults -fno-warn-orphans #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Presburger #-}

{- | This module provides the functionality to make length-parametrized types
   from existing 'CFreeMonoid' sequential types.

   Most of the complexity of operations for @Sized f n a@ are the same as
   original operations for @f@. For example, '!!' is O(1) for
   @Sized Vector n a@ but O(i) for @Sized [] n a@.

  This module also provides powerful view types and pattern synonyms to
  inspect the sized sequence. See <#ViewsAndPatterns Views and Patterns> for more detail.
-}
module Data.Sized
  ( -- * Main Data-types
    Sized (),
    SomeSized (..),
    DomC (),

    -- * Accessors

    -- ** Length information
    length,
    sLength,
    null,

    -- ** Indexing
    (!!),
    (%!!),
    index,
    sIndex,
    head,
    last,
    uncons,
    uncons',
    Uncons (..),
    unsnoc,
    unsnoc',
    Unsnoc (..),

    -- ** Slicing
    tail,
    init,
    take,
    takeAtMost,
    drop,
    splitAt,
    splitAtMost,

    -- * Construction

    -- ** Initialisation
    empty,
    singleton,
    toSomeSized,
    replicate,
    replicate',
    generate,
    generate',

    -- ** Concatenation
    cons,
    (<|),
    snoc,
    (|>),
    append,
    (++),
    concat,

    -- ** Zips
    zip,
    zipSame,
    zipWith,
    zipWithSame,
    unzip,
    unzipWith,

    -- * Transformation
    map,
    reverse,
    intersperse,
    nub,
    sort,
    sortBy,
    insert,
    insertBy,

    -- * Conversion

    -- ** List
    toList,
    fromList,
    fromList',
    unsafeFromList,
    unsafeFromList',
    fromListWithDefault,
    fromListWithDefault',

    -- ** Base container
    unsized,
    toSized,
    toSized',
    unsafeToSized,
    unsafeToSized',
    toSizedWithDefault,
    toSizedWithDefault',

    -- * Querying

    -- ** Partitioning
    Partitioned (..),
    takeWhile,
    dropWhile,
    span,
    break,
    partition,

    -- ** Searching
    elem,
    notElem,
    find,
    findIndex,
    sFindIndex,
    findIndices,
    sFindIndices,
    elemIndex,
    sElemIndex,
    sUnsafeElemIndex,
    elemIndices,
    sElemIndices,

    -- * Views and Patterns
    -- $ViewsAndPatterns

    -- ** Views
    -- $views

    -- ** Patterns
    -- $patterns

    -- ** Definitions
    viewCons,
    ConsView (..),
    viewSnoc,
    SnocView (..),
    pattern Nil,
    pattern (:<),
    pattern (:>),
  )
where

import Control.Applicative (ZipList (..), (<*>))
import Control.Subcategory
  ( CApplicative (..),
    CFoldable (..),
    CFreeMonoid (..),
    CFunctor (..),
    CPointed (..),
    CRepeat (..),
    CSemialign (..),
    CTraversable (..),
    CUnzip (..),
    CZip (..),
    Constrained (Dom),
    cfromList,
    ctoList,
  )
import Data.Coerce (coerce)
import Data.Constraint (Dict (..), withDict)
import qualified Data.Foldable as F
import Data.Kind (Type)
import qualified Data.List as L
import Data.Maybe (fromJust)
import Data.Monoid (Monoid (..), (<>))
import qualified Data.Sequence as Seq
import Data.Sized.Internal
import Data.These (These (..))
import Data.Type.Equality (gcastWith, (:~:) (..))
import Data.Type.Natural
import Data.Type.Ordinal (Ordinal (..), ordToNatural)
import Data.Typeable (Typeable)
import qualified Data.Vector as V
import qualified Data.Vector.Storable as SV
import qualified Data.Vector.Unboxed as UV
import Unsafe.Coerce (unsafeCoerce)
import Prelude
  ( Bool (..),
    Enum (..),
    Eq (..),
    Functor,
    Int,
    Maybe (..),
    Num (..),
    Ord (..),
    Ordering,
    Show (..),
    const,
    flip,
    fmap,
    fromIntegral,
    uncurry,
    ($),
    (.),
  )
import qualified Prelude as P

--------------------------------------------------------------------------------
-- Main data-types
--------------------------------------------------------------------------------

{- | 'Sized' vector with the length is existentially quantified.
   This type is used mostly when the return type's length cannot
   be statically determined beforehand.

 @SomeSized sn xs :: SomeSized f a@ stands for the 'Sized' sequence
 @xs@ of element type @a@ and length @sn@.

 Since 0.7.0.0
-}
data SomeSized f a where
  SomeSized ::
    SNat n ->
    Sized f n a ->
    SomeSized f a

deriving instance Typeable SomeSized

instance Show (f a) => Show (SomeSized f a) where
  showsPrec d (SomeSized _ s) =
    P.showParen (d > 9) $
      P.showString "SomeSized _ " . showsPrec 10 s

instance Eq (f a) => Eq (SomeSized f a) where
  (SomeSized _ (Sized xs)) == (SomeSized _ (Sized ys)) = xs == ys

--------------------------------------------------------------------------------
-- Accessors
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
--- Length infromation
--------------------------------------------------------------------------------

{- | Returns the length of wrapped containers.
   If you use @unsafeFromList@ or similar unsafe functions,
   this function may return different value from type-parameterized length.

 Since 0.8.0.0 (type changed)
-}
length ::
  forall f (n :: Nat) a.
  (Dom f a, KnownNat n) =>
  Sized f n a ->
  Int
length = const $ fromIntegral $ fromSNat $ sNat @n
{-# INLINE CONLIKE [1] length #-}

lengthTLZero :: Sized f 0 a -> Int
lengthTLZero = P.const 0
{-# INLINE lengthTLZero #-}

{-# RULES
"length/0" [~1] length = lengthTLZero
  #-}

{- | @SNat@ version of 'length'.

 Since 0.8.0.0 (type changed)
-}
sLength ::
  forall f (n :: Nat) a.
  (Dom f a, KnownNat n) =>
  Sized f n a ->
  SNat n
sLength _ = sNat @n
{-# INLINE [2] sLength #-}

{- | Test if the sequence is empty or not.

 Since 0.7.0.0
-}
null ::
  forall f (n :: Nat) a.
  (CFoldable f, Dom f a) =>
  Sized f n a ->
  Bool
null = coerce $ cnull @f @a
{-# INLINE CONLIKE [2] null #-}

nullTL0 :: Sized f 0 a -> Bool
nullTL0 = P.const True
{-# INLINE nullTL0 #-}

nullPeanoSucc :: Sized f (S n) a -> Bool
nullPeanoSucc = P.const False
{-# INLINE nullPeanoSucc #-}

nullTLSucc :: Sized f (n + 1) a -> Bool
nullTLSucc = P.const False
{-# INLINE nullTLSucc #-}

{-# RULES
"null/0" [~2] null = nullTL0
"null/0" [~2] null = nullTLSucc
"null/0" [~1] forall (vec :: 1 <= n => Sized f n a).
  null vec =
    False
"null/Sn" [~2] null = nullPeanoSucc
  #-}

--------------------------------------------------------------------------------
--- Indexing
--------------------------------------------------------------------------------

{- | (Unsafe) indexing with @Int@s.
   If you want to check boundary statically, use '%!!' or 'sIndex'.

 Since 0.7.0.0
-}
(!!) ::
  forall f (m :: Nat) a.
  (CFoldable f, Dom f a, (1 <= m)) =>
  Sized f m a ->
  Int ->
  a
(!!) = coerce $ cindex @f @a
{-# INLINE (!!) #-}

{- | Safe indexing with 'Ordinal's.

 Since 0.7.0.0
-}
(%!!) ::
  forall f (n :: Nat) c.
  (CFoldable f, Dom f c) =>
  Sized f n c ->
  Ordinal n ->
  c
(%!!) = coerce $ (. (P.fromIntegral . ordToNatural)) . cindex @f @c
{-# INLINE (%!!) #-}
{-# SPECIALIZE (%!!) :: Sized [] (n :: Nat) a -> Ordinal n -> a #-}
{-# SPECIALIZE (%!!) :: Sized V.Vector (n :: Nat) a -> Ordinal n -> a #-}
{-# SPECIALIZE (%!!) :: UV.Unbox a => Sized UV.Vector (n :: Nat) a -> Ordinal n -> a #-}
{-# SPECIALIZE (%!!) :: SV.Storable a => Sized SV.Vector (n :: Nat) a -> Ordinal n -> a #-}
{-# SPECIALIZE (%!!) :: Sized Seq.Seq (n :: Nat) a -> Ordinal n -> a #-}

{- | Flipped version of '!!'.

 Since 0.7.0.0
-}
index ::
  forall f (m :: Nat) a.
  (CFoldable f, Dom f a, (1 <= m)) =>
  Int ->
  Sized f m a ->
  a
index = flip (!!)
{-# INLINE index #-}

{- | Flipped version of '%!!'.

 Since 0.7.0.0
-}
sIndex ::
  forall f (n :: Nat) c.
  (CFoldable f, Dom f c) =>
  Ordinal n ->
  Sized f n c ->
  c
sIndex = flip $ (%!!) @f @n @c
{-# INLINE sIndex #-}

{- | Take the first element of non-empty sequence.
   If you want to make case-analysis for general sequence,
   see  <#ViewsAndPatterns Views and Patterns> section.

 Since 0.7.0.0
-}
head ::
  forall f (n :: Nat) a.
  (CFoldable f, Dom f a, (0 < n)) =>
  Sized f n a ->
  a
head = coerce $ chead @f @a
{-# INLINE head #-}

{- | Take the last element of non-empty sequence.
   If you want to make case-analysis for general sequence,
   see  <#ViewsAndPatterns Views and Patterns> section.

 Since 0.7.0.0
-}
last ::
  forall f (n :: Nat) a.
  ((0 < n), CFoldable f, Dom f a) =>
  Sized f n a ->
  a
last = coerce $ clast @f @a
{-# INLINE last #-}

{- | Take the 'head' and 'tail' of non-empty sequence.
   If you want to make case-analysis for general sequence,
   see  <#ViewsAndPatterns Views and Patterns> section.

 Since 0.7.0.0
-}
uncons ::
  forall f (n :: Nat) a.
  (KnownNat n, CFreeMonoid f, Dom f a, (1 <= n)) =>
  Sized f n a ->
  Uncons f n a
uncons =
  withKnownNat
    (sPred $ sNat @n)
    $ uncurry (Uncons @f @(Pred n) @a) . coerce (fromJust . cuncons @f @a)

{- | 'uncons' with explicit specified length @n@

   Since 0.7.0.0
-}
uncons' ::
  forall f (n :: Nat) a proxy.
  (KnownNat n, CFreeMonoid f, Dom f a) =>
  proxy n ->
  Sized f (Succ n) a ->
  Uncons f (Succ n) a
uncons' _ =
  withKnownNat (sSucc $ sNat @n) uncons
{-# INLINE uncons' #-}

data Uncons f (n :: Nat) a where
  Uncons ::
    forall f (n :: Nat) a.
    KnownNat n =>
    a ->
    Sized f n a ->
    Uncons f (1 + n) a

{- | Take the 'init' and 'last' of non-empty sequence.
   If you want to make case-analysis for general sequence,
   see  <#ViewsAndPatterns Views and Patterns> section.

 Since 0.7.0.0
-}
unsnoc ::
  forall f (n :: Nat) a.
  (KnownNat n, CFreeMonoid f, Dom f a, (0 < n)) =>
  Sized f n a ->
  Unsnoc f n a
unsnoc =
  withKnownNat
    (sPred $ sNat @n)
    $ uncurry (Unsnoc @f @(Pred n)) . coerce (fromJust . cunsnoc @f @a)
{-# NOINLINE [1] unsnoc #-}

data Unsnoc f n a where
  Unsnoc :: forall f n a. Sized f (n :: Nat) a -> a -> Unsnoc f (Succ n) a

{- | 'unsnoc'' with explicit specified length @n@

   Since 0.7.0.0
-}
unsnoc' ::
  forall f (n :: Nat) a proxy.
  (KnownNat n, CFreeMonoid f, Dom f a) =>
  proxy n ->
  Sized f (Succ n) a ->
  Unsnoc f (Succ n) a
unsnoc' _ =
  withKnownNat (sSucc $ sNat @n) unsnoc
{-# INLINE unsnoc' #-}

--------------------------------------------------------------------------------
--- Slicing
--------------------------------------------------------------------------------

{- | Take the tail of non-empty sequence.
   If you want to make case-analysis for general sequence,
   see  <#ViewsAndPatterns Views and Patterns> section.

 Since 0.7.0.0
-}
tail ::
  forall f (n :: Nat) a.
  (CFreeMonoid f, Dom f a) =>
  Sized f (1 + n) a ->
  Sized f n a
tail = coerce $ ctail @f @a
{-# INLINE tail #-}

{- | Take the initial segment of non-empty sequence.
   If you want to make case-analysis for general sequence,
   see  <#ViewsAndPatterns Views and Patterns> section.

 Since 0.7.0.0
-}
init ::
  forall f (n :: Nat) a.
  (CFreeMonoid f, Dom f a) =>
  Sized f (n + 1) a ->
  Sized f n a
init = coerce $ cinit @f @a
{-# INLINE init #-}

{- | @take k xs@ takes first @k@ element of @xs@ where
 the length of @xs@ should be larger than @k@.

 Since 0.7.0.0
-}
take ::
  forall (n :: Nat) f (m :: Nat) a.
  (CFreeMonoid f, Dom f a, (n <= m)) =>
  SNat n ->
  Sized f m a ->
  Sized f n a
take = coerce $ ctake @f @a . P.fromIntegral . fromSNat @n
{-# INLINE take #-}

{- | @'takeAtMost' k xs@ takes first at most @k@ elements of @xs@.

 Since 0.7.0.0
-}
takeAtMost ::
  forall (n :: Nat) f m a.
  (CFreeMonoid f, Dom f a) =>
  SNat n ->
  Sized f m a ->
  Sized f (Min n m) a
takeAtMost = coerce $ ctake @f @a . P.fromIntegral . fromSNat @n
{-# INLINE takeAtMost #-}

{- | @drop k xs@ drops first @k@ element of @xs@ and returns
 the rest of sequence, where the length of @xs@ should be larger than @k@.

 Since 0.7.0.0
-}
drop ::
  forall (n :: Nat) f (m :: Nat) a.
  (CFreeMonoid f, Dom f a, (n <= m)) =>
  SNat n ->
  Sized f m a ->
  Sized f (m - n) a
drop = coerce $ cdrop @f @a . P.fromIntegral . fromSNat @n
{-# INLINE drop #-}

{- | @splitAt k xs@ split @xs@ at @k@, where
 the length of @xs@ should be less than or equal to @k@.

 Since 0.7.0.0
-}
splitAt ::
  forall (n :: Nat) f m a.
  (CFreeMonoid f, Dom f a, (n <= m)) =>
  SNat n ->
  Sized f m a ->
  (Sized f n a, Sized f (m -. n) a)
splitAt =
  coerce $ csplitAt @f @a . P.fromIntegral . fromSNat @n
{-# INLINE splitAt #-}

{- | @splitAtMost k xs@ split @xs@ at @k@.
   If @k@ exceeds the length of @xs@, then the second result value become empty.

 Since 0.7.0.0
-}
splitAtMost ::
  forall (n :: Nat) f (m :: Nat) a.
  (CFreeMonoid f, Dom f a) =>
  SNat n ->
  Sized f m a ->
  (Sized f (Min n m) a, Sized f (m -. n) a)
splitAtMost =
  coerce $ csplitAt @f @a . P.fromIntegral . fromSNat @n
{-# INLINE splitAtMost #-}

--------------------------------------------------------------------------------
-- Construction
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
--- Initialisation
--------------------------------------------------------------------------------

{- | Empty sequence.

 Since 0.7.0.0 (type changed)
-}
empty ::
  forall f a.
  (Monoid (f a), Dom f a) =>
  Sized f (0) a
empty = coerce $ mempty @(f a)
{-# INLINE empty #-}

{- | Sequence with one element.

 Since 0.7.0.0
-}
singleton :: forall f a. (CPointed f, Dom f a) => a -> Sized f (1) a
singleton = coerce $ cpure @f @a
{-# INLINE singleton #-}

{- | Consruct the 'Sized' sequence from base type, but
   the length parameter is dynamically determined and
   existentially quantified; see also 'SomeSized'.

 Since 0.7.0.0
-}
toSomeSized ::
  forall f a.
  (Dom f a, CFoldable f) =>
  f a ->
  SomeSized f a
{-# INLINE toSomeSized #-}
toSomeSized = \xs ->
  case toSomeSNat $ P.fromIntegral $ clength xs of
    SomeSNat sn -> withKnownNat sn $ SomeSized sn $ unsafeToSized sn xs

{- | Replicates the same value.

 Since 0.7.0.0
-}
replicate ::
  forall f (n :: Nat) a.
  (CFreeMonoid f, Dom f a) =>
  SNat n ->
  a ->
  Sized f n a
replicate = coerce $ creplicate @f @a . P.fromIntegral . fromSNat @n
{-# INLINE replicate #-}

{- | 'replicate' with the length inferred.

 Since 0.7.0.0
-}
replicate' ::
  forall f (n :: Nat) a.
  (KnownNat (n :: Nat), CFreeMonoid f, Dom f a) =>
  a ->
  Sized f n a
replicate' = replicate (sNat @n)
{-# INLINE replicate' #-}

{- | Construct a sequence of the given length by applying the function to each index.

 Since 0.7.0.0
-}
generate ::
  forall f (n :: Nat) (a :: Type).
  (CFreeMonoid f, Dom f a) =>
  SNat n ->
  (Ordinal n -> a) ->
  Sized f n a
generate = coerce $ \sn ->
  withKnownNat sn $
    cgenerate @f @a (P.fromIntegral $ fromSNat @n sn)
      . (. toEnum @(Ordinal n))
{-# INLINE [1] generate #-}

{- | 'generate' with length inferred.

   Since 0.8.0.0
-}
generate' ::
  forall f (n :: Nat) (a :: Type).
  (KnownNat n, CFreeMonoid f, Dom f a) =>
  (Ordinal n -> a) ->
  Sized f n a
generate' = generate sNat
{-# INLINE [1] generate' #-}

genVector ::
  forall (n :: Nat) a.
  SNat n ->
  (Ordinal n -> a) ->
  Sized V.Vector n a
genVector n f = withKnownNat n $ Sized $ V.generate (P.fromIntegral $ fromSNat n) (f . toEnum)
{-# INLINE genVector #-}

genSVector ::
  forall (n :: Nat) a.
  (SV.Storable a) =>
  SNat n ->
  (Ordinal n -> a) ->
  Sized SV.Vector n a
genSVector n f = withKnownNat n $ Sized $ SV.generate (P.fromIntegral $ fromSNat n) (f . toEnum)
{-# INLINE genSVector #-}

genSeq ::
  forall (n :: Nat) a.
  SNat n ->
  (Ordinal n -> a) ->
  Sized Seq.Seq n a
genSeq n f = withKnownNat n $ Sized $ Seq.fromFunction (P.fromIntegral $ fromSNat n) (f . toEnum)
{-# INLINE genSeq #-}

{-# RULES
"generate/Vector" [~1] generate = genVector
"generate/SVector" [~1] forall
  (n :: SNat (n :: Nat))
  (f :: SV.Storable a => Ordinal n -> a).
  generate n f =
    genSVector n f
"generate/UVector" [~1] forall
  (n :: SNat (n :: Nat))
  (f :: UV.Unbox a => Ordinal n -> a).
  generate n f =
    withKnownNat n $ Sized (UV.generate (P.fromIntegral $ fromSNat n) (f . toEnum))
"generate/Seq" [~1] generate = genSeq
  #-}

--------------------------------------------------------------------------------
--- Concatenation
--------------------------------------------------------------------------------

{- | Append an element to the head of sequence.

 Since 0.8.0.0
-}
cons ::
  forall f (n :: Nat) a.
  (CFreeMonoid f, Dom f a) =>
  a ->
  Sized f n a ->
  Sized f (1 + n) a
cons = coerce $ ccons @f @a
{-# INLINE cons #-}

{- | Infix version of 'cons'.

 Since 0.8.0.0
-}
(<|) ::
  forall f (n :: Nat) a.
  (CFreeMonoid f, Dom f a) =>
  a ->
  Sized f n a ->
  Sized f (1 + n) a
(<|) = cons
{-# INLINE (<|) #-}

infixr 5 <|

{- | Append an element to the tail of sequence.

 Since 0.7.0.0
-}
snoc ::
  forall f (n :: Nat) a.
  (CFreeMonoid f, Dom f a) =>
  Sized f n a ->
  a ->
  Sized f (n + 1) a
snoc (Sized xs) a = Sized $ csnoc xs a
{-# INLINE snoc #-}

{- | Infix version of 'snoc'.

 Since 0.7.0.0
-}
(|>) ::
  forall f (n :: Nat) a.
  (CFreeMonoid f, Dom f a) =>
  Sized f n a ->
  a ->
  Sized f (n + 1) a
(|>) = snoc
{-# INLINE (|>) #-}

infixl 5 |>

{- | Append two lists.

 Since 0.7.0.0
-}
append ::
  forall f (n :: Nat) (m :: Nat) a.
  (CFreeMonoid f, Dom f a) =>
  Sized f n a ->
  Sized f m a ->
  Sized f (n + m) a
append = coerce $ mappend @(f a)
{-# INLINE append #-}

{- | Infix version of 'append'.

 Since 0.7.0.0
-}
(++) ::
  forall f (n :: Nat) (m :: Nat) a.
  (CFreeMonoid f, Dom f a) =>
  Sized f n a ->
  Sized f m a ->
  Sized f (n + m) a
(++) = append

infixr 5 ++

{- | Concatenates multiple sequences into one.

 Since 0.7.0.0
-}
concat ::
  forall f' (m :: Nat) f (n :: Nat) a.
  ( CFreeMonoid f
  , CFunctor f'
  , CFoldable f'
  , Dom f a
  , Dom f' (f a)
  , Dom f' (Sized f n a)
  ) =>
  Sized f' m (Sized f n a) ->
  Sized f (m * n) a
concat = coerce $ cfoldMap @f' @(Sized f n a) runSized
{-# INLINE [2] concat #-}

--------------------------------------------------------------------------------
--- Zips
--------------------------------------------------------------------------------

{- | Zipping two sequences. Length is adjusted to shorter one.

 Since 0.7.0.0
-}
zip ::
  forall f (n :: Nat) a (m :: Nat) b.
  (Dom f a, CZip f, Dom f b, Dom f (a, b)) =>
  Sized f n a ->
  Sized f m b ->
  Sized f (Min n m) (a, b)
zip = coerce $ czip @f @a @b

{- | 'zip' for the sequences of the same length.

 Since 0.7.0.0
-}
zipSame ::
  forall f (n :: Nat) a b.
  (Dom f a, CZip f, Dom f b, Dom f (a, b)) =>
  Sized f n a ->
  Sized f n b ->
  Sized f n (a, b)
zipSame = coerce $ czip @f @a @b
{-# INLINE [1] zipSame #-}

{- | Zipping two sequences with funtion. Length is adjusted to shorter one.

 Since 0.7.0.0
-}
zipWith ::
  forall f (n :: Nat) a (m :: Nat) b c.
  (Dom f a, CZip f, Dom f b, CFreeMonoid f, Dom f c) =>
  (a -> b -> c) ->
  Sized f n a ->
  Sized f m b ->
  Sized f (Min n m) c
zipWith = coerce $ czipWith @f @a @b @c
{-# INLINE [1] zipWith #-}

{- | 'zipWith' for the sequences of the same length.

 Since 0.7.0.0
-}
zipWithSame ::
  forall f (n :: Nat) a b c.
  (Dom f a, CZip f, Dom f b, CFreeMonoid f, Dom f c) =>
  (a -> b -> c) ->
  Sized f n a ->
  Sized f n b ->
  Sized f n c
zipWithSame = coerce $ czipWith @f @a @b @c
{-# INLINE [1] zipWithSame #-}

{- | Unzipping the sequence of tuples.

 Since 0.7.0.0
-}
unzip ::
  forall f (n :: Nat) a b.
  (CUnzip f, Dom f a, Dom f b, Dom f (a, b)) =>
  Sized f n (a, b) ->
  (Sized f n a, Sized f n b)
unzip = coerce $ cunzip @f @a @b
{-# INLINE unzip #-}

{- | Unzipping the sequence of tuples.

 Since 0.7.0.0
-}
unzipWith ::
  forall f (n :: Nat) a b c.
  (CUnzip f, Dom f a, Dom f b, Dom f c) =>
  (a -> (b, c)) ->
  Sized f n a ->
  (Sized f n b, Sized f n c)
unzipWith = coerce $ cunzipWith @f @a @b @c
{-# INLINE unzipWith #-}

--------------------------------------------------------------------------------
-- Transformation
--------------------------------------------------------------------------------

{- | Map function.

 Since 0.7.0.0
-}
map ::
  forall f (n :: Nat) a b.
  (CFreeMonoid f, Dom f a, Dom f b) =>
  (a -> b) ->
  Sized f n a ->
  Sized f n b
map f = Sized . cmap f . runSized
{-# INLINE map #-}

{- | Reverse function.

 Since 0.7.0.0
-}
reverse ::
  forall f (n :: Nat) a.
  (Dom f a, CFreeMonoid f) =>
  Sized f n a ->
  Sized f n a
reverse = coerce $ creverse @f @a
{-# INLINE reverse #-}

{- | Intersperces.

 Since 0.7.0.0
-}
intersperse ::
  forall f (n :: Nat) a.
  (CFreeMonoid f, Dom f a) =>
  a ->
  Sized f n a ->
  Sized f ((2 * n) -. 1) a
intersperse = coerce $ cintersperse @f @a
{-# INLINE intersperse #-}

{- | Remove all duplicates.

 Since 0.7.0.0
-}
nub ::
  forall f (n :: Nat) a.
  (Dom f a, Eq a, CFreeMonoid f) =>
  Sized f n a ->
  SomeSized f a
nub = toSomeSized . coerce (cnub @f @a)

{- | Sorting sequence by ascending order.

 Since 0.7.0.0
-}
sort ::
  forall f (n :: Nat) a.
  (CFreeMonoid f, Dom f a, Ord a) =>
  Sized f n a ->
  Sized f n a
sort = coerce $ csort @f @a

{- | Generalized version of 'sort'.

 Since 0.7.0.0
-}
sortBy ::
  forall f (n :: Nat) a.
  (CFreeMonoid f, Dom f a) =>
  (a -> a -> Ordering) ->
  Sized f n a ->
  Sized f n a
sortBy = coerce $ csortBy @f @a

{- | Insert new element into the presorted sequence.

 Since 0.7.0.0
-}
insert ::
  forall f (n :: Nat) a.
  (CFreeMonoid f, Dom f a, Ord a) =>
  a ->
  Sized f n a ->
  Sized f (Succ n) a
insert = coerce $ cinsert @f @a

{- | Generalized version of 'insert'.

 Since 0.7.0.0
-}
insertBy ::
  forall f (n :: Nat) a.
  (CFreeMonoid f, Dom f a) =>
  (a -> a -> Ordering) ->
  a ->
  Sized f n a ->
  Sized f (Succ n) a
insertBy = coerce $ cinsertBy @f @a

--------------------------------------------------------------------------------
-- Conversion
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
--- List
--------------------------------------------------------------------------------

{- | Convert to list.

 Since 0.7.0.0
-}
toList ::
  forall f (n :: Nat) a.
  (CFoldable f, Dom f a) =>
  Sized f n a ->
  [a]
toList = coerce $ ctoList @f @a
{-# INLINE [2] toList #-}

{-# RULES
"toList/List"
  Data.Sized.toList =
    runSized
  #-}

{- | If the given list is shorter than @n@, then returns @Nothing@
   Otherwise returns @Sized f n a@ consisting of initial @n@ element
   of given list.

   Since 0.7.0.0 (type changed)
-}
fromList ::
  forall f (n :: Nat) a.
  (CFreeMonoid f, Dom f a) =>
  SNat n ->
  [a] ->
  Maybe (Sized f n a)
fromList Zero _ = Just $ Sized (mempty :: f a)
fromList sn xs =
  let len = P.fromIntegral $ fromSNat sn
   in if P.length xs < len
        then Nothing
        else Just $ Sized $ ctake len $ cfromList xs
{-# INLINEABLE [2] fromList #-}

{- | 'fromList' with the result length inferred.

 Since 0.7.0.0
-}
fromList' ::
  forall f (n :: Nat) a.
  (Dom f a, CFreeMonoid f, KnownNat n) =>
  [a] ->
  Maybe (Sized f n a)
fromList' = fromList sNat
{-# INLINE fromList' #-}

{- | Unsafe version of 'fromList'. If the length of the given list does not
   equal to @n@, then something unusual happens.

 Since 0.7.0.0
-}
unsafeFromList ::
  forall f (n :: Nat) a.
  (CFreeMonoid f, Dom f a) =>
  SNat n ->
  [a] ->
  Sized f n a
unsafeFromList = const $ coerce $ cfromList @f @a
{-# INLINE [1] unsafeFromList #-}

{- | 'unsafeFromList' with the result length inferred.

 Since 0.7.0.0
-}
unsafeFromList' ::
  forall f (n :: Nat) a.
  (KnownNat n, CFreeMonoid f, Dom f a) =>
  [a] ->
  Sized f n a
unsafeFromList' = unsafeFromList sNat
{-# INLINE [1] unsafeFromList' #-}

{-# RULES
"unsafeFromList'/List" [~1]
  unsafeFromList' =
    Sized
"unsafeFromList'/Vector" [~1]
  unsafeFromList' =
    Sized . V.fromList
"unsafeFromList'/Seq" [~1]
  unsafeFromList' =
    Sized . Seq.fromList
"unsafeFromList'/SVector" [~1] forall (xs :: SV.Storable a => [a]).
  unsafeFromList' xs =
    Sized (SV.fromList xs)
"unsafeFromList'/UVector" [~1] forall (xs :: UV.Unbox a => [a]).
  unsafeFromList' xs =
    Sized (UV.fromList xs)
  #-}

{- | Construct a @Sized f n a@ by padding default value if the given list is short.

   Since 0.5.0.0 (type changed)
-}
fromListWithDefault ::
  forall f (n :: Nat) a.
  (Dom f a, CFreeMonoid f) =>
  SNat n ->
  a ->
  [a] ->
  Sized f n a
fromListWithDefault sn def xs =
  let len = P.fromIntegral $ fromSNat sn
   in Sized $
        cfromList (ctake len xs)
          <> creplicate (len - clength xs) def
{-# INLINEABLE fromListWithDefault #-}

{- | 'fromListWithDefault' with the result length inferred.

 Since 0.7.0.0
-}
fromListWithDefault' ::
  forall f (n :: Nat) a.
  (KnownNat n, CFreeMonoid f, Dom f a) =>
  a ->
  [a] ->
  Sized f n a
fromListWithDefault' = fromListWithDefault sNat
{-# INLINE fromListWithDefault' #-}

--------------------------------------------------------------------------------
--- Base containes
--------------------------------------------------------------------------------

{- | Forget the length and obtain the wrapped base container.

 Since 0.7.0.0
-}
unsized :: forall f (n :: Nat) a. Sized f n a -> f a
unsized = runSized
{-# INLINE unsized #-}

{- | If the length of the input is shorter than @n@, then returns @Nothing@.
   Otherwise returns @Sized f n a@ consisting of initial @n@ element
   of the input.

 Since 0.7.0.0
-}
toSized ::
  forall f (n :: Nat) a.
  (CFreeMonoid f, Dom f a) =>
  SNat (n :: Nat) ->
  f a ->
  Maybe (Sized f n a)
toSized sn xs =
  let len = P.fromIntegral $ fromSNat sn
   in if clength xs < len
        then Nothing
        else Just $ unsafeToSized sn $ ctake len xs
{-# INLINEABLE [2] toSized #-}

{- | 'toSized' with the result length inferred.

 Since 0.7.0.0
-}
toSized' ::
  forall f (n :: Nat) a.
  (Dom f a, CFreeMonoid f, KnownNat n) =>
  f a ->
  Maybe (Sized f n a)
toSized' = toSized sNat
{-# INLINE toSized' #-}

{- | Unsafe version of 'toSized'. If the length of the given list does not
   equal to @n@, then something unusual happens.

 Since 0.7.0.0
-}
unsafeToSized :: forall f (n :: Nat) a. SNat n -> f a -> Sized f n a
unsafeToSized _ = Sized
{-# INLINE [2] unsafeToSized #-}

{- | 'unsafeToSized' with the result length inferred.

 Since 0.7.0.0
-}
unsafeToSized' ::
  forall f (n :: Nat) a.
  (KnownNat n, Dom f a) =>
  f a ->
  Sized f n a
unsafeToSized' = unsafeToSized sNat
{-# INLINE unsafeToSized' #-}

{- | Construct a @Sized f n a@ by padding default value if the given list is short.

 Since 0.7.0.0
-}
toSizedWithDefault ::
  forall f (n :: Nat) a.
  (CFreeMonoid f, Dom f a) =>
  SNat (n :: Nat) ->
  a ->
  f a ->
  Sized f n a
toSizedWithDefault sn def xs =
  let len = P.fromIntegral $ fromSNat sn
   in Sized $ ctake len xs <> creplicate (len - clength xs) def
{-# INLINEABLE toSizedWithDefault #-}

{- | 'toSizedWithDefault' with the result length inferred.

 Since 0.7.0.0
-}
toSizedWithDefault' ::
  forall f (n :: Nat) a.
  (KnownNat n, CFreeMonoid f, Dom f a) =>
  a ->
  f a ->
  Sized f n a
toSizedWithDefault' = toSizedWithDefault sNat
{-# INLINE toSizedWithDefault' #-}

--------------------------------------------------------------------------------
-- Querying
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
--- Partitioning
--------------------------------------------------------------------------------

{- | The type @Partitioned f n a@ represents partitioned sequence of length @n@.
   Value @Partitioned lenL ls lenR rs@ stands for:

   * Entire sequence is divided into @ls@ and @rs@, and their length
     are @lenL@ and @lenR@ resp.

   * @lenL + lenR = n@

 Since 0.7.0.0
-}
data Partitioned f n a where
  Partitioned ::
    (Dom f a) =>
    SNat n ->
    Sized f n a ->
    SNat m ->
    Sized f m a ->
    Partitioned f (n + m) a

{- | Take the initial segment as long as elements satisfys the predicate.

 Since 0.7.0.0
-}
takeWhile ::
  forall f (n :: Nat) a.
  (Dom f a, CFreeMonoid f) =>
  (a -> Bool) ->
  Sized f n a ->
  SomeSized f a
takeWhile = (toSomeSized .) . coerce (ctakeWhile @f @a)
{-# INLINE takeWhile #-}

{- | Drop the initial segment as long as elements satisfys the predicate.

 Since 0.7.0.0
-}
dropWhile ::
  forall f (n :: Nat) a.
  (CFreeMonoid f, Dom f a) =>
  (a -> Bool) ->
  Sized f n a ->
  SomeSized f a
dropWhile = (toSomeSized .) . coerce (cdropWhile @f @a)
{-# INLINE dropWhile #-}

{- | Split the sequence into the longest prefix
   of elements that satisfy the predicate
   and the rest.

 Since 0.7.0.0
-}
span ::
  forall f (n :: Nat) a.
  (CFreeMonoid f, Dom f a) =>
  (a -> Bool) ->
  Sized f n a ->
  Partitioned f n a
span = (unsafePartitioned @n .) . coerce (cspan @f @a)
{-# INLINE span #-}

{- | Split the sequence into the longest prefix
   of elements that do not satisfy the
   predicate and the rest.

 Since 0.7.0.0
-}
break ::
  forall f (n :: Nat) a.
  (CFreeMonoid f, Dom f a) =>
  (a -> Bool) ->
  Sized f n a ->
  Partitioned f n a
break = (unsafePartitioned @n .) . coerce (cbreak @f @a)
{-# INLINE break #-}

{- | Split the sequence in two parts, the first one containing those elements that satisfy the predicate and the second one those that don't.

 Since 0.7.0.0
-}
partition ::
  forall f (n :: Nat) a.
  (CFreeMonoid f, Dom f a) =>
  (a -> Bool) ->
  Sized f n a ->
  Partitioned f n a
partition = (unsafePartitioned @n .) . coerce (cpartition @f @a)
{-# INLINE partition #-}

unsafePartitioned ::
  forall (n :: Nat) f a.
  (CFreeMonoid f, Dom f a) =>
  (f a, f a) ->
  Partitioned f n a
unsafePartitioned (l, r) =
  case (toSomeSized l, toSomeSized r) of
    ( SomeSized (lenL :: SNat nl) ls
      , SomeSized (lenR :: SNat nr) rs
      ) ->
        gcastWith
          ( unsafeCoerce $ Refl @() ::
              n :~: nl + nr
          )
          $ Partitioned lenL ls lenR rs

--------------------------------------------------------------------------------
--- Searching
--------------------------------------------------------------------------------

{- | Membership test; see also 'notElem'.

 Since 0.7.0.0
-}
elem ::
  forall f (n :: Nat) a.
  (CFoldable f, Dom f a, Eq a) =>
  a ->
  Sized f n a ->
  Bool
elem = coerce $ celem @f @a
{-# INLINE elem #-}

{- | Negation of 'elem'.

 Since 0.7.0.0
-}
notElem ::
  forall f (n :: Nat) a.
  (CFoldable f, Dom f a, Eq a) =>
  a ->
  Sized f n a ->
  Bool
notElem = coerce $ cnotElem @f @a
{-# INLINE notElem #-}

{- | Find the element satisfying the predicate.

 Since 0.7.0.0
-}
find ::
  forall f (n :: Nat) a.
  (CFoldable f, Dom f a) =>
  (a -> Bool) ->
  Sized f n a ->
  Maybe a
find = coerce $ cfind @f @a
{-# INLINE [1] find #-}

{-# RULES
"find/List" [~1] forall p.
  find p =
    L.find @[] p . runSized
"find/Vector" [~1] forall p.
  find p =
    V.find p . runSized
"find/Storable Vector" [~1] forall (p :: SV.Storable a => a -> Bool).
  find p =
    SV.find p . runSized
"find/Unboxed Vector" [~1] forall (p :: UV.Unbox a => a -> Bool).
  find p =
    UV.find p . runSized
  #-}

{- | @'findIndex' p xs@ find the element satisfying @p@ and returns its index if exists.

 Since 0.7.0.0
-}
findIndex ::
  forall f (n :: Nat) a.
  (CFoldable f, Dom f a) =>
  (a -> Bool) ->
  Sized f n a ->
  Maybe Int
findIndex = coerce $ cfindIndex @f @a
{-# INLINE findIndex #-}

{- | 'Ordinal' version of 'findIndex'.

 Since 0.7.0.0
-}
sFindIndex ::
  forall f (n :: Nat) a.
  (KnownNat (n :: Nat), CFoldable f, Dom f a) =>
  (a -> Bool) ->
  Sized f n a ->
  Maybe (Ordinal n)
sFindIndex = (fmap toEnum .) . coerce (cfindIndex @f @a)
{-# INLINE sFindIndex #-}

{- | @'findIndices' p xs@ find all elements satisfying @p@ and returns their indices.

 Since 0.7.0.0
-}
findIndices ::
  forall f (n :: Nat) a.
  (CFoldable f, Dom f a) =>
  (a -> Bool) ->
  Sized f n a ->
  [Int]
findIndices = coerce $ cfindIndices @f @a
{-# INLINE findIndices #-}
{-# SPECIALIZE findIndices :: (a -> Bool) -> Sized [] n a -> [Int] #-}

{- | 'Ordinal' version of 'findIndices'.

 Since 0.7.0.0
-}
sFindIndices ::
  forall f (n :: Nat) a.
  (CFoldable f, Dom f a, KnownNat (n :: Nat)) =>
  (a -> Bool) ->
  Sized f n a ->
  [Ordinal n]
sFindIndices p = P.fmap (toEnum . P.fromIntegral) . findIndices p
{-# INLINE sFindIndices #-}

{-# RULES
"Foldable.sum/Vector"
  F.sum =
    V.sum . runSized
  #-}

{- | Returns the index of the given element in the list, if exists.

 Since 0.7.0.0
-}
elemIndex ::
  forall f (n :: Nat) a.
  (CFoldable f, Eq a, Dom f a) =>
  a ->
  Sized f n a ->
  Maybe Int
elemIndex = coerce $ celemIndex @f @a
{-# INLINE elemIndex #-}

{- | Ordinal version of 'elemIndex'.
   Since 0.7.0.0, we no longer do boundary check inside the definition.

   Since 0.7.0.0
-}
sElemIndex
  , sUnsafeElemIndex ::
    forall f (n :: Nat) a.
    (KnownNat n, CFoldable f, Dom f a, Eq a) =>
    a ->
    Sized f n a ->
    Maybe (Ordinal n)
sElemIndex = (fmap toEnum .) . coerce (celemIndex @f @a)
{-# INLINE sElemIndex #-}

-- | Since 0.5.0.0 (type changed)
sUnsafeElemIndex = sElemIndex
{-# DEPRECATED sUnsafeElemIndex "No difference with sElemIndex; use sElemIndex instead." #-}

{- | Returns all indices of the given element in the list.

 Since 0.7.0.0
-}
elemIndices ::
  forall f (n :: Nat) a.
  (CFoldable f, Dom f a, Eq a) =>
  a ->
  Sized f n a ->
  [Int]
elemIndices = coerce $ celemIndices @f @a
{-# INLINE elemIndices #-}

{- | Ordinal version of 'elemIndices'

 Since 0.7.0.0
-}
sElemIndices ::
  forall f (n :: Nat) a.
  (CFoldable f, KnownNat (n :: Nat), Dom f a, Eq a) =>
  a ->
  Sized f n a ->
  [Ordinal n]
sElemIndices = (fmap toEnum .) . elemIndices
{-# INLINE sElemIndices #-}

--------------------------------------------------------------------------------
-- Views and Patterns
--------------------------------------------------------------------------------

{- $ViewsAndPatterns #ViewsAndPatterns#

   With GHC's @ViewPatterns@ and @PatternSynonym@ extensions,
   we can pattern-match on arbitrary @Sized f n a@ if @f@ is list-like functor.
   Curretnly, there are two direction view and patterns: Cons and Snoc.
   Assuming underlying sequence type @f@ has O(1) implementation for 'cnull', 'chead'
   (resp. 'clast') and 'ctail' (resp. 'cinit'), We can view and pattern-match on
   cons (resp. snoc) of @Sized f n a@ in O(1).
-}

{- $views #views#

   With @ViewPatterns@ extension, we can pattern-match on 'Sized' value as follows:

@
slen :: ('KnownNat' n, 'Dom f a' f) => 'Sized' f n a -> 'SNat' n
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
slen :: ('KnownNat' n, 'Dom f a' f) => 'Sized' f n a -> 'SNat' n
slen ('viewSnoc' -> 'NilSV')     = 'SZ'
slen ('viewSnoc' -> as '-::' _) = 'SS' (slen as)
@
-}

{- | View of the left end of sequence (cons-side).

 Since 0.7.0.0
-}
data ConsView f n a where
  NilCV :: ConsView f (0) a
  (:-) ::
    (KnownNat n, KnownNat (1 + n)) =>
    a ->
    Sized f n a ->
    ConsView f (1 + n) a

infixr 5 :-

{- | Case analysis for the cons-side of sequence.

 Since 0.5.0.0 (type changed)
-}
viewCons ::
  forall f (n :: Nat) a.
  (KnownNat n, CFreeMonoid f, Dom f a) =>
  Sized f n a ->
  ConsView f n a
viewCons sz = case zeroOrSucc $ sNat @n of
  IsZero -> NilCV
  IsSucc n' ->
    withKnownNat n' $
      withKnownNat (sOne %+ n') $
        case uncons' n' sz of
          Uncons a xs -> a :- xs

{- | View of the left end of sequence (snoc-side).

 Since 0.7.0.0
-}
data SnocView f n a where
  NilSV :: SnocView f (0) a
  (:-::) :: KnownNat (n :: Nat) => Sized f n a -> a -> SnocView f (n + 1) a

infixl 5 :-::

{- | Case analysis for the snoc-side of sequence.

 Since 0.5.0.0 (type changed)
-}
viewSnoc ::
  forall f (n :: Nat) a.
  (KnownNat n, CFreeMonoid f, Dom f a) =>
  Sized f n a ->
  SnocView f n a
viewSnoc sz = case zeroOrSucc (sNat @n) of
  IsZero -> NilSV
  IsSucc (n' :: SNat n') ->
    withKnownNat n' $
      case unsnoc' n' sz of
        Unsnoc (xs :: Sized f m a) a ->
          gcastWith
            (unsafeCoerce (Refl @()) :: n' :~: m)
            $ xs :-:: a

{- $patterns #patterns#

   So we can pattern match on both end of sequence via views, but
   it is rather clumsy to nest it. For example:

@
nextToHead :: ('Dom f a' f, 'KnownNat' n) => 'Sized' f ('S' ('S' n)) a -> a
nextToHead ('viewCons' -> _ ':-' ('viewCons' -> a ':-' _)) = a
@

   In such a case, with @PatternSynonyms@ extension we can write as follows:

@
nextToHead :: ('Dom f a' f, 'KnownNat' n) => 'Sized' f ('S' ('S' n)) a -> a
nextToHead (_ ':<' a ':<' _) = a
@

   Of course, we can also rewrite above @slen@ example usNat @PatternSynonyms@:

@
slen :: ('KnownNat' n, 'Dom f a' f) => 'Sized' f n a -> 'SNat' n
slen 'Nil'      = 'SZ'
slen (_ ':<' as) = 'SS' (slen as)
@

   So, we can use @':<'@ and @'Nil'@ (resp. @':>'@ and @'Nil'@) to
   pattern-match directly on cons-side (resp. snoc-side) as we usually do for lists.
   @'Nil'@, @':<'@, and @':>'@ are neither functions nor data constructors,
   but pattern synonyms so we cannot use them in expression contexts.
   For more detail on pattern synonyms, see
   <http://www.haskell.org/ghc/docs/latest/html/users_guide/syntax-extns.html#pattern-synonyms GHC Users Guide>
   and
   <https://ghc.haskell.org/trac/ghc/wiki/PatternSynonyms HaskellWiki>.
-}

infixr 5 :<

-- | Pattern synonym for cons-side uncons.
pattern (:<) ::
  forall (f :: Type -> Type) a (n :: Nat).
  (Dom f a, KnownNat n, CFreeMonoid f) =>
  forall (n1 :: Nat).
  (n ~ (1 + n1), KnownNat n1) =>
  a ->
  Sized f n1 a ->
  Sized f n a
pattern a :< as <-
  (viewCons -> a :- as)
  where
    a :< as = a <| as

chkNil ::
  forall f (n :: Nat) a.
  (KnownNat n) =>
  Sized f n a ->
  ZeroOrSucc n
chkNil = const $ zeroOrSucc $ sNat @n

-- | Pattern synonym for a nil sequence.
pattern Nil ::
  forall f (n :: Nat) a.
  (KnownNat n, CFreeMonoid f, Dom f a) =>
  (n ~ 0) =>
  Sized f n a
pattern Nil <-
  (chkNil -> IsZero)
  where
    Nil = empty

infixl 5 :>

-- | Pattern synonym for snoc-side unsnoc.
pattern (:>) ::
  forall (f :: Type -> Type) a (n :: Nat).
  (Dom f a, KnownNat n, CFreeMonoid f) =>
  forall (n1 :: Nat).
  (n ~ (n1 + 1), KnownNat n1) =>
  Sized f n1 a ->
  a ->
  Sized f n a
pattern a :> b <-
  (viewSnoc -> a :-:: b)
  where
    a :> b = a |> b

{-# COMPLETE (:<), Nil #-}

{-# COMPLETE (:>), Nil #-}

class Dom f a => DomC f a

instance Dom f a => DomC f a

-- | Applicative instance, generalizing @'Data.Monoid.ZipList'@.
instance
  ( Functor f
  , CFreeMonoid f
  , CZip f
  , KnownNat n
  , forall a. DomC f a
  ) =>
  P.Applicative (Sized f (n :: Nat))
  where
  {-# SPECIALIZE instance KnownNat n => P.Applicative (Sized [] (n :: Nat)) #-}
  {-# SPECIALIZE instance KnownNat n => P.Applicative (Sized Seq.Seq (n :: Nat)) #-}
  {-# SPECIALIZE instance KnownNat n => P.Applicative (Sized V.Vector (n :: Nat)) #-}

  pure (x :: a) =
    withDict (Dict @(DomC f a)) $
      replicate' x
  {-# INLINE pure #-}

  (fs :: Sized f n (a -> b)) <*> (xs :: Sized f n a) =
    withDict (Dict @(DomC f b)) $
      withDict (Dict @(DomC f a)) $
        withDict (Dict @(DomC f (a -> b))) $
          zipWithSame ($) fs xs
  {-# INLINE [1] (<*>) #-}

{-# RULES
"<*>/List" [~1] forall fs xs.
  Sized fs <*> Sized xs =
    Sized (getZipList (ZipList fs <*> ZipList xs))
"<*>/Seq" [~1] forall fs xs.
  Sized fs <*> Sized xs =
    Sized (Seq.zipWith ($) fs xs)
"<*>/Vector" [~1] forall fs xs.
  Sized fs <*> Sized xs =
    Sized (V.zipWith ($) fs xs)
  #-}

instance
  (CFreeMonoid f, KnownNat (n :: Nat)) =>
  CPointed (Sized f n)
  where
  cpure = replicate'

instance
  (CFreeMonoid f, CZip f) =>
  CApplicative (Sized f n)
  where
  pair = zipSame
  (<.>) = zipWithSame ($)
  (<.) = P.const
  (.>) = P.flip P.const

{- | __N.B.__ Since @calign@ is just zipping for fixed @n@,
   we require more strong 'CZip' constraint here.
-}
instance (CZip f, CFreeMonoid f) => CSemialign (Sized f n) where
  calignWith =
    coerce (\f -> czipWith @f @a @b @c ((f .) . These)) ::
      forall a b c.
      (Dom f a, Dom f b, Dom f c) =>
      (These a b -> c) ->
      Sized f n a ->
      Sized f n b ->
      Sized f n c
  {-# INLINE [1] calignWith #-}
  calign =
    coerce $ czipWith @f @a @b These ::
      forall a b.
      (Dom f a, Dom f b, Dom f (These a b)) =>
      Sized f n a ->
      Sized f n b ->
      Sized f n (These a b)
  {-# INLINE [1] calign #-}

instance (CZip f, CFreeMonoid f) => CZip (Sized f n) where
  czipWith =
    coerce $ czipWith @f @a @b @c ::
      forall a b c.
      (Dom f a, Dom f b, Dom f c) =>
      (a -> b -> c) ->
      Sized f n a ->
      Sized f n b ->
      Sized f n c
  {-# INLINE [1] czipWith #-}
  czip =
    coerce $ czip @f @a @b ::
      forall a b.
      (Dom f a, Dom f b, Dom f (a, b)) =>
      Sized f n a ->
      Sized f n b ->
      Sized f n (a, b)
  {-# INLINE [1] czip #-}

instance
  (KnownNat (n :: Nat), CZip f, CFreeMonoid f) =>
  CRepeat (Sized f n)
  where
  crepeat = replicate'
  {-# INLINE [1] crepeat #-}

instance CTraversable f => CTraversable (Sized f n) where
  ctraverse = \f -> fmap coerce . ctraverse f . runSized
  {-# INLINE ctraverse #-}
