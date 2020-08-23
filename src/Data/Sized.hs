{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE AllowAmbiguousTypes, CPP, ConstraintKinds, DataKinds          #-}
{-# LANGUAGE DeriveDataTypeable, DeriveFoldable, DeriveFunctor             #-}
{-# LANGUAGE DeriveTraversable, ExplicitNamespaces, FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances, GADTs, GeneralizedNewtypeDeriving          #-}
{-# LANGUAGE KindSignatures, LambdaCase, LiberalTypeSynonyms               #-}
{-# LANGUAGE MultiParamTypeClasses, NoMonomorphismRestriction              #-}
{-# LANGUAGE PatternSynonyms, PolyKinds, QuantifiedConstraints, ScopedTypeVariables, RankNTypes   #-}
{-# LANGUAGE StandaloneDeriving, TypeApplications, TypeFamilies            #-}
{-# LANGUAGE TypeInType, TypeOperators, UndecidableInstances, ViewPatterns #-}
#if __GLASGOW_HASKELL__ && __GLASGOW_HASKELL__ >= 806
{-# LANGUAGE NoStarIsType #-}
#endif

{-# OPTIONS_GHC -fno-warn-type-defaults -fno-warn-orphans #-}
{-# OPTIONS_GHC -fenable-rewrite-rules #-}
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
    Sized(), SomeSized(..),
    DomC(),
    -- * Accessors
    -- ** Length information
    length, sLength, null,
    -- ** Indexing
    (!!), (%!!), index, sIndex, head, last,
    uncons, uncons', unsnoc, unsnoc',
    -- ** Slicing
    tail, init, take, takeAtMost, drop, splitAt, splitAtMost,
    -- * Construction
    -- ** Initialisation
    empty, singleton, toSomeSized, replicate, replicate', generate,
    -- ** Concatenation
    cons, (<|), snoc, (|>), append, (++), concat,
    -- ** Zips
    zip, zipSame, zipWith, zipWithSame, unzip,
    -- * Transformation
    map, fmap, reverse, intersperse, nub, sort, sortBy, insert, insertBy,
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
    elem, notElem, find, findF, findIndex, findIndexIF,
    sFindIndex, sFindIndexIF,
    findIndices, findIndicesIF, sFindIndices, sFindIndicesIF,
    elemIndex, sElemIndex, sUnsafeElemIndex, elemIndices, sElemIndices,
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

import           Control.Applicative          ((<$>), (<*>), ZipList(..))
import           Control.Lens.Indexed         (FoldableWithIndex (..), ifind)
import           Data.Foldable                (Foldable)
import qualified Data.Foldable                as F
import           Data.Kind                    (Type)
import Data.Monoid
import qualified Data.List                    as L
import           Data.Monoid                  (Endo (..), First (..))
import qualified Data.Sequence                as Seq
import           Data.Singletons.Prelude.Bool 
import Data.Constraint
import           Data.Singletons.Prelude      (SomeSing(..), PNum (..), POrd (..))
import           Data.Singletons.Prelude      (Sing (..), SingI (..))
import           Data.Singletons.Prelude      (withSing, withSingI)
import Control.Subcategory
import           Data.Singletons.Prelude.Enum (PEnum (..))
import qualified Data.Type.Natural            as Peano
import           Data.Type.Natural.Class
import           Data.Type.Ordinal            (HasOrdinal, Ordinal (..), enumOrdinal)
import           Data.Type.Ordinal            (ordToNatural, unsafeNaturalToOrd)
import           Data.Typeable                (Typeable)
import qualified Data.Vector                  as V
import qualified Data.Vector.Storable         as SV
import qualified Data.Vector.Unboxed          as UV
import qualified GHC.TypeLits                 as TL
import           Prelude                      (Bool (..), Enum (..), Eq (..))
import           Prelude                      (Functor, Int, Maybe (..))
import           Prelude                      (Num (..), Ord (..), Ordering)
import           Prelude                      (Show (..), flip, fst, ($), (.))
import qualified Prelude                      as P
import           Unsafe.Coerce                (unsafeCoerce)
import Data.Coerce (coerce)
import Data.Maybe (fromJust)
import Data.These (These(..))

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
-- Since 0.7.0.0
data SomeSized f nat a where
  SomeSized :: Sing n
            -> Sized f (n :: nat) a
            -> SomeSized f nat a

deriving instance Typeable SomeSized

instance Show (f a) => Show (SomeSized f nat a) where
  showsPrec d (SomeSized _ s) = P.showParen (d > 9) $
    P.showString "SomeSized _ " . showsPrec 10 s
instance Eq (f a) => Eq (SomeSized f nat a) where
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
-- Since 0.7.0.0
length :: forall f n a. (CFoldable f, Dom f a) => Sized f n a -> Int
length = coerce $ clength @f @a
{-# INLINE CONLIKE [1] length #-}

lengthTLZero :: Sized f 0 a -> Int
lengthTLZero = P.const 0
{-# INLINE lengthTLZero #-}

lengthPeanoZero :: Sized f 'Peano.Z a -> Int
lengthPeanoZero = P.const 0
{-# INLINE lengthPeanoZero #-}

{-# RULES
"length/0" [~1] length = lengthTLZero
"length/Z" [~1] length = lengthPeanoZero
  #-}

-- | @Sing@ version of 'length'.
--
-- Since 0.5.0.0 (type changed)
sLength :: forall f nat (n :: nat) a. (HasOrdinal nat, CFoldable f, Dom f a)
        => Sized f n a -> Sing n
sLength (Sized xs) =
  case fromNatural (P.fromIntegral $ clength xs) of
    SomeSing (n :: Sing (k :: nat)) -> unsafeCoerce n
{-# INLINE[2] sLength #-}

-- | Test if the sequence is empty or not.
--
-- Since 0.7.0.0
null
  :: forall f n a. (CFoldable f, Dom f a)
  => Sized f n a -> Bool
null = coerce $ cnull @f @a
{-# INLINE CONLIKE [2] null #-}

nullTL0 :: Sized f 0 a -> Bool
nullTL0 = P.const True
{-# INLINE nullTL0 #-}

nullPeano0 :: Sized f 'Peano.Z a -> Bool
nullPeano0 = P.const True
{-# INLINE nullPeano0 #-}

nullPeanoSucc :: Sized f (S n) a -> Bool
nullPeanoSucc = P.const False
{-# INLINE nullPeanoSucc #-}

nullTLSucc :: Sized f (n + 1) a -> Bool
nullTLSucc = P.const False
{-# INLINE nullTLSucc #-}

{-# RULES
"null/0"  [~2] null = nullTL0
"null/0"  [~1] forall (vec :: (1 TL.<= n) => Sized f n a).
  null vec = False
"null/0"  [~2] null = nullTLSucc
"null/Z"  [~2] null = nullPeano0
"null/Sn" [~2] null = nullPeanoSucc
#-}

--------------------------------------------------------------------------------
--- Indexing
--------------------------------------------------------------------------------

-- | (Unsafe) indexing with @Int@s.
--   If you want to check boundary statically, use '%!!' or 'sIndex'.
--
-- Since 0.7.0.0
(!!)
  :: forall f m a. (CFoldable f, Dom f a, (1 <= m) ~ 'True)
  => Sized f m a -> Int -> a
(!!) = coerce $ cindex @f @a
{-# INLINE (!!) #-}

-- | Safe indexing with 'Ordinal's.
--
-- Since 0.7.0.0
(%!!) :: forall f n c. (HasOrdinal nat, CFoldable f, Dom f c) => Sized f n c -> Ordinal (n :: nat) -> c
(%!!) = coerce $ (. (P.fromIntegral . ordToNatural)) . cindex @f @c
{-# INLINE (%!!) #-}
{-# SPECIALISE (%!!) :: Sized [] (n :: TL.Nat) a -> Ordinal n -> a #-}
{-# SPECIALISE (%!!) :: Sized [] (n :: Peano.Nat) a -> Ordinal n -> a #-}
{-# SPECIALISE (%!!) :: Sized V.Vector (n :: TL.Nat) a -> Ordinal n -> a #-}
{-# SPECIALISE (%!!) :: Sized V.Vector (n :: Peano.Nat) a -> Ordinal n -> a #-}
{-# SPECIALISE (%!!) :: UV.Unbox a => Sized UV.Vector (n :: TL.Nat) a -> Ordinal n -> a #-}
{-# SPECIALISE (%!!) :: UV.Unbox a => Sized UV.Vector (n :: Peano.Nat) a -> Ordinal n -> a #-}
{-# SPECIALISE (%!!) :: SV.Storable a => Sized SV.Vector (n :: TL.Nat) a -> Ordinal n -> a #-}
{-# SPECIALISE (%!!) :: SV.Storable a => Sized SV.Vector (n :: Peano.Nat) a -> Ordinal n -> a #-}
{-# SPECIALISE (%!!) :: Sized Seq.Seq (n :: TL.Nat) a -> Ordinal n -> a #-}
{-# SPECIALISE (%!!) :: Sized Seq.Seq (n :: Peano.Nat) a -> Ordinal n -> a #-}

-- | Flipped version of '!!'.
--
-- Since 0.7.0.0
index
  :: (CFoldable f, Dom f a, (1 <= m) ~ 'True)
  => Int -> Sized f m a -> a
index =  flip (!!)
{-# INLINE index #-}

-- | Flipped version of '%!!'.
--
-- Since 0.7.0.0
sIndex
  :: (HasOrdinal nat, CFoldable f, Dom f c)
  => Ordinal (n :: nat) -> Sized f n c -> c
sIndex = flip (%!!)
{-# INLINE sIndex #-}

-- | Take the first element of non-empty sequence.
--   If you want to make case-analysis for general sequence,
--   see  <#ViewsAndPatterns Views and Patterns> section.
--
-- Since 0.7.0.0
head
  :: forall nat f (n :: nat) a. 
      (HasOrdinal nat, CFoldable f, Dom f a, (Zero nat < n) ~ 'True)
  => Sized f n a -> a
head = coerce $ chead @f @a
{-# INLINE head #-}

-- | Take the last element of non-empty sequence.
--   If you want to make case-analysis for general sequence,
--   see  <#ViewsAndPatterns Views and Patterns> section.
--
-- Since 0.7.0.0
last :: forall nat f (n :: nat) a. 
  (HasOrdinal nat, (Zero nat < n) ~ 'True, CFoldable f, Dom f a)
  => Sized f n a -> a
last = coerce $ clast @f @a
{-# INLINE last #-}

-- | Take the 'head' and 'tail' of non-empty sequence.
--   If you want to make case-analysis for general sequence,
--   see  <#ViewsAndPatterns Views and Patterns> section.
--
-- Since 0.7.0.0
uncons :: forall f n a. (CFreeMonoid f, Dom f a)
  => Sized f (Succ n) a -> (a, Sized f n a)
uncons = coerce $ fromJust . cuncons @f @a

uncons'
  :: (CFreeMonoid f, Dom f a)
  => proxy n -> Sized f (Succ n) a -> (a, Sized f n a)
uncons' _  = uncons
{-# INLINE uncons' #-}

-- | Take the 'init' and 'last' of non-empty sequence.
--   If you want to make case-analysis for general sequence,
--   see  <#ViewsAndPatterns Views and Patterns> section.
--
-- Since 0.7.0.0
unsnoc :: (CFreeMonoid f, Dom f a) => Sized f (Succ n) a -> (Sized f n a, a)
unsnoc = ((,) <$> Sized . cinit <*> clast) . runSized
{-# NOINLINE [1] unsnoc #-}

unsnocSeq :: Sized Seq.Seq (Succ n) a -> (Sized Seq.Seq n a, a)
unsnocSeq (Sized ~(Seq.viewr -> xs Seq.:> x)) = (Sized xs, x)
{-# INLINE unsnocSeq #-}

unsnocVector :: Sized V.Vector (Succ n) a -> (Sized V.Vector n a, a)
unsnocVector (Sized v) = (Sized (V.init v), V.last v)
{-# INLINE unsnocVector #-}

{-# RULES
"unsnoc/Seq"     [~1] unsnoc = unsnocSeq
"unsnoc/Vector"  [~1] unsnoc = unsnocVector
 #-}

unsnoc'
  :: (CFreeMonoid f, Dom f a)
  => proxy n -> Sized f (Succ n) a -> (Sized f n a, a)
unsnoc' _  = unsnoc
{-# INLINE unsnoc' #-}


--------------------------------------------------------------------------------
--- Slicing
--------------------------------------------------------------------------------

-- | Take the tail of non-empty sequence.
--   If you want to make case-analysis for general sequence,
--   see  <#ViewsAndPatterns Views and Patterns> section.
--
-- Since 0.7.0.0
tail
  :: forall nat f n a. (HasOrdinal nat, CFreeMonoid f, Dom f a)
  => Sized f (Succ n) a -> Sized f (n :: nat) a
tail = coerce $ ctail @f @a
{-# INLINE tail #-}

-- | Take the initial segment of non-empty sequence.
--   If you want to make case-analysis for general sequence,
--   see  <#ViewsAndPatterns Views and Patterns> section.
--
-- Since 0.7.0.0
init
  :: forall nat f n a. (HasOrdinal nat, CFreeMonoid f, Dom f a)
  => Sized f (Succ n) a -> Sized f n a
init = coerce $ cinit @f @a
{-# INLINE init #-}

-- | @take k xs@ takes first @k@ element of @xs@ where
-- the length of @xs@ should be larger than @k@.
-- It is really sad, that this function
-- takes at least O(k) regardless of base container.
--
-- Since 0.7.0.0
take :: (CFreeMonoid f, Dom f a, (n <= m) ~ 'True, HasOrdinal nat)
     => Sing (n :: nat) -> Sized f m a -> Sized f n a
take sn = Sized . ctake (P.fromIntegral $ toNatural sn) . runSized
{-# INLINE take #-}

-- | @take k xs@ takes first @k@ element of @xs@ at most.
-- It is really sad, that this function
-- takes at least O(k) regardless of base container.
--
-- Since 0.7.0.0
takeAtMost :: (CFreeMonoid f, Dom f a, HasOrdinal nat)
           => Sing (n :: nat) -> Sized f m a -> Sized f (Min n m) a
takeAtMost sn = Sized . ctake (P.fromIntegral $ toNatural sn) . runSized
{-# INLINE takeAtMost #-}

-- | @drop k xs@ drops first @k@ element of @xs@ and returns
-- the rest of sequence, where the length of @xs@ should be larger than @k@.
-- It is really sad, that this function
-- takes at least O(k) regardless of base container.
--
-- Since 0.7.0.0
drop :: (HasOrdinal nat, CFreeMonoid f, Dom f a, (n <= m) ~ 'True)
     => Sing (n :: nat) -> Sized f m a -> Sized f (m - n) a
drop sn = Sized . cdrop (P.fromIntegral $ toNatural sn) . runSized
{-# INLINE drop #-}

-- | @splitAt k xs@ split @xs@ at @k@, where
-- the length of @xs@ should be less than or equal to @k@.
-- It is really sad, that this function
-- takes at least O(k) regardless of base container.
--
-- Since 0.7.0.0
splitAt :: (CFreeMonoid f, Dom f a , (n <= m) ~ 'True, HasOrdinal nat)
        => Sing (n :: nat) -> Sized f m a -> (Sized f n a, Sized f (m -. n) a)
splitAt n (Sized xs) =
  let (as, bs) = csplitAt (P.fromIntegral $ toNatural n) xs
  in (Sized as, Sized bs)
{-# INLINE splitAt #-}

-- | @splitAtMost k xs@ split @xs@ at @k@.
--   If @k@ exceeds the length of @xs@, then the second result value become empty.
-- It is really sad, that this function
-- takes at least O(k) regardless of base container.
--
-- Since 0.7.0.0
splitAtMost :: (HasOrdinal nat, CFreeMonoid f, Dom f a)
            => Sing (n :: nat) -> Sized f m a -> (Sized f (Min n m) a, Sized f (m -. n) a)
splitAtMost n (Sized xs) =
  let (as, bs) = csplitAt (P.fromIntegral $ toNatural n) xs
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
-- Since 0.5.0.0 (type changed)
empty
  :: forall f nat a. (Monoid (f a), HasOrdinal nat, Dom f a)
  => Sized f (Zero nat :: nat) a
empty = Sized mempty
{-# INLINE empty #-}

-- | Sequence with one element.
--
-- Since 0.7.0.0
singleton :: forall nat f a. (CPointed f, Dom f a) => a -> Sized f (One nat) a
singleton = Sized . cpure
{-# INLINE singleton #-}

-- | Consruct the 'Sized' sequence from base type, but
--   the length parameter is dynamically determined and
--   existentially quantified; see also 'SomeSized'.
--
-- Since 0.7.0.0
toSomeSized
  :: forall nat f a. (HasOrdinal nat, Dom f a, CFoldable f)
  => f a -> SomeSized f nat a
toSomeSized = \xs ->
  case fromNatural $ P.fromIntegral $ clength xs of
    SomeSing sn -> withSingI sn $ SomeSized sn $ unsafeToSized sn xs

-- | Replicates the same value.
--
-- Since 0.7.0.0
replicate :: forall f nat (n :: nat) a. (HasOrdinal nat, CFreeMonoid f, Dom f a)
          => Sing n -> a -> Sized f n a
replicate sn a = Sized $ creplicate (P.fromIntegral $ toNatural sn) a
{-# INLINE replicate #-}

-- | 'replicate' with the length inferred.
--
-- Since 0.7.0.0
replicate'
  :: (HasOrdinal nat, SingI (n :: nat), CFreeMonoid f, Dom f a)
  => a -> Sized f n a
replicate' = withSing replicate
{-# INLINE replicate' #-}

generate :: forall (nat :: Type) (n :: nat) (a :: Type) f.
            (CFreeMonoid f, Dom f a, HasOrdinal nat)
         => Sing n -> (Ordinal n -> a) -> Sized f n a
generate n f = unsafeFromList n [f i | i <- enumOrdinal n ]
{-# INLINE [1] generate #-}

genVector :: forall nat (n :: nat) a.
            (HasOrdinal nat)
          => Sing n -> (Ordinal n -> a) -> Sized V.Vector n a
genVector n f = withSingI n $ Sized $ V.generate (P.fromIntegral $ toNatural n) (f . toEnum)
{-# INLINE genVector #-}

genSVector :: forall nat (n :: nat) a.
             (HasOrdinal nat, SV.Storable a)
           => Sing n -> (Ordinal n -> a) -> Sized SV.Vector n a
genSVector n f = withSingI n $ Sized $ SV.generate (P.fromIntegral $ toNatural n) (f . toEnum)
{-# INLINE genSVector #-}

genSeq :: forall nat (n :: nat) a.
          (HasOrdinal nat)
       => Sing n -> (Ordinal n -> a) -> Sized Seq.Seq n a
genSeq n f = withSingI n $ Sized $ Seq.fromFunction (P.fromIntegral $ toNatural n)  (f . toEnum)
{-# INLINE genSeq #-}

{-# RULES
"generate/Vector"  [~1] generate = genVector
"generate/SVector" [~1] forall (n :: HasOrdinal nat => Sing (n :: nat))
                       (f :: SV.Storable a => Ordinal n -> a).
  generate n f = genSVector n f
"generate/UVector" [~1] forall (n :: HasOrdinal nat => Sing (n :: nat))
                       (f :: UV.Unbox a => Ordinal n -> a).
  generate n f = withSingI n $ Sized (UV.generate (P.fromIntegral $ toNatural n) (f . toEnum))
"generate/Seq" [~1] generate = genSeq
#-}

--------------------------------------------------------------------------------
--- Concatenation
--------------------------------------------------------------------------------

-- | Append an element to the head of sequence.
--
-- Since 0.7.0.0
cons :: (CFreeMonoid f, Dom f a) => a -> Sized f n a -> Sized f (Succ n) a
cons a = Sized . ccons a . runSized
{-# INLINE cons #-}

-- | Infix version of 'cons'.
--
-- Since 0.7.0.0
(<|) :: (CFreeMonoid f, Dom f a) => a -> Sized f n a -> Sized f (Succ n) a
(<|) = cons
{-# INLINE (<|) #-}
infixr 5 <|

-- | Append an element to the tail of sequence.
--
-- Since 0.7.0.0
snoc :: (CFreeMonoid f, Dom f a) => Sized f n a -> a -> Sized f (Succ n) a
snoc (Sized xs) a = Sized $ csnoc xs a
{-# INLINE snoc #-}

-- | Infix version of 'snoc'.
--
-- Since 0.7.0.0
(|>) :: (CFreeMonoid f, Dom f a) => Sized f n a -> a -> Sized f (Succ n) a
(|>) = snoc
{-# INLINE (|>) #-}
infixl 5 |>

-- | Append two lists.
--
-- Since 0.7.0.0
append :: (CFreeMonoid f, Dom f a) => Sized f n a -> Sized f m a -> Sized f (n + m) a
append (Sized xs) (Sized ys) = Sized $ mappend xs ys
{-# INLINE append #-}

-- | Infix version of 'append'.
--
-- Since 0.7.0.0
(++) :: (CFreeMonoid f, Dom f a) => Sized f n a -> Sized f m a -> Sized f (n + m) a
(++) = append
infixr 5 ++

-- | Concatenates multiple sequences into one.
--
-- Since 0.7.0.0
concat :: forall f f' m n a. 
  (CFreeMonoid f, CFunctor f', CFoldable f', Dom f a, Dom f' (f a),
    Dom f' (Sized f n a)
  )
  => Sized f' m (Sized f n a) -> Sized f (m * n) a
concat =  Sized . cfold . cmap runSized . runSized
{-# INLINE [2] concat #-}

--------------------------------------------------------------------------------
--- Zips
--------------------------------------------------------------------------------

-- | Zipping two sequences. Length is adjusted to shorter one.
--
-- Since 0.7.0.0
zip :: forall f a b n m. (Dom f a, CZip f, Dom f b, Dom f (a, b))
    => Sized f n a -> Sized f m b -> Sized f (Min n m) (a, b)
zip = coerce $ czip @f @a @b

-- | 'zip' for the sequences of the same length.
--
-- Since 0.7.0.0
zipSame :: forall f a b n. (Dom f a, CZip f, Dom f b, Dom f (a, b))
        => Sized f n a -> Sized f n b -> Sized f n (a, b)
zipSame = coerce $ czip @f @a @b
{-# INLINE [1] zipSame #-}

coerceBin
  :: forall f a b c n m l.
    (f a -> f b -> f c)
  -> Sized f n a -> Sized f m b -> Sized f l c
{-# INLINE coerceBin #-}
coerceBin = coerce

-- | Zipping two sequences with funtion. Length is adjusted to shorter one.
--
-- Since 0.7.0.0
zipWith :: forall f a b c n m. (Dom f a, CZip f, Dom f b, CFreeMonoid f, Dom f c)
    => (a -> b -> c) -> Sized f n a -> Sized f m b -> Sized f (Min n m) c
zipWith = coerce $ czipWith @f @a @b @c
{-# INLINE [1] zipWith #-}

{-# RULES
"zipWith/Seq" [~1]
  zipWith = \f -> coerceBin @Seq.Seq $ Seq.zipWith f
"zipWith/Vector" [~1] forall f.
  zipWith f = (Sized .) . (. runSized) . V.zipWith f . runSized
"zipWith/UVector" [~1]
  forall (f :: (UV.Unbox a, UV.Unbox b, UV.Unbox c) => a -> b -> c).
  zipWith f = (Sized .) . (. runSized) . UV.zipWith f . runSized
"zipWith/MVector" [~1]
  forall (f :: (SV.Storable a, SV.Storable b, SV.Storable c) => a -> b -> c).
  zipWith f = (Sized .) . (. runSized) . SV.zipWith f . runSized
  #-}


zipWithSameList
  :: forall a b c n. (a -> b -> c) 
  -> Sized [] n a -> Sized [] n b -> Sized [] n c
zipWithSameList = coerce $ P.zipWith @a @b @c

zipWithSameSeq
  :: forall a b c n. (a -> b -> c) 
  -> Sized Seq.Seq n a -> Sized Seq.Seq n b -> Sized Seq.Seq n c
zipWithSameSeq = coerce $ Seq.zipWith @a @b @c

zipWithSameVec
  :: forall a b c n. (a -> b -> c) 
  -> Sized V.Vector n a -> Sized V.Vector n b -> Sized V.Vector n c
zipWithSameVec = coerce $ V.zipWith @a @b @c

zipWithSameUVec
  :: forall a b c n. 
      (UV.Unbox a, UV.Unbox b, UV.Unbox c)
  => (a -> b -> c) 
  -> Sized UV.Vector n a -> Sized UV.Vector n b -> Sized UV.Vector n c
zipWithSameUVec = coerce $ UV.zipWith @a @b @c
-- | 'zipWith' for the sequences of the same length.
--
-- Since 0.7.0.0
zipWithSame
  :: forall f a b c n. (Dom f a, CZip f, Dom f b, CFreeMonoid f, Dom f c)
  => (a -> b -> c) -> Sized f n a -> Sized f n b -> Sized f n c
{-# SPECIALISE INLINE [1] zipWithSame
  :: (a -> b -> c) -> Sized [] n a -> Sized [] n b -> Sized [] n c
  #-}
{-# SPECIALISE INLINE [1] zipWithSame
  :: (a -> b -> c)
  -> Sized V.Vector n a -> Sized V.Vector n b -> Sized V.Vector n c
  #-}
{-# SPECIALISE INLINE [1] zipWithSame
  :: (UV.Unbox a, UV.Unbox b, UV.Unbox c) 
  => (a -> b -> c)
  -> Sized UV.Vector n a -> Sized UV.Vector n b -> Sized UV.Vector n c
  #-}
{-# SPECIALISE INLINE [1] zipWithSame
  :: (SV.Storable a, SV.Storable b, SV.Storable c) 
  => (a -> b -> c)
  -> Sized SV.Vector n a -> Sized SV.Vector n b -> Sized SV.Vector n c
  #-}
zipWithSame = coerce $ czipWith @f @a @b @c
{-# INLINE [1] zipWithSame #-}

{-# RULES
"zipWithSame/Seq"
  zipWithSame = zipWithSameSeq
"zipWithSame/List"
  zipWithSame = zipWithSameList
"zipWithSame/Vector"
  zipWithSame = zipWithSameVec
"zipWithSame/UVector"
  forall (f :: (UV.Unbox a, UV.Unbox b, UV.Unbox c) => a -> b -> c).
  zipWithSame f = zipWithSameUVec f

"zipWithSame/MVector" [~1]
  forall (f :: (SV.Storable a, SV.Storable b, SV.Storable c) => a -> b -> c).
  zipWithSame f = (Sized .) . (. runSized) . Seq.zipWith f . runSized
  #-}

-- | Unzipping the sequence of tuples.
--
-- Since 0.7.0.0
unzip :: (CUnzip f, Dom f a, Dom f b, Dom f (a, b))
      => Sized f n (a, b) -> (Sized f n a, Sized f n b)
unzip (Sized xys) =
  let (xs, ys) = cunzip xys
  in (Sized xs, Sized ys)
{-# INLINE unzip #-}

--------------------------------------------------------------------------------
-- Transformation
--------------------------------------------------------------------------------

-- | Map function.
--
-- Since 0.7.0.0
map :: (CFunctor f, Dom f a, Dom f b) => (a -> b) -> Sized f n a -> Sized f n b
map f = Sized . cmap f . runSized
{-# INLINE map #-}

fmap :: forall f n a b. Functor f => (a -> b) -> Sized f n a -> Sized f n b
fmap f = Sized . P.fmap f . runSized
{-# INLINE fmap #-}

-- | Reverse function.
--
-- Since 0.7.0.0
reverse :: (Dom f a, CFreeMonoid f) => Sized f n a -> Sized f n a
reverse = Sized .  creverse . runSized
{-# INLINE reverse #-}

-- | Intersperces.
--
-- Since 0.7.0.0
intersperse
  :: (CFreeMonoid f, Dom f a)
  => a -> Sized f n a -> Sized f ((FromInteger 2 TL.* n) -. 1) a
intersperse a = Sized . cintersperse a . runSized
{-# INLINE intersperse #-}

-- | Remove all duplicates.
--
-- Since 0.7.0.0
nub
  :: (HasOrdinal nat, Dom f a, Eq a, CFreeMonoid f)
  => Sized f n a -> SomeSized f nat a
nub = toSomeSized . cnub . runSized

-- | Sorting sequence by ascending order.
--
-- Since 0.7.0.0
sort :: (CFreeMonoid f, Dom f a, Ord a)
     => Sized f n a -> Sized f n a
sort = Sized . csort . runSized

-- | Generalized version of 'sort'.
--
-- Since 0.7.0.0
sortBy
  :: (CFreeMonoid f, Dom f a)
  => (a -> a -> Ordering) -> Sized f n a -> Sized f n a
sortBy cmp = Sized . csortBy cmp . runSized

-- | Insert new element into the presorted sequence.
--
-- Since 0.7.0.0
insert
  :: (CFreeMonoid f, Dom f a, Ord a)
  => a -> Sized f n a -> Sized f (Succ n) a
insert a = Sized . cinsert a . runSized

-- | Generalized version of 'insert'.
--
-- Since 0.7.0.0
insertBy :: (CFreeMonoid f, Dom f a) => (a -> a -> Ordering) -> a -> Sized f n a -> Sized f (Succ n) a
insertBy cmp a = Sized . cinsertBy cmp a . runSized


--------------------------------------------------------------------------------
-- Conversion
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
--- List
--------------------------------------------------------------------------------

-- | Convert to list.
--
-- Since 0.7.0.0
toList :: (CFoldable f, Dom f a) => Sized f n a -> [a]
toList = ctoList . runSized
{-# INLINE [2] toList #-}

{-# RULES
"toList/List"
  Data.Sized.toList = runSized
  #-}

-- | If the given list is shorter than @n@, then returns @Nothing@
--   Otherwise returns @Sized f n a@ consisting of initial @n@ element
--   of given list.
--
--   Since 0.5.0.0 (type changed)
fromList :: forall f nat (n :: nat) a. (HasOrdinal nat, CFreeMonoid f, Dom f a)
         => Sing n -> [a] -> Maybe (Sized f n a)
fromList Zero _ = Just $ Sized (mempty :: f a)
fromList sn xs =
  let len = P.fromIntegral $ toNatural sn
  in if P.length xs < len
     then Nothing
     else Just $ unsafeFromList sn $ P.take len xs
{-# INLINABLE [2] fromList #-}

-- | 'fromList' with the result length inferred.
--
-- Since 0.7.0.0
fromList' :: (Dom f a, CFreeMonoid f, SingI (n :: TL.Nat)) => [a] -> Maybe (Sized f n a)
fromList' = withSing fromList
{-# INLINE fromList' #-}

-- | Unsafe version of 'fromList'. If the length of the given list does not
--   equal to @n@, then something unusual happens.
--
-- Since 0.7.0.0
unsafeFromList :: forall (nat :: Type) f (n :: nat) a.
  (CFreeMonoid f, Dom f a) => Sing n -> [a] -> Sized f n a
unsafeFromList _ xs = Sized $ cfromList xs
{-# INLINE [1] unsafeFromList #-}

-- | 'unsafeFromList' with the result length inferred.
--
-- Since 0.7.0.0
unsafeFromList'
  :: (SingI (n :: TL.Nat), CFreeMonoid f, Dom f a)
  => [a] -> Sized f n a
unsafeFromList' = withSing unsafeFromList
{-# INLINE [1] unsafeFromList' #-}
{-# RULES
"unsafeFromList'/List" [~1]
  unsafeFromList' = Sized
"unsafeFromList'/Vector" [~1]
  unsafeFromList' = Sized . V.fromList
"unsafeFromList'/Seq" [~1]
  unsafeFromList' = Sized . Seq.fromList
"unsafeFromList'/SVector" [~1] forall (xs :: SV.Storable a => [a]).
  unsafeFromList'  xs = Sized (SV.fromList xs)
"unsafeFromList'/UVector" [~1] forall (xs :: UV.Unbox a => [a]).
  unsafeFromList'  xs = Sized (UV.fromList xs)
  #-}


-- | Construct a @Sized f n a@ by padding default value if the given list is short.
--
--   Since 0.5.0.0 (type changed)
fromListWithDefault
  :: forall f nat (n :: nat) a. 
      (HasOrdinal nat, Dom f a, CFreeMonoid f)
  => Sing n -> a -> [a] -> Sized f n a
fromListWithDefault sn def xs =
  let len = P.fromIntegral $ toNatural sn
  in Sized $ cfromList (ctake len xs) <> 
        creplicate (len - clength xs) def
{-# INLINABLE fromListWithDefault #-}

-- | 'fromListWithDefault' with the result length inferred.
--
-- Since 0.7.0.0
fromListWithDefault'
  :: (SingI (n :: TL.Nat), CFreeMonoid f, Dom f a)
  => a -> [a] -> Sized f n a
fromListWithDefault' = withSing fromListWithDefault
{-# INLINE fromListWithDefault' #-}

--------------------------------------------------------------------------------
--- Base containes
--------------------------------------------------------------------------------

-- | Forget the length and obtain the wrapped base container.
--
-- Since 0.7.0.0
unsized :: Sized f n a -> f a
unsized = runSized
{-# INLINE unsized #-}

-- | If the length of the input is shorter than @n@, then returns @Nothing@.
--   Otherwise returns @Sized f n a@ consisting of initial @n@ element
--   of the input.
--
-- Since 0.7.0.0
toSized :: (HasOrdinal nat, CFreeMonoid f, Dom f a)
        => Sing (n :: nat) -> f a -> Maybe (Sized f n a)
toSized sn xs =
  let len = P.fromIntegral $ toNatural sn
  in if clength xs < len
     then Nothing
     else Just $ unsafeToSized sn $ ctake len xs
{-# INLINABLE [2] toSized #-}

-- | 'toSized' with the result length inferred.
--
-- Since 0.7.0.0
toSized'
  :: (Dom f a, CFreeMonoid f, SingI (n :: TL.Nat))
  => f a -> Maybe (Sized f n a)
toSized' = withSing toSized
{-# INLINE toSized' #-}

-- | Unsafe version of 'toSized'. If the length of the given list does not
--   equal to @n@, then something unusual happens.
--
-- Since 0.7.0.0
unsafeToSized :: Sing n -> f a -> Sized f n a
unsafeToSized _ = Sized
{-# INLINE [2] unsafeToSized #-}

-- | 'unsafeToSized' with the result length inferred.
--
-- Since 0.7.0.0
unsafeToSized' :: (SingI (n :: TL.Nat), Dom f a) => f a -> Sized f n a
unsafeToSized' = withSing unsafeToSized
{-# INLINE unsafeToSized' #-}

-- | Construct a @Sized f n a@ by padding default value if the given list is short.
--
-- Since 0.7.0.0
toSizedWithDefault :: (HasOrdinal nat, CFreeMonoid f, Dom f a)
                   => Sing (n :: nat) -> a -> f a -> Sized f n a
toSizedWithDefault sn def xs =
  let len = P.fromIntegral $ toNatural sn
  in Sized $ ctake len xs <> creplicate (len - clength xs) def
{-# INLINABLE toSizedWithDefault #-}

-- | 'toSizedWithDefault' with the result length inferred.
--
-- Since 0.7.0.0
toSizedWithDefault'
  :: (SingI (n :: TL.Nat), CFreeMonoid f, Dom f a)
  => a -> f a -> Sized f n a
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
-- Since 0.7.0.0
data Partitioned f n a where
  Partitioned :: (Dom f a)
              => Sing n
              -> Sized f (n :: TL.Nat) a
              -> Sing m
              -> Sized f (m :: TL.Nat) a
              -> Partitioned f (n + m) a

-- | Take the initial segment as long as elements satisfys the predicate.
--
-- Since 0.7.0.0
takeWhile :: (HasOrdinal nat, Dom f a, CFreeMonoid f)
          => (a -> Bool) -> Sized f n a -> SomeSized f nat a
takeWhile p = toSomeSized . ctakeWhile p . runSized
{-# INLINE takeWhile #-}

-- | Drop the initial segment as long as elements satisfys the predicate.
--
-- Since 0.7.0.0
dropWhile :: (HasOrdinal nat, CFreeMonoid f, Dom f a)
          => (a -> Bool) -> Sized f n a -> SomeSized f nat a
dropWhile p = toSomeSized . cdropWhile p . runSized
{-# INLINE dropWhile #-}

-- | Invariant: @'ListLike' (f a) a@ instance must be implemented
-- to satisfy the following property:
-- @length (fst (span p xs)) + length (snd (span p xs)) == length xs@
-- Otherwise, this function introduces severe contradiction.
--
-- Since 0.7.0.0
span :: (CFreeMonoid f, Dom f a)
     => (a -> Bool) -> Sized f n a -> Partitioned f n a
span p xs =
  let (as, bs) = cspan p $ runSized xs
  in case (toSomeSized as, toSomeSized bs) of
    (SomeSized lenL ls, SomeSized lenR rs) ->
      unsafeCoerce $ Partitioned lenL ls lenR rs
{-# INLINE span #-}

-- | Invariant: @'ListLike' (f a) a@ instance must be implemented
-- to satisfy the following property:
-- @length (fst (break p xs)) + length (snd (break p xs)) == length xs@
-- Otherwise, this function introduces severe contradiction.
--
-- Since 0.7.0.0
break :: (CFreeMonoid f, Dom f a)
     => (a -> Bool) -> Sized f n a -> Partitioned f n a
break p (Sized xs) =
  let (as, bs) = cbreak p xs
  in case (toSomeSized as, toSomeSized bs) of
    (SomeSized lenL ls, SomeSized lenR rs) ->
      unsafeCoerce $ Partitioned lenL ls lenR rs
{-# INLINE break #-}

-- | Invariant: @'ListLike' (f a) a@ instance must be implemented
-- to satisfy the following property:
-- @length (fst (partition p xs)) + length (snd (partition p xs)) == length xs@
-- Otherwise, this function introduces severe contradiction.
--
-- Since 0.7.0.0
partition :: (CFreeMonoid f, Dom f a)
     => (a -> Bool) -> Sized f n a -> Partitioned f n a
partition p (Sized xs) =
         let (as, bs) = cpartition p xs
         in case (toSomeSized as, toSomeSized bs) of
           (SomeSized lenL ls, SomeSized lenR rs) ->
             unsafeCoerce $ Partitioned lenL ls lenR rs
{-# INLINE partition #-}

--------------------------------------------------------------------------------
--- Searching
--------------------------------------------------------------------------------
-- | Membership test; see also 'notElem'.
--
-- Since 0.7.0.0
elem :: forall f a n. (CFoldable f, Dom f a, Eq a) => a -> Sized f n a -> Bool
elem = coerce $ celem @f @a
{-# INLINE elem #-}

-- | Negation of 'elem'.
--
-- Since 0.7.0.0
notElem
  :: forall f a n. (CFoldable f, Dom f a, Eq a)
  => a -> Sized f n a -> Bool
notElem = coerce $ cnotElem @f @a
{-# INLINE notElem #-}

-- | Find the element satisfying the predicate.
--
-- Since 0.7.0.0
find :: Foldable f => (a -> Bool) -> Sized f n a -> Maybe a
find p = F.find p
{-# INLINE[1] find #-}
{-# RULES
"find/List" [~1] forall p.
  find p = L.find p . runSized
"find/Vector" [~1] forall p.
  find p = V.find p . runSized
"find/Storable Vector" [~1] forall (p :: SV.Storable a => a -> Bool).
  find p = SV.find p . runSized
"find/Unboxed Vector" [~1] forall (p :: UV.Unbox a => a -> Bool).
  find p = UV.find p . runSized
  #-}

-- | @'Foldable'@ version of @'find'@.
findF :: (Foldable f) => (a -> Bool) -> Sized f n a -> Maybe a
findF p = getFirst. F.foldMap (\a -> if p a then First (Just a) else First Nothing) . runSized
{-# INLINE [1] findF #-}
{-# SPECIALISE [0] findF :: (a -> Bool) -> Sized Seq.Seq n a -> Maybe a #-}
{-# RULES
"findF/list"   [~1] findF = (. runSized) . L.find
"findF/Vector" [~1] findF = (. runSized) . V.find
  #-}

-- | @'findIndex' p xs@ find the element satisfying @p@ and returns its index if exists.
--
-- Since 0.7.0.0
findIndex
  :: forall nat f a (n :: nat) . 
    (CFoldable f, Dom f a)
  => (a -> Bool) -> Sized f n a -> Maybe Int
findIndex = coerce $ cfindIndex @f @a
{-# INLINE findIndex #-}

-- | 'Ordinal' version of 'findIndex'.
--
-- Since 0.7.0.0
sFindIndex :: (SingI (n :: nat), CFoldable f, Dom f a, HasOrdinal nat)
           => (a -> Bool) -> Sized f n a -> Maybe (Ordinal n)
sFindIndex p = P.fmap toEnum . findIndex p
{-# INLINE sFindIndex #-}

-- | @'findIndex'@ implemented in terms of @'FoldableWithIndex'@
findIndexIF :: (FoldableWithIndex i f) => (a -> Bool) -> Sized f n a -> Maybe i
findIndexIF p = P.fmap fst . ifind (P.const p) . runSized
{-# INLINE [1] findIndexIF #-}
{-# RULES
"findIndexIF/list" [~1] forall p.
  findIndexIF p = L.findIndex p . runSized
"findIndexIF/vector" [~1] forall p.
  findIndexIF p = V.findIndex p . runSized
  #-}

-- | @'sFindIndex'@ implemented in terms of @'FoldableWithIndex'@
sFindIndexIF :: (FoldableWithIndex i f, P.Integral i, HasOrdinal nat, SingI n)
             => (a -> Bool) -> Sized f (n :: nat) a -> Maybe (Ordinal n)
sFindIndexIF p = P.fmap fst . ifind (P.const p)
{-# INLINE [1] sFindIndexIF #-}
{-# RULES
"sFindIndexIF/list" [~1] forall p .
  sFindIndexIF p = P.fmap toEnum . L.findIndex p . runSized
"sFindIndexIF/vector" [~1] forall p.
  sFindIndexIF p = P.fmap toEnum . V.findIndex p . runSized
  #-}

-- | @'findIndices' p xs@ find all elements satisfying @p@ and returns their indices.
--
-- Since 0.7.0.0
findIndices
  :: forall nat f a (n :: nat).
    (CFoldable f, Dom f a) => (a -> Bool) -> Sized f n a -> [Int]
findIndices = coerce $ cfindIndices @f @a
{-# INLINE findIndices #-}
{-# SPECIALISE findIndices :: (a -> Bool) -> Sized [] n a -> [Int] #-}

-- | @'findIndices'@ implemented in terms of @'FoldableWithIndex'@
findIndicesIF :: (FoldableWithIndex i f) => (a -> Bool) -> Sized f n a -> [i]
findIndicesIF p = flip appEndo [] . ifoldMap (\i x -> if p x then Endo (i:) else Endo P.id) . runSized
{-# INLINE [1] findIndicesIF #-}
{-# RULES
"findIndicesIF/list" [~1] forall p.
  findIndicesIF p = L.findIndices p . runSized
"findIndicesIF/vector" [~1] forall p.
  findIndicesIF p = V.toList . V.findIndices p . runSized
  #-}


-- | 'Ordinal' version of 'findIndices'.
--
-- Since 0.7.0.0
sFindIndices :: (HasOrdinal nat, CFoldable f, Dom f a, SingI (n :: nat))
             => (a -> Bool) -> Sized f n a -> [Ordinal n]
sFindIndices p = P.fmap (toEnum . P.fromIntegral) . findIndices p
{-# INLINE sFindIndices #-}

sFindIndicesIF :: (FoldableWithIndex i f, P.Integral i, HasOrdinal nat, SingI n)
               => (a -> Bool) -> Sized f (n :: nat) a -> [Ordinal n]
sFindIndicesIF p = flip appEndo [] .
                   ifoldMap (\i x -> if p x then Endo (P.toEnum (P.fromIntegral i):) else Endo P.id) .
                   runSized
{-# INLINE [1] sFindIndicesIF #-}
{-# RULES
"sFindIndicesIF/list" [~1] forall p.
  sFindIndicesIF p = P.map toEnum . L.findIndices p . runSized
"sFindIndicesIF/vector" [~1] forall p.
  sFindIndicesIF p = V.toList . V.map toEnum . V.findIndices p . runSized
  #-}

{-# RULES
"Foldable.sum/Vector"
  F.sum = V.sum . runSized
  #-}

-- | Returns the index of the given element in the list, if exists.
--
-- Since 0.7.0.0
elemIndex :: (CFoldable f, Eq a, Dom f a) => a -> Sized f n a -> Maybe Int
elemIndex a (Sized xs) = celemIndex a xs
{-# INLINE elemIndex #-}

-- | Ordinal version of 'elemIndex'.
--   Since 0.7.0.0, we no longer do boundary check inside the definition. 
--
--   Since 0.7.0.0
sElemIndex, sUnsafeElemIndex :: forall nat (n :: nat) f a.
              (SingI n, CFoldable f, Dom f a, Eq a, HasOrdinal nat)
           => a -> Sized f n a -> Maybe (Ordinal n)
sElemIndex a (Sized xs) =
  unsafeNaturalToOrd . P.fromIntegral <$> celemIndex a xs
{-# INLINE sElemIndex #-}

-- | Since 0.5.0.0 (type changed)
sUnsafeElemIndex = sElemIndex

-- | Returns all indices of the given element in the list.
--
-- Since 0.7.0.0
elemIndices :: (CFoldable f, Dom f a, Eq a) => a -> Sized f n a -> [Int]
elemIndices a = celemIndices a . runSized
{-# INLINE elemIndices #-}

-- | Ordinal version of 'elemIndices'
--
-- Since 0.7.0.0
sElemIndices :: (CFoldable f, HasOrdinal nat, SingI (n :: nat), Dom f a, Eq a)
             => a -> Sized f n a -> [Ordinal n]
sElemIndices p = P.fmap (unsafeNaturalToOrd . P.fromIntegral) . elemIndices p
{-# INLINE sElemIndices #-}

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
slen :: ('SingI' n, 'Dom f a' f) => 'Sized' f n a -> 'Sing' n
slen ('viewCons' -> 'NilCV')    = 'SZ'
slen ('viewCons' -> _ ':-' as) = 'SS' (slen as)
slen _                          = error "impossible"
@

   The constraint @('SingI' n, 'Dom f a' f)@ is needed for view function.
   In the above, we have extra wildcard pattern (@_@) at the last.
   Code compiles if we removed it, but current GHC warns for incomplete pattern,
   although we know first two patterns exhausts all the case.

   Equivalently, we can use snoc-style pattern-matching:

@
slen :: ('SingI' n, 'Dom f a' f) => 'Sized' f n a -> 'Sing' n
slen ('viewSnoc' -> 'NilSV')     = 'SZ'
slen ('viewSnoc' -> as '-::' _) = 'SS' (slen as)
@
-}

-- | View of the left end of sequence (cons-side).
--
-- Since 0.7.0.0
data ConsView f n a where
  NilCV :: ConsView f (Zero nat) a
  (:-) :: SingI n => a -> Sized f n a -> ConsView f (Succ n) a

infixr 5 :-

-- | Case analysis for the cons-side of sequence.
--
-- Since 0.5.0.0 (type changed)
viewCons :: forall f a nat (n :: nat). (HasOrdinal nat, CFreeMonoid f,Dom f a)
         => Sized f n a
         -> ConsView f n a
viewCons sz = case zeroOrSucc (sLength sz) of
  IsZero   -> NilCV
  IsSucc n' -> withSingI n' $ P.uncurry (:-) (uncons' n' sz)

-- | View of the left end of sequence (snoc-side).
--
-- Since 0.7.0.0
data SnocView f n a where
  NilSV :: SnocView f (Zero nat) a
  (:-::) :: SingI n => Sized f n a -> a -> SnocView f (Succ n) a
infixl 5 :-::

-- | Case analysis for the snoc-side of sequence.
--
-- Since 0.5.0.0 (type changed)
viewSnoc :: forall nat f (n :: nat) a. (HasOrdinal nat, CFreeMonoid f, Dom f a)
         => Sized f n a
         -> SnocView f n a
viewSnoc sz = case zeroOrSucc (sLength sz) of
  IsZero   -> NilSV
  IsSucc n' ->
    withSingI n' $ P.uncurry (:-::) (unsnoc' n' sz)

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

infixr 5 :<
-- | Pattern synonym for cons-side uncons.
pattern (:<) :: forall nat f (n :: nat) a.
                (CFreeMonoid f, Dom f a, HasOrdinal nat)
             => forall (n1 :: nat).
                (n ~ Succ n1, SingI n1)
             => a -> Sized f n1 a -> Sized f n a
pattern a :< as <- (viewCons -> a :- as) where
   a :< as = a <| as

pattern NilL :: forall nat f (n :: nat) a.
                (CFreeMonoid f, Dom f a,  HasOrdinal nat)
             => (n ~ Zero nat) => Sized f n a
pattern NilL   <- (viewCons -> NilCV) where
  NilL = empty

infixl 5 :>

pattern (:>) :: forall nat f (n :: nat) a.
                (CFreeMonoid f, Dom f a, HasOrdinal nat)
             => forall (n1 :: nat).
                (n ~ Succ n1, SingI n1)
             => Sized f n1 a -> a -> Sized f n a
pattern a :> b <- (viewSnoc -> a :-:: b) where
  a :> b = a |> b

pattern NilR :: forall nat f (n :: nat) a.
                (CFreeMonoid f, Dom f a,  HasOrdinal nat)
             => n ~ Zero nat => Sized f n a
pattern NilR   <- (viewSnoc -> NilSV) where
  NilR = empty

class Dom f a => DomC f a
instance Dom f a => DomC f a

-- | Applicative instance, generalizing @'Data.Monoid.ZipList'@.
instance 
  ( Functor f, CFreeMonoid f, CZip f,
    HasOrdinal nat, SingI n, forall a. DomC f a)
      => P.Applicative (Sized f (n :: nat)) where
  {-# SPECIALISE instance TL.KnownNat n => P.Applicative (Sized [] (n :: TL.Nat)) #-}
  {-# SPECIALISE instance TL.KnownNat n => P.Applicative (Sized Seq.Seq (n :: TL.Nat)) #-}
  {-# SPECIALISE instance TL.KnownNat n => P.Applicative (Sized V.Vector (n :: TL.Nat)) #-}

  pure (x :: a) = withDict (Dict @(DomC f a))
    $ replicate' x
  {-# INLINE pure #-}

  (fs :: Sized f n (a -> b)) <*> (xs :: Sized f n a) =
    withDict (Dict @(DomC f b))
    $ withDict (Dict @(DomC f a))
    $ withDict (Dict @(DomC f (a -> b)))
    $ zipWithSame ($) fs xs
  {-# INLINE [1] (<*>) #-}
{-# RULES
"<*>/List" [~1] forall fs xs.
  Sized fs <*> Sized xs = Sized (getZipList (ZipList fs <*> ZipList xs))
"<*>/Seq" [~1] forall fs xs.
  Sized fs <*> Sized xs = Sized (Seq.zipWith ($) fs xs)
"<*>/Vector" [~1] forall fs xs.
  Sized fs <*> Sized xs = Sized (V.zipWith ($) fs xs)
 #-}

instance Constrained f => Constrained (Sized f n) where
  type Dom (Sized f n) a = Dom f a

instance (CFreeMonoid f, PeanoOrder nat, SingI (n :: nat))
      => CPointed (Sized f n) where
  cpure = replicate'

instance (CFunctor f) => CFunctor (Sized f n) where
  cmap = coerce . cmap @f 

instance (CFreeMonoid f, CZip f)
      => CApplicative (Sized f n) where
  pair = zipSame
  (<.>) = zipWithSame ($)
  (<.) = P.const
  (.>) = P.flip P.const

-- | __N.B.__ Since @calign@ is just zipping for fixed @n@,
--   we require more strong 'CZip' constraint here.
instance (CZip f, CFreeMonoid f) => CSemialign (Sized f n) where
  calignWith = coerce (\f -> czipWith @f @a @b @c ((f .) . These))
    :: forall a b c. 
        (Dom f a, Dom f b, Dom f c)
    => (These a b -> c) -> Sized f n a -> Sized f n b -> Sized f n c
  {-# INLINE [1] calignWith #-}
  calign = coerce $ czipWith @f @a @b These
    :: forall a b.
      (Dom f a, Dom f b, Dom f (These a b))
    => Sized f n a -> Sized f n b -> Sized f n (These a b)
  {-# INLINE [1] calign #-} 

instance (CZip f, CFreeMonoid f) => CZip (Sized f n) where
  czipWith = coerce $ czipWith @f @a @b @c
    :: forall a b c. 
        (Dom f a, Dom f b, Dom f c)
    => (a -> b -> c) -> Sized f n a -> Sized f n b -> Sized f n c
  {-# INLINE [1] czipWith #-}
  czip = coerce $ czip @f @a @b
    :: forall a b.
      (Dom f a, Dom f b, Dom f (a, b))
    => Sized f n a -> Sized f n b -> Sized f n (a, b)
  {-# INLINE [1] czip #-} 

instance 
  (PeanoOrder nat, SingI (n :: nat), CZip f, CFreeMonoid f)
  => CRepeat (Sized f n) where
  crepeat = replicate'
  {-# INLINE [1] crepeat #-}  
