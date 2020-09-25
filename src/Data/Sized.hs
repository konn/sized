{-# LANGUAGE AllowAmbiguousTypes, CPP, ConstraintKinds, DataKinds          #-}
{-# LANGUAGE DeriveDataTypeable, DeriveFoldable, DeriveFunctor             #-}
{-# LANGUAGE DeriveTraversable, DerivingStrategies, ExplicitNamespaces     #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, GADTs                    #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, InstanceSigs, KindSignatures      #-}
{-# LANGUAGE LambdaCase, LiberalTypeSynonyms, MultiParamTypeClasses        #-}
{-# LANGUAGE NoMonomorphismRestriction, NoStarIsType, PatternSynonyms      #-}
{-# LANGUAGE PolyKinds, QuantifiedConstraints, RankNTypes                  #-}
{-# LANGUAGE ScopedTypeVariables, StandaloneDeriving, TypeApplications     #-}
{-# LANGUAGE TypeFamilies, TypeInType, TypeOperators, UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses, ViewPatterns                         #-}

{-# OPTIONS_GHC -fno-warn-type-defaults -fno-warn-orphans #-}
{-# OPTIONS_GHC -fenable-rewrite-rules #-}
-- | This module provides the functionality to make length-parametrized types
--   from existing 'CFreeMonoid' sequential types.
--
--   Most of the complexity of operations for @Sized f n a@ are the same as
--   original operations for @f@. For example, '!!' is O(1) for
--   @Sized Vector n a@ but O(i) for @Sized [] n a@.
--
--  This module also provides powerful view types and pattern synonyms to
--  inspect the sized sequence. See <#ViewsAndPatterns Views and Patterns> for more detail.
module Data.Sized
  ( -- * Main Data-types
    Sized(), SomeSized'(..),
    DomC(),
    -- * Accessors
    -- ** Length information
    length, sLength, null,
    -- ** Indexing
    (!!), (%!!), index, sIndex, head, last,
    uncons, uncons', Uncons(..),
    unsnoc, unsnoc', Unsnoc(..),
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
    Partitioned(..),
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
    viewCons, ConsView (..), viewSnoc, SnocView(..),

    pattern (:<), pattern NilL , pattern (:>), pattern NilR,
  ) where

import Data.Sized.Internal

import           Control.Applicative          (ZipList (..), (<*>))
import           Control.Subcategory          (CApplicative (..),
                                               CFoldable (..), CFreeMonoid (..),
                                               CFunctor (..), CPointed (..),
                                               CRepeat (..), CSemialign (..),
                                               CTraversable (..), CUnzip (..),
                                               CZip (..), Constrained (Dom),
                                               cfromList, ctoList)
import           Data.Coerce                  (coerce)
import           Data.Constraint              (Dict (..), withDict)
import qualified Data.Foldable                as F
import           Data.Kind                    (Type)
import qualified Data.List                    as L
import           Data.Maybe                   (fromJust)
import           Data.Monoid                  (Monoid (..), (<>))
import qualified Data.Sequence                as Seq
import           Data.Singletons.Prelude      (SingI (..), SomeSing (..),
                                               withSing, withSingI)
import           Data.Singletons.Prelude.Bool (Sing)
import           Data.Singletons.Prelude.Enum (PEnum (..), sPred, sSucc)
import           Data.These                   (These (..))
import           Data.Type.Equality           ((:~:) (..), gcastWith)
import qualified Data.Type.Natural            as Peano
import           Data.Type.Natural.Class      (type (-.), IsPeano (..), One,
                                               PNum (..), POrd (..),
                                               PeanoOrder (..), S, SNum (..),
                                               Zero, pattern Zero,
                                               ZeroOrSucc (..), sOne, sZero)
import           Data.Type.Ordinal            (HasOrdinal, Ordinal (..),
                                               ordToNatural)
import           Data.Typeable                (Typeable)
import qualified Data.Vector                  as V
import qualified Data.Vector.Storable         as SV
import qualified Data.Vector.Unboxed          as UV
import qualified GHC.TypeLits                 as TL
import           Prelude                      (Bool (..), Enum (..), Eq (..),
                                               Functor, Int, Maybe (..),
                                               Num (..), Ord (..), Ordering,
                                               Show (..), const, flip, fmap,
                                               fromIntegral, uncurry, ($), (.))
import qualified Prelude                      as P
import           Proof.Propositional          (IsTrue (..), withWitness)
import           Unsafe.Coerce                (unsafeCoerce)

--------------------------------------------------------------------------------
-- Main data-types
--------------------------------------------------------------------------------

-- | 'Sized' vector with the length is existentially quantified.
--   This type is used mostly when the return type's length cannot
--   be statically determined beforehand.
--
-- @SomeSized' sn xs :: SomeSized' f a@ stands for the 'Sized' sequence
-- @xs@ of element type @a@ and length @sn@.
--
-- Since 0.7.0.0
data SomeSized' f nat a where
  SomeSized' :: Sing n
            -> Sized f (n :: nat) a
            -> SomeSized' f nat a

deriving instance Typeable SomeSized'

instance Show (f a) => Show (SomeSized' f nat a) where
  showsPrec d (SomeSized' _ s) = P.showParen (d > 9) $
    P.showString "SomeSized' _ " . showsPrec 10 s
instance Eq (f a) => Eq (SomeSized' f nat a) where
  (SomeSized' _ (Sized xs)) == (SomeSized' _ (Sized ys)) = xs == ys

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
-- Since 0.8.0.0 (type changed)
length
  :: forall nat f (n :: nat) a.
    (IsPeano nat, Dom f a, SingI n)
  => Sized f n a -> Int
length = const $ fromIntegral $ toNatural $ sing @n
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
-- Since 0.8.0.0 (type changed)
sLength :: forall nat f (n :: nat) a.
            (HasOrdinal nat, Dom f a, SingI n)
        => Sized f n a -> Sing n
sLength _ = sing @n
{-# INLINE[2] sLength #-}

-- | Test if the sequence is empty or not.
--
-- Since 0.7.0.0
null
  :: forall nat f (n :: nat) a. (CFoldable f, Dom f a)
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
"null/0"  [~2] null = nullTLSucc
"null/0"  [~1] forall (vec :: 1 TL.<= n => Sized f n a).
  null vec = False
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
  :: forall nat f (m :: nat) a. (CFoldable f, Dom f a, (One nat <= m) ~ 'True)
  => Sized f m a -> Int -> a
(!!) = coerce $ cindex @f @a
{-# INLINE (!!) #-}

-- | Safe indexing with 'Ordinal's.
--
-- Since 0.7.0.0
(%!!)
  :: forall nat f (n :: nat) c.
    (HasOrdinal nat, CFoldable f, Dom f c)
  => Sized f n c -> Ordinal n -> c
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
  :: forall nat f (m :: nat) a.
      (CFoldable f, Dom f a, (One nat <= m) ~ 'True)
  => Int -> Sized f m a -> a
index =  flip (!!)
{-# INLINE index #-}

-- | Flipped version of '%!!'.
--
-- Since 0.7.0.0
sIndex
  :: forall nat f (n :: nat) c. (HasOrdinal nat, CFoldable f, Dom f c)
  => Ordinal n -> Sized f n c -> c
sIndex = flip $ (%!!) @nat @f @n @c
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
uncons :: forall nat f (n :: nat) a.
  (PeanoOrder nat, SingI n, CFreeMonoid f, Dom f a, (Zero nat < n) ~ 'True)
  => Sized f n a -> Uncons f n a
uncons =
  withSingI
    (sPred $ sing @n)
  $ gcastWith
      (succAndPlusOneL $ sPred $ sing @n)
  $ gcastWith
      (lneqRightPredSucc sZero (sing @n) Witness
      )
  $ uncurry (Uncons @nat @f @(Pred n) @a) . coerce (fromJust . cuncons @f @a)

-- | 'uncons' with explicit specified length @n@
--
--   Since 0.7.0.0
uncons'
  :: forall nat f (n :: nat) a proxy.
    (HasOrdinal nat, SingI n, CFreeMonoid f, Dom f a)
  => proxy n -> Sized f (Succ n) a -> Uncons f (Succ n) a
uncons' _  = withSingI (sSucc $ sing @n)
  $ withWitness (lneqZero $ sing @n) uncons
{-# INLINE uncons' #-}

data Uncons f (n :: nat) a where
  Uncons :: forall nat f (n :: nat) a. SingI n
    => a -> Sized f n a -> Uncons f (One nat + n) a

-- | Take the 'init' and 'last' of non-empty sequence.
--   If you want to make case-analysis for general sequence,
--   see  <#ViewsAndPatterns Views and Patterns> section.
--
-- Since 0.7.0.0
unsnoc
  :: forall nat f (n :: nat) a.
    (HasOrdinal nat, SingI n, CFreeMonoid f, Dom f a, (Zero nat < n) ~ 'True)
  => Sized f n a -> Unsnoc f n a
unsnoc = withSingI
    (sPred $ sing @n)
  $ gcastWith
      (lneqRightPredSucc sZero (sing @n) Witness
      )
  $ uncurry (Unsnoc @nat @f @(Pred n)) . coerce (fromJust . cunsnoc @f @a)
{-# NOINLINE [1] unsnoc #-}

data Unsnoc f n a where
  Unsnoc :: forall nat f n a. Sized f (n :: nat) a -> a -> Unsnoc f (Succ n) a

-- | 'unsnoc'' with explicit specified length @n@
--
--   Since 0.7.0.0
unsnoc'
  :: forall nat f (n :: nat) a proxy.
    (HasOrdinal nat, SingI n, CFreeMonoid f, Dom f a)
  => proxy n -> Sized f (Succ n) a -> Unsnoc f (Succ n) a
unsnoc' _  =
  withSingI (sSucc $ sing @n)
  $ withWitness (lneqZero $ sing @n) unsnoc
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
  :: forall nat f (n :: nat) a. (HasOrdinal nat, CFreeMonoid f, Dom f a)
  => Sized f (One nat + n) a -> Sized f n a
tail = coerce $ ctail @f @a
{-# INLINE tail #-}

-- | Take the initial segment of non-empty sequence.
--   If you want to make case-analysis for general sequence,
--   see  <#ViewsAndPatterns Views and Patterns> section.
--
-- Since 0.7.0.0
init
  :: forall nat f (n :: nat) a. (HasOrdinal nat, CFreeMonoid f, Dom f a)
  => Sized f (n + One nat) a -> Sized f n a
init = coerce $ cinit @f @a
{-# INLINE init #-}

-- | @take k xs@ takes first @k@ element of @xs@ where
-- the length of @xs@ should be larger than @k@.
--
-- Since 0.7.0.0
take
  :: forall nat (n :: nat) f (m :: nat) a.
    (CFreeMonoid f, Dom f a, (n <= m) ~ 'True, HasOrdinal nat)
  => Sing n -> Sized f m a -> Sized f n a
take = coerce $ ctake @f @a . P.fromIntegral . toNatural @nat @n
{-# INLINE take #-}

-- | @'takeAtMost' k xs@ takes first at most @k@ elements of @xs@.
--
-- Since 0.7.0.0
takeAtMost
  :: forall nat (n :: nat) f m a.
      (CFreeMonoid f, Dom f a, HasOrdinal nat)
  => Sing n -> Sized f m a -> Sized f (Min n m) a
takeAtMost = coerce $ ctake @f @a . P.fromIntegral . toNatural @nat @n
{-# INLINE takeAtMost #-}

-- | @drop k xs@ drops first @k@ element of @xs@ and returns
-- the rest of sequence, where the length of @xs@ should be larger than @k@.
--
-- Since 0.7.0.0
drop
  :: forall nat (n :: nat) f (m :: nat) a.
    (HasOrdinal nat, CFreeMonoid f, Dom f a, (n <= m) ~ 'True)
  => Sing n -> Sized f m a -> Sized f (m - n) a
drop = coerce $ cdrop @f @a . P.fromIntegral . toNatural @nat @n
{-# INLINE drop #-}

-- | @splitAt k xs@ split @xs@ at @k@, where
-- the length of @xs@ should be less than or equal to @k@.
--
-- Since 0.7.0.0
splitAt
  :: forall nat (n :: nat) f m a.
      (CFreeMonoid f, Dom f a , (n <= m) ~ 'True, HasOrdinal nat)
  => Sing n -> Sized f m a -> (Sized f n a, Sized f (m -. n) a)
splitAt =
  coerce $ csplitAt @f @a . P.fromIntegral . toNatural @nat @n
{-# INLINE splitAt #-}

-- | @splitAtMost k xs@ split @xs@ at @k@.
--   If @k@ exceeds the length of @xs@, then the second result value become empty.
--
-- Since 0.7.0.0
splitAtMost
  :: forall nat (n :: nat) f (m :: nat) a.
      (HasOrdinal nat, CFreeMonoid f, Dom f a)
  => Sing n -> Sized f m a -> (Sized f (Min n m) a, Sized f (m -. n) a)
splitAtMost =
  coerce $ csplitAt @f @a . P.fromIntegral . toNatural @nat @n
{-# INLINE splitAtMost #-}


--------------------------------------------------------------------------------
-- Construction
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
--- Initialisation
--------------------------------------------------------------------------------

-- | Empty sequence.
--
-- Since 0.7.0.0 (type changed)
empty
  :: forall nat f a. (Monoid (f a), HasOrdinal nat, Dom f a)
  => Sized f (Zero nat) a
empty = coerce $ mempty @(f a)
{-# INLINE empty #-}

-- | Sequence with one element.
--
-- Since 0.7.0.0
singleton :: forall nat f a. (CPointed f, Dom f a) => a -> Sized f (One nat) a
singleton = coerce $ cpure @f @a
{-# INLINE singleton #-}

-- | Consruct the 'Sized' sequence from base type, but
--   the length parameter is dynamically determined and
--   existentially quantified; see also 'SomeSized''.
--
-- Since 0.7.0.0
toSomeSized
  :: forall nat f a. (HasOrdinal nat, Dom f a, CFoldable f)
  => f a -> SomeSized' f nat a
toSomeSized = \xs ->
  case fromNatural $ P.fromIntegral $ clength xs of
    SomeSing sn -> withSingI sn $ SomeSized' sn $ unsafeToSized sn xs

-- | Replicates the same value.
--
-- Since 0.7.0.0
replicate :: forall nat f (n :: nat) a. (HasOrdinal nat, CFreeMonoid f, Dom f a)
          => Sing n -> a -> Sized f n a
replicate = coerce $ creplicate @f @a . P.fromIntegral . toNatural @nat @n
{-# INLINE replicate #-}

-- | 'replicate' with the length inferred.
--
-- Since 0.7.0.0
replicate'
  :: forall nat f (n :: nat) a.
    (HasOrdinal nat, SingI (n :: nat), CFreeMonoid f, Dom f a)
  => a -> Sized f n a
replicate' = withSing replicate
{-# INLINE replicate' #-}

-- | Construct a sequence of the given length by applying the function to each index.
--
-- Since 0.7.0.0
generate
  :: forall (nat :: Type) f (n :: nat) (a :: Type).
      (CFreeMonoid f, Dom f a, HasOrdinal nat)
  => Sing n -> (Ordinal n -> a) -> Sized f n a
generate = coerce $ \sn -> withSingI sn $
  cgenerate @f @a (P.fromIntegral $ toNatural @nat @n sn)
    . (. toEnum @(Ordinal n))
{-# INLINE [1] generate #-}

-- | 'generate' with length inferred.
--
--   Since 0.8.0.0
generate'
  :: forall (nat :: Type) f (n :: nat) (a :: Type).
      (SingI n, CFreeMonoid f, Dom f a, HasOrdinal nat)
  => (Ordinal n -> a) -> Sized f n a
generate' = generate sing
{-# INLINE [1] generate' #-}

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
-- Since 0.8.0.0
cons
  :: forall nat f (n :: nat) a.
    (CFreeMonoid f, Dom f a)
  => a -> Sized f n a -> Sized f (One nat + n) a
cons = coerce $ ccons @f @a
{-# INLINE cons #-}

-- | Infix version of 'cons'.
--
-- Since 0.8.0.0
(<|)
  :: forall nat f (n :: nat) a. (CFreeMonoid f, Dom f a)
  => a -> Sized f n a -> Sized f (One nat + n) a
(<|) = cons
{-# INLINE (<|) #-}
infixr 5 <|

-- | Append an element to the tail of sequence.
--
-- Since 0.7.0.0
snoc
  :: forall nat f (n :: nat) a.
      (CFreeMonoid f, Dom f a)
  => Sized f n a -> a -> Sized f (n + One nat) a
snoc (Sized xs) a = Sized $ csnoc xs a
{-# INLINE snoc #-}

-- | Infix version of 'snoc'.
--
-- Since 0.7.0.0
(|>) :: forall nat f (n :: nat) a.
  (CFreeMonoid f, Dom f a) => Sized f n a -> a -> Sized f (n + One nat) a
(|>) = snoc
{-# INLINE (|>) #-}
infixl 5 |>

-- | Append two lists.
--
-- Since 0.7.0.0
append
  :: forall nat f (n :: nat) (m :: nat) a.
    (CFreeMonoid f, Dom f a)
  => Sized f n a -> Sized f m a -> Sized f (n + m) a
append = coerce $ mappend @(f a)
{-# INLINE append #-}

-- | Infix version of 'append'.
--
-- Since 0.7.0.0
(++)
  :: forall nat f (n :: nat) (m :: nat) a.
    (CFreeMonoid f, Dom f a)
  => Sized f n a -> Sized f m a -> Sized f (n + m) a
(++) = append
infixr 5 ++

-- | Concatenates multiple sequences into one.
--
-- Since 0.7.0.0
concat :: forall nat f' (m :: nat) f (n :: nat) a.
  (CFreeMonoid f, CFunctor f', CFoldable f', Dom f a, Dom f' (f a),
    Dom f' (Sized f n a)
  )
  => Sized f' m (Sized f n a) -> Sized f (m * n) a
concat = coerce $ cfoldMap @f' @(Sized f n a) runSized
{-# INLINE [2] concat #-}

--------------------------------------------------------------------------------
--- Zips
--------------------------------------------------------------------------------

-- | Zipping two sequences. Length is adjusted to shorter one.
--
-- Since 0.7.0.0
zip
  :: forall nat f (n :: nat) a (m :: nat) b.
    (Dom f a, CZip f, Dom f b, Dom f (a, b))
  => Sized f n a -> Sized f m b -> Sized f (Min n m) (a, b)
zip = coerce $ czip @f @a @b

-- | 'zip' for the sequences of the same length.
--
-- Since 0.7.0.0
zipSame
  :: forall nat f (n :: nat) a b.
      (Dom f a, CZip f, Dom f b, Dom f (a, b))
  => Sized f n a -> Sized f n b -> Sized f n (a, b)
zipSame = coerce $ czip @f @a @b
{-# INLINE [1] zipSame #-}

-- | Zipping two sequences with funtion. Length is adjusted to shorter one.
--
-- Since 0.7.0.0
zipWith
  :: forall nat f (n :: nat) a (m :: nat) b c.
    (Dom f a, CZip f, Dom f b, CFreeMonoid f, Dom f c)
  => (a -> b -> c)
  -> Sized f n a
  -> Sized f m b
  -> Sized f (Min n m) c
zipWith = coerce $ czipWith @f @a @b @c
{-# INLINE [1] zipWith #-}

-- | 'zipWith' for the sequences of the same length.
--
-- Since 0.7.0.0
zipWithSame
  :: forall nat f (n :: nat) a b c.
      (Dom f a, CZip f, Dom f b, CFreeMonoid f, Dom f c)
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

-- | Unzipping the sequence of tuples.
--
-- Since 0.7.0.0
unzip
  :: forall nat f (n :: nat) a b.
      (CUnzip f, Dom f a, Dom f b, Dom f (a, b))
  => Sized f n (a, b) -> (Sized f n a, Sized f n b)
unzip = coerce $ cunzip @f @a @b
{-# INLINE unzip #-}

-- | Unzipping the sequence of tuples.
--
-- Since 0.7.0.0
unzipWith
  :: forall nat f (n :: nat) a b c.
      (CUnzip f, Dom f a, Dom f b, Dom f c)
  => (a -> (b, c))
  -> Sized f n a -> (Sized f n b, Sized f n c)
unzipWith = coerce $ cunzipWith @f @a @b @c
{-# INLINE unzipWith #-}

--------------------------------------------------------------------------------
-- Transformation
--------------------------------------------------------------------------------

-- | Map function.
--
-- Since 0.7.0.0
map
  :: forall nat f (n :: nat) a b.
    (CFreeMonoid f, Dom f a, Dom f b)
  => (a -> b) -> Sized f n a -> Sized f n b
map f = Sized . cmap f . runSized
{-# INLINE map #-}

-- | Reverse function.
--
-- Since 0.7.0.0
reverse
  :: forall nat f (n :: nat) a.
    (Dom f a, CFreeMonoid f)
  => Sized f n a -> Sized f n a
reverse = coerce $ creverse @f @a
{-# INLINE reverse #-}

-- | Intersperces.
--
-- Since 0.7.0.0
intersperse
  :: forall nat f (n :: nat) a.
    (CFreeMonoid f, Dom f a)
  => a -> Sized f n a -> Sized f ((FromInteger 2 * n) -. One nat) a
intersperse = coerce $ cintersperse @f @a
{-# INLINE intersperse #-}

-- | Remove all duplicates.
--
-- Since 0.7.0.0
nub
  :: forall nat f (n :: nat) a.
      (HasOrdinal nat, Dom f a, Eq a, CFreeMonoid f)
  => Sized f n a -> SomeSized' f nat a
nub = toSomeSized . coerce (cnub @f @a)

-- | Sorting sequence by ascending order.
--
-- Since 0.7.0.0
sort :: forall nat f (n :: nat) a.
    (CFreeMonoid f, Dom f a, Ord a)
  => Sized f n a -> Sized f n a
sort = coerce $ csort @f @a

-- | Generalized version of 'sort'.
--
-- Since 0.7.0.0
sortBy
  :: forall nat f (n :: nat) a. (CFreeMonoid f, Dom f a)
  => (a -> a -> Ordering) -> Sized f n a -> Sized f n a
sortBy = coerce $ csortBy @f @a

-- | Insert new element into the presorted sequence.
--
-- Since 0.7.0.0
insert
  :: forall nat f (n :: nat) a.
    (CFreeMonoid f, Dom f a, Ord a)
  => a -> Sized f n a -> Sized f (Succ n) a
insert = coerce $ cinsert @f @a

-- | Generalized version of 'insert'.
--
-- Since 0.7.0.0
insertBy
  :: forall nat f (n :: nat) a.
    (CFreeMonoid f, Dom f a)
  => (a -> a -> Ordering) -> a -> Sized f n a -> Sized f (Succ n) a
insertBy = coerce $ cinsertBy @f @a

--------------------------------------------------------------------------------
-- Conversion
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
--- List
--------------------------------------------------------------------------------

-- | Convert to list.
--
-- Since 0.7.0.0
toList
  :: forall nat f (n :: nat) a.
    (CFoldable f, Dom f a)
  => Sized f n a -> [a]
toList = coerce $ ctoList @f @a
{-# INLINE [2] toList #-}

{-# RULES
"toList/List"
  Data.Sized.toList = runSized
  #-}

-- | If the given list is shorter than @n@, then returns @Nothing@
--   Otherwise returns @Sized f n a@ consisting of initial @n@ element
--   of given list.
--
--   Since 0.7.0.0 (type changed)
fromList
  :: forall nat f (n :: nat) a.
      (HasOrdinal nat, CFreeMonoid f, Dom f a)
  => Sing n -> [a] -> Maybe (Sized f n a)
fromList Zero _ = Just $ Sized (mempty :: f a)
fromList sn xs =
  let len = P.fromIntegral $ toNatural sn
  in if P.length xs < len
     then Nothing
     else Just $ Sized $ ctake len $ cfromList xs
{-# INLINABLE [2] fromList #-}

-- | 'fromList' with the result length inferred.
--
-- Since 0.7.0.0
fromList'
  :: forall nat f (n :: nat) a.
    (PeanoOrder nat, Dom f a, CFreeMonoid f, SingI n)
  => [a] -> Maybe (Sized f n a)
fromList' = withSing fromList
{-# INLINE fromList' #-}

-- | Unsafe version of 'fromList'. If the length of the given list does not
--   equal to @n@, then something unusual happens.
--
-- Since 0.7.0.0
unsafeFromList
  :: forall (nat :: Type) f (n :: nat) a.
    (CFreeMonoid f, Dom f a)
  => Sing n -> [a] -> Sized f n a
unsafeFromList = const $ coerce $ cfromList  @f @a
{-# INLINE [1] unsafeFromList #-}

-- | 'unsafeFromList' with the result length inferred.
--
-- Since 0.7.0.0
unsafeFromList'
  :: forall nat f (n :: nat) a.
      (SingI n, CFreeMonoid f, Dom f a)
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
  :: forall nat f (n :: nat) a.
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
  :: forall nat f (n :: nat) a. (PeanoOrder nat, SingI n, CFreeMonoid f, Dom f a)
  => a -> [a] -> Sized f n a
fromListWithDefault' = withSing fromListWithDefault
{-# INLINE fromListWithDefault' #-}

--------------------------------------------------------------------------------
--- Base containes
--------------------------------------------------------------------------------

-- | Forget the length and obtain the wrapped base container.
--
-- Since 0.7.0.0
unsized :: forall nat f (n :: nat) a. Sized f n a -> f a
unsized = runSized
{-# INLINE unsized #-}

-- | If the length of the input is shorter than @n@, then returns @Nothing@.
--   Otherwise returns @Sized f n a@ consisting of initial @n@ element
--   of the input.
--
-- Since 0.7.0.0
toSized
  :: forall nat f (n :: nat) a.
      (HasOrdinal nat, CFreeMonoid f, Dom f a)
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
  :: forall nat f (n :: nat) a.
    (PeanoOrder nat, Dom f a, CFreeMonoid f, SingI n)
  => f a -> Maybe (Sized f n a)
toSized' = withSing toSized
{-# INLINE toSized' #-}

-- | Unsafe version of 'toSized'. If the length of the given list does not
--   equal to @n@, then something unusual happens.
--
-- Since 0.7.0.0
unsafeToSized :: forall nat f (n :: nat) a. Sing n -> f a -> Sized f n a
unsafeToSized _ = Sized
{-# INLINE [2] unsafeToSized #-}

-- | 'unsafeToSized' with the result length inferred.
--
-- Since 0.7.0.0
unsafeToSized'
  :: forall nat f (n :: nat) a.
    (SingI n, Dom f a)
  => f a -> Sized f n a
unsafeToSized' = withSing unsafeToSized
{-# INLINE unsafeToSized' #-}

-- | Construct a @Sized f n a@ by padding default value if the given list is short.
--
-- Since 0.7.0.0
toSizedWithDefault
  :: forall nat f (n :: nat) a.
    (HasOrdinal nat, CFreeMonoid f, Dom f a)
  => Sing (n :: nat) -> a -> f a -> Sized f n a
toSizedWithDefault sn def xs =
  let len = P.fromIntegral $ toNatural sn
  in Sized $ ctake len xs <> creplicate (len - clength xs) def
{-# INLINABLE toSizedWithDefault #-}

-- | 'toSizedWithDefault' with the result length inferred.
--
-- Since 0.7.0.0
toSizedWithDefault'
  :: forall nat f (n :: nat) a.
      (PeanoOrder nat, SingI n, CFreeMonoid f, Dom f a)
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
              -> Sized f n a
              -> Sing m
              -> Sized f m a
              -> Partitioned f (n + m) a

-- | Take the initial segment as long as elements satisfys the predicate.
--
-- Since 0.7.0.0
takeWhile
  :: forall nat f (n :: nat) a.
    (HasOrdinal nat, Dom f a, CFreeMonoid f)
  => (a -> Bool) -> Sized f n a -> SomeSized' f nat a
takeWhile = (toSomeSized .) . coerce (ctakeWhile @f @a)
{-# INLINE takeWhile #-}

-- | Drop the initial segment as long as elements satisfys the predicate.
--
-- Since 0.7.0.0
dropWhile
  :: forall nat f (n :: nat) a.
      (HasOrdinal nat, CFreeMonoid f, Dom f a)
  => (a -> Bool) -> Sized f n a -> SomeSized' f nat a
dropWhile = (toSomeSized .) . coerce (cdropWhile @f @a)
{-# INLINE dropWhile #-}

-- | Split the sequence into the longest prefix
--   of elements that satisfy the predicate
--   and the rest.
--
-- Since 0.7.0.0
span
  :: forall nat f (n :: nat) a.
      (HasOrdinal nat, CFreeMonoid f, Dom f a)
  => (a -> Bool) -> Sized f n a -> Partitioned f n a
span = (unsafePartitioned @nat @n .) . coerce (cspan @f @a)
{-# INLINE span #-}

-- | Split the sequence into the longest prefix
--   of elements that do not satisfy the
--   predicate and the rest.
--
-- Since 0.7.0.0
break
  :: forall nat f (n :: nat) a.
      (HasOrdinal nat, CFreeMonoid f, Dom f a)
  => (a -> Bool) -> Sized f n a -> Partitioned f n a
break = (unsafePartitioned @nat @n .) . coerce (cbreak @f @a)
{-# INLINE break #-}

-- | Split the sequence in two parts, the first one containing those elements that satisfy the predicate and the second one those that don't.
--
-- Since 0.7.0.0
partition
  :: forall nat f (n :: nat) a.
      (HasOrdinal nat, CFreeMonoid f, Dom f a)
  => (a -> Bool) -> Sized f n a -> Partitioned f n a
partition = (unsafePartitioned @nat @n .) . coerce (cpartition @f @a)
{-# INLINE partition #-}

unsafePartitioned
  :: forall nat (n :: nat) f a.
    (HasOrdinal nat, CFreeMonoid f, Dom f a)
  => (f a, f a) -> Partitioned f n a
unsafePartitioned (l, r) =
  case (toSomeSized @nat l, toSomeSized @nat r) of
    ( SomeSized' (lenL :: Sing nl) ls,
      SomeSized' (lenR :: Sing nr) rs
      ) ->
        gcastWith
        (unsafeCoerce $ Refl @()
          :: n :~: nl + nr
        )
        $ Partitioned lenL ls lenR rs

--------------------------------------------------------------------------------
--- Searching
--------------------------------------------------------------------------------
-- | Membership test; see also 'notElem'.
--
-- Since 0.7.0.0
elem
  :: forall nat f (n :: nat) a.
    (CFoldable f, Dom f a, Eq a)
  => a -> Sized f n a -> Bool
elem = coerce $ celem @f @a
{-# INLINE elem #-}

-- | Negation of 'elem'.
--
-- Since 0.7.0.0
notElem
  :: forall nat f (n :: nat) a.
    (CFoldable f, Dom f a, Eq a)
  => a -> Sized f n a -> Bool
notElem = coerce $ cnotElem @f @a
{-# INLINE notElem #-}

-- | Find the element satisfying the predicate.
--
-- Since 0.7.0.0
find
  :: forall nat f (n :: nat) a.
      (CFoldable f, Dom f a)
  => (a -> Bool) -> Sized f n a -> Maybe a
find = coerce $ cfind @f @a
{-# INLINE[1] find #-}
{-# RULES
"find/List" [~1] forall p.
  find p = L.find @[] p . runSized
"find/Vector" [~1] forall p.
  find p = V.find p . runSized
"find/Storable Vector" [~1] forall (p :: SV.Storable a => a -> Bool).
  find p = SV.find p . runSized
"find/Unboxed Vector" [~1] forall (p :: UV.Unbox a => a -> Bool).
  find p = UV.find p . runSized
  #-}

-- | @'findIndex' p xs@ find the element satisfying @p@ and returns its index if exists.
--
-- Since 0.7.0.0
findIndex
  :: forall nat f (n :: nat) a .
    (CFoldable f, Dom f a)
  => (a -> Bool) -> Sized f n a -> Maybe Int
findIndex = coerce $ cfindIndex @f @a
{-# INLINE findIndex #-}

-- | 'Ordinal' version of 'findIndex'.
--
-- Since 0.7.0.0
sFindIndex
  :: forall nat f (n :: nat) a .
    (SingI (n :: nat), CFoldable f, Dom f a, HasOrdinal nat)
  => (a -> Bool) -> Sized f n a -> Maybe (Ordinal n)
sFindIndex = (fmap toEnum .) . coerce (cfindIndex @f @a)
{-# INLINE sFindIndex #-}

-- | @'findIndices' p xs@ find all elements satisfying @p@ and returns their indices.
--
-- Since 0.7.0.0
findIndices
  :: forall nat f (n :: nat) a .
    (CFoldable f, Dom f a) => (a -> Bool) -> Sized f n a -> [Int]
findIndices = coerce $ cfindIndices @f @a
{-# INLINE findIndices #-}
{-# SPECIALISE findIndices :: (a -> Bool) -> Sized [] n a -> [Int] #-}

-- | 'Ordinal' version of 'findIndices'.
--
-- Since 0.7.0.0
sFindIndices
  :: forall nat f (n :: nat) a .
    (HasOrdinal nat, CFoldable f, Dom f a, SingI (n :: nat))
  => (a -> Bool) -> Sized f n a -> [Ordinal n]
sFindIndices p = P.fmap (toEnum . P.fromIntegral) . findIndices p
{-# INLINE sFindIndices #-}


{-# RULES
"Foldable.sum/Vector"
  F.sum = V.sum . runSized
  #-}

-- | Returns the index of the given element in the list, if exists.
--
-- Since 0.7.0.0
elemIndex :: forall nat f (n :: nat) a .
  (CFoldable f, Eq a, Dom f a) => a -> Sized f n a -> Maybe Int
elemIndex = coerce $ celemIndex @f @a
{-# INLINE elemIndex #-}

-- | Ordinal version of 'elemIndex'.
--   Since 0.7.0.0, we no longer do boundary check inside the definition.
--
--   Since 0.7.0.0
sElemIndex, sUnsafeElemIndex :: forall nat f (n :: nat) a.
              (SingI n, CFoldable f, Dom f a, Eq a, HasOrdinal nat)
           => a -> Sized f n a -> Maybe (Ordinal n)
sElemIndex = (fmap toEnum .) . coerce (celemIndex @f @a)
{-# INLINE sElemIndex #-}

-- | Since 0.5.0.0 (type changed)
sUnsafeElemIndex = sElemIndex
{-# DEPRECATED sUnsafeElemIndex "No difference with sElemIndex; use sElemIndex instead." #-}

-- | Returns all indices of the given element in the list.
--
-- Since 0.7.0.0
elemIndices
  :: forall nat f (n :: nat) a .
    (CFoldable f, Dom f a, Eq a) => a -> Sized f n a -> [Int]
elemIndices = coerce $ celemIndices @f @a
{-# INLINE elemIndices #-}

-- | Ordinal version of 'elemIndices'
--
-- Since 0.7.0.0
sElemIndices
  :: forall nat f (n :: nat) a .
    (CFoldable f, HasOrdinal nat, SingI (n :: nat), Dom f a, Eq a)
  => a -> Sized f n a -> [Ordinal n]
sElemIndices = (fmap toEnum .) . elemIndices
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
  (:-) :: SingI n => a -> Sized f n a -> ConsView f (One nat + n) a

infixr 5 :-

-- | Case analysis for the cons-side of sequence.
--
-- Since 0.5.0.0 (type changed)
viewCons :: forall nat f (n :: nat) a .
  (HasOrdinal nat, SingI n, CFreeMonoid f,Dom f a)
  => Sized f n a
  -> ConsView f n a
viewCons sz = case zeroOrSucc $ sing @n of
  IsZero -> NilCV
  IsSucc n' ->
    withSingI n'
    $ withSingI (sOne %+ n')
    $ case uncons' n' sz of
        Uncons a xs -> a :- xs

-- | View of the left end of sequence (snoc-side).
--
-- Since 0.7.0.0
data SnocView f n a where
  NilSV :: SnocView f (Zero nat) a
  (:-::) :: SingI (n :: nat) => Sized f n a -> a -> SnocView f (n + One nat) a
infixl 5 :-::

-- | Case analysis for the snoc-side of sequence.
--
-- Since 0.5.0.0 (type changed)
viewSnoc :: forall nat f (n :: nat) a.
    (HasOrdinal nat, SingI n, CFreeMonoid f, Dom f a)
         => Sized f n a
         -> SnocView f n a
viewSnoc sz = case zeroOrSucc (sing @n) of
  IsZero   -> NilSV
  IsSucc (n' :: Sing n') ->
    withSingI n' $
    gcastWith (succAndPlusOneR n') $
    case unsnoc' n' sz of
      Unsnoc (xs :: Sized f m a) a ->
        gcastWith
          (unsafeCoerce (Refl @()) :: n' :~: m)
        $ xs :-:: a

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
pattern (:<)
  :: forall nat (f :: Type -> Type) a (n :: nat).
      (Dom f a, PeanoOrder nat, SingI n, CFreeMonoid f)
  => forall (n1 :: nat). (n ~ (One nat + n1), SingI n1)
  => a -> Sized f n1 a -> Sized f n a
pattern a :< as <- (viewCons -> a :- as) where
   a :< as = a <| as

pattern NilL :: forall nat f (n :: nat) a.
                (SingI n, CFreeMonoid f, Dom f a,  HasOrdinal nat)
             => (n ~ Zero nat) => Sized f n a
pattern NilL   <- (viewCons -> NilCV) where
  NilL = empty

infixl 5 :>

pattern (:>)
  :: forall nat (f :: Type -> Type) a (n :: nat).
      (Dom f a, PeanoOrder nat, SingI n, CFreeMonoid f)
  => forall (n1 :: nat). (n ~ (n1 + One nat), SingI n1)
  => Sized f n1 a -> a -> Sized f n a
pattern a :> b <- (viewSnoc -> a :-:: b) where
  a :> b = a |> b

pattern NilR :: forall nat f (n :: nat) a.
                (SingI n, CFreeMonoid f, Dom f a,  HasOrdinal nat)
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

instance (CFreeMonoid f, PeanoOrder nat, SingI (n :: nat))
      => CPointed (Sized f n) where
  cpure = replicate'

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

instance CTraversable f => CTraversable (Sized f n) where
  ctraverse = \f -> fmap coerce . ctraverse f . runSized
  {-# INLINE ctraverse #-}
