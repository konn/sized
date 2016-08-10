{-# LANGUAGE AllowAmbiguousTypes, ConstraintKinds, DataKinds               #-}
{-# LANGUAGE DeriveDataTypeable, DeriveFoldable, DeriveFunctor             #-}
{-# LANGUAGE DeriveTraversable, ExplicitNamespaces, FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances, GADTs, GeneralizedNewtypeDeriving          #-}
{-# LANGUAGE KindSignatures, LambdaCase, LiberalTypeSynonyms               #-}
{-# LANGUAGE MultiParamTypeClasses, NoMonomorphismRestriction              #-}
{-# LANGUAGE PatternSynonyms, PolyKinds, ScopedTypeVariables               #-}
{-# LANGUAGE StandaloneDeriving, TypeApplications, TypeFamilies            #-}
{-# LANGUAGE TypeInType, TypeOperators, UndecidableInstances, ViewPatterns #-}
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
         instLL, instFunctor, ListLikeF,
         withListLikeF, withListLikeF',
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
         empty, singleton, toSomeSized, replicate, replicate',
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
import qualified Data.List                    as L
import           Data.ListLike                (ListLike)
import qualified Data.ListLike                as LL
import           Data.Monoid                  (Endo (..), First (..))
import qualified Data.Sequence                as Seq
import           Data.Singletons.Prelude      (PNum (..), POrd (..), SOrd (..))
import           Data.Singletons.Prelude      (Sing (..), SingI (..))
import           Data.Singletons.Prelude      (withSing, withSingI)
import           Data.Singletons.Prelude.Enum (PEnum (..))
import           Data.Type.Monomorphic        (Monomorphic (..))
import           Data.Type.Monomorphic        (Monomorphicable (..))
import qualified Data.Type.Natural            as Peano
import           Data.Type.Natural.Class
import           Data.Type.Ordinal            (HasOrdinal, Ordinal (..))
import           Data.Type.Ordinal            (ordToInt, unsafeFromInt)
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
data SomeSized f nat a where
  SomeSized :: (ListLike (f a) a)
            => Sing n
            -> Sized f (n :: nat) a
            -> SomeSized f nat a

deriving instance Typeable SomeSized

instance Show (f a) => Show (SomeSized f nat a) where
  showsPrec d (SomeSized _ s) = P.showParen (d > 9) $
    P.showString "SomeSized _ " . showsPrec 10 s
instance Eq (f a) => Eq (SomeSized f nat a) where
  (SomeSized _ (Sized xs)) == (SomeSized _ (Sized ys)) = xs == ys

demote' :: HasOrdinal nat => Sing (n :: nat) -> MonomorphicRep (Sing :: nat -> Type)
demote' = demote . Monomorphic
{-# SPECIALISE demote' :: Sing (n :: TL.Nat) -> P.Integer #-}
{-# SPECIALISE demote' :: Sing (n :: Peano.Nat) -> P.Integer #-}

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
length :: ListLike (f a) a => Sized f n a -> Int
length = LL.length . runSized
{-# INLINE [1] length #-}
{-# RULES
"length/0" [~1] forall (xs :: Sized f 0 a).
  length xs = 0
"length/Z" [~1] forall (xs :: Sized f 'Peano.Z a).
  length xs = 0
  #-}

-- | @Sing@ version of 'length'.
--
-- Since 0.2.0.0
sLength :: forall f (n :: nat) a. (HasOrdinal nat, ListLike (f a) a)
        => Sized f n a -> Sing n
sLength (Sized xs) =
  case promote (P.fromIntegral $ LL.length xs) of
    Monomorphic (n :: Sing (k :: nat)) -> unsafeCoerce n
{-# INLINE[2] sLength #-}
{-# RULES
"sLength/KnownNat" [~1] forall (xs :: TL.KnownNat n => Sized f n a).
  sLength xs = sing :: Sing n
"sLength/SingI" [~2] forall (xs :: SingI n => Sized f n a).
  sLength xs = sing :: Sing n
  #-}

-- | Test if the sequence is empty or not.
--
-- Since 0.1.0.0
null :: ListLike (f a) a => Sized f n a -> Bool
null = LL.null . runSized
{-# INLINE CONLIKE [1] null #-}
{-# RULES
"null/0" [~1] forall (xs :: Sized f 0 a).
  null xs = True

"null/Z" [~1] forall (xs :: Sized f 'Peano.Z a).
  null xs = True
#-}

--------------------------------------------------------------------------------
--- Indexing
--------------------------------------------------------------------------------

-- | (Unsafe) indexing with @Int@s.
--   If you want to check boundary statically, use '%!!' or 'sIndex'.
--
-- Since 0.1.0.0
(!!) :: (ListLike (f a) a) => Sized f (Succ m) a -> Int -> a
Sized xs !! n = LL.index xs n
{-# INLINE (!!) #-}

-- | Safe indexing with 'Ordinal's.
--
-- Since 0.1.0.0
(%!!) :: (HasOrdinal nat, LL.ListLike (f c) c) => Sized f n c -> Ordinal (n :: nat) -> c
Sized xs %!! n = LL.index xs $ P.fromIntegral $ ordToInt n
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
-- Since 0.1.0.0
index :: (ListLike (f a) a) => Int -> Sized f (Succ m) a -> a
index n (Sized xs) =  LL.index xs n
{-# INLINE index #-}

-- | Flipped version of '%!!'.
--
-- Since 0.1.0.0
sIndex :: (HasOrdinal nat, ListLike (f c) c) => Ordinal (n :: nat) -> Sized f n c -> c
sIndex = flip (%!!)
{-# INLINE sIndex #-}

-- | Take the first element of non-empty sequence.
--   If you want to make case-analysis for general sequence,
--   see  <#ViewsAndPatterns Views and Patterns> section.
--
-- Since 0.1.0.0
head :: (HasOrdinal nat, ListLike (f a) b, (Zero nat :< n) ~ 'True) => Sized f n a -> b
head = LL.head . runSized
{-# INLINE head #-}

-- | Take the last element of non-empty sequence.
--   If you want to make case-analysis for general sequence,
--   see  <#ViewsAndPatterns Views and Patterns> section.
--
-- Since 0.1.0.0
last :: (HasOrdinal nat, (Zero nat :< n) ~ 'True, ListLike (f a) b) => Sized f n a -> b
last = LL.last . runSized
{-# INLINE last #-}

-- | Take the 'head' and 'tail' of non-empty sequence.
--   If you want to make case-analysis for general sequence,
--   see  <#ViewsAndPatterns Views and Patterns> section.
--
-- Since 0.1.0.0
uncons :: ListLike (f a) b => Sized f (Succ n) a -> (b, Sized f n a)
uncons = ((,) <$> LL.head <*> Sized . LL.tail) . runSized
{-# INLINE [1] uncons #-}
{-# RULES
"uncons/[]" [~1] forall (x :: a) (xs:: [a]).
  uncons (Sized (x : xs)) = (x, Sized xs)
"uncons/Seq" [~1] forall (xs:: Seq.Seq a).
  uncons (Sized xs) =
    case Seq.viewl xs of { (x Seq.:< ys) -> (x, Sized ys)
                         ; _ -> P.error "Empty seq with non-zero index!"
                         }
  #-}

uncons' :: ListLike (f a) b => proxy n -> Sized f (Succ n) a -> (b, Sized f n a)
uncons' _  = uncons
{-# INLINE uncons' #-}

-- | Take the 'init' and 'last' of non-empty sequence.
--   If you want to make case-analysis for general sequence,
--   see  <#ViewsAndPatterns Views and Patterns> section.
--
-- Since 0.1.0.0
unsnoc :: ListLike (f a) b => Sized f (Succ n) a -> (Sized f n a, b)
unsnoc = ((,) <$> Sized . LL.init <*> LL.last) . runSized
{-# NOINLINE [1] unsnoc #-}
{-# RULES
"unsnoc/Seq" [~1] forall (xs:: Seq.Seq a).
  unsnoc (Sized xs) =
    case Seq.viewr xs of { (ys Seq.:> x) -> (Sized ys, x)
                         ; _ -> P.error "Empty seq with non-zero index!"
                         }
  #-}

unsnoc' :: ListLike (f a) b => proxy n -> Sized f (Succ n) a -> (Sized f n a, b)
unsnoc' _  = unsnoc
{-# INLINE unsnoc' #-}


--------------------------------------------------------------------------------
--- Slicing
--------------------------------------------------------------------------------

-- | Take the tail of non-empty sequence.
--   If you want to make case-analysis for general sequence,
--   see  <#ViewsAndPatterns Views and Patterns> section.
--
-- Since 0.1.0.0
tail :: (HasOrdinal nat, ListLike (f a) a)=> Sized f (Succ n) a -> Sized f (n :: nat) a
tail = Sized . LL.tail . runSized
{-# INLINE tail #-}

-- | Take the initial segment of non-empty sequence.
--   If you want to make case-analysis for general sequence,
--   see  <#ViewsAndPatterns Views and Patterns> section.
--
-- Since 0.1.0.0
init :: ListLike (f a) a => Sized f (Succ n) a -> Sized f n a
init = Sized . LL.init . runSized
{-# INLINE init #-}

-- | @take k xs@ takes first @k@ element of @xs@ where
-- the length of @xs@ should be larger than @k@.
-- It is really sad, that this function
-- takes at least O(k) regardless of base container.
--
-- Since 0.1.0.0
take :: (ListLike (f a) a, (n :<= m) ~ 'True, HasOrdinal nat)
     => Sing (n :: nat) -> Sized f m a -> Sized f n a
take sn = Sized . LL.genericTake (demote' sn) . runSized
{-# INLINE take #-}

-- | @take k xs@ takes first @k@ element of @xs@ at most.
-- It is really sad, that this function
-- takes at least O(k) regardless of base container.
--
-- Since 0.1.0.0
takeAtMost :: (ListLike (f a) a, HasOrdinal nat)
           => Sing (n :: nat) -> Sized f m a -> Sized f (Min n m) a
takeAtMost sn = Sized . LL.genericTake (demote $ Monomorphic sn) . runSized
{-# INLINE takeAtMost #-}

-- | @drop k xs@ drops first @k@ element of @xs@ and returns
-- the rest of sequence, where the length of @xs@ should be larger than @k@.
-- It is really sad, that this function
-- takes at least O(k) regardless of base container.
--
-- Since 0.1.0.0
drop :: (HasOrdinal nat, ListLike (f a) a, (n :<= m) ~ 'True)
     => Sing (n :: nat) -> Sized f m a -> Sized f (m :- n) a
drop sn = Sized . LL.genericDrop (demote' sn) . runSized
{-# INLINE drop #-}

-- | @splitAt k xs@ split @xs@ at @k@, where
-- the length of @xs@ should be less than or equal to @k@.
-- It is really sad, that this function
-- takes at least O(k) regardless of base container.
--
-- Since 0.1.0.0
splitAt :: (ListLike (f a) a , (n :<= m) ~ 'True, HasOrdinal nat)
        => Sing (n :: nat) -> Sized f m a -> (Sized f n a, Sized f (m :-. n) a)
splitAt n (Sized xs) =
  let (as, bs) = LL.genericSplitAt (demote' n) xs
  in (Sized as, Sized bs)
{-# INLINE splitAt #-}

-- | @splitAtMost k xs@ split @xs@ at @k@.
--   If @k@ exceeds the length of @xs@, then the second result value become empty.
-- It is really sad, that this function
-- takes at least O(k) regardless of base container.
--
-- Since 0.1.0.0
splitAtMost :: (HasOrdinal nat, ListLike (f a) a)
            => Sing (n :: nat) -> Sized f m a -> (Sized f (Min n m) a, Sized f (m :-. n) a)
splitAtMost n (Sized xs) =
  let (as, bs) = LL.genericSplitAt (demote' n) xs
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
empty :: forall f a. (HasOrdinal nat, ListLike (f a) a) => Sized f (Zero nat :: nat) a
empty = Sized LL.empty
{-# INLINE empty #-}

-- | Sequence with one element.
--
-- Since 0.1.0.0
singleton :: forall f a. ListLike (f a) a => a -> Sized f 1 a
singleton = Sized . LL.singleton
{-# INLINE singleton #-}

-- | Consruct the 'Sized' sequence from base type, but
--   the length parameter is dynamically determined and
--   existentially quantified; see also 'SomeSized'.
--
-- Since 0.1.0.0
toSomeSized :: forall nat f a. (HasOrdinal nat, ListLike (f a) a)
            => f a -> SomeSized f nat a
toSomeSized = \xs ->
  case promote $ LL.genericLength xs of
    Monomorphic sn -> withSingI sn $ SomeSized sn $ unsafeToSized sn xs

-- | Replicates the same value.
--
-- Since 0.1.0.0
replicate :: forall f (n :: nat) a. (HasOrdinal nat, ListLike (f a) a)
          => Sing n -> a -> Sized f n a
replicate sn a = Sized $ LL.genericReplicate (demote $ Monomorphic sn) a
{-# INLINE replicate #-}

-- | 'replicate' with the length inferred.
--
-- Since 0.1.0.0
replicate' :: (HasOrdinal nat, SingI (n :: nat), ListLike (f a) a) => a -> Sized f n a
replicate' = withSing replicate
{-# INLINE replicate' #-}

--------------------------------------------------------------------------------
--- Concatenation
--------------------------------------------------------------------------------

-- | Append an element to the head of sequence.
--
-- Since 0.1.0.0
cons :: (ListLike (f a) b) => b -> Sized f n a -> Sized f (Succ n) a
cons a = Sized . LL.cons a . runSized
{-# INLINE cons #-}

-- | Infix version of 'cons'.
--
-- Since 0.1.0.0
(<|) :: (ListLike (f a) b) => b -> Sized f n a -> Sized f (Succ n) a
(<|) = cons
{-# INLINE (<|) #-}
infixr 5 <|

-- | Append an element to the tail of sequence.
--
-- Since 0.1.0.0
snoc :: (ListLike (f a) b) => Sized f n a -> b -> Sized f (Succ n) a
snoc (Sized xs) a = Sized $ LL.snoc xs a
{-# INLINE snoc #-}

-- | Infix version of 'snoc'.
--
-- Since 0.1.0.0
(|>) :: (ListLike (f a) b) => Sized f n a -> b -> Sized f (Succ n) a
(|>) = snoc
{-# INLINE (|>) #-}
infixl 5 |>

-- | Append two lists.
--
-- Since 0.1.0.0
append :: ListLike (f a) a => Sized f n a -> Sized f m a -> Sized f (n :+ m) a
append (Sized xs) (Sized ys) = Sized $ LL.append xs ys
{-# INLINE append #-}

-- | Infix version of 'append'.
--
-- Since 0.1.0.0
(++) :: (ListLike (f a) a) => Sized f n a -> Sized f m a -> Sized f (n :+ m) a
(++) = append
infixr 5 ++

-- | Concatenates multiple sequences into one.
--
-- Since 0.1.0.0
concat :: forall f f' m n a. (Functor f', Foldable f', ListLike (f a) a)
       => Sized f' m (Sized f n a) -> Sized f (m :* n) a
concat =  Sized . F.foldr LL.append LL.empty . P.fmap runSized
{-# INLINE [2] concat #-}

{-# RULES
"concat/list-list" [~1] forall (xss :: [Sized [] n a]).
  concat (Sized xss) = Sized (L.concatMap runSized xss)
"concat/list-list" [~2] forall (xss :: (ListLike (f a) a, ListLike (f (Sized f n a)) (Sized f n a))
                                   => f (Sized f n a)).
  concat (Sized xss) = Sized (LL.concatMap runSized xss)
  #-}

--------------------------------------------------------------------------------
--- Zips
--------------------------------------------------------------------------------

-- | Zipping two sequences. Length is adjusted to shorter one.
--
-- Since 0.1.0.0
zip :: (ListLike (f a) a, ListLike (f b) b, ListLike (f (a, b)) (a, b))
    => Sized f n a -> Sized f m b -> Sized f (Min n m) (a, b)
zip (Sized xs) (Sized ys) = Sized $ LL.zip xs ys
{-# INLINE [1] zip #-}
{-# RULES
"zip/Seq" [~1] forall xs ys.
  zip (Sized xs) (Sized ys) = Sized (Seq.zip xs ys)
"zip/List" [~1] forall xs ys.
  zip (Sized xs) (Sized ys) = Sized (P.zip xs ys)
"zip/Vector" [~1] forall xs ys.
  zip (Sized xs) (Sized ys) = Sized (V.zip xs ys)
"zip/UVector" [~1]
  forall (xs :: UV.Unbox a => UV.Vector a) (ys :: UV.Unbox b => UV.Vector b).
  zip (Sized xs) (Sized ys) = Sized (UV.zip xs ys)
  #-}

-- | 'zip' for the sequences of the same length.
--
-- Since 0.1.0.0
zipSame :: (ListLike (f a) a, ListLike (f b) b, ListLike (f (a, b)) (a, b))
        => Sized f n a -> Sized f n b -> Sized f n (a, b)
zipSame (Sized xs) (Sized ys) = Sized $ LL.zip xs ys
{-# INLINE [1] zipSame #-}
{-# RULES
"zipSame/Seq" [~1] forall xs ys.
  zipSame (Sized xs) (Sized ys) = Sized (Seq.zip xs ys)
"zipSame/List" [~1] forall xs ys.
  zipSame (Sized xs) (Sized ys) = Sized (P.zip xs ys)
"zipSame/Vector" [~1] forall xs ys.
  zipSame (Sized xs) (Sized ys) = Sized (V.zip xs ys)
"zipSame/UVector" [~1]
  forall (xs :: UV.Unbox a => UV.Vector a) (ys :: UV.Unbox b => UV.Vector b).
  zipSame (Sized xs) (Sized ys) = Sized (UV.zip xs ys)
  #-}

-- | Zipping two sequences with funtion. Length is adjusted to shorter one.
--
-- Since 0.1.0.0
zipWith :: (ListLike (f a) a, ListLike (f b) b, ListLike (f c) c)
    => (a -> b -> c) -> Sized f n a -> Sized f m b -> Sized f (Min n m) c
zipWith f (Sized xs) (Sized ys) = Sized $ LL.zipWith f xs ys
{-# INLINE [1] zipWith #-}

{-# RULES
"zipWith/Seq" [~1] forall f xs ys.
  zipWith f (Sized xs) (Sized ys) = Sized (Seq.zipWith f xs ys)
"zipWith/List" [~1] forall f xs ys.
  zipWith f (Sized xs) (Sized ys) = Sized (P.zipWith f xs ys)
"zipWith/Vector" [~1] forall f xs ys.
  zipWith f (Sized xs) (Sized ys) = Sized (V.zipWith f xs ys)
"zipWith/UVector" [~1]
  forall (f :: (UV.Unbox a, UV.Unbox b, UV.Unbox c) => a -> b -> c)
    xs ys.
  zipWith f (Sized xs) (Sized ys) = Sized (UV.zipWith f xs ys)
"zipWith/MVector" [~1]
  forall (f :: (SV.Storable a, SV.Storable b, SV.Storable c) => a -> b -> c)
    xs ys.
  zipWith f (Sized xs) (Sized ys) = Sized (SV.zipWith f xs ys)
  #-}

-- | 'zipWith' for the sequences of the same length.
--
-- Since 0.1.0.0
zipWithSame :: (ListLike (f a) a, ListLike (f b) b, ListLike (f c) c)
            => (a -> b -> c) -> Sized f n a -> Sized f n b -> Sized f n c
zipWithSame f (Sized xs) (Sized ys) = Sized $ LL.zipWith f xs ys
{-# INLINE [1] zipWithSame #-}

{-# RULES
"zipWithSame/Seq" [~1] forall f xs ys.
  zipWithSame f (Sized xs) (Sized ys) = Sized (Seq.zipWith f xs ys)
"zipWithSame/List" [~1] forall f xs ys.
  zipWithSame f (Sized xs) (Sized ys) = Sized (P.zipWith f xs ys)
"zipWithSame/Vector" [~1] forall f xs ys.
  zipWithSame f (Sized xs) (Sized ys) = Sized (V.zipWith f xs ys)
"zipWithSame/UVector" [~1]
  forall (f :: (UV.Unbox a, UV.Unbox b, UV.Unbox c) => a -> b -> c)
    xs ys.
  zipWithSame f (Sized xs) (Sized ys) = Sized (UV.zipWith f xs ys)
"zipWithSame/MVector" [~1]
  forall (f :: (SV.Storable a, SV.Storable b, SV.Storable c) => a -> b -> c)
    xs ys.
  zipWithSame f (Sized xs) (Sized ys) = Sized (SV.zipWith f xs ys)
  #-}

-- | Unzipping the sequence of tuples.
--
-- Since 0.1.0.0
unzip :: (ListLike (f a) a, ListLike (f b) b, ListLike (f (a, b)) (a,b))
      => Sized f n (a, b) -> (Sized f n a, Sized f n b)
unzip (Sized xys) =
  let (xs, ys) = LL.unzip xys
  in (Sized xs, Sized ys)
{-# INLINE unzip #-}


--------------------------------------------------------------------------------
-- Transformation
--------------------------------------------------------------------------------

-- | Map function.
--
-- Since 0.1.0.0
map :: (ListLike (f a) a, ListLike (f b) b) => (a -> b) -> Sized f n a -> Sized f n b
map f = Sized . LL.map f . runSized
{-# INLINE map #-}

fmap :: forall f n a b. Functor f => (a -> b) -> Sized f n a -> Sized f n b
fmap f = Sized . P.fmap f . runSized
{-# INLINE fmap #-}

-- | Reverse function.
--
-- Since 0.1.0.0
reverse :: ListLike (f a) a => Sized f n a -> Sized f n a
reverse = Sized .  LL.reverse . runSized
{-# INLINE reverse #-}

-- | Intersperces.
--
-- Since 0.1.0.0
intersperse :: ListLike (f a) a => a -> Sized f n a -> Sized f ((FromInteger 2 :* n) :-. 1) a
intersperse a = Sized . LL.intersperse a . runSized
{-# INLINE intersperse #-}

-- | Remove all duplicates.
--
-- Since 0.1.0.0
nub :: (HasOrdinal nat, ListLike (f a) a, Eq a) => Sized f n a -> SomeSized f nat a
nub = toSomeSized . LL.nub . runSized

-- | Sorting sequence by ascending order.
--
-- Since 0.1.0.0
sort :: (ListLike (f a) a, Ord a)
     => Sized f n a -> Sized f n a
sort = Sized . LL.sort . runSized

-- | Generalized version of 'sort'.
--
-- Since 0.1.0.0
sortBy :: (ListLike (f a) a) => (a -> a -> Ordering) -> Sized f n a -> Sized f n a
sortBy cmp = Sized . LL.sortBy cmp . runSized

-- | Insert new element into the presorted sequence.
--
-- Since 0.1.0.0
insert :: (ListLike (f a) a, Ord a) => a -> Sized f n a -> Sized f (Succ n) a
insert a = Sized . LL.insert a . runSized

-- | Generalized version of 'insert'.
--
-- Since 0.1.0.0
insertBy :: (ListLike (f a) a) => (a -> a -> Ordering) -> a -> Sized f n a -> Sized f (Succ n) a
insertBy cmp a = Sized . LL.insertBy cmp a . runSized


--------------------------------------------------------------------------------
-- Conversion
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
--- List
--------------------------------------------------------------------------------

-- | Convert to list.
--
-- Since 0.1.0.0
toList :: ListLike (f a) a => Sized f n a -> [a]
toList = LL.toList . runSized
{-# INLINE [2] toList #-}

{-# RULES
"toList/" forall (xs :: Sized [] a n).
  Data.Sized.toList xs = runSized xs
  #-}

-- | If the given list is shorter than @n@, then returns @Nothing@
--   Otherwise returns @Sized f n a@ consisting of initial @n@ element
--   of given list.
--
-- Since 0.1.0.0
fromList :: forall f n a. (HasOrdinal nat, ListLike (f a) a)
         => Sing (n :: nat) -> [a] -> Maybe (Sized f n a)
fromList Zero _ = Just $ Sized (LL.empty :: f a)
fromList sn xs =
  let len = P.fromIntegral $ demote $ Monomorphic sn
  in if P.length xs < len
     then Nothing
     else Just $ unsafeFromList sn $ P.take len xs
{-# INLINABLE [2] fromList #-}

-- | 'fromList' with the result length inferred.
--
-- Since 0.1.0.0
fromList' :: (ListLike (f a) a, SingI (n :: TL.Nat)) => [a] -> Maybe (Sized f n a)
fromList' = withSing fromList
{-# INLINE fromList' #-}

-- | Unsafe version of 'fromList'. If the length of the given list does not
--   equal to @n@, then something unusual happens.
--
-- Since 0.1.0.0
unsafeFromList :: forall f n a. ListLike (f a) a => Sing n -> [a] -> Sized f n a
unsafeFromList _ xs = Sized $ LL.fromList xs
{-# INLINE [2] unsafeFromList #-}

-- | 'unsafeFromList' with the result length inferred.
--
-- Since 0.1.0.0
unsafeFromList' :: (SingI (n :: TL.Nat), ListLike (f a) a) => [a] -> Sized f n a
unsafeFromList' = withSing unsafeFromList
{-# INLINE unsafeFromList' #-}

-- | Construct a @Sized f n a@ by padding default value if the given list is short.
--
-- Since 0.1.0.0
fromListWithDefault :: forall f (n :: nat) a. (HasOrdinal nat, ListLike (f a) a)
                    => Sing n -> a -> [a] -> Sized f n a
fromListWithDefault sn def xs =
  let len = demote' sn
  in Sized $ LL.fromList (L.genericTake len xs) `LL.append` LL.genericReplicate (len - L.genericLength xs) def
{-# INLINABLE fromListWithDefault #-}

-- | 'fromListWithDefault' with the result length inferred.
--
-- Since 0.1.0.0
fromListWithDefault' :: (SingI (n :: TL.Nat), ListLike (f a) a) => a -> [a] -> Sized f n a
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
toSized :: (HasOrdinal nat, ListLike (f a) a)
        => Sing (n :: nat) -> f a -> Maybe (Sized f n a)
toSized sn xs =
  let len = demote' sn
  in if LL.genericLength xs < len
     then Nothing
     else Just $ unsafeToSized sn $ LL.genericTake len xs
{-# INLINABLE [2] toSized #-}

-- | 'toSized' with the result length inferred.
--
-- Since 0.1.0.0
toSized' :: (ListLike (f a) a, SingI (n :: TL.Nat)) => f a -> Maybe (Sized f n a)
toSized' = withSing toSized
{-# INLINE toSized' #-}

-- | Unsafe version of 'toSized'. If the length of the given list does not
--   equal to @n@, then something unusual happens.
--
-- Since 0.1.0.0
unsafeToSized :: Sing n -> f a -> Sized f n a
unsafeToSized _ = Sized
{-# INLINE [2] unsafeToSized #-}

-- | 'unsafeToSized' with the result length inferred.
--
-- Since 0.1.0.0
unsafeToSized' :: (SingI (n :: TL.Nat), ListLike (f a) a) => f a -> Sized f n a
unsafeToSized' = withSing unsafeToSized
{-# INLINE unsafeToSized' #-}

-- | Construct a @Sized f n a@ by padding default value if the given list is short.
--
-- Since 0.1.0.0
toSizedWithDefault :: (HasOrdinal nat, ListLike (f a) a)
                   => Sing (n :: nat) -> a -> f a -> Sized f n a
toSizedWithDefault sn def xs =
  let len = P.fromIntegral $ demote (Monomorphic sn)
  in Sized $ LL.take len xs `LL.append` LL.replicate (len - LL.length xs) def
{-# INLINABLE toSizedWithDefault #-}

-- | 'toSizedWithDefault' with the result length inferred.
--
-- Since 0.1.0.0
toSizedWithDefault' :: (SingI (n :: TL.Nat), ListLike (f a) a) => a -> f a -> Sized f n a
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
  Partitioned :: (ListLike (f a) a)
              => Sing n
              -> Sized f (n :: TL.Nat) a
              -> Sing m
              -> Sized f (m :: TL.Nat) a
              -> Partitioned f (n :+ m) a

-- | Take the initial segment as long as elements satisfys the predicate.
--
-- Since 0.1.0.0
takeWhile :: (HasOrdinal nat, ListLike (f a) a)
          => (a -> Bool) -> Sized f n a -> SomeSized f nat a
takeWhile p = toSomeSized . LL.takeWhile p . runSized
{-# INLINE takeWhile #-}

-- | Drop the initial segment as long as elements satisfys the predicate.
--
-- Since 0.1.0.0
dropWhile :: (HasOrdinal nat, ListLike (f a) a)
          => (a -> Bool) -> Sized f n a -> SomeSized f nat a
dropWhile p = toSomeSized . LL.dropWhile p . runSized
{-# INLINE dropWhile #-}

-- | Invariant: @'ListLike' (f a) a@ instance must be implemented
-- to satisfy the following property:
-- @length (fst (span p xs)) + length (snd (span p xs)) == length xs@
-- Otherwise, this function introduces severe contradiction.
--
-- Since 0.1.0.0
span :: ListLike (f a) a
     => (a -> Bool) -> Sized f n a -> Partitioned f n a
span p xs =
  let (as, bs) = LL.span p $ runSized xs
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
break :: ListLike (f a) a
     => (a -> Bool) -> Sized f n a -> Partitioned f n a
break p (Sized xs) =
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
partition :: ListLike (f a) a
     => (a -> Bool) -> Sized f n a -> Partitioned f n a
partition p (Sized xs) =
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
elem :: (ListLike (f a) a, Eq a) => a -> Sized f n a -> Bool
elem a = LL.elem a . runSized
{-# INLINE elem #-}

-- | Negation of 'elem'.
--
-- Since 0.1.0.0
notElem :: (ListLike (f a) a, Eq a) => a -> Sized f n a -> Bool
notElem a = LL.notElem a . runSized
{-# INLINE notElem #-}

-- | Find the element satisfying the predicate.
--
-- Since 0.1.0.0
find :: Foldable f => (a -> Bool) -> Sized f n a -> Maybe a
find p = F.find p
{-# INLINE[1] find #-}
{-# RULES
"find/List" [~1] forall p (xs :: [a]).
  find p (Sized xs) = L.find p xs
"find/Vector" [~1] forall p xs.
  find p (Sized xs) = V.find p xs
"find/Storable Vector" [~1] forall p (xs :: SV.Storable a => SV.Vector a).
  find p (Sized xs) = SV.find p xs
"find/Unboxed Vector" [~1] forall p (xs :: UV.Unbox a => UV.Vector a).
  find p (Sized xs) = UV.find p xs
  #-}

-- | @'Foldable'@ version of @'find'@.
findF :: (Foldable f) => (a -> Bool) -> Sized f n a -> Maybe a
findF p = getFirst. F.foldMap (\a -> if p a then First (Just a) else First Nothing) . runSized
{-# INLINE [1] findF #-}
{-# SPECIALISE [0] findF :: (a -> Bool) -> Sized Seq.Seq n a -> Maybe a #-}
{-# RULES
"findF/list" [~1] forall p.
  findF p = L.find p
  #-}

-- | @'findIndex' p xs@ find the element satisfying @p@ and returns its index if exists.
--
-- Since 0.1.0.0
findIndex :: ListLike (f a) a => (a -> Bool) -> Sized f n a -> Maybe Int
findIndex p = LL.findIndex p . runSized
{-# INLINE findIndex #-}

-- | 'Ordinal' version of 'findIndex'.
--
-- Since 0.1.0.0
sFindIndex :: (SingI (n :: nat), ListLike (f a) a, HasOrdinal nat)
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
-- {-# RULES
-- "sFindIndexIF/list" [~1] forall p .
--   sFindIndexIF p = P.fmap toEnum . L.findIndex p . runSized
-- "sFindIndexIF/vector" [~1] forall p.
--   sFindIndexIF p = P.fmap toEnum . V.findIndex p . runSized
--   #-}

-- | @'findIndices' p xs@ find all elements satisfying @p@ and returns their indices.
--
-- Since 0.1.0.0
findIndices :: ListLike (f a) a => (a -> Bool) -> Sized f n a -> [Int]
findIndices p = LL.findIndices p . runSized
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
-- Since 0.1.0.0
sFindIndices :: (HasOrdinal nat, SingI (n :: nat), ListLike (f a) a)
             => (a -> Bool) -> Sized f n a -> [Ordinal n]
sFindIndices p = P.fmap (toEnum . P.fromIntegral) . findIndices p
{-# INLINE sFindIndices #-}

sFindIndicesIF :: (FoldableWithIndex i f, P.Integral i, HasOrdinal nat, SingI n)
               => (a -> Bool) -> Sized f (n :: nat) a -> [Ordinal n]
sFindIndicesIF p = flip appEndo [] .
                   ifoldMap (\i x -> if p x then Endo (P.toEnum (P.fromIntegral i):) else Endo P.id) .
                   runSized
{-# INLINE [1] sFindIndicesIF #-}
-- {-# RULES
-- "sFindIndicesIF/list" [~1] forall p.
--   sFindIndicesIF p = P.map toEnum . L.findIndices p . runSized
-- "sFindIndicesIF/vector" [~1] forall p.
--   sFindIndicesIF p = V.toList . V.map toEnum . V.findIndices p . runSized
--   #-}

-- | Returns the index of the given element in the list, if exists.
--
-- Since 0.1.0.0
elemIndex :: (Eq a, ListLike (f a) a) => a -> Sized f n a -> Maybe Int
elemIndex a (Sized xs) = LL.elemIndex a xs
{-# INLINE elemIndex #-}

-- | Ordinal version of 'elemIndex'
--   It statically checks boundary invariants.
--   If you don't internal structure on @'Sized'@,
--   then @'sUnsafeElemIndex'@ is much faster and
--   also safe for most cases.
--
--   Since 0.1.0.0
sElemIndex :: forall (n :: nat) f a.
              (SingI n, ListLike (f a) a, Eq a, HasOrdinal nat)
           => a -> Sized f n a -> Maybe (Ordinal n)
sElemIndex a (Sized xs) = do
  i <- LL.elemIndex a xs
  case promote (P.fromIntegral i) of
    Monomorphic sn ->
      case sn %:< (sing :: Sing n) of
        STrue  -> Just (OLt sn)
        SFalse -> Nothing
{-# INLINE sElemIndex #-}

sUnsafeElemIndex :: forall (n :: nat) f a.
                    (SingI n, ListLike (f a) a, Eq a, HasOrdinal nat)
                 => a -> Sized f n a -> Maybe (Ordinal n)
sUnsafeElemIndex a (Sized xs) =
  unsafeFromInt . P.fromIntegral <$> LL.elemIndex a xs

-- | Returns all indices of the given element in the list.
--
-- Since 0.1.0.0
elemIndices :: (ListLike (f a) a, Eq a) => a -> Sized f n a -> [Int]
elemIndices a = LL.elemIndices a . runSized
{-# INLINE elemIndices #-}

-- | Ordinal version of 'elemIndices'
--
-- Since 0.1.0.0
sElemIndices :: (HasOrdinal nat, SingI (n :: nat), ListLike (f a) a, Eq a)
             => a -> Sized f n a -> [Ordinal n]
sElemIndices p = P.fmap (unsafeFromInt . P.fromIntegral) . elemIndices p
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
slen :: ('SingI' n, 'ListLike (f a) a' f) => 'Sized' f n a -> 'Sing' n
slen ('viewCons' -> 'NilCV')    = 'SZ'
slen ('viewCons' -> _ '::-' as) = 'SS' (slen as)
slen _                          = error "impossible"
@

   The constraint @('SingI' n, 'ListLike (f a) a' f)@ is needed for view function.
   In the above, we have extra wildcard pattern (@_@) at the last.
   Code compiles if we removed it, but current GHC warns for incomplete pattern,
   although we know first two patterns exhausts all the case.

   Equivalently, we can use snoc-style pattern-matching:

@
slen :: ('SingI' n, 'ListLike (f a) a' f) => 'Sized' f n a -> 'Sing' n
slen ('viewSnoc' -> 'NilSV')     = 'SZ'
slen ('viewSnoc' -> as ':-::' _) = 'SS' (slen as)
@
-}

-- | View of the left end of sequence (cons-side).
--
-- Since 0.1.0.0
data ConsView f n a where
  NilCV :: ConsView f (Zero nat) a
  (::-) :: SingI n => a -> Sized f n a -> ConsView f (Succ n) a

infixr 5 ::-

-- | Case analysis for the cons-side of sequence.
--
-- Since 0.1.0.0
viewCons :: forall f a (n :: nat). (HasOrdinal nat, ListLike (f a) a)
         => Sized f n a
         -> ConsView f n a
viewCons sz = case zeroOrSucc (sLength sz) of
  IsZero   -> NilCV
  IsSucc n' -> withSingI n' $ P.uncurry (::-) (uncons' n' sz)

-- | View of the left end of sequence (snoc-side).
--
-- Since 0.1.0.0
data SnocView f n a where
  NilSV :: SnocView f (Zero nat) a
  (:-::) :: SingI n => Sized f n a -> a -> SnocView f (Succ n) a
infixl 5 :-::

-- | Case analysis for the snoc-side of sequence.
--
-- Since 0.1.0.0
viewSnoc :: forall f (n :: nat) a. (HasOrdinal nat, ListLike (f a) a)
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
nextToHead :: ('ListLike (f a) a' f, 'SingI' n) => 'Sized' f ('S' ('S' n)) a -> a
nextToHead ('viewCons' -> _ '::-' ('viewCons' -> a '::-' _)) = a
@

   In such a case, with @PatternSynonyms@ extension we can write as follows:

@
nextToHead :: ('ListLike (f a) a' f, 'SingI' n) => 'Sized' f ('S' ('S' n)) a -> a
nextToHead (_ ':<' a ':<' _) = a
@

   Of course, we can also rewrite above @slen@ example using @PatternSynonyms@:

@
slen :: ('SingI' n, 'ListLike (f a) a' f) => 'Sized' f n a -> 'Sing' n
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
                (ListLike (f a) a, HasOrdinal nat)
             => forall (n1 :: nat).
                (n ~ Succ n1, SingI n1)
             => a -> Sized f n1 a -> Sized f n a
pattern a :< as <- (viewCons -> a ::- as) where
   a :< as = a <| as

pattern NilL :: forall nat f (n :: nat) a.
                (ListLike (f a) a,  HasOrdinal nat)
             => (n ~ Zero nat) => Sized f n a
pattern NilL   <- (viewCons -> NilCV) where
  NilL = empty

infixl 5 :>

pattern (:>) :: forall nat f (n :: nat) a.
                (ListLike (f a) a, HasOrdinal nat)
             => forall (n1 :: nat).
                (n ~ Succ n1, SingI n1)
             => Sized f n1 a -> a -> Sized f n a
pattern a :> b <- (viewSnoc -> a :-:: b) where
  a :> b = a |> b

pattern NilR :: forall nat f (n :: nat) a.
                (ListLike (f a) a,  HasOrdinal nat)
             => n ~ Zero nat => Sized f n a
pattern NilR   <- (viewSnoc -> NilSV) where
  NilR = empty

-- | Applicative instance, generalizing @'Data.Monoid.ZipList'@.
instance (Functor f, HasOrdinal nat, SingI n, ListLikeF f)
      => P.Applicative (Sized f (n :: nat)) where
  {-# SPECIALISE instance TL.KnownNat n => P.Applicative (Sized [] (n :: TL.Nat)) #-}
  {-# SPECIALISE instance TL.KnownNat n => P.Applicative (Sized Seq.Seq (n :: TL.Nat)) #-}
  {-# SPECIALISE instance TL.KnownNat n => P.Applicative (Sized V.Vector (n :: TL.Nat)) #-}

  pure (x :: a) =
    withListLikeF (Nothing :: Maybe (f a)) $
    replicate' x
  {-# INLINE pure #-}

  (fs :: Sized f n (a -> b)) <*> (xs :: Sized f n a) =
    withListLikeF (Nothing :: Maybe (f (a -> b))) $
    withListLikeF (Nothing :: Maybe (f a)) $
    withListLikeF (Nothing :: Maybe (f b)) $
    zipWithSame ($) fs xs
  {-# INLINE [1] (<*>) #-}
{-# RULES
"<*>/List" [~1] forall fs xs.
  Sized fs <*> Sized xs = Sized (getZipList (ZipList fs <*> ZipList xs))
"<*>/Seq" [~1] forall fs xs.
  Sized fs <*> Sized xs = Sized (Seq.zipWith ($) fs xs)
"<*>/Vector" [~1] forall fs xs.
  Sized fs <*> Sized xs = Sized (V.zipWith ($) fs xs)
 #-}
