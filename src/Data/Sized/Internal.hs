{-# LANGUAGE CPP, ConstraintKinds, DataKinds, DeriveDataTypeable           #-}
{-# LANGUAGE DeriveFunctor, DeriveTraversable, DerivingStrategies          #-}
{-# LANGUAGE ExplicitNamespaces, FlexibleContexts, FlexibleInstances       #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, KindSignatures                    #-}
{-# LANGUAGE LiberalTypeSynonyms, MultiParamTypeClasses, PolyKinds         #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables, StandaloneDeriving           #-}
{-# LANGUAGE TypeFamilies, TypeInType, TypeOperators, UndecidableInstances #-}
#if __GLASGOW_HASKELL__ && __GLASGOW_HASKELL__ >= 806
{-# LANGUAGE NoStarIsType #-}
#endif
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.Sized.Internal (Sized(..)) where
import           Control.DeepSeq      (NFData (..))
import           Control.Lens.At      (Index, IxValue, Ixed (..))
import           Control.Lens.Indexed (FoldableWithIndex (..),
                                       FunctorWithIndex (..),
                                       TraversableWithIndex (..))
import           Control.Subcategory  (CFoldable, CFunctor, Constrained)
import           Data.Hashable        (Hashable (..))
import           Data.Kind            (Type)
import           Data.MonoTraversable (Element, MonoFoldable (..),
                                       MonoFunctor (..), MonoTraversable (..))
import qualified Data.Sequence        as Seq
import           Data.Type.Ordinal    (Ordinal (..), ordToNatural,
                                       unsafeNaturalToOrd)
import           Data.Typeable        (Typeable)
import qualified Data.Vector          as V
import qualified Data.Vector.Storable as SV
import qualified Data.Vector.Unboxed  as UV
import           GHC.TypeNats

-- | @Sized@ wraps a sequential type 'f' and makes length-parametrized version.
--
-- Here, 'f' must be the instance of 'CFreeMonoid' (f a) a@ for all @a@.
--
-- Since 0.2.0.0
newtype Sized (f :: Type -> Type) (n :: Nat) a =
  Sized { runSized :: f a
        } deriving (Eq, Ord, Typeable,
                    Functor, Foldable, Traversable)
          deriving newtype
                (Constrained, CFoldable, CFunctor)

type instance Element (Sized f n a) = Element (f a)

-- | Since 0.2.0.0
deriving instance MonoFoldable (f a)
               => MonoFoldable (Sized f n a)

-- | Since 0.2.0.0
deriving instance MonoFunctor (f a)
               => MonoFunctor (Sized f n a)

-- | Since 0.2.0.0
instance {-# OVERLAPPABLE #-} (MonoTraversable (f a))
      => MonoTraversable (Sized f n a) where
  {-# SPECIALISE instance MonoTraversable (Sized [] n a) #-}
  {-# SPECIALISE instance MonoTraversable (Sized V.Vector n a) #-}
  {-# SPECIALISE instance MonoTraversable (Sized Seq.Seq n a) #-}
  {-# SPECIALISE instance UV.Unbox a => MonoTraversable (Sized UV.Vector n a) #-}
  {-# SPECIALISE instance SV.Storable a => MonoTraversable (Sized SV.Vector n a) #-}
  otraverse f = fmap Sized . otraverse f . runSized
  omapM f = fmap Sized . omapM f. runSized

-- | Since 0.6.0.0
instance {-# OVERLAPPING #-} SV.Storable a => MonoTraversable (Sized SV.Vector n a) where
  otraverse f = fmap Sized . otraverse f . runSized
  omapM f = fmap Sized . omapM f . runSized

-- | Since 0.6.0.0
instance {-# OVERLAPPING #-} UV.Unbox a => MonoTraversable (Sized UV.Vector n a) where
  otraverse f = fmap Sized . otraverse f . runSized
  omapM f = fmap Sized . omapM f . runSized

deriving instance NFData (f a) => NFData (Sized f n a)
deriving instance Hashable (f a) => Hashable (Sized f n a)

instance Show (f a) => Show (Sized f n a) where
  showsPrec d (Sized x) = showsPrec d x

-- | Since 0.2.0.0
type instance Index (Sized f n a) = Ordinal n

-- | Since 0.3.0.0
type instance IxValue (Sized f n a) = IxValue (f a)
instance (Integral (Index (f a)), Ixed (f a))
         => Ixed (Sized f (n :: Nat) a) where
  {-# SPECIALISE instance Ixed (Sized [] (n :: Nat) a) #-}
  {-# SPECIALISE instance Ixed (Sized V.Vector (n :: Nat) a) #-}
  {-# SPECIALISE instance SV.Storable a => Ixed (Sized SV.Vector (n :: Nat) a) #-}
  {-# SPECIALISE instance UV.Unbox a => Ixed (Sized UV.Vector (n :: Nat) a) #-}
  {-# SPECIALISE instance Ixed (Sized Seq.Seq (n :: Nat) a) #-}
  {-# INLINE ix #-}
  ix n f = fmap Sized . ix (fromIntegral $ ordToNatural n) f . runSized

-- | Since 0.2.0.0
instance (Integral i, FunctorWithIndex i f, KnownNat n)
      => FunctorWithIndex (Ordinal n) (Sized f n) where
  imap f = Sized . imap (f . unsafeNaturalToOrd . fromIntegral) . runSized
  {-# INLINE imap #-}
  {-# SPECIALISE instance KnownNat n
                       => FunctorWithIndex (Ordinal n) (Sized [] (n :: Nat)) #-}
  {-# SPECIALISE instance KnownNat n
                       => FunctorWithIndex (Ordinal n) (Sized V.Vector (n :: Nat)) #-}
  {-# SPECIALISE instance KnownNat n
                       => FunctorWithIndex (Ordinal n) (Sized Seq.Seq (n :: Nat)) #-}

-- | Since 0.4.0.0
instance {-# OVERLAPPABLE #-}  (Integral i, FoldableWithIndex i f, KnownNat n)
      => FoldableWithIndex (Ordinal n) (Sized f n) where
  ifoldMap f = ifoldMap (f . unsafeNaturalToOrd . fromIntegral) . runSized
  {-# INLINE ifoldMap #-}

  ifoldr f e = ifoldr (f . unsafeNaturalToOrd . fromIntegral) e . runSized
  {-# INLINE ifoldr #-}

  ifoldl f e = ifoldl (f . unsafeNaturalToOrd . fromIntegral) e . runSized
  {-# INLINE ifoldl #-}

  ifoldr' f e = ifoldr' (f . unsafeNaturalToOrd . fromIntegral) e . runSized
  {-# INLINE ifoldr' #-}

  ifoldl' f e = ifoldl' (f . unsafeNaturalToOrd . fromIntegral) e . runSized
  {-# INLINE ifoldl' #-}

  {-# SPECIALISE instance KnownNat n
                       => FoldableWithIndex (Ordinal n) (Sized [] (n :: Nat)) #-}
  {-# SPECIALISE instance KnownNat n
                       => FoldableWithIndex (Ordinal n) (Sized V.Vector (n :: Nat)) #-}
  {-# SPECIALISE instance KnownNat n
                       => FoldableWithIndex (Ordinal n) (Sized Seq.Seq (n :: Nat)) #-}
-- | Since 0.2.0.0
instance (Integral i, TraversableWithIndex i f, KnownNat n)
      => TraversableWithIndex (Ordinal n) (Sized f n) where
  itraverse f = fmap Sized . itraverse (f . unsafeNaturalToOrd . fromIntegral) . runSized
  {-# INLINE itraverse #-}

  {-# SPECIALISE instance KnownNat n
                       => TraversableWithIndex (Ordinal n) (Sized [] (n :: Nat)) #-}
  {-# SPECIALISE instance KnownNat n
                       => TraversableWithIndex (Ordinal n) (Sized V.Vector (n :: Nat)) #-}
  {-# SPECIALISE instance KnownNat n
                       => TraversableWithIndex (Ordinal n) (Sized Seq.Seq (n :: Nat)) #-}
