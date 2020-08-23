{-# LANGUAGE CPP, ConstraintKinds, DataKinds, DeriveDataTypeable           #-}
{-# LANGUAGE DeriveFunctor, DeriveTraversable, ExplicitNamespaces          #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances                           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, KindSignatures                    #-}
{-# LANGUAGE LiberalTypeSynonyms, MultiParamTypeClasses, PolyKinds         #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables, StandaloneDeriving           #-}
{-# LANGUAGE TypeFamilies, TypeInType, TypeOperators, UndecidableInstances #-}
#if __GLASGOW_HASKELL__ && __GLASGOW_HASKELL__ >= 806
{-# LANGUAGE NoStarIsType #-}
#endif
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.Sized.Internal (Sized(..)) where
import           Control.DeepSeq         (NFData (..))
import           Control.Lens.At         (Index, IxValue, Ixed (..))
import           Control.Lens.Indexed    (FoldableWithIndex (..),
                                          FunctorWithIndex (..),
                                          TraversableWithIndex (..))
import           Data.Foldable           (Foldable)
import           Data.Hashable           (Hashable (..))
import           Data.Kind               (Type)
import           Data.MonoTraversable    (Element, MonoFoldable (..),
                                          MonoFunctor (..),
                                          MonoTraversable (..))
import qualified Data.Sequence           as Seq
import           Data.Singletons.Prelude (SingI)
import           Data.Traversable        (Traversable)
import qualified Data.Type.Natural       as PN
import           Data.Type.Ordinal       (HasOrdinal, Ordinal (..),
                                          ordToNatural, unsafeNaturalToOrd)
import           Data.Typeable           (Typeable)
import qualified Data.Vector             as V
import qualified Data.Vector.Storable    as SV
import qualified Data.Vector.Unboxed     as UV
import qualified GHC.TypeLits            as TL

-- | @Sized@ wraps a sequential type 'f' and makes length-parametrized version.
--
-- Here, 'f' must be the instance of 'Functor' and @'ListLike' (f a) a@ for all @a@.
-- This constraint is expressed by 'ListLikeF'.
-- Folding and traversing function such as 'all' and 'foldl'' is available
-- via 'Foldable' or 'Traversable' class, if 'f' is the instance of them.
--
-- Since 0.2.0.0
newtype Sized (f :: Type -> Type) (n :: nat) a =
  Sized { runSized :: f a
        } deriving (Eq, Ord, Typeable,
                    Functor, Foldable, Traversable)

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
instance (Integral (Index (f a)), Ixed (f a), HasOrdinal nat)
         => Ixed (Sized f (n :: nat) a) where
  {-# SPECIALISE instance Ixed (Sized [] (n :: TL.Nat) a) #-}
  {-# SPECIALISE instance Ixed (Sized [] (n :: PN.Nat) a) #-}
  {-# SPECIALISE instance Ixed (Sized V.Vector (n :: TL.Nat) a) #-}
  {-# SPECIALISE instance Ixed (Sized V.Vector (n :: PN.Nat) a) #-}
  {-# SPECIALISE instance SV.Storable a => Ixed (Sized SV.Vector (n :: TL.Nat) a) #-}
  {-# SPECIALISE instance SV.Storable a => Ixed (Sized SV.Vector (n :: PN.Nat) a) #-}
  {-# SPECIALISE instance UV.Unbox a => Ixed (Sized UV.Vector (n :: TL.Nat) a) #-}
  {-# SPECIALISE instance UV.Unbox a => Ixed (Sized UV.Vector (n :: PN.Nat) a) #-}
  {-# SPECIALISE instance Ixed (Sized Seq.Seq (n :: TL.Nat) a) #-}
  {-# SPECIALISE instance Ixed (Sized Seq.Seq (n :: PN.Nat) a) #-}
  {-# INLINE ix #-}
  ix n f = fmap Sized . ix (fromIntegral $ ordToNatural n) f . runSized

-- | Since 0.2.0.0
instance (Integral i, FunctorWithIndex i f, HasOrdinal nat, SingI n)
      => FunctorWithIndex (Ordinal (n :: nat)) (Sized f n) where
  imap f = Sized . imap (f . unsafeNaturalToOrd . fromIntegral) . runSized
  {-# INLINE imap #-}
  {-# SPECIALISE instance TL.KnownNat n
                       => FunctorWithIndex (Ordinal n) (Sized [] (n :: TL.Nat)) #-}
  {-# SPECIALISE instance SingI n
                       => FunctorWithIndex (Ordinal n) (Sized [] (n :: PN.Nat)) #-}
  {-# SPECIALISE instance TL.KnownNat n
                       => FunctorWithIndex (Ordinal n) (Sized V.Vector (n :: TL.Nat)) #-}
  {-# SPECIALISE instance SingI n
                       => FunctorWithIndex (Ordinal n) (Sized V.Vector (n :: PN.Nat)) #-}
  {-# SPECIALISE instance TL.KnownNat n
                       => FunctorWithIndex (Ordinal n) (Sized Seq.Seq (n :: TL.Nat)) #-}
  {-# SPECIALISE instance SingI n
                       => FunctorWithIndex (Ordinal n) (Sized Seq.Seq (n :: PN.Nat)) #-}

-- | Since 0.4.0.0
instance {-# OVERLAPPABLE #-}  (Integral i, FoldableWithIndex i f, HasOrdinal nat, SingI n)
      => FoldableWithIndex (Ordinal (n :: nat)) (Sized f n) where
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

  {-# SPECIALISE instance TL.KnownNat n
                       => FoldableWithIndex (Ordinal n) (Sized [] (n :: TL.Nat)) #-}
  {-# SPECIALISE instance SingI n
                       => FoldableWithIndex (Ordinal n) (Sized [] (n :: PN.Nat)) #-}
  {-# SPECIALISE instance TL.KnownNat n
                       => FoldableWithIndex (Ordinal n) (Sized V.Vector (n :: TL.Nat)) #-}
  {-# SPECIALISE instance SingI n
                       => FoldableWithIndex (Ordinal n) (Sized V.Vector (n :: PN.Nat)) #-}
  {-# SPECIALISE instance TL.KnownNat n
                       => FoldableWithIndex (Ordinal n) (Sized Seq.Seq (n :: TL.Nat)) #-}
  {-# SPECIALISE instance SingI n
                       => FoldableWithIndex (Ordinal n) (Sized Seq.Seq (n :: PN.Nat)) #-}

-- | Since 0.2.0.0
instance (Integral i, TraversableWithIndex i f, HasOrdinal nat, SingI n)
      => TraversableWithIndex (Ordinal (n :: nat)) (Sized f n) where
  itraverse f = fmap Sized . itraverse (f . unsafeNaturalToOrd . fromIntegral) . runSized
  {-# INLINE itraverse #-}

  {-# SPECIALISE instance TL.KnownNat n
                       => TraversableWithIndex (Ordinal n) (Sized [] (n :: TL.Nat)) #-}
  {-# SPECIALISE instance SingI n
                       => TraversableWithIndex (Ordinal n) (Sized [] (n :: PN.Nat)) #-}
  {-# SPECIALISE instance TL.KnownNat n
                       => TraversableWithIndex (Ordinal n) (Sized V.Vector (n :: TL.Nat)) #-}
  {-# SPECIALISE instance SingI n
                       => TraversableWithIndex (Ordinal n) (Sized V.Vector (n :: PN.Nat)) #-}
  {-# SPECIALISE instance TL.KnownNat n
                       => TraversableWithIndex (Ordinal n) (Sized Seq.Seq (n :: TL.Nat)) #-}
  {-# SPECIALISE instance SingI n
                       => TraversableWithIndex (Ordinal n) (Sized Seq.Seq (n :: PN.Nat))  #-}
