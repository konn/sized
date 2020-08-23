{-# LANGUAGE CPP, ConstraintKinds, DataKinds, DeriveDataTypeable           #-}
{-# LANGUAGE DeriveFunctor, DeriveTraversable, EmptyDataDecls              #-}
{-# LANGUAGE ExplicitNamespaces, FlexibleContexts, FlexibleInstances       #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, KindSignatures                    #-}
{-# LANGUAGE LiberalTypeSynonyms, MultiParamTypeClasses, PatternSynonyms   #-}
{-# LANGUAGE PolyKinds, RankNTypes, ScopedTypeVariables                    #-}
{-# LANGUAGE StandaloneDeriving, TemplateHaskell, TypeFamilies, TypeInType #-}
{-# LANGUAGE TypeOperators, UndecidableInstances, ViewPatterns             #-}
#if __GLASGOW_HASKELL__ && __GLASGOW_HASKELL__ >= 806
{-# LANGUAGE NoStarIsType #-}
#endif
module Data.Sized.Flipped (Flipped(..),
                           pattern (:<), pattern NilL,
                           pattern (:>), pattern NilR) where
import qualified Data.Sized          as Orig
import           Data.Sized.Internal

import           Control.DeepSeq              (NFData (..))
import           Control.Lens.At              (Index, IxValue, Ixed (..))
import           Control.Lens.TH              (makeWrapped)
import           Control.Lens.Wrapped         (_Wrapped)
import           Control.Subcategory
import           Data.Hashable                (Hashable (..))
import           Data.Kind                    (Type)
import           Data.MonoTraversable         (Element, MonoFoldable (..))
import           Data.MonoTraversable         (MonoFunctor (..))
import           Data.MonoTraversable         (MonoTraversable (..))
import qualified Data.Sequence                as Seq
import           Data.Singletons.Prelude.Enum (PEnum (..))
import qualified Data.Type.Natural            as PN
import           Data.Type.Natural.Class      (Zero)
import           Data.Type.Ordinal            (HasOrdinal, Ordinal (..))
import           Data.Typeable                (Typeable)
import qualified Data.Vector                  as V
import qualified Data.Vector.Storable         as SV
import qualified Data.Vector.Unboxed          as UV
import qualified GHC.TypeLits                 as TL

-- | Wrapper for @'Sized'@ which takes length as its last element, instead of the second.
--
--   Since 0.2.0.0
newtype Flipped f a n = Flipped { runFlipped :: Sized f n a }
                      deriving (Show, Eq, Ord, Typeable, NFData, Hashable)

makeWrapped ''Flipped

type instance Index (Flipped f a n) = Ordinal n
type instance IxValue (Flipped f a n) = IxValue (f a)
type instance Element (Flipped f a n) = Element (Sized f n a)
deriving instance MonoFunctor (f a) => MonoFunctor (Flipped f a n)
deriving instance MonoFoldable (f a) => MonoFoldable (Flipped f a n)
instance (MonoTraversable (f a)) => MonoTraversable (Flipped f a n) where
  otraverse = _Wrapped . otraverse
  {-# INLINE otraverse #-}

  omapM = _Wrapped . omapM
  {-# INLINE omapM #-}

instance (Integral (Index (f a)), Ixed (f a), HasOrdinal nat)
      => Ixed (Flipped f a (n :: nat)) where
  {-# SPECIALISE instance Ixed (Flipped [] a (n :: TL.Nat)) #-}
  {-# SPECIALISE instance Ixed (Flipped [] a (n :: PN.Nat)) #-}
  {-# SPECIALISE instance Ixed (Flipped V.Vector a (n :: TL.Nat)) #-}
  {-# SPECIALISE instance Ixed (Flipped V.Vector a (n :: PN.Nat)) #-}
  {-# SPECIALISE instance SV.Storable a => Ixed (Flipped SV.Vector a (n :: TL.Nat)) #-}
  {-# SPECIALISE instance SV.Storable a => Ixed (Flipped SV.Vector a (n :: PN.Nat)) #-}
  {-# SPECIALISE instance UV.Unbox a => Ixed (Flipped UV.Vector a (n :: TL.Nat)) #-}
  {-# SPECIALISE instance UV.Unbox a => Ixed (Flipped UV.Vector a (n :: PN.Nat)) #-}
  {-# SPECIALISE instance Ixed (Flipped Seq.Seq a (n :: TL.Nat)) #-}
  {-# SPECIALISE instance Ixed (Flipped Seq.Seq a (n :: PN.Nat)) #-}
  ix o = _Wrapped . ix o
  {-# INLINE ix #-}

pattern (:<) :: forall nat (f :: Type -> Type) (n :: nat) a.
                (CFreeMonoid f, Dom f a, HasOrdinal nat)
              => forall (n1 :: nat). (n ~ Succ n1, PN.SingI n1)
              => a -> Flipped f a n1 -> Flipped f a n
pattern a :< as <- Flipped (a Orig.:< (Flipped -> as)) where
  a :< Flipped as = Flipped (a Orig.:< as)

pattern NilL :: forall nat (f :: Type -> Type) (n :: nat) a.
                (CFreeMonoid f, Dom f a, HasOrdinal nat)
             => n ~ Zero nat => Flipped f a n
pattern NilL = Flipped Orig.NilL

pattern (:>) :: forall nat (f :: Type -> Type) (n :: nat) a.
                (CFreeMonoid f, Dom f a, HasOrdinal nat)
             => forall (n1 :: nat). (n ~ Succ n1, PN.SingI n1)
             => Flipped f a n1 -> a -> Flipped f a n
pattern as :> a <- Flipped ((Flipped -> as) Orig.:> a) where
  Flipped as :> a = Flipped (as Orig.:> a)

pattern NilR :: forall nat (f :: Type -> Type) (n :: nat) a.
                (CFreeMonoid f, Dom f a, HasOrdinal nat)
             => n ~ Zero nat => Flipped f a n
pattern NilR = Flipped Orig.NilR
