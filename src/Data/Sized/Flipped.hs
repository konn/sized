{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

#if __GLASGOW_HASKELL__ && __GLASGOW_HASKELL__ >= 806
{-# LANGUAGE NoStarIsType #-}
#endif
module Data.Sized.Flipped (Flipped (..)) where

import Control.DeepSeq (NFData (..))
import Control.Lens.At (Index, IxValue, Ixed (..))
import Control.Lens.TH (makeWrapped)
import Control.Lens.Wrapped (_Wrapped)
import Data.Hashable (Hashable (..))
import Data.MonoTraversable (Element, MonoFoldable (..), MonoFunctor (..), MonoTraversable (..))
import qualified Data.Sequence as Seq
import Data.Sized.Internal
import qualified Data.Type.Natural as PN
import Data.Type.Ordinal (Ordinal (..))
import Data.Typeable (Typeable)
import qualified Data.Vector as V
import qualified Data.Vector.Storable as SV
import qualified Data.Vector.Unboxed as UV
import qualified GHC.TypeLits as TL

{- | Wrapper for @'Sized'@ which takes length as its last element, instead of the second.

   Since 0.2.0.0
-}
newtype Flipped f a n = Flipped {runFlipped :: Sized f n a}
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

instance
  (Integral (Index (f a)), Ixed (f a)) =>
  Ixed (Flipped f a n)
  where
  {-# SPECIALIZE instance Ixed (Flipped [] a (n :: TL.Nat)) #-}
  {-# SPECIALIZE instance Ixed (Flipped [] a (n :: PN.Nat)) #-}
  {-# SPECIALIZE instance Ixed (Flipped V.Vector a (n :: TL.Nat)) #-}
  {-# SPECIALIZE instance Ixed (Flipped V.Vector a (n :: PN.Nat)) #-}
  {-# SPECIALIZE instance SV.Storable a => Ixed (Flipped SV.Vector a (n :: TL.Nat)) #-}
  {-# SPECIALIZE instance SV.Storable a => Ixed (Flipped SV.Vector a (n :: PN.Nat)) #-}
  {-# SPECIALIZE instance UV.Unbox a => Ixed (Flipped UV.Vector a (n :: TL.Nat)) #-}
  {-# SPECIALIZE instance UV.Unbox a => Ixed (Flipped UV.Vector a (n :: PN.Nat)) #-}
  {-# SPECIALIZE instance Ixed (Flipped Seq.Seq a (n :: TL.Nat)) #-}
  {-# SPECIALIZE instance Ixed (Flipped Seq.Seq a (n :: PN.Nat)) #-}
  ix o = _Wrapped . ix o
  {-# INLINE ix #-}
