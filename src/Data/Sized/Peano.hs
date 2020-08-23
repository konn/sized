{-# LANGUAGE DataKinds, GADTs, KindSignatures, MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms, PolyKinds, RankNTypes, TypeInType      #-}
{-# LANGUAGE ViewPatterns                                            #-}
-- | This module exports @'S.Sized'@ type specialized to
--   type-level Peano numeral @'PN.Nat'@.
module Data.Sized.Peano
       (Ordinal, Sized, module Data.Sized,
        pattern (:<), pattern NilL, pattern (:>), pattern NilR) where
import           Data.Sized hiding ((:<), (:>), NilL, NilR, Sized)
import qualified Data.Sized as S

import           Control.Subcategory
import           Data.Kind                    (Type)
import           Data.Singletons.Prelude      (SingI)
import           Data.Singletons.Prelude.Enum (PEnum (..))
import qualified Data.Type.Natural            as PN
import qualified Data.Type.Ordinal            as O

type Ordinal = (O.Ordinal :: PN.Nat -> Type)
type Sized = (S.Sized :: (Type -> Type) -> PN.Nat -> Type -> Type)

pattern (:<) :: forall f (n :: PN.Nat) a.
                (CFreeMonoid f, Dom f a)
             => forall (n1 :: PN.Nat).
                (n ~ Succ n1, SingI n1)
             => a -> Sized f n1 a -> Sized f n a
pattern a :< b = a S.:< b
infixr 5 :<

pattern NilL :: forall f (n :: PN.Nat) a.
                (CFreeMonoid f, Dom f a)
             => n ~ 'PN.Z => Sized f n a
pattern NilL = S.NilL

pattern (:>) :: forall f (n :: PN.Nat) a.
                (CFreeMonoid f, Dom f a)
             => forall (n1 :: PN.Nat).
                (n ~ Succ n1, SingI n1)
             => Sized f n1 a -> a -> Sized f n a
pattern a :> b = a S.:> b
infixl 5 :>

pattern NilR :: forall f (n :: PN.Nat) a.
                (CFreeMonoid f, Dom f a)
             => n ~ 'PN.Z => Sized f n a
pattern NilR = S.NilR
