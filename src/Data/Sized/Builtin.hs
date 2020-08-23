{-# LANGUAGE CPP, DataKinds, GADTs, KindSignatures, MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms, PolyKinds, RankNTypes, TypeInType           #-}
{-# LANGUAGE ViewPatterns                                                 #-}
#if __GLASGOW_HASKELL__ && __GLASGOW_HASKELL__ >= 806
{-# LANGUAGE NoStarIsType #-}
#endif
-- | This module exports @'S.Sized'@ type specialized to
--   GHC's built-in type numeral @'TL.Nat'@.
module Data.Sized.Builtin
       (Ordinal, Sized, module Data.Sized,
        pattern (:<), pattern NilL, pattern (:>), pattern NilR) where
import           Data.Sized hiding ((:<), (:>), NilL, NilR, Sized)
import qualified Data.Sized as S

import           Control.Subcategory
import           Data.Kind                    (Type)
import           Data.Singletons.Prelude      (SingI)
import           Data.Singletons.Prelude.Enum (PEnum (..))
import qualified Data.Type.Ordinal            as O
import qualified GHC.TypeLits                 as TL

type Ordinal = (O.Ordinal :: TL.Nat -> Type)
type Sized = (S.Sized :: (Type -> Type) -> TL.Nat -> Type -> Type)

pattern (:<) :: forall f (n :: TL.Nat) a.
                (CFreeMonoid f, Dom f a)
             => forall (n1 :: TL.Nat).
                (n ~ Succ n1, SingI n1)
             => a -> Sized f n1 a -> Sized f n a
pattern a :< b = a S.:< b
infixr 5 :<

pattern NilL :: forall f (n :: TL.Nat) a.
                (CFreeMonoid f, Dom f a)
             => n ~ 0 => Sized f n a
pattern NilL = S.NilL

pattern (:>) :: forall f (n :: TL.Nat) a.
                (CFreeMonoid f, Dom f a)
             => forall (n1 :: TL.Nat).
                (n ~ Succ n1, SingI n1)
             => Sized f n1 a -> a -> Sized f n a
pattern a :> b = a S.:> b
infixl 5 :>

pattern NilR :: forall f (n :: TL.Nat) a.
                (CFreeMonoid f, Dom f a,  SingI n)
             => n ~ 0 => Sized f n a
pattern NilR = S.NilR
