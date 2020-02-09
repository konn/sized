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

import           Data.ListLike                (ListLike)
import           Data.Singletons.Prelude      (SingI)
import           Data.Singletons.Prelude.Enum (PEnum (..))
import qualified Data.Type.Ordinal            as O
import qualified GHC.TypeLits                 as TL

type Ordinal (n :: TL.Nat) = O.Ordinal n
type Sized f (n :: TL.Nat) = S.Sized f n

pattern (:<) :: forall f (n :: TL.Nat) a.
                (ListLike (f a) a)
             => forall (n1 :: TL.Nat).
                (n ~ Succ n1, SingI n1)
             => a -> Sized f n1 a -> Sized f n a
pattern a :< b = a S.:< b
infixr 5 :<

pattern NilL :: forall f (n :: TL.Nat) a.
                (ListLike (f a) a)
             => n ~ 0 => Sized f n a
pattern NilL = S.NilL

pattern (:>) :: forall f (n :: TL.Nat) a.
                (ListLike (f a) a)
             => forall (n1 :: TL.Nat).
                (n ~ Succ n1, SingI n1)
             => Sized f n1 a -> a -> Sized f n a
pattern a :> b = a S.:> b
infixl 5 :>

pattern NilR :: forall f (n :: TL.Nat) a.
                (ListLike (f a) a,  SingI n)
             => n ~ 0 => Sized f n a
pattern NilR = S.NilR
