{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Presburger #-}

module Main where

import Data.Sequence (Seq)
import Data.Sized (Sized, pattern Nil, pattern (:<))
import qualified Data.Sized as S
import Data.Type.Equality
import Data.Type.Natural
import Data.Type.Natural.Lemma.Arithmetic
import qualified Data.Vector as V
import Data.Void (absurd)

main :: IO ()
main = do
  print (() :< () :< Nil :: Sized [] 2 ())
  print (() :< () :< Nil :: Sized Seq 2 ())
  print $ S.sFindIndex (== 5) (1 :< 2 :< 3 :< 4 :< 5 :< Nil :: Sized Seq 5 Int)
  print $ 2 :< S.tail (0 :< 1 :< 2 :< 3 :< 4 :< 5 :< Nil :: Sized Seq 6 Int)

patBin1 :: Sized V.Vector 2 Int -> Int
patBin1 (_ :< _ :< Nil) = 42

unBin :: (Sized V.Vector 2 a -> b) -> a -> a -> b
unBin f a b =
  f (a :< b :< Nil)

unBin' :: ((Sized V.Vector 2 a -> b) -> b) -> (a -> a -> b) -> b
unBin' fromF f =
  fromF (\(a :< b :< Nil) -> f a b)

unBin'Builtin :: ((Sized V.Vector 2 a -> b) -> b) -> (a -> a -> b) -> b
unBin'Builtin fromF f =
  fromF (\(a :< b :< Nil) -> f a b)

veced :: Sized V.Vector 0 a -> ()
veced Nil = ()
veced _ = error "Could not happen"

veced2 :: Sized V.Vector 1 a -> a
veced2 (a :< Nil) = a
veced2 _ = error "cannot happen"

vecNum :: (Num a, KnownNat n) => Sized [] n a -> a
vecNum Nil = 0
vecNum (a :< _) = a

zipSame :: forall a b n. KnownNat n => Sized [] n a -> Sized [] n b -> Sized [] n (a, b)
zipSame Nil Nil = Nil
zipSame (a :< as) (b :< bs) = (a, b) :< zipSame as bs
zipSame Nil (:<) {} = absurd $ succNonCyclic (sNat @n) Refl
zipSame (:<) {} Nil = absurd $ succNonCyclic (sNat @n) Refl

-- >>> zipSame @() @Int (() :< Nil) Nil
-- Couldn't match type ‘1’ with ‘0’ arisNat from a use of ‘:<’
