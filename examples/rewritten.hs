{-# LANGUAGE DataKinds, ExplicitNamespaces, GADTs, PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables, TypeApplications, TypeOperators  #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Presburger #-}
{-# OPTIONS_GHC -Wall #-}
module Main where
import           Data.Sequence      (Seq)
import           Data.Sized         (Sized, pattern (:<), pattern Nil)
import qualified Data.Sized         as S
import qualified Data.Sized.Builtin as Bin
import           Data.Type.Equality
import           Data.Type.Natural  (IsPeano (succNonCyclic), Nat (S, Z),
                                     SingI (sing))
import qualified Data.Vector        as V
import           Data.Void          (absurd)
import           GHC.TypeNats

main :: IO ()
main = do
  print  (() :< () :< Nil :: Sized [] 2 ())
  print (() :< () :< Nil :: Sized Seq 2 ())
  print $ S.sFindIndex (== 5) (1 :< 2 :< 3 :< 4 :< 5 :< Nil :: Sized Seq 5 Int)
  print $ 2 :< S.tail (0 :< 1 :< 2 :< 3 :< 4 :< 5 :< Nil :: Sized Seq 6 Int)

patBin1 :: Sized V.Vector 2 Int -> Int
patBin1 (a :< b :< Nil) = 42

unBin :: (Sized V.Vector 2 a -> b) -> a -> a -> b
unBin f a b =
  f (a :< b :< Nil)

unBin' :: ((Bin.Sized V.Vector 2 a -> b) -> b) -> (a -> a -> b) -> b
unBin' fromF f =
  fromF (\(a :< b :< Nil) -> f a b)

unBin'Builtin :: ((Sized V.Vector 2 a -> b) -> b) -> (a -> a -> b) -> b
unBin'Builtin fromF f =
  fromF (\(a Bin.:< b Bin.:< Bin.Nil) -> f a b)

veced :: Bin.Sized V.Vector 0 a -> ()
veced Bin.Nil = ()
veced _       = error "Could not happen"

veced2 :: Bin.Sized V.Vector 1 a -> a
veced2 (a Bin.:< Bin.Nil) = a
veced2 _                  = error "cannot happen"

vecNum :: (Num a, KnownNat n) => Bin.Sized [] n a -> a
vecNum Bin.Nil      = 0
vecNum (a Bin.:< _) = a

zipSame :: forall a b n. KnownNat n => Bin.Sized [] n a -> Bin.Sized [] n b -> Bin.Sized [] n (a,b)
zipSame Bin.Nil Bin.Nil             = Nil
zipSame (a Bin.:< as) (b Bin.:< bs) = (a, b) :< zipSame as bs
zipSame Bin.Nil (Bin.:<){}          = absurd $ succNonCyclic (sing @n) Refl
zipSame (Bin.:<){} Bin.Nil          = absurd $ succNonCyclic (sing @n) Refl

-- >>> zipSame @() @Int (() :< Nil) Nil
-- Couldn't match type ‘1’ with ‘0’ arising from a use of ‘:<’
