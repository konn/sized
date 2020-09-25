{-# LANGUAGE DataKinds, RankNTypes, TemplateHaskell #-}
{-# OPTIONS_GHC -O2 -fno-hpc #-}
{-# OPTIONS_GHC -dsuppress-idinfo -dsuppress-coercions
      -dsuppress-type-applications
      -dsuppress-module-prefixes -dsuppress-type-signatures
      -dsuppress-uniques #-}
module Main where
import           Control.Subcategory
import qualified Data.Sequence           as Seq
import           Data.Singletons.Prelude
import           Data.Sized.Builtin      (Sized, zipWithSame)
import qualified Data.Sized.Builtin      as SV
import qualified Data.Vector             as V
import qualified Data.Vector.Generic     as G
import           Data.Vector.Storable    (Storable)
import qualified Data.Vector.Storable    as S
import           Data.Vector.Unboxed     (Unbox)
import qualified Data.Vector.Unboxed     as U
import           Numeric.Natural         (Natural)
import           Shared
import           Test.Hspec
import           Test.Inspection

type LSized = Sized []
type VSized = Sized V.Vector
type USized = Sized U.Vector
type SSized = Sized S.Vector
type SeqSized = Sized Seq.Seq

zipWith_subcat_List
  :: (Int -> Int -> Int) -> [Int] -> [Int] -> [Int]
zipWith_subcat_List = czipWith

zipWith_List
  :: (Int -> Int -> Int) -> LSized n Int -> LSized m Int -> LSized (Min n m) Int
zipWith_List = SV.zipWith

zipWithSame_List
  :: (Int -> Int -> Int) -> LSized n Int -> LSized n Int -> LSized n Int
zipWithSame_List = zipWithSame

zipWith_List_Prel :: (Int -> Int -> Int) -> [Int] -> [Int] -> [Int]
zipWith_List_Prel = zipWith

zipWithSame_Boxed :: (a -> b -> c) -> VSized n a -> VSized n b -> VSized n c
zipWithSame_Boxed = zipWithSame

zipWithSame_Boxed_mono
  :: (Int -> (Integer -> Bool) -> [Int])
  -> VSized n Int -> VSized n (Integer -> Bool) -> VSized n [Int]
zipWithSame_Boxed_mono = zipWithSame

zipWithSame_Unboxed
  :: (Unbox a, Unbox b, Unbox c)
  => (a -> b -> c) -> USized n a -> USized n b -> USized n c
zipWithSame_Unboxed = zipWithSame

zipWithSame_Unboxed_monomorphic
  :: (Int -> Char -> Bool) -> USized n Int -> USized n Char -> USized n Bool
zipWithSame_Unboxed_monomorphic = zipWithSame

zipWith_Unboxed
  :: (Unbox a, Unbox b, Unbox c)
  => (a -> b -> c) -> U.Vector a -> U.Vector b -> U.Vector c
zipWith_Unboxed = U.zipWith

zipWith_Unboxed_monomorphic
  :: (Int -> Char -> Bool) -> U.Vector Int -> U.Vector Char -> U.Vector Bool
zipWith_Unboxed_monomorphic = U.zipWith

zipWithSame_Storable
  :: (Storable a, Storable b, Storable c)
  => (a -> b -> c) -> SSized n a -> SSized n b -> SSized n c
zipWithSame_Storable = zipWithSame

zipWithSame_Seq
  :: (a -> b -> c) -> SeqSized n a -> SeqSized n b -> SeqSized n c
zipWithSame_Seq = zipWithSame

zipWith_Boxed :: (a -> b -> c) -> V.Vector a -> V.Vector b -> V.Vector c
zipWith_Boxed = V.zipWith

length_two :: Dom f a => Sized f 2 a -> Int
length_two = SV.length

const_two_dom :: Dom f a => Sized f 2 a -> Int
const_two_dom = const 2

main :: IO ()
main = hspec $ do
  describe "czipWith" $ do
    $(inspecting "doesn't contain type classes"
      $ hasNoTypeClasses 'zipWith_subcat_List
      )
  describe "zipWith" $ do
    $(inspecting "doesn't contain type classes"
      $ hasNoTypeClasses 'zipWith_List
      )
  describe "zipWithSame" $ do
    describe "list" $ do
      it "doesn't contain type classes" $
        checkInspection
        $(inspectTest
          $ hasNoTypeClasses 'zipWithSame_List
          )
      it "is almost the same as the original zipWith (list)" $
        checkInspection
          $(inspectTest $
              'zipWithSame_List ==- 'zipWith_List_Prel
          )
    describe "Boxed Vector" $ do
      it "doesn't contain type classes, except for G.Vector" $
        checkInspection
        $(inspectTest
          $ 'zipWithSame_Boxed `hasNoTypeClassesExcept`
            [''G.Vector]
          )
      it "is almost the same as the original zipWith (Boxed)" $
        checkInspection
          $(inspectTest $
              'zipWithSame_Boxed ==- 'zipWith_Boxed
          )
    describe "Unboxed Vector" $ do
      it "doesn't contain type classes except for Unbox" $
        checkInspection
        $(inspectTest
          $ 'zipWithSame_Unboxed `hasNoTypeClassesExcept`
            [''Unbox]
          )
      it "doesn't contain type classes if fully instnatiated" $
        checkInspection
        $(inspectTest
          $ hasNoTypeClasses 'zipWithSame_Unboxed_monomorphic
          )
      it "is almost the same as the original zipWith, if fully instantiated" $
        checkInspection
          $(inspectTest $
              'zipWithSame_Unboxed_monomorphic
              ==- 'zipWith_Unboxed_monomorphic
          )
  describe "length" $ do
    it "is a constant function when length is concrete (with Dom dictionary)" $
      checkInspection
        $(inspectTest $
          'length_two ==- 'const_two_dom
          )
    it "doesn't contain Integer when the length is concrete" $
      checkInspection
        $(inspectTest $ hasNoType 'length_two ''Integer
        )
    it "doesn't contain Natural when the length is concrete" $
      checkInspection
        $(inspectTest $ hasNoType 'length_two ''Natural
        )
