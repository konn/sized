{-# LANGUAGE DataKinds, TemplateHaskell #-}
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
import           Data.Vector.Storable    (Storable)
import qualified Data.Vector.Storable    as S
import           Data.Vector.Unboxed     (Unbox)
import qualified Data.Vector.Unboxed     as U
import           Shared
import           Test.Hspec
import           Test.Inspection

type LSized = Sized []
type VSized = Sized V.Vector
type USized = Sized U.Vector
type SSized = Sized S.Vector
type SeqSized = Sized Seq.Seq

zipWith_LL_List
  :: (Int -> Int -> Int) -> [Int] -> [Int] -> [Int]
zipWith_LL_List = czipWith

zipWith_List
  :: (Int -> Int -> Int) -> LSized n Int -> LSized m Int -> LSized (Min n m) Int
zipWith_List = SV.zipWith

zipWithSame_List
  :: (Int -> Int -> Int) -> LSized n Int -> LSized n Int -> LSized n Int
zipWithSame_List = zipWithSame

inspect $ coreOf 'zipWith_LL_List

zipWith_List_Prel :: (Int -> Int -> Int) -> [Int] -> [Int] -> [Int]
zipWith_List_Prel = zipWith

zipWithSame_Boxed :: (a -> b -> c) -> VSized n a -> VSized n b -> VSized n c
zipWithSame_Boxed = zipWithSame

zipWithSame_Unboxed
  :: (Unbox a, Unbox b, Unbox c)
  => (a -> b -> c) -> USized n a -> USized n b -> USized n c
zipWithSame_Unboxed = zipWithSame

zipWithSame_Storable
  :: (Storable a, Storable b, Storable c)
  => (a -> b -> c) -> SSized n a -> SSized n b -> SSized n c
zipWithSame_Storable = zipWithSame

zipWithSame_Seq
  :: (a -> b -> c) -> SeqSized n a -> SeqSized n b -> SeqSized n c
zipWithSame_Seq = zipWithSame

main :: IO ()
main = hspec $ do
  describe "czipWith" $ do
    $(inspecting "doesn't contain type classes"
      $ hasNoTypeClasses 'zipWith_LL_List
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
