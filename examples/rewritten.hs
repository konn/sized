{-# LANGUAGE DataKinds, ExplicitNamespaces, GADTs, PatternSynonyms #-}
{-# LANGUAGE TypeOperators                                         #-}
module Main where
import           Data.Sequence       (Seq)
import           Data.Sized          (pattern (:<), pattern NilL, Sized)
import qualified Data.Sized          as S
import qualified Data.Sized.Internal as SI
import           Data.Type.Natural   (Nat (S, Z))

main :: IO ()
main = do
  print $ S.uncons (() :< () :< NilL :: Sized [] 2 ())
  print $ S.uncons (() :< () :< NilL :: Sized Seq 2 ())
  print $ S.sFindIndexIF (== 5) (1 :< 2 :< 3 :< 4 :< 5 :< NilL :: Sized Seq 5 Int)
  print $ 2 :< S.tail (0 :< 1 :< 2 :< 3 :< 4 :< 5 :< NilL :: Sized Seq 6 Int)
