{-# LANGUAGE DataKinds, TemplateHaskell #-}
{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -O2 -fno-hpc #-}
{-# OPTIONS_GHC -dsuppress-idinfo -dsuppress-coercions
      -dsuppress-type-applications
      -dsuppress-module-prefixes -dsuppress-type-signatures
      -dsuppress-uniques #-}
module Shared where
import Language.Haskell.TH
import Test.Hspec
import Test.Inspection


checkInspection
  :: Result -> Expectation
checkInspection Success{} = pure ()
checkInspection (Failure msg) =
  fail msg

inspecting :: String -> Obligation -> Q Exp
inspecting desc reg =
  [|it desc $ checkInspection $(inspectTest reg)|]


data GHCVer = GHC8_8 | GHC8_10 | GHC9_0 | GHC9_2
  deriving (Show, Eq, Ord)

ghcVer :: GHCVer
#if __GLASGOW_HASKELL__ == 902
ghcVer = GHC9_2
#elif __GLASGOW_HASKELL__ == 900
ghcVer = GHC9_0
#elif __GLASGOW_HASKELL__ == 810
ghcVer = GHC8_10
#elif __GLASGOW_HASKELL__ == 808
ghcVer = GHC8_8
#else
ghcVer = error "Coudld not determine GHC Version: __GLASGOW_HASKELL__"
#endif
