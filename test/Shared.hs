{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -O2 -fno-hpc #-}

module Shared where

import Language.Haskell.TH (ExpQ)
import Test.Tasty.Inspection

inspecting :: String -> Obligation -> ExpQ
inspecting title obl = inspectTest $ obl {testName = Just title}

data GHCVer = GHC8_8 | GHC8_10 | GHC9_0 | GHC9_2 | GHC9_4 | GHC9_6 | GHC9_8 | GHC9_10
  deriving (Show, Eq, Ord)

ghcVer :: GHCVer
#if __GLASGOW_HASKELL__ == 910
ghcVer = GHC9_10
#elif __GLASGOW_HASKELL__ == 908
ghcVer = GHC9_8
#elif __GLASGOW_HASKELL__ == 906
ghcVer = GHC9_6
#elif __GLASGOW_HASKELL__ == 904
ghcVer = GHC9_4
#elif __GLASGOW_HASKELL__ == 902
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
