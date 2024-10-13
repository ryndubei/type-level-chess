{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
module Common.TypeOr.InstanceLeft (introLeft) where

import Common.TypeOr.Class
import Data.Kind

instance {-# INCOHERENT #-} (a :: Constraint) => (a :||: b) where
  byCases f _ = f

introLeft :: a => (a :||: b => r) -> r
introLeft f = f
