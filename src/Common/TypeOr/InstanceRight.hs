{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
module Common.TypeOr.InstanceRight (introRight) where

import Common.TypeOr.Class
import Data.Kind

instance {-# INCOHERENT #-} (b :: Constraint) => (a \/ b) where
  byCases _ g = g

introRight :: b => (a \/ b => r) -> r
introRight f = f