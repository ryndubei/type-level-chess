{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
module Common.TypeOr
  ( type (\/)(byCases)
  , introLeft
  , introRight
  )
  where

import Common.TypeOr.Class
import Common.TypeOr.InstanceLeft
import Common.TypeOr.InstanceRight

-- | example usage
integralOrShow :: forall x. (Integral x \/ Show x) => x -> String
integralOrShow x = byCases @(Integral x) @(Show x)
  (show (toInteger x))
  (show x)
