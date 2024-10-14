{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE RequiredTypeArguments #-}
module Common.TypeOr
  ( type (\/)
  , introLeft
  , introRight
  , byCases
  )
  where

import Common.TypeOr.Class
-- The instances must go in different files because GHC complains otherwise
import Common.TypeOr.InstanceLeft
import Common.TypeOr.InstanceRight

-- | in all uses of byCases, the type arguments are mandatory,
-- so we expose this version of the function
byCases :: forall a -> forall b -> (a \/ b) => (a => r) -> (b => r) -> r
byCases _ _ = byCases'

-- | example usage
integralOrShow :: forall t. (Integral t \/ Show t) => t -> String
integralOrShow x = byCases (Integral t) (Show t)
  (show (toInteger x))
  (show x)
