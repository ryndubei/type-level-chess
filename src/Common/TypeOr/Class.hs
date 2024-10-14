{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE RequiredTypeArguments #-}
module Common.TypeOr.Class (type (\/)(..)) where

import Data.Kind

class (a :: Constraint) \/ (b :: Constraint) where
  byCases' :: (a => r) -> (b => r) -> r

infixr 3 \/
