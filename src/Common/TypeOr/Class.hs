{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE RequiredTypeArguments #-}
module Common.TypeOr.Class (type (\/)(..)) where

import Data.Kind

-- | Disjunction between constraints. If more than one constraint matches
-- at the same time, then the leftmost one takes priority in any invocation
-- of 'byCases'.
class (a :: Constraint) \/ (b :: Constraint) where
  byCases' :: (a => r) -> (b => r) -> r

infixr 3 \/
