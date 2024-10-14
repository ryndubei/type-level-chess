{-# LANGUAGE DataKinds #-}
module Chess (gameTree) where

import Chess.Moves
import Chess.Types
import Data.Singletons
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)

data Move = Move { moveFrom :: Cell, moveTo :: Cell }
  deriving (Eq, Ord, Show)

data SomeBoard = forall facts. SingI facts => SomeBoard (Board facts)

instance Show SomeBoard where
  show (SomeBoard (_ :: Board facts)) = "case " ++ show (sing @facts) ++ " of (_ :: facts) -> SomeBoard (Board :: Board facts)"

data GameTree (c :: Colour) = GameTree
  { board :: SomeBoard
  , branches :: (Map Move (GameTree (Opponent c)))
  } deriving Show

gameTree :: forall colourToMove facts. (SingI colourToMove, SingI facts) => Board facts -> GameTree colourToMove
gameTree board = GameTree (SomeBoard board) $ Map.fromList undefined
