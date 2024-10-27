{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE ImpredicativeTypes #-}
module Chess (gameTree) where

import Chess.Moves
import Chess.Types
import Data.Singletons
import Data.Dependent.Map (DMap)
import qualified Data.Dependent.Map as DMap
import Data.GADT.Compare
import Data.Type.Equality
import Data.Singletons.Decide
import Data.Ord.Singletons

data Move' colour facts params
  = forall moveFrom moveTo facts'.
    ( params ~ '(moveFrom, moveTo, facts')
    ) => Move' { moveFrom :: (SCell moveFrom)
               , moveTo :: (SCell moveTo)
               , facts' :: (SFactSet facts')
               , move :: (Move colour moveFrom moveTo facts facts')
               }

instance GEq (Move' colour facts) where
  geq (Move' moveFrom1 moveTo1 _ (MovePawn1 _)) (Move' moveFrom2 moveTo2 _ (MovePawn1 _)) =
    case (moveFrom1 %~ moveFrom2, moveTo1 %~ moveTo2) of
      (Proved Refl, Proved Refl) -> Just Refl
      (Disproved _, _) -> Nothing
      (_, Disproved _) -> Nothing

instance GCompare (Move' colour facts) where
  gcompare (Move' moveFrom1 moveTo1 _ (MovePawn1 _)) (Move' moveFrom2 moveTo2 _ (MovePawn1 _)) =
    case (moveFrom1 %~ moveFrom2, moveTo1 %~ moveTo2) of
      (Proved Refl, Proved Refl) -> GEQ
      (Proved Refl, _) -> case sCompare moveTo1 moveTo2 of
        SGT -> GGT
        _ -> GLT
      _ -> case (sCompare moveFrom1 moveFrom2) of
        SGT -> GGT
        _ -> GLT

data SomeBoard = forall facts. SingI facts => SomeBoard (Board facts)

instance Show SomeBoard where
  show (SomeBoard (_ :: Board facts)) = "case " ++ show (sing @facts) ++ " of (_ :: facts) -> SomeBoard (Board :: Board facts)"

data GameTree' colour params = forall moveFrom moveTo facts.
  ( params ~ '(moveFrom, moveTo, facts)
  ) => GameTree' (GameTree colour facts)

data GameTree (colour :: Colour) (facts :: FactSet) = GameTree
  { board :: Board facts
  , branches :: forall moveFrom moveTo facts'. Either
      (Move colour moveFrom moveTo facts facts' -> Void)
      (Move colour moveFrom moveTo facts facts')
      -- DMap (Move' c facts) (GameTree' (Opponent c))
  -- idea: some list of allowed moves, then two fields:
  -- allowed moves
  -- function from disallowed moves to Void
  -- and the fields are guaranteed to cover all possible moves

  -- forall (prop :: Cell -> Cell -> FactSet -> FactSet -> Bool) (allowedMoves :: [...]).
  -- ...
  -- if prop is false, then the move is absurd
  -- , propNeg :: forall moveFrom moveTo facts'.
  --       (prop moveFrom moveTo facts facts' :~: 'False)
  --    -> Move colour moveFrom moveTo facts facts'
  --    -> Void
  -- if prop is pos, then the move is in allowedMoves
  -- , propPos :: forall moveFrom moveTo facts'.
  --      (prop moveFrom moveTo facts facts' :~: 'True)
  --   -> (Elem (Move ...) allowedMoves :~: 'True)
  -- we have a term-level representation of the allowed moves
  -- , sAllowedMoves :: SList allowedMoves (or otherwise)
  }

gameTree :: forall colourToMove facts. (SingI colourToMove, SingI facts) => Board facts -> GameTree colourToMove facts
gameTree board = GameTree board $ undefined
