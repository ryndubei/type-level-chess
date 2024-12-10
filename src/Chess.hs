{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE RequiredTypeArguments #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE PartialTypeSignatures #-}
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
import Data.Bool.Singletons (SBool(..))
import Common.TheoremProving
import Data.Kind
import Chess.Board

{-
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
-}

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

testFact :: forall fact facts
         -> (SingI facts, SingI fact)
         => Either ('True :~: FactHolds fact facts) ('False :~: FactHolds fact facts)
testFact fact facts = case sFactHolds (sing @fact) (sing @facts) of
  STrue -> Left Refl
  SFalse -> Right Refl

tryMove :: forall colour moveFrom moveTo facts facts'.
           SColour colour
        -> SCell moveFrom
        -> SCell moveTo
        -> SFactSet facts
        -> SFactSet facts'
        -> BoardInvariant facts
        -> Either (Move colour moveFrom moveTo facts facts' -> Void) (Move colour moveFrom moveTo facts facts')
tryMove sColour sMoveFrom sMoveTo sFacts sFacts' = undefined

contra :: forall (a :: Piece) (b :: Piece). SPiece a -> (a :~: b) -> ((a == b) :~: 'False) -> Void
contra sA Refl Refl = case sA of

tryMoveWithPiece :: forall colour moveFrom moveTo facts facts' piece.
                    SColour colour
                 -> SCell moveFrom
                 -> SCell moveTo
                 -> SFactSet facts
                 -> SFactSet facts'
                 -> SPiece piece
                 -> BoardInvariant facts
                 -> ( -- we have a piece of the right type at this cell
                      Holds (HasPiece piece colour moveFrom) facts
                      -- and there is no other type of piece here
                    --, forall piece'. Holds (HasPiece piece' colour moveFrom) facts => piece ~ piece'
                    )
                 => Either (Move colour moveFrom moveTo facts facts' -> Void) (Move colour moveFrom moveTo facts facts')
--tryMoveWithPiece sColour sMoveFrom sMoveTo sFacts sFacts' SBishop boardInvariant =
--  let -- uniq :: forall p -> (FactHolds (HasPiece p colour moveFrom) facts :~: 'True) -> (Bishop :~: p)
--      -- uniq p = fst . pieceAtUnique boardInvariant Bishop p colour colour moveFrom Refl
--   in Left $ \move -> case move of
--        MovePawn1 _ -> case uniq Pawn Refl of {}
--        MovePawn2 _ -> case uniq Pawn Refl of {}
--        CapturePawn _ _ -> case uniq Pawn Refl of {}
--        MoveKing _ -> case uniq King Refl of {}
--        CaptureKing _ _ -> case uniq King Refl of {}
tryMoveWithPiece sColour sMoveFrom sMoveTo sFacts sFacts' SPawn boardInvariant =
  let -- uniq :: forall p -> (FactHolds (HasPiece p colour moveFrom) facts :~: 'True) -> (Bishop :~: p)
      -- uniq p = fst . pieceAtUnique boardInvariant Bishop p colour colour moveFrom Refl
   in undefined
