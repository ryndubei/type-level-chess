{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RequiredTypeArguments #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ImpredicativeTypes #-}

module Chess.Moves
  ( Board
  , initialBoard
  , movePawn1
  , movePawn2
  , capturePawn
  , moveKing
  , captureKing
  , Unthreatened'(..)
  , Threatened'(..)
  , Move(..)
  , makeMove
  , module Common.TypeOr
  )
  where

import Chess.Types
import Prelude.Singletons
import Data.Kind
import Data.Singletons.Base.Enum

import Common.TypeOr
import qualified Fcf as F
import qualified Fcf.Data.List as F
import Data.Void

data Board (facts :: FactSet) = Board

type role Board nominal

type HasKing = HasPiece King

type Unthreatened (cell :: Cell) (by :: Colour) (facts :: FactSet) =
  ( UnthreatenedBy Knight cell by facts
  , UnthreatenedBy Bishop cell by facts
  , UnthreatenedBy Rook cell by facts
  , UnthreatenedBy Pawn cell by facts
  , UnthreatenedBy Queen cell by facts
  -- Don't need to check this except when moving the king:
  -- , UnthreatenedByKing cell by facts
  )

-- TODO
type family UnthreatenedBy (piece :: Piece) (cell :: Cell) (by :: Colour) (facts :: FactSet) :: Constraint where
  UnthreatenedBy Knight cell by facts = ()
  UnthreatenedBy Bishop cell by facts = ()
  UnthreatenedBy Rook cell by facts = ()
  UnthreatenedBy Pawn cell by facts = ()
  UnthreatenedBy Queen cell by facts = ()

type UnthreatenedByKing cell by facts = () :: Constraint

type ReallyUnthreatened (cell :: Cell) (by :: Colour) (facts :: FactSet) =
  ( Unthreatened cell by facts
  , UnthreatenedByKing cell by facts
  )

-- Helpers for initialBoard
type CellsOfVertical = ((F.Flip F.Map) (EnumFromTo MinBound MaxBound) F.<=< F.Pure1 (F.Flip (F.Pure2 'Cell)))
type PawnRankCells (c :: Colour) = F.Eval (CellsOfVertical (PawnRank c))
type CellsToFacts (f :: Cell -> F.Exp Fact) (cs :: [Cell]) = F.Eval (F.Map f cs)
type Pawns (c :: Colour) = CellsToFacts (F.Pure1 (HasPiece Pawn c)) (PawnRankCells c)

initialBoard :: ( whitePawns ~ Pawns White
                , blackPawns ~ Pawns Black
                , blackKing ~ HasKing Black ('Cell E Eight)
                , whiteKing ~ HasKing White ('Cell E One)
                , emptyCells ~ F.Eval (F.ConcatMap CellsOfVertical (EnumFromTo Three Six))
                , emptyFacts ~ CellsToFacts (F.Pure1 IsEmpty) emptyCells
                , facts ~ FactSetFromList
                    ( whitePawns
                   ++ blackPawns
                   ++ '[blackKing]
                   ++ '[whiteKing]
                   ++ emptyFacts
                    )
                ) => Board facts
initialBoard = Board

data Move (colour :: Colour) (moveFrom :: Cell) (moveTo :: Cell) (facts :: FactSet) (facts' :: FactSet) where
  MovePawn1 :: ( Holds (HasPiece Pawn colour moveFrom) facts
               , Holds (IsEmpty moveTo) facts
               , moveFrom ~ 'Cell hFrom vFrom
               , moveTo ~ 'Cell hFrom vTo
               , vTo ~ Forward colour vFrom
               , 'True ~ If (colour == White)
                   (vTo < MaxBound vFrom)
                   (vTo > MinBound vFrom)
               , facts' ~ DeleteInsert
                   [IsEmpty moveTo, HasPiece Pawn colour moveFrom]
                   [IsEmpty moveFrom, HasPiece Pawn colour moveTo]
                   facts
               , Holds (HasKing colour kingCell) facts
               )
            => Unthreatened' kingCell (Opponent colour) facts'
            -> Move colour moveFrom moveTo facts facts'
 
makeMove :: Move colour moveFrom moveTo facts facts' -> Board facts -> Board facts'
makeMove !_ Board = Board

-- there is no capture at 'moveTo' by a piece of colour 'by'
data Unthreatened' (moveTo :: Cell) (by :: Colour) (facts :: FactSet)
  = forall realPiece. Holds (HasPiece realPiece (Opponent by) moveTo) facts => UnthreatenedActual
      (Proxy realPiece)
      (forall moveFrom facts'. Move by moveFrom moveTo facts facts' -> Void)
  | Holds (IsEmpty moveTo) facts => UnthreatenedHypothetical
      ( forall moveFrom facts1 facts' hypotheticalPiece.
        facts1 ~ DeleteInsert '[IsEmpty moveTo] '[HasPiece hypotheticalPiece (Opponent by) moveTo] facts
      => Move by moveFrom moveTo facts1 facts'
      -> Void
      )
  -- ^ if it's empty, suppose it isn't.

-- there exists a capture at 'moveTo' by a piece of colour 'by'
data Threatened' (moveTo :: Cell) (by :: Colour) (facts :: FactSet)
  = forall facts1 hypotheticalPiece facts' moveFrom.
    ( Holds (IsEmpty moveTo) facts
    , facts1 ~ DeleteInsert '[IsEmpty moveTo] '[HasPiece hypotheticalPiece (Opponent by) moveTo] facts
    ) => ThreatenedHypothetical 
           (Proxy hypotheticalPiece)
           (Move by moveFrom moveTo facts1 facts')
  | forall realPiece facts' moveFrom.
    Holds (HasPiece realPiece (Opponent by) moveTo) facts
    => ThreatenedActual
         (Proxy realPiece)
         (Move by moveFrom moveTo facts facts')

type role Unthreatened' nominal nominal nominal

movePawn1 :: forall (colour :: Colour)
          -> forall (moveFrom :: Cell)
          -> forall (moveTo :: Cell)
          -> forall (kingCell :: Cell)
          -> ( Holds (HasPiece Pawn colour moveFrom) facts
             , Holds (IsEmpty moveTo) facts
             , moveFrom ~ 'Cell hFrom vFrom
             , moveTo ~ 'Cell hFrom vTo
             , vTo ~ Forward colour vFrom
             , 'True ~ If (colour == White)
                 (vTo < MaxBound vFrom)
                 (vTo > MinBound vFrom)
             , facts' ~ DeleteInsert
                 [IsEmpty moveTo, HasPiece Pawn colour moveFrom]
                 [IsEmpty moveFrom, HasPiece Pawn colour moveTo]
                 facts
             , Holds (HasKing colour kingCell) facts
             , Unthreatened kingCell (Opponent colour) facts'
             )
           => Board facts
           -> Board facts'
movePawn1 _ _ _ _ Board = Board

movePawn2 :: forall (colour :: Colour)
          -> forall (moveFrom :: Cell)
          -> forall (moveTo :: Cell)
          -> forall (kingCell :: Cell)
          -> ( Holds (HasPiece Pawn colour moveFrom) facts
             , Holds (IsEmpty moveTo) facts
             , moveFrom ~ 'Cell hFrom (PawnRank colour)
             , moveTo ~ 'Cell hFrom vTo
             , vTo ~ Forward colour (Forward colour (PawnRank colour))
             , facts' ~ DeleteInsert
                 [IsEmpty moveTo, HasPiece Pawn colour moveFrom]
                 [IsEmpty moveFrom, HasPiece Pawn colour moveTo]
                 facts
             , Holds (HasKing colour kingCell) facts
             , Unthreatened kingCell (Opponent colour) facts'
             )
           => Board facts
           -> Board facts'
movePawn2 _ _ _ _ Board = Board

capturePawn :: forall (colour :: Colour)
            -> forall (moveFrom :: Cell)
            -> forall (moveTo :: Cell)
            -> forall (kingCell :: Cell)
            -> forall (opponentPiece :: Piece)
            -> ( Holds (HasPiece Pawn colour moveFrom) facts
               , Holds (HasPiece opponentPiece (Opponent colour) moveTo) facts
               , moveFrom ~ 'Cell hFrom vFrom
               , moveTo ~ 'Cell hTo vTo
               , vTo ~ Forward colour vFrom
               -- Note that we now use an explicit disjunction constraint
               -- (a, b \/ c) => t
               -- instead of
               -- a => (b => t, c => t)
               -- as in Frog
               , hTo ~ Rightward hFrom \/ hTo ~ Leftward hFrom
               , facts' ~ DeleteInsert
                   [HasPiece opponentPiece (Opponent colour) moveTo, HasPiece Pawn colour moveFrom]
                   [IsEmpty moveFrom, HasPiece Pawn colour moveTo]
                   facts
               , Holds (HasKing colour kingCell) facts
               , Unthreatened kingCell (Opponent colour) facts'
               )
             => Board facts
             -> Board facts'
capturePawn _ _ _ _ _ Board = Board

moveKing :: forall (colour :: Colour)
         -> forall (moveFrom :: Cell)
         -> forall (moveTo :: Cell)
         -> ( Holds (HasKing colour moveFrom) facts
            , Holds (IsEmpty moveTo) facts
            , moveFrom ~ 'Cell hFrom vFrom
            , moveTo ~ 'Cell hTo vTo
            , facts' ~ DeleteInsert
                [IsEmpty moveTo, HasKing colour moveFrom]
                [IsEmpty moveFrom, HasKing colour moveTo]
                facts
            , ( (hTo ~ Succ hFrom \/ hTo ~ Pred hFrom)
              , (vTo ~ vFrom \/ vTo ~ Succ vFrom \/ vTo ~ Pred vFrom)
              )
              \/
              ( (hTo ~ hFrom \/ hTo ~ Succ hFrom \/ hTo ~ Pred hFrom)
              , (vTo ~ Succ vFrom \/ vTo ~ Pred vFrom)
              )
            , Unthreatened moveTo (Opponent colour) facts'
            )
         => Board facts
         -> Board facts'
moveKing _ _ _ Board = Board

captureKing :: forall (colour :: Colour)
            -> forall (moveFrom :: Cell)
            -> forall (moveTo :: Cell)
            -> forall (opponentPiece :: Piece)
            -> ( Holds (HasKing colour moveFrom) facts
               , Holds (HasPiece opponentPiece (Opponent colour) moveTo) facts
               , moveFrom ~ 'Cell hFrom vFrom
               , moveTo ~ 'Cell hTo vTo
               , facts' ~ DeleteInsert
                   [HasPiece opponentPiece (Opponent colour) moveTo, HasKing colour moveFrom]
                   [IsEmpty moveFrom, HasKing colour moveTo]
                   facts
               , ( (hTo ~ Succ hFrom \/ hTo ~ Pred hFrom)
                 , (vTo ~ vFrom \/ vTo ~ Succ vFrom \/ vTo ~ Pred vFrom)
                 )
                 \/
                 ( (hTo ~ hFrom \/ hTo ~ Succ hFrom \/ hTo ~ Pred hFrom)
                 , (vTo ~ Succ vFrom \/ vTo ~ Pred vFrom)
                 )
               , ReallyUnthreatened moveTo (Opponent colour) facts'
               )
             => Board facts
             -> Board facts'
captureKing _ _ _ _ Board = Board

