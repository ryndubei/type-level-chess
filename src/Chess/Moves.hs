{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RequiredTypeArguments #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ImpredicativeTypes #-}

module Chess.Moves
  ( Board
  , movePawn1
  , movePawn2
  )
  where

import Chess.Types
import Prelude.Singletons
import Data.Kind

data Board (facts :: FactSet) = Board

type role Board nominal

type Unthreatened (cell :: Cell) (by :: Colour) (facts :: FactSet) =
  ( UnthreatenedByKnight cell by facts
  , UnthreatenedByBishop cell by facts
  , UnthreatenedByRook cell by facts
  , UnthreatenedByPawn cell by facts
  , UnthreatenedByQueen cell by facts
  , UnthreatenedByKing cell by facts
  )

-- TODO
type UnthreatenedByKnight cell by facts = () :: Constraint
type UnthreatenedByBishop cell by facts = () :: Constraint
type UnthreatenedByRook cell by facts = () :: Constraint
type UnthreatenedByPawn cell by facts = () :: Constraint
type UnthreatenedByQueen cell by facts = () :: Constraint
type UnthreatenedByKing cell by facts = () :: Constraint

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
