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
