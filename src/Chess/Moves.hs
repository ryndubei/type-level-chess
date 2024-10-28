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

data Board (facts :: FactSet) = Board

type role Board nominal

type HasKing = HasPiece King

type Unthreatened (h :: Horizontal) (v :: Vertical) (target :: Colour) (facts :: FactSet) =
  ( UnthreatenedBy Knight h v target facts
  , UnthreatenedBy Bishop h v target facts
  , UnthreatenedBy Rook h v target facts
  , UnthreatenedBy Pawn h v target facts
  , UnthreatenedBy Queen h v target facts
  -- Don't need to check this except when moving the king:
  -- , UnthreatenedBy King h v target facts
  )

-- TODO
type family UnthreatenedBy (piece :: Piece) (h :: Horizontal) (v :: Vertical) (target :: Colour) (facts :: FactSet) :: Constraint where
  UnthreatenedBy Knight h v target facts = ()
  UnthreatenedBy Bishop h v target facts = ()
  UnthreatenedBy Rook h v target facts = ()
  UnthreatenedBy Pawn h v target facts = ()
  UnthreatenedBy Queen h v target facts = ()
  UnthreatenedBy King h v target facts = ()

type ReallyUnthreatened (h :: Horizontal) (v :: Vertical) (target :: Colour) (facts :: FactSet) =
  ( Unthreatened h v target facts
  , UnthreatenedBy King h v target facts
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

movePawn1 :: forall (colour :: Colour)
          -> forall (moveFrom :: Cell)
          -> forall (moveTo :: Cell)
          -> forall (kingCell :: Cell)
          -> ( Holds (HasPiece Pawn colour moveFrom) facts
             , Holds (IsEmpty moveTo) facts
             , moveFrom ~ 'Cell hFrom vFrom
             , moveTo ~ 'Cell hFrom vTo
             , kingCell ~ 'Cell hKing vKing
             , vTo ~ Forward colour vFrom
             , 'True ~ If (colour == White)
                 (vTo < MaxBound vFrom)
                 (vTo > MinBound vFrom)
             , facts' ~ DeleteInsert
                 [IsEmpty moveTo, HasPiece Pawn colour moveFrom]
                 [IsEmpty moveFrom, HasPiece Pawn colour moveTo]
                 facts
             , Holds (HasKing colour kingCell) facts
             , Unthreatened hKing vKing colour facts'
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
             , kingCell ~ 'Cell hKing vKing
             , vTo ~ Forward colour (Forward colour (PawnRank colour))
             , facts' ~ DeleteInsert
                 [IsEmpty moveTo, HasPiece Pawn colour moveFrom]
                 [IsEmpty moveFrom, HasPiece Pawn colour moveTo]
                 facts
             , Holds (HasKing colour kingCell) facts
             , Unthreatened hKing vKing colour facts'
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
               , kingCell ~ 'Cell hKing vKing
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
               , Unthreatened hKing vKing colour facts'
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
            , ReallyUnthreatened hTo vTo colour facts'
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
               , ReallyUnthreatened hTo vTo colour facts'
               )
             => Board facts
             -> Board facts'
captureKing _ _ _ _ Board = Board

