{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RequiredTypeArguments #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE StrictData #-}

module Chess.Moves
  ( Board
  , initialBoard
  , Unthreatened'(..)
  , Threatened'(..)
  , Move(..)
  , makeMove
  , module Common.TypeOr
  )
  where

import Chess.Types
import Prelude.Singletons
import Data.Singletons.Base.Enum

import Common.TypeOr
import qualified Fcf as F
import qualified Fcf.Data.List as F
import Data.Void
import Common.Terminating
import qualified Control.Category
import Data.Kind

data Board (facts :: FactSet) = Board

type role Board nominal

type HasKing = HasPiece King

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
  MovePawn2 :: ( Holds (HasPiece Pawn colour moveFrom) facts
               , Holds (IsEmpty moveTo) facts
               , moveFrom ~ 'Cell hFrom (PawnRank colour)
               , moveTo ~ 'Cell hFrom vTo
               , vTo ~ Forward colour (Forward colour (PawnRank colour))
               , facts' ~ DeleteInsert
                   [IsEmpty moveTo, HasPiece Pawn colour moveFrom]
                   [IsEmpty moveFrom, HasPiece Pawn colour moveTo]
                   facts
               , Holds (HasKing colour kingCell) facts
               )
            => Unthreatened' kingCell (Opponent colour) facts'
            -> Move colour moveFrom moveTo facts facts'
  CapturePawn :: ( Holds (HasPiece Pawn colour moveFrom) facts
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
                 )
              => Unthreatened' kingCell (Opponent colour) facts'
              -> Proxy opponentPiece -- aughhhhh no visible forall in GADTs yet, see GHC issue !25127 
              -> Move colour moveFrom moveTo facts facts'
  MoveKing :: ( Holds (HasKing colour moveFrom) facts
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
              )
           => Unthreatened' kingCell (Opponent colour) facts'
           -> Move colour moveFrom moveTo facts facts'
  CaptureKing :: ( Holds (HasKing colour moveFrom) facts
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
                 )
              => Unthreatened' kingCell (Opponent colour) facts'
              -> Proxy opponentPiece
              -> Move colour moveFrom moveTo facts facts'

makeMove :: Move colour moveFrom moveTo facts facts' -> Board facts -> Board facts'
makeMove !_ Board = Board

-- there is no capture at 'moveTo' by a piece of colour 'by'
data Unthreatened' (moveTo :: Cell) (by :: Colour) (facts :: FactSet)
  = forall realPiece. Holds (HasPiece realPiece (Opponent by) moveTo) facts => UnthreatenedActual
      (Proxy realPiece)
      -- PROBLEM: this is not sound: suppose we have UnthreateendActual (\m -> undefined):
      -- haskell does not have termination checking and
      -- we'll likely never call the function used as evidence of the move not existing,
      -- (because it is supposed to state the move does not exist)
      -- so we can force an invalid sequence of moves to typecheck by this route,
      -- and worse yet, it will even be non-bottom at runtime.
      --
      -- can:
      -- - have some kind of "terminating arrow" type (a -|> b) that is
      -- externally guaranteed to either be bottom itself or never bottom
      -- regardless of input: would probably require to make an entire DSL to
      -- do termination checking on within haskell - ideally at compile-time.
      -- - do something with LinearTypes to force previous proofs of Unthreatened
      -- to evaluate if we hit a move that we previously claimed to be impossible:
      -- would require somehow finding all moves in the future that are implied
      -- to be impossible by some past move being impossible, and then keeping
      -- track of these moves.
      (forall moveFrom facts'. Move by moveFrom moveTo facts facts' -> Void)
  | Holds (IsEmpty moveTo) facts => UnthreatenedHypothetical
      ( forall moveFrom facts1 facts' hypotheticalPiece.
        facts1 ~ DeleteInsert '[IsEmpty moveTo] '[HasPiece hypotheticalPiece (Opponent by) moveTo] facts
      => Move by moveFrom moveTo facts1 facts' -|> Void
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

data IsMove (t :: Type) :: F.Exp Bool

type family IsMove' m where
  IsMove' (Move _ _ _ _ _) = True
  IsMove' _ = False

type instance F.Eval (IsMove m) = IsMove' m

-- TODO: TermLiteral instance for Move

-- | Terminating function type
newtype a -|> b = TermFn (TermExpr IsMove () '[] (a -> b))

instance Control.Category.Category (-|>) where
  id = TermFn $ TermLamE (TermVarE TermVarNil)
  (.) (TermFn f) (TermFn g) =
    TermFn $ TermLamE (TermAppE (weakenRight _ f) (TermAppE (weakenRight _ g) (TermVarE TermVarNil)))
