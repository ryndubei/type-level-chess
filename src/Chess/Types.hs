{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module Chess.Types 
  ( -- * Colour
    Colour(..)
  , SColour(..)
  , Opponent
  , sOpponent
    -- * Cells
  , Vertical(..)
  , SVertical(..)
  , Horizontal(..)
  , SHorizontal(..)
  , Cell(..)
  , SCell(..)
  , Forward
  , sForward
  , Backward
  , sBackward
  , Leftward
  , sLeftward
  , Rightward
  , sRightward
  , PawnRank
  , sPawnRank
    -- * Pieces
  , Piece(..)
  , SPiece(..)
    -- * Facts
  , Fact(..)
  , SFact(..)
  , Holds
  , FactSet
  , SFactSet
  , FactHolds
  , sFactHolds
  , EmptyFactSet
  , sEmptyFactSet
  , DeleteFact
  , sDeleteFact
  , DeleteFacts
  , sDeleteFacts
  , InsertFact
  , sInsertFact
  , InsertFacts
  , sInsertFacts
  , DeleteInsert
  , sDeleteInsert
  , FactSetFromList
  , sFactSetFromList
  )
  where

import Data.Singletons.TH
import Prelude.Singletons
import Data.Singletons.Base.Enum
import Data.Foldable.Singletons

data Colour = Black | White

data Horizontal = A | B | C | D | E | F | G | H
  deriving (Eq, Ord, Read, Show, Enum, Bounded)

data Vertical = One | Two | Three | Four | Five | Six | Seven | Eight
  deriving (Eq, Ord, Read, Show, Enum, Bounded)

data Cell = Cell
  { hor :: Horizontal
  , ver :: Vertical
  }
  deriving (Eq, Ord, Read, Show, Bounded)

data Piece = Pawn | Knight | Bishop | Rook | Queen | King

data Fact
  = HasPiece Piece Colour Cell
  | Unmoved Cell
  | IsEmpty Cell

{-
Idea for implementing en-passant:

New field in 'FactSet' (or in 'Board') storing (Maybe Cell). This field is
updated with a 'Just' value whenever a pawn moves by two cells, and wiped with
'Nothing' whenever any other move is made.
-}
newtype FactSet = FactSet [Fact]

$(genSingletons [''Horizontal, ''Vertical, ''Cell, ''Fact, ''Colour, ''FactSet, ''Piece])

$(singEqInstances [''Horizontal, ''Vertical, ''Cell, ''Fact, ''Colour, ''Piece, ''FactSet])

$(singOrdInstances [''Horizontal, ''Vertical, ''Cell, ''Fact, ''Colour, ''Piece, ''FactSet])

$(singEnumInstances [''Horizontal, ''Vertical])

$(singBoundedInstances [''Horizontal, ''Vertical])

$(singDecideInstances [''Horizontal, ''Vertical, ''Cell, ''Fact, ''Colour, ''Piece])

$(showSingInstances [''Horizontal, ''Vertical, ''Colour, ''Cell, ''Fact, ''FactSet, ''Piece])

$(singletonsOnly [d|
  opponent :: Colour -> Colour
  opponent Black = White
  opponent White = Black

  forward :: Colour -> Vertical -> Vertical
  forward White v = succ v
  forward Black v = pred v

  backward :: Colour -> Vertical -> Vertical
  backward White v = pred v
  backward Black v = succ v

  pawnRank :: Colour -> Vertical
  pawnRank White = Two
  pawnRank Black = Seven

  leftward :: Horizontal -> Horizontal
  leftward = pred

  rightward :: Horizontal -> Horizontal
  rightward = succ

  factHolds :: Fact -> FactSet -> Bool
  factHolds fact (FactSet facts) = fact `elem` facts

  emptyFactSet :: FactSet
  emptyFactSet = FactSet []

  deleteFact :: Fact -> FactSet -> FactSet
  deleteFact fact (FactSet facts) = FactSet $ filter (/= fact) facts

  insertFact :: Fact -> FactSet -> FactSet
  insertFact fact (FactSet facts) = FactSet $ fact : facts

  deleteFacts :: [Fact] -> FactSet -> FactSet
  deleteFacts delFacts facts = foldl' (flip deleteFact) facts delFacts

  insertFacts :: [Fact] -> FactSet -> FactSet
  insertFacts insFacts facts = foldl' (flip insertFact) facts insFacts

  deleteInsert :: [Fact] -> [Fact] -> FactSet -> FactSet
  deleteInsert delFacts insFacts facts = insertFacts insFacts (deleteFacts delFacts facts)

  factSetFromList :: [Fact] -> FactSet
  -- can't use 'nub' because that causes the reduction stack to overflow, so we just take the
  -- list of facts blindly, then compensate by filtering out all fact duplicates
  -- instead of using the 'delete' operation
  factSetFromList facts = FactSet facts
  |])

type Holds (fact :: Fact) (facts :: FactSet) = 'True ~ FactHolds fact facts
