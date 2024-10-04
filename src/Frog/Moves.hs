{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RequiredTypeArguments #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ImpredicativeTypes #-}

module Frog.Moves
  ( Board
  , initialBoard
  , moveFrog
  , captureFrog
  )
  where

import Frog.Types
import Fcf
import Fcf.Data.List
import Data.Singletons.Base.Enum

data Board (facts :: FactSet) = Board

type role Board nominal

data HelperMap :: [a] -> (a -> b) -> Exp [b]
type instance Eval (HelperMap '[] f) = '[]
type instance Eval (HelperMap (x ': xs) f) = f x ': Eval (HelperMap xs f)

initialBoard :: ( frogFacts ~ '[ HasFrog White ('Cell A One), HasFrog Black ('Cell H Eight)]
                , horizontalsInner ~ '[ B, C, D, E, F, G ]
                , verticalsInner ~ '[ Two, Three, Four, Five, Six, Seven ]
                , (emptyRowsInner :: [Vertical -> Cell]) ~ Eval (Map (Pure1 'Cell) horizontalsInner)
                , emptyCellsInner ~ Eval (ConcatMap (HelperMap verticalsInner) emptyRowsInner)
                , emptyCellsOuterA ~ Eval (Map (Pure1 ('Cell 'A)) '[ Two, Three, Four, Five, Six, Seven, Eight])
                , emptyCellsOuterH ~ Eval (Map (Pure1 ('Cell 'H)) '[ One, Two, Three, Four, Five, Six, Seven])
                , emptyCellsOuter1 ~ '[ 'Cell B One, 'Cell C One, 'Cell D One, 'Cell E One, 'Cell F One, 'Cell G One, 'Cell H One ]
                , emptyCellsOuter8 ~ '[ 'Cell A Eight, 'Cell B Eight, 'Cell C Eight, 'Cell D Eight, 'Cell E Eight, 'Cell F Eight, 'Cell G Eight ]
                , emptyCells ~ Eval (Concat '[emptyCellsInner, emptyCellsOuterA, emptyCellsOuterH, emptyCellsOuter1, emptyCellsOuter8])
                , emptyCellFacts ~ Eval (Map (Pure1 (IsEmpty)) emptyCells)
                ) => Board (FactSetFromList (Eval (frogFacts ++ emptyCellFacts)))
initialBoard = Board

moveFrog :: forall (colour :: Colour)
        -> forall (moveFrom :: Cell)
        -> forall (moveTo :: Cell)
        -> ( Holds (HasFrog colour moveFrom) facts
           , Holds (IsEmpty moveTo) facts
           , moveFrom ~ 'Cell hFrom vFrom
           , moveTo ~ 'Cell hTo vTo
           , facts' ~ DeleteInsert
               [IsEmpty moveTo, HasFrog colour moveFrom]
               [IsEmpty moveFrom, HasFrog colour moveTo]
               facts
           )
        => Board facts
        -- type-level disjunction!
        -> ( (hFrom ~ hTo, vTo ~ Succ vFrom) => Board facts'
           , (hFrom ~ hTo, vTo ~ Pred vFrom) => Board facts'
           , (hTo ~ Succ hFrom, vTo ~ vFrom) => Board facts'
           , (hTo ~ Pred hFrom, vTo ~ vFrom) => Board facts'
           )
moveFrog _ _ _ Board = (Board, Board, Board, Board)

captureFrog :: forall colour
           -> forall moveFrom
           -> forall moveTo
           -> ( Holds (HasFrog colour moveFrom) facts
              , Holds (HasFrog (Opponent colour) moveTo) facts
              , moveFrom ~ 'Cell hFrom vFrom
              , moveTo ~ 'Cell hTo vTo
              , facts' ~ DeleteInsert
                  [HasFrog (Opponent colour) moveTo, HasFrog colour moveFrom]
                  [IsEmpty moveFrom, HasFrog colour moveTo]
                  facts
              )
           => Board facts
           -> ( (hTo ~ Succ hFrom, vTo ~ Succ vFrom) => Board facts'
              , (hTo ~ Pred hFrom, vTo ~ Pred vFrom) => Board facts'
              , (hTo ~ Pred hFrom, vTo ~ Succ vFrom) => Board facts'
              , (hTo ~ Succ hFrom, vTo ~ Pred vFrom) => Board facts'
              )
captureFrog _ _ _ Board = (Board, Board, Board, Board)
