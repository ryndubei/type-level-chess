{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RequiredTypeArguments #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ImpredicativeTypes #-}

module Frog (gameTree) where
import Data.Typeable
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Frog.Types
import Frog.Moves
import Data.Singletons
import Data.Singletons.Decide
import Data.Bool.Singletons
import Data.Singletons.Base.Enum
import Control.Applicative

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
gameTree board = GameTree (SomeBoard board) . Map.fromList $ do
  -- Yes, this is O(mn) with the set of facts. Be glad I did not make it O(mn^2).
  -- (could easily improve by searching through the facts set for
  -- HasFrog colourToMove c for some 'c', instead of every 'c')
  hs1 <- [minBound .. maxBound] :: [Horizontal]
  vs1 <- [minBound .. maxBound] :: [Vertical]

  let moveFrom = Cell hs1 vs1
      mboard1 :: Maybe (Cell -> Maybe SomeBoard)
      mboard1 = case toSing moveFrom of
        SomeSing (sMvf :: Sing mvf) -> case singInstance sMvf of
          SingInstance -> 
            (\f -> \moveTo -> case toSing moveTo of
              SomeSing (sMvt :: Sing mvt) -> case singInstance sMvt of
                SingInstance -> f mvt
            ) <$> tryMove colourToMove mvf board

  -- Shortcut, using the assumption that we always must have some piece at the moveFrom cell
  board1 <- maybe empty pure mboard1

  -- Take nearby cells to hs1 and vs1, assuming that all movement is to adjacent cells only.
  hs2 <- [pred hs1 | hs1 > minBound] ++ [hs1] ++ [succ hs1 | hs1 < maxBound] :: [Horizontal]
  vs2 <- [pred vs1 | vs1 > minBound] ++ [vs1] ++ [succ vs1 | vs1 < maxBound] :: [Vertical]

  let moveTo = Cell hs2 vs2
      move = Move{moveFrom, moveTo}
      mboard = board1 moveTo

  SomeBoard board' <- maybe empty pure mboard
  let subGameTree = case sing @colourToMove of
        SBlack -> gameTree @'White board'
        SWhite -> gameTree @'Black board'
  pure (move, subGameTree)

tryMove :: forall (colourToMove :: Colour)
        -> forall (moveFrom :: Cell)
        -> (SingI colourToMove, SingI moveFrom, SingI facts)
        => Board facts
        -> Maybe (forall (moveTo :: Cell) -> SingI moveTo => Maybe SomeBoard)
tryMove colourToMove moveFrom board =
  let hasFrogToMove = testFact (HasFrog colourToMove moveFrom) board
  in case hasFrogToMove of
    Proved Refl -> Just $ \moveTo -> tryMove' colourToMove moveFrom moveTo board Refl
    _ -> Nothing

tryMove' :: forall (colourToMove :: Colour)
         -> forall (moveFrom :: Cell)
         -> forall (moveTo :: Cell)
         -> (SingI colourToMove, SingI moveFrom, SingI moveTo, SingI facts)
         => Board facts
         -> ('True :~: FactHolds (HasFrog colourToMove moveFrom) facts)
         -> Maybe SomeBoard
tryMove' colourToMove moveFrom moveTo (board :: Board facts) Refl =
  case singInstance (sOpponent (sing @colourToMove)) of
    SingInstance -> case (sing @moveFrom, sing @moveTo) of
      (SCell (shFrom :: Sing hFrom) (svFrom :: Sing vFrom), SCell (shTo :: Sing hTo) (svTo :: Sing vTo)) ->
        let isAttacking = testFact (HasFrog (Opponent colourToMove) moveTo) board
    
            movingV :: Maybe (Either (vTo :~: Succ vFrom) (vTo :~: Pred vFrom))
            movingV = movedToAdjacent svFrom svTo
    
            movingH :: Maybe (Either (hTo :~: Succ hFrom) (hTo :~: Pred hFrom))
            movingH = movedToAdjacent shFrom shTo
    
            fromToSameH = shFrom %~ shTo
    
            fromToSameV = svFrom %~ svTo
    
            isMoving = testFact (IsEmpty moveTo) board
        in if
        | Proved Refl <- isAttacking ->
            {-
            proveNewFactSet is unfortunately necessary in order to prove to
            the typechecker that (SFactSet facts') exists.
            
            The alternative is making Board a newtype and storing SFactSet facts'
            there, but that transfers the responsibility of doing the runtime
            insertions/deletions to the moveFrog/captureFrog functions. That
            would in turn require adding the extra constraints SingI colour,
            SingI moveFrom and SingI moveTo to their type signatures. I chose
            not to do this to keep the moves specifications in Frog.Moves as simple
            as possible.

            The deletes/inserts have to appear in exactly the order they do in the type signatures
            in Frog.Moves.

            As far as I know, GHC cannot infer the deletes/inserts automatically.
            -}
            proveNewFactSet
              [HasFrog (Opponent colourToMove) moveTo, HasFrog colourToMove moveFrom]
              [IsEmpty moveFrom, HasFrog colourToMove moveTo]
              facts $
                case (movingV, movingH) of
                  (Just (Left Refl), Just (Left Refl)) ->
                    let (b1,_,_,_) = captureFrog colourToMove moveFrom moveTo board
                     in Just $ SomeBoard b1
                  (Just (Right Refl), Just (Right Refl)) ->
                    let (_,b2,_,_) = captureFrog colourToMove moveFrom moveTo board
                     in Just $ SomeBoard b2
                  (Just (Left Refl), Just (Right Refl)) ->
                    let (_,_,b3,_) = captureFrog colourToMove moveFrom moveTo board
                     in Just $ SomeBoard b3
                  (Just (Right Refl), Just (Left Refl)) ->
                    let (_,_,_,b4) = captureFrog colourToMove moveFrom moveTo board
                     in Just $ SomeBoard b4
                  _ -> Nothing
        | Proved Refl <- isMoving ->
          proveNewFactSet
            [IsEmpty moveTo, HasFrog colourToMove moveFrom]
            [IsEmpty moveFrom, HasFrog colourToMove moveTo]
            facts $
              case (movingV, fromToSameH, movingH, fromToSameV) of
                (Just (Left Refl), Proved Refl, _, _) ->
                  let (b1,_,_,_) = moveFrog colourToMove moveFrom moveTo board
                   in Just $ SomeBoard b1
                (Just (Right Refl), Proved Refl, _, _) ->
                  let (_,b2,_,_) = moveFrog colourToMove moveFrom moveTo board
                   in Just $ SomeBoard b2
                (_, _, Just (Left Refl), Proved Refl) ->
                  let (_,_,b3,_) = moveFrog colourToMove moveFrom moveTo board
                   in Just $ SomeBoard b3
                (_, _, Just (Right Refl), Proved Refl) ->
                  let (_,_,_,b4) = moveFrog colourToMove moveFrom moveTo board
                   in Just $ SomeBoard b4
                _ -> Nothing
        | otherwise -> Nothing

testFact :: forall (fact :: Fact)
          -> (SingI fact, SingI facts)
          => Board facts
          -> Decision ('True :~: FactHolds fact facts)
testFact fact (_ :: Board facts) = STrue %~ sFactHolds (sing @fact) (sing @facts)

movedToAdjacent :: (SDecide k, SBounded k, SEnum k) => Sing (start :: k) -> Sing (end :: k) -> Maybe (Either (end :~: Succ start) (end :~: Pred start))
movedToAdjacent sStart sEnd =
  case (sStart %~ sMaxBound, sStart %~ sMinBound) of
    (Proved _, Proved _) -> Nothing
    (Proved Refl, _) -> case (sEnd %~ sPred sStart) of
      Proved Refl -> Just (Right Refl)
      Disproved _ -> Nothing
    (_, Proved Refl) -> case (sEnd %~ sSucc sStart) of
      Proved Refl -> Just (Left Refl)
      Disproved _ -> Nothing
    (_, _) -> case (sEnd %~ sSucc sStart, sEnd %~ sPred sStart) of
      (Proved Refl, _) -> Just (Left Refl)
      (_, Proved Refl) -> Just (Right Refl)
      (_, _) -> Nothing

proveNewFactSet :: forall deletes
                -> forall inserts
                -> forall facts
                -> (SingI deletes, SingI inserts, SingI facts)
                => (SingI (DeleteInsert deletes inserts facts) => r)
                -> r
proveNewFactSet deletes inserts facts r =
  case singInstance (sDeleteInsert (sing @deletes) (sing @inserts) (sing @facts)) of
    SingInstance -> r

testGame = 
  let (_,_,a,_) = moveFrog White (Cell A One) (Cell B One) (initialBoard)
      (_,b,_,_) = moveFrog Black (Cell H Eight) (Cell H Seven) a
      (_,_,c,_) = moveFrog White (Cell B One) (Cell C One) b
      (_,d,_,_) = moveFrog Black (Cell H Seven) (Cell H Six) c
      (_,_,e,_) = moveFrog White (Cell C One) (Cell D One) d
      (_,f,_,_) = moveFrog Black (Cell H Six) (Cell H Five) e
      (_,_,g,_) = moveFrog White (Cell D One) (Cell E One) f
      (_,h,_,_) = moveFrog Black (Cell H Five) (Cell H Four) g
      (_,_,i,_) = moveFrog White (Cell E One) (Cell F One) h
      (_,j,_,_) = moveFrog Black (Cell H Four) (Cell H Three) i
      (_,_,k,_) = moveFrog White (Cell F One) (Cell G One) j
      (_,l,_,_) = moveFrog Black (Cell H Three) (Cell H Two) k
      (_,_,m,_) = moveFrog White (Cell G One) (Cell H One) l
      (_,_,_,n) = moveFrog Black (Cell H Two) (Cell G Two) m
      (_,_,o,_) = captureFrog White (Cell H One) (Cell G Two) n
   in o