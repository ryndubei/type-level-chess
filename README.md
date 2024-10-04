# type-level-chess

**WORK IN PROGRESS:** not chess yet.

Currently, this library generates the game tree for only a heavily-simplified,
chess-like game that I named "Frog".

- We still have an 8x8 board.
- But: there are only two pieces on it, one black and one white. The white and
  black pieces are initially placed in opposite corners of the board, A1 and H8,
  respectively.
- Each piece can move to an adjacent cell once per (its colour's) turn, either
  directly horizontally/vertically to an empty cell, or capturing the opponent
  piece diagonally.

Again, this is very simple, but it suffices for a proof-of-concept.
It should be possible to "easily" write a full specification of chess by just
adding extra `Fact`s and moves to use them (including verifying that the king
is/isn't in check), while still keeping the same structure.

The way moves are specified takes inspiration from
[PDDL](https://en.wikipedia.org/wiki/Planning_Domain_Definition_Language). A
move is defined by constructing a function `Board facts -> Board facts'`, where
`facts` and `facts'` are collections of `Fact`s about the board state. 
Pre-conditions in `facts` and post-conditions in `facts'` are encoded using type 
equality constraints, and pre-conditions cannot have negations. For example:

```haskell
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
        -> ( (hFrom ~ hTo, vTo ~ Succ vFrom) => Board facts'
           , (hFrom ~ hTo, vTo ~ Pred vFrom) => Board facts'
           , (hTo ~ Succ hFrom, vTo ~ vFrom) => Board facts'
           , (hTo ~ Pred hFrom, vTo ~ vFrom) => Board facts'
           )
moveFrog _ _ _ Board = (Board, Board, Board, Board)
```

## Related work

The only similar project that I found is [Chesskell: a two player game at the type level](https://dl.acm.org/doi/pdf/10.1145/3471874.3472987)[^1]

[^1]: Toby Bailey and Michael B. Gale. 2021. Chesskell: A Two-Player Game at the Type Level. In _Proceedings of the 14th ACM SIGPLAN International Haskell Symposium (Haskell ’21), August 26-27, 2021, Virtual, Republic of Korea._ ACM, New York, NY, USA, 12 pages. https://doi.org/10.1145/3471874.3472987

Chesskell's approach essentially makes heavy use of the Haskell type system's
Turing-completeness in order to transfer all term-level computations for
checking moves almost-verbatim to the type level. The typechecker not only
verifies that moves are valid, it even has the power to find all valid moves if
needed. This allows writing helpful custom type errors, but it is very slow
and memory-intensive to compile, taking 25GB for an 8-move game. The resulting
types also exist solely on the type level, and therefore cannot be used at runtime 
due to type erasure.

While I have not confirmed this with a full chess implementation yet, I
anticipate that my approach will require much less memory and time to compile,
due to reducing the typechecker's responsibilities to trivial constraint checks.

Besides, my approach also uses the `singletons` library, which allows making
these checks at runtime instead, while still maintaining type safety - hence
being able to generate an infinite game tree. Not only does this greatly reduce
the amount of work done by the compiler, this also lets us typecheck games in
practical scenarios, where they are not hardcoded constants.
