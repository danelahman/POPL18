{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------
---- Code accompanying Section 7 of the paper "Handling fibred algebraic effects" ----
--------------------------------------------------------------------------------------
------------ Natural state-passing presentation of stateful computations -------------
--------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------

open import eMLTT

module StatePassing where

{- Types of locations and store values, the former are a decidable set -}

postulate
  Loc : Set
  Val : Loc -> Set
  isDec : (l l' : Loc) -> (l == l') + (l == l' -> Zero)
  isSet : {l l' : Loc} -> (p q : l == l') -> p == q


{- Stores and lookup/update operations on them -}

Store = (l : Loc) -> Val l

sel : Store -> (l : Loc) -> Val l
sel s l = s l

upd : Store -> (l : Loc) -> (v : Val l) -> Store
upd s l v l' = +-elim (isDec l l') (λ p -> transport p v) (λ _ -> sel s l')


{- The state-passing representation of stateful computations -}

State : Set -> Set
State X = Store -> (X × Store)

get : {X : Set} -> (l : Loc) -> (Val l -> State X) -> State X
get l k s = k (sel s l) s

put : {X : Set} -> (l : Loc) -> (v : Val l) -> State X -> State X
put l v k s = k (upd s l v)
