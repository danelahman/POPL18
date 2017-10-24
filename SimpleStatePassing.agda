{-# OPTIONS --without-K #-}

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
---- Code accompanying Section 7 of the paper "Handling fibred algebraic effects" ---
-------------------------------------------------------------------------------------
------------ Natural state-passing presentation of stateful computations ------------
-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------

open import eMLTT

module SimpleStatePassing where

{- Types of locations and store values; the former is assumed to have decidable equality -}

postulate
  Loc : Set
  Val : Set
  isDec : (l l' : Loc) -> (l == l') + (l == l' -> Zero)


{- Stores and lookup/update operations on them -}

Store = Loc -> Val

sel : Store -> Loc -> Val
sel s l = s l

upd : Store -> Loc -> Val -> Store
upd s l v l' = +-elim (isDec l l') (λ _ -> v) (λ _ -> sel s l')


{- The state-passing representation of stateful computations -}

State : Set -> Set
State X = Store -> (X × Store)

get : {X : Set} -> Loc -> (Val -> State X) -> State X
get l k s = k (sel s l) s

put : {X : Set} -> Loc -> Val -> State X -> State X
put l v k s = k (upd s l v)
