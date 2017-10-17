{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------
---- Code accompanying Section 7 of the paper "Handling fibred algebraic effects" ----
--------------------------------------------------------------------------------------
--- Using a handler to lift predicates from return values to stateful computations ---
--------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------

open import StatePassing
open import eMLTT

module StateLifting where

{- Canonical elements of type UFA for the theory of global state -}

data UF (X : Set) : Set where
  F-return : (x : X) -> UF X
  F-get    : (l : Loc) -> (Val l -> UF X) -> UF X
  F-put    : (l : Loc) -> (v : Val l) -> UF X -> UF X


{- Handling stateful computations as state-passing value function -}

handled-with : {X Y : Set} -> UF X -> (X -> State Y) -> State Y
handled-with (F-return x)  f = f x
handled-with (F-get l c)   f = get l (λ v -> handled-with (c v) f)
handled-with (F-put l v c) f = put l v (handled-with c f)


{- The weakest precondition transformer defined using the handling construct -}

wp : {X : Set} -> (Q : X -> Store -> U) -> UF X -> Store -> U
wp {X} Q c s = fst ((handled-with {X} {U} c (λ x s' -> Q x s' , s')) s)


{- Dijkstra's weakest precondition semantics of stateful programs -}

wp-eq1 : {X : Set}
         {Q : X -> Store -> U}
         {x : X}
         {s : Store}
      -> wp Q (F-return x) s == Q x s
wp-eq1 = refl _

wp-eq2 : {X : Set}
         {Q : X -> Store -> U}
         {l : Loc}
         {c : Val l -> UF X}
         {s : Store}
      -> wp Q (F-get l c) s == wp Q (c (sel s l)) s
wp-eq2 = refl _

wp-eq3 : {X : Set}
         {Q : X -> Store -> U}
         {l : Loc}
         {v : Val l}
         {c : UF X}
         {s : Store}
      -> wp Q (F-put l v c) s == wp Q c (upd s l v)
wp-eq3 = refl _

