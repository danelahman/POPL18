{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------
---- Code accompanying Section 7 of the paper "Handling fibred algebraic effects" ----
--------------------------------------------------------------------------------------
---------- Using a handler to define a predicate that disallows all writes -----------
--------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------

open import eMLTT

module IONoWrites where

{- A representation of the canonical elements of type UFA for the theory of input-output of bits -}

data UF (X : Set) : Set where
  F-return : (x : X) -> UF X
  F-read   : (One + One -> UF X) -> UF X
  F-write  : One + One -> UF X -> UF X


{- Handling IO-computations using the handler for disallowing writes -}

handled-with : {X : Set} -> UF X -> (X -> U) -> U
handled-with (F-return x)  f = f x
handled-with (F-read c)    f = pi-c (sum-c (one-c) (one-c)) (λ v -> handled-with (c v) f)
handled-with (F-write v c) f = zero-c


{- Predicate that disallows all writes -}

no-w : {X : Set} -> UF X -> U
no-w c = handled-with c (λ _ -> one-c)


{- Example use of this predicate -}

ex : {X : Set}
  -> (f : One + One -> One + One)
  -> (c : One + One -> UF X)
  -> (El (no-w {X} (F-read (λ v -> F-write (f v) (c v))))) ==₁ (One + One -> Zero)
ex f c = refl _
