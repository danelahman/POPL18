{-# OPTIONS --without-K #-}

----------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------
------------ Code accompanying Section 7 of the paper "Handling fibred algebraic effects" ----------
----------------------------------------------------------------------------------------------------
-- Using a handler to define a predicate that holds if the computation follows the given protocol --
----------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

open import eMLTT

module IOPatterns where

{- Canonical elements of type UFA for the theory of input-output of bits -}

data UF (X : Set) : Set where
  F-return : (x : X) -> UF X
  F-read   : (One + One -> UF X) -> UF X
  F-write  : One + One -> UF X -> UF X


{- Type of protocols -}

data Protocol : Set where
  r  : (One + One -> Protocol) -> Protocol
  w  : (One + One -> U) -> Protocol -> Protocol
  e  : Protocol
  or : Protocol -> Protocol -> Protocol


{- Handling IO-computations using the handler for protocols -}

handled-with : {X : Set} -> UF X -> (X -> Protocol -> U) -> Protocol -> U
handled-with (F-return x)  f p       = f x p
handled-with (F-read c)    f (r p)   = pi-c (sum-c one-c one-c)
                                            (λ v -> handled-with (c v) f (p v))
handled-with (F-write v c) f (w q p) = sig-c (q v)
                                             (λ w -> handled-with c f p)
handled-with c f (or p0 p1)          = sum-c (handled-with c f p0)
                                             (handled-with c f p1)
handled-with _             _ _       = zero-c


{- Predicate that holds when the given computation follows the given protocol -}

follows-protocol : {X : Set} -> UF X -> Protocol -> U
follows-protocol c p = handled-with c v-ret p

  where v-ret : {X : Set} -> X -> Protocol -> U
        v-ret x e = one-c
        v-ret _ _ = zero-c


{- Example uses of this predicate -}

ex-c : UF One
ex-c = F-write (inl ⋆) (F-read (λ v -> F-write v (F-return ⋆)))

ex1-p : Protocol
ex1-p = w (λ _ -> one-c) (r (λ v -> w (λ _ -> one-c) e))

ex1 :     El (follows-protocol ex-c ex1-p)
      ==₁ Sigma One (λ _ -> One + One -> Sigma One (λ _ -> One))
ex1 = refl _

ex1-witness : Sigma One (λ _ -> One + One -> Sigma One (λ _ -> One))
ex1-witness = ⋆ , (λ _ -> ⋆ , ⋆)

ex2-p : Protocol
ex2-p = w (λ _ -> one-c) (w (λ _ -> one-c) e)

ex2 :     El (follows-protocol ex-c ex2-p)
      ==₁ Sigma One (λ _ -> Zero)
ex2 = refl _
