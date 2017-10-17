{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------
---- Code accompanying Section 7 of the paper "Handling fibred algebraic effects" ----
--------------------------------------------------------------------------------------
------ Using handlers to lift predicates from return values to IO-computations -------
--------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------

open import eMLTT

module IOLifting where

{- Canonical elements of type UFA for the theory of input-output of bits -}

data UF (X : Set) : Set where
  F-return : (x : X) -> UF X
  F-read   : (One + One -> UF X) -> UF X
  F-write  : One + One -> UF X -> UF X


{- Handling IO-computations using the handler involving the Sigma-type -}

handled-with-sig : {X : Set} -> UF X -> (X -> U) -> U
handled-with-sig (F-return x)  f = f x
handled-with-sig (F-read c)    f = sig-c (sum-c one-c one-c)
                                         (λ v -> handled-with-sig (c v) f)
handled-with-sig (F-write v c) f = handled-with-sig c f


{- Handling IO-computations using the handler involving the Pi-type -}

handled-with-pi : {X : Set} -> UF X -> (X -> U) -> U
handled-with-pi (F-return x)  f = f x
handled-with-pi (F-read c)    f = pi-c (sum-c one-c one-c)
                                       (λ v -> handled-with-pi (c v) f)
handled-with-pi (F-write v c) f = handled-with-pi c f


{- The possibility modality -}

possibility-modality : {X : Set} -> (X -> U) -> UF X -> U
possibility-modality P c = handled-with-sig c P


{- The necessity modality -}

necessity-modality : {X : Set} -> (X -> U) -> UF X -> U
necessity-modality P c = handled-with-pi c P
