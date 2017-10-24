{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------
---- Code accompanying Section 7 of the paper "Handling fibred algebraic effects" ----
--------------------------------------------------------------------------------------
------ Showing that decidability is closed under finite products and coproducts ------
--------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------

open import eMLTT

module DecExamples where

{- Definition of decidable propositional equality for a set X -}

isDec : Set -> Set
isDec X = (x x' : X) -> (x == x') + (x == x' -> Zero)


{- Zero is decidable -}
isDec-zero : isDec Zero
isDec-zero x x' = inr (λ _ -> x)


{- One is decidable -}
isDec-one : isDec One
isDec-one ⋆ ⋆ = inl (refl ⋆) --using pattern-matching on x and y to simulate definitional eta-expansion for One


{- Coproduct of decidable types is decidable, using the encode part of the encode-decode method -}

+-elim₁ : {X Y : Set}
          {Z : X + Y -> Set₁}
       -> (xy : X + Y)
       -> ((x : X) -> Z (inl x))
       -> ((y : Y) -> Z (inr y))
       -> Z xy
+-elim₁ (inl x) f g = f x
+-elim₁ (inr y) f g = g y

codeX : {X Y : Set} -> X -> X + Y -> Set
codeX x0 xy = +-elim₁ xy (λ x -> x0 == x) (λ _ -> Zero)

encodeX : {X Y : Set}
       -> (x0 : X)
       -> (xy : X + Y)
       -> (p : inl x0 == xy)
       -> codeX x0 xy
encodeX x0 xy p = transport {Y = λ xy -> codeX x0 xy} p (refl x0)

codeY : {X Y : Set} -> Y -> X + Y -> Set
codeY y0 xy = +-elim₁ xy (λ _ -> Zero) (λ y -> y0 == y)

encodeY : {X Y : Set}
       -> (y0 : Y)
       -> (xy : X + Y)
       -> (p : inr y0 == xy)
       -> codeY y0 xy
encodeY y0 xy p = transport {Y = λ xy -> codeY y0 xy} p (refl y0)

isDec-coprod : {X Y : Set} -> isDec X -> isDec Y -> isDec (X + Y)
isDec-coprod {X} {Y} p q xy xy'
  = (+-elim {Z = λ xy -> (xy' : X + Y) -> (xy == xy') + (xy == xy' -> Zero)}
            xy
            (λ x xy' -> +-elim {Z = λ xy' -> (inl x == xy') + (inl x == xy' -> Zero)}
                               xy'
                               (λ x' -> +-elim (p x x')
                                               (λ r -> inl (app-cong r))
                                               (λ r -> inr (λ r' -> r (encodeX x (inl x') r'))) )
                               (λ y' -> (inr (λ r -> encodeX x (inr y') r))))
            (λ y xy' -> +-elim {Z = λ xy' -> (inr y == xy') + (inr y == xy' -> Zero)}
                               xy'
                               (λ x' -> inr (λ r -> encodeY y (inl x') r))
                               (λ y' -> +-elim (q y y')
                                               (λ r -> inl (app-cong r))
                                               (λ r -> inr (λ r' -> r (encodeY y (inr y') r')))))
          ) xy'


{- Product of decidable types is decidable -}

isDec-prod-aux : {X Y : Set}
              -> {x x' : X}
              -> {y y' : Y}
              -> x == x'
              -> y == y'
              -> (x , y) == (x' , y')
isDec-prod-aux {X} {Y} {x} {x'} {y} {y'} p q =
    (x , y)
  ==⟨ app-cong {f = λ x -> (x , y)} p ⟩
    (x' , y)
  ==⟨ app-cong {f = λ y -> (x' , y)} q ⟩
    (x' , y')
  ∎

isDec-prod : {X Y : Set} -> isDec X -> isDec Y -> isDec (X × Y)
isDec-prod {X} {Y} p q xy xy'
  = (×-elim {Z = λ xy -> (xy' : X × Y) -> (xy == xy') + (xy == xy' -> Zero)}
            xy
            (λ x y xy' -> ×-elim {Z = λ xy' -> ((x , y) == xy') + ((x , y) == xy' -> Zero)}
                                 xy'
                                 (λ x' y' -> +-elim (p x x')
                                                    (λ r -> +-elim (q y y')
                                                                   (λ r' -> inl (isDec-prod-aux r r'))
                                                                   (λ r -> inr (λ r' -> r (app-cong {f = λ x -> snd x} r'))))
                                                    (λ r -> inr (λ r' -> r (app-cong {f = λ x -> fst x} r')))))
          ) xy'

