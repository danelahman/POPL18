{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------
---- Code accompanying Section 7 of the paper "Handling fibred algebraic effects" ----
--------------------------------------------------------------------------------------
------ Showing that being a set is closed under finite products and coproducts -------
--------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------

open import eMLTT

module Sets where

{- Definition of sets -}

isSet : Set -> Set
isSet X = {x x' : X} -> (p q : x == x') -> p == q


{- Zero is a set (Example 3.1.3 in the HoTT book) -}

isSet-zero : isSet Zero
isSet-zero {x} {x'} p q = zero-elim {X = λ _ -> p == q} x


{- One is a set (Example 3.1.2 in the HoTT book) -}

one-eq-fun1 : {x y : One} -> x == y -> One
one-eq-fun1 p = ⋆

one-eq-fun2 : {x y : One} -> One -> x == y
one-eq-fun2 {⋆} {⋆} _ = refl ⋆ --using pattern-matching on x and y to simulate definitional eta-expansion for One

one-eq-iso1 : {x y : One}
           -> (p : x == y)
           -> one-eq-fun2 (one-eq-fun1 p) == p
one-eq-iso1 {x} {y} p =
    one-eq-fun2 (one-eq-fun1 p)
  ==⟨ eq-elim {Y = λ x y p -> one-eq-fun2 (one-eq-fun1 p) == p} p (λ {⋆ -> refl (refl ⋆)}) ⟩ --using pattern-matching on x to simulate definitional eta-expansion for One
    p
  ∎

one-eq-iso2 : {x y : One}
           -> (z : One)
           -> one-eq-fun1 {x} {y} (one-eq-fun2 z) == z
one-eq-iso2 {x} {y} ⋆ = --using pattern-matching on x and y to simulate definitional eta-expansion for One
    one-eq-fun1 {x} {y} (one-eq-fun2 ⋆)
  ==⟨ refl ⋆ ⟩
    ⋆
  ∎

isSet-one : isSet One
isSet-one {x} {y} p q =
    p
  ==⟨ sym (one-eq-iso1 p) ⟩
    one-eq-fun2 (one-eq-fun1 p)
  ==⟨ refl (one-eq-fun2 ⋆) ⟩
    one-eq-fun2 (one-eq-fun1 q)
  ==⟨ one-eq-iso1 q ⟩
    q
  ∎


{- Coproduct of sets is a set (Exercise 3.2 in the HoTT book) -}

+-elim₁ : {X Y : Set} {Z : X + Y -> Set₁} -> (xy : X + Y) -> ((x : X) -> Z (inl x)) -> ((y : Y) -> Z (inr y)) -> Z xy
+-elim₁ (inl x) f g = f x
+-elim₁ (inr y) f g = g y

codeX : {X Y : Set} -> X -> X + Y -> Set
codeX x0 xy = +-elim₁ xy (λ x -> x0 == x) (λ _ -> Zero)

encodeX : {X Y : Set} -> (x0 : X) -> (xy : X + Y) -> (p : inl x0 == xy) -> codeX x0 xy
encodeX x0 xy p = transport {Y = λ xy -> codeX x0 xy} p (refl x0)

decodeX : {X Y : Set} -> (x0 : X) -> (xy : X + Y) -> (c : codeX x0 xy) -> inl x0 == xy
decodeX x0 xy = +-elim {Z = λ xy -> codeX x0 xy -> inl x0 == xy} xy (λ x c -> app-cong {f = inl} c) (λ y c -> zero-elim c)

encodeX-iso1 : {X Y : Set}
            -> (x0 : X)
            -> (xy : X + Y)
            -> (p : inl x0 == xy)
            -> decodeX x0 xy (encodeX x0 xy p) == p
encodeX-iso1 x0 xy p =
    decodeX x0 xy (encodeX x0 xy p)
  ==⟨ based-eq-elim {Y = λ xy p -> decodeX x0 xy (encodeX x0 xy p) == p} p (refl (refl (inl x0))) ⟩
    p
  ∎

encodeX-iso2-aux : {X Y : Set}
                -> (x0 : X)
                -> (x : X)
                -> (c : codeX {X} {Y} x0 (inl x))
                -> encodeX {X} {Y} x0 (inl x) (decodeX x0 (inl x) c) == c
encodeX-iso2-aux x0 x c =
    encodeX x0 (inl x) (decodeX x0 (inl x) c)
  ==⟨ based-eq-elim {Y = λ x c -> encodeX x0 (inl x) (decodeX x0 (inl x) c) == c} c (refl (refl x0)) ⟩
    c
  ∎

encodeX-iso2 : {X Y : Set}
            -> (x0 : X)
            -> (xy : X + Y)
            -> (c : codeX x0 xy)
            -> encodeX x0 xy (decodeX x0 xy c) == c
encodeX-iso2 x0 xy c =
    encodeX x0 xy (decodeX x0 xy c)
  ==⟨ (+-elim {Z = λ xy -> (c : codeX x0 xy) -> encodeX x0 xy (decodeX x0 xy c) == c}
              xy
              (λ x c -> encodeX-iso2-aux x0 x c)
              (λ y c -> zero-elim {X = λ _ -> encodeX x0 (inr y) (decodeX x0 (inr y) c) == c} c))
      c ⟩
    c
  ∎

codeY : {X Y : Set} -> Y -> X + Y -> Set
codeY y0 xy = +-elim₁ xy (λ _ -> Zero) (λ y -> y0 == y)

encodeY : {X Y : Set} -> (y0 : Y) -> (xy : X + Y) -> (p : inr y0 == xy) -> codeY y0 xy
encodeY y0 xy p = transport {Y = λ xy -> codeY y0 xy} p (refl y0)

decodeY : {X Y : Set} -> (y0 : Y) -> (xy : X + Y) -> (c : codeY y0 xy) -> inr y0 == xy
decodeY y0 xy = +-elim {Z = λ xy -> codeY y0 xy -> inr y0 == xy} xy (λ _ c -> zero-elim c) (λ _ c -> app-cong {f = inr} c)

encodeY-iso1 : {X Y : Set}
            -> (y0 : Y)
            -> (xy : X + Y)
            -> (p : inr y0 == xy)
            -> decodeY y0 xy (encodeY y0 xy p) == p
encodeY-iso1 y0 xy p =
    decodeY y0 xy (encodeY y0 xy p)
  ==⟨ based-eq-elim {Y = λ xy p -> decodeY y0 xy (encodeY y0 xy p) == p} p (refl (refl (inr y0))) ⟩
    p
  ∎

encodeY-iso2-aux : {X Y : Set}
                -> (y0 : Y)
                -> (y : Y)
                -> (c : codeY {X} {Y} y0 (inr y))
                -> encodeY {X} {Y} y0 (inr y) (decodeY y0 (inr y) c) == c
encodeY-iso2-aux y0 y c =
    encodeY y0 (inr y) (decodeY y0 (inr y) c)
  ==⟨ based-eq-elim {Y = λ y c -> encodeY y0 (inr y) (decodeY y0 (inr y) c) == c} c (refl (refl y0)) ⟩
    c
  ∎

encodeY-iso2 : {X Y : Set}
            -> (y0 : Y)
            -> (xy : X + Y)
            -> (c : codeY y0 xy)
            -> encodeY y0 xy (decodeY y0 xy c) == c
encodeY-iso2 y0 xy c =
    encodeY y0 xy (decodeY y0 xy c)
  ==⟨ (+-elim {Z = λ xy -> (c : codeY y0 xy) -> encodeY y0 xy (decodeY y0 xy c) == c}
              xy
              (λ x c -> zero-elim {X = λ _ -> encodeY y0 (inl x) (decodeY y0 (inl x) c) == c} c)
              (λ y c -> encodeY-iso2-aux y0 y c))
       c ⟩
    c
  ∎

isSet-coprod : {X Y : Set}
            -> isSet X
            -> isSet Y
            -> isSet (X + Y)
isSet-coprod {X} {Y} is1 is2 {inl x} {inl x'} p q =
  let p'  = encodeX x (inl x') p in -- : x == x'
  let q'  = encodeX x (inl x') q in -- : x == x'
  let pq' = is1 {x} {x'} p' q' in   -- : encodeX x (inl x') p == encodeX x (inl x') q
    p
  ==⟨ sym (encodeX-iso1 x (inl x') p) ⟩
    decodeX x (inl x') (encodeX x (inl x') p)
  ==⟨ app-cong {f = app-cong} pq' ⟩
    decodeX x (inl x') (encodeX x (inl x') q)
  ==⟨ encodeX-iso1 x (inl x') q ⟩
    q
  ∎
isSet-coprod {X} {Y} is1 is2 {inl x} {inr y}  p q =
    p
  ==⟨ zero-elim {X = λ _ -> p == q} (encodeX x (inr y) p) ⟩
    q
  ∎
isSet-coprod {X} {Y} is1 is2 {inr y} {inl x}  p q =
    p
  ==⟨ zero-elim {X = λ _ -> p == q} (encodeY y (inl x) p) ⟩
    q
  ∎
isSet-coprod {X} {Y} is1 is2 {inr y} {inr y'} p q =
  let p'  = encodeY y (inr y') p in -- : y == y'
  let q'  = encodeY y (inr y') q in -- : y == y'
  let pq' = is2 {y} {y'} p' q' in   -- : encodeY y (inr y') p == encodeY y (inr y') q
    p
  ==⟨ sym (encodeY-iso1 y (inr y') p) ⟩
    decodeY y (inr y') (encodeY y (inr y') p)
  ==⟨ app-cong {f = app-cong} pq' ⟩
    decodeY y (inr y') (encodeY y (inr y') q)
  ==⟨ encodeY-iso1 y (inr y') q ⟩
    q
  ∎
  

{- Product of sets is a set (Example 3.1.5 in the HoTT book) -}

pair-eq-aux : {X Y : Set}
           -> {x x' : X}
           -> {y y' : Y}
           -> x == x'
           -> y == y'
           -> (x , y) == (x' , y')
pair-eq-aux {X} {Y} {x} {x'} {y} {y'} p q =
    (x , y)
  ==⟨ app-cong {f = λ x -> (x , y)} p ⟩
    (x' , y)
  ==⟨ app-cong {f = λ y -> (x' , y)} q ⟩
    (x' , y')
  ∎

pair-eq : {X Y : Set}
       -> (xy xy' : X × Y)
       -> fst xy == fst xy'
       -> snd xy == snd xy'
       -> xy == xy'
pair-eq {X} {Y} xy xy' p q =
    xy
  ==⟨ (×-elim {Z = λ xy -> fst xy == fst xy' -> snd xy == snd xy' -> xy == xy'}
              xy
              (λ x y p q -> (×-elim {Z = λ xy' -> fst (x , y) == fst xy' -> snd (x , y) == snd xy' -> (x , y) == xy'}
                                    xy'
                                    (λ x' y' p q -> pair-eq-aux p q))
                             p q))
       p q ⟩
    xy'
  ∎

pair-eq-eta : {X Y : Set}
           -> (xy xy' : X × Y)
           -> (p : xy == xy')
           -> p == pair-eq xy xy' (app-cong p) (app-cong p)
pair-eq-eta {X} {Y} xy xy' p =
    p
  ==⟨ eq-elim {Y = λ xy xy' p -> p == pair-eq xy xy' (app-cong p) (app-cong p)}
              p
              (λ xy → ×-elim {Z = λ xy → refl xy == pair-eq xy xy (app-cong {f = fst} (refl xy)) (app-cong {f = snd} (refl xy))}
                             xy
                             (λ x y -> (refl (refl (x , y))))) ⟩
    pair-eq xy xy' (app-cong p) (app-cong p)
  ∎

isSet-prod : {X Y : Set} -> isSet X -> isSet Y -> isSet (X × Y)
isSet-prod {X} {Y} is1 is2 {x , y} {x' , y'} p q =
  let pX = app-cong {f = fst} p in
  let pY = app-cong {f = snd} p in
  let qX = app-cong {f = fst} q in
  let qY = app-cong {f = snd} q in
  let rX = is1 pX qX in
  let rY = is2 pY qY in
    p
  ==⟨ pair-eq-eta (x , y) (x' , y') p ⟩
    pair-eq (x , y) (x' , y') (app-cong {f = fst} p) (app-cong {f = snd} p)
  ==⟨ app-cong {f = λ z -> pair-eq (x , y) (x' , y') z (app-cong {f = snd} p)} rX ⟩
    pair-eq (x , y) (x' , y') (app-cong {f = fst} q) (app-cong {f = snd} p)
  ==⟨ app-cong {f = λ z -> pair-eq (x , y) (x' , y') (app-cong {f = fst} q) z} rY ⟩
    pair-eq (x , y) (x' , y') (app-cong {f = fst} q) (app-cong {f = snd} q)
  ==⟨ sym (pair-eq-eta (x , y) (x' , y') q) ⟩
    q
  ∎
