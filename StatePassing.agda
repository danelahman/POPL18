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

{- Types of locations and store values; the former is assumed to have decidable equality -}

postulate
  Loc : Set
  Val : Loc -> Set
  isDec : (l l' : Loc) -> (l == l') + (l == l' -> Zero)


{- Hedberg's theorem for Loc, showing that being a set follows from decidable equality     -}
{- See Section 3.2 of Michael Hedberg's "A coherence theorem for Martin-Löf’s type theory" -}

con : {l l' : Loc} -> ((l == l') + (l == l' -> Zero)) -> l == l' -> l == l'
con d p = +-elim d (λ q -> q) (λ _ -> p)

isCon : {l l' : Loc}
     -> (d : (l == l') + (l == l' -> Zero))
     -> (p q : l == l')
     -> con d p == con d q
isCon d p q = +-elim {Z = λ d -> con d p == con d q}
                     d
                     (λ r -> refl r)
                     (λ r -> zero-elim {X = λ _ -> con (inr r) p == con (inr r) q} (r q))

linv : ({l l' : Loc} -> l == l' -> l == l') -> {l l' : Loc} -> l == l' -> l == l'
linv f {l} p = trans (sym (f (refl l))) p

sym-cancel : {X : Set}
          -> {x x' : X}
          -> (p : x == x')
          -> trans (sym p) p == refl x'
sym-cancel {X} {x} {x'} p =
    trans (sym p) p
  ==⟨ eq-elim {Y = λ x x' p -> trans (sym p) p == refl x'}
              p
              (λ x -> refl (refl x)) ⟩
    refl x'
  ∎

isLinv-aux : (f : {l l' : Loc} -> l == l' -> l == l')
          -> (l : Loc)
          -> linv f (f (refl l)) == refl l
isLinv-aux f l =
    linv f (f (refl l))
  ==⟨ refl _ ⟩
    trans (sym (f (refl l))) (f (refl l))
  ==⟨ sym-cancel (f (refl l)) ⟩
    refl l
  ∎

isLinv : (f : {l l' : Loc} -> l == l' -> l == l')
      -> {l l' : Loc}
      -> (p : l == l')
      -> linv f (f p) == p
isLinv f p =
    linv f (f p)
  ==⟨ eq-elim {Y = λ l l' p -> linv f (f p) == p} p (λ l -> isLinv-aux f l) ⟩
    p
  ∎

isSet : {l l' : Loc}
     -> (p q : l == l')
     -> p == q
isSet {l} {l'} p q =
    p
  ==⟨ sym (isLinv (λ {l} {l'} p -> con (isDec l l') p) p) ⟩
    linv (λ {l} {l'} r -> con (isDec l l') r) (con (isDec l l') p)
  ==⟨ app-cong {f = λ pq -> linv (λ {l} {l'} r -> con (isDec l l') r) pq}
               (isCon (isDec l l') p q) ⟩
    linv (λ {l} {l'} r -> con (isDec l l') r) (con (isDec l l') q)
  ==⟨ isLinv (λ {l} {l'} p -> con (isDec l l') p) q ⟩
    q
  ∎
  

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
