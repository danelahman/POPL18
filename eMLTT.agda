{-# OPTIONS --without-K #-}

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
---- Code accompanying Section 7 of the paper Handling fibred algebraic effects" ----
-------------------------------------------------------------------------------------
---------- A shallow embedding of the the relevant value fragment of eMLTT ----------
-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------

module eMLTT where

{- Propositional equality -}

data _==_ {X : Set} : X -> X -> Set where
  refl : (x : X) -> x == x

data _==₁_ {X : Set₁} : X -> X -> Set₁ where --a substitute for definitional equality between eMLTT types (used in `IONoWrites.agda` and `IOPatterns.agda`)
  refl : (x : X) -> x ==₁ x

postulate
  fun-ext : {X : Set} {Y : X -> Set} {f g : (x : X) -> Y x} -> ((x : X) -> f x == g x) -> f == g

eq-elim : {X : Set} {Y : (x : X) -> (x' : X) -> x == x' -> Set} {x x' : X} -> (p : x == x') -> ((x : X) -> Y x x (refl x)) -> Y x x' p
eq-elim (refl x) f = f x

based-eq-elim : {X : Set} {x : X} {Y : (x' : X) -> x == x' -> Set} {x' : X} -> (p : x == x') -> Y x (refl x) -> Y x' p
based-eq-elim (refl x) y = y

sym : {X : Set} {x x' : X} -> x == x' -> x' == x
sym {X} {x} {x'} p = eq-elim {Y = λ x x' _ -> x' == x} p (λ x -> refl x)

trans : {X : Set} {x x' x'' : X} -> x == x' -> x' == x'' -> x == x''
trans {X} {x} {x'} {x''} p = eq-elim {Y = λ x x' _ -> x' == x'' -> x == x''} p (λ x q -> q)

transport : {X : Set} {Y : X -> Set} {x x' : X} -> x == x' -> Y x -> Y x'
transport {X} {Y} p = eq-elim {Y = λ x x' _ -> Y x -> Y x'} p (λ x y -> y)

app-cong : {X Y : Set} {f : X -> Y} {x x' : X} -> x == x' -> f x == f x'
app-cong {X} {Y} {f} p = eq-elim {Y = λ x x' _ -> f x == f x'} p (λ x -> refl (f x))

dapp-cong : {X : Set} {Y : X -> Set} {f : (x : X) -> Y x} {x x' : X} -> (p : x == x') -> transport p (f x) == f x'
dapp-cong {X} {Y} {f} p = eq-elim {Y = λ x x' p -> transport p (f x) == f x'} p (λ x -> refl (f x))

_==⟨_⟩_ : {X : Set} -> (x : X) -> {x' x'' : X} -> (x == x') -> (x' == x'') -> (x == x'')
x ==⟨ p ⟩ q = trans p q

_∎ : {X : Set} -> (x : X) -> x == x
x ∎ = refl x

infix  3 _∎
infixr 2 _==⟨_⟩_


{- Natural numbers -}

data Nat : Set where
  zero : Nat
  succ : Nat -> Nat

nat-elim : {X : Nat -> Set} -> X zero -> ((n : Nat) -> X n -> X (succ n)) -> (n : Nat) -> X n
nat-elim z s zero = z
nat-elim z s (succ n) = s n (nat-elim z s n)


{- Unit type -}

data One : Set where
  ⋆ : One


{- Finite coproducts -}

data Zero : Set where

zero-elim : {X : Zero -> Set} -> (z : Zero) -> X z
zero-elim ()

data _+_ (X Y : Set) : Set where
  inl : (x : X) -> X + Y
  inr : (y : Y) -> X + Y

+-elim : {X Y : Set} {Z : X + Y -> Set} -> (xy : X + Y) -> ((x : X) -> Z (inl x)) -> ((y : Y) -> Z (inr y)) -> Z xy
+-elim (inl x) f g = f x
+-elim (inr y) f g = g y


{- Value Sigma-type -}

data Sigma (X : Set) (Y : X -> Set) : Set where
  _,_ : (x : X) -> Y x -> Sigma X Y

sigma-elim : {X : Set} {Y : X -> Set} {Z : Sigma X Y -> Set} -> (xy : Sigma X Y) -> ((x : X) -> (y : Y x) -> Z (x , y)) -> Z xy
sigma-elim (x , y) f = f x y

fst : {X : Set} {Y : X -> Set} -> Sigma X Y -> X
fst xy = sigma-elim xy (λ x y -> x)

snd : {X : Set} {Y : X -> Set} -> (xy : Sigma X Y) -> Y (fst xy)
snd {X} {Y} xy = sigma-elim {X} {Y} {λ xy -> Y (fst xy)} xy (λ x y -> y)

_×_ : Set -> Set -> Set
X × Y = Sigma X (λ _ → Y)

×-elim : {X Y : Set} {Z : X × Y -> Set} -> (xy : X × Y) -> ((x : X) -> (y : Y) -> Z (x , y)) -> Z xy
×-elim {X} {Y} {Z} xy f = sigma-elim {X} {λ _ → Y} {Z} xy f


{- Value universe a la Tarski -}

mutual 
  data U : Set where
    nat-c  : U
    one-c  : U
    zero-c : U
    sum-c  : U -> U -> U
    sig-c  : (c : U) -> (El c -> U) -> U
    pi-c   : (c : U) -> (El c -> U) -> U
    eq-c   : (c : U) -> El c -> El c -> U

  El : U -> Set
  El nat-c         = Nat
  El one-c         = One
  El zero-c        = Zero
  El (sum-c c0 c1) = (El c0) + (El c1)
  El (sig-c c0 c1) = Sigma (El c0) (λ x -> El (c1 x))
  El (pi-c c0 c1)  = (x : El c0) -> El (c1 x)
  El (eq-c c x y)  = x == y
  
