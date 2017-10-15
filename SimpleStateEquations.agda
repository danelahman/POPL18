{-# OPTIONS --without-K #-}

----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------
------ Code accompanying Section 7 of the paper Handling fibred algebraic effects" -----
----------------------------------------------------------------------------------------
-- Showing how to prove the proof obligations corresponding to global state equations --
----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------

open import SimpleStatePassing
open import eMLTT

module SimpleStateEquations where

{- First global state equation -}

eq1-aux' : {X : Set}
        -> (l : Loc)
        -> (c : State X)
        -> (s : Store)
        -> (l' : Loc)
        -> upd s l (s l) l' == s l'
eq1-aux' l c s l' =
    upd s l (s l) l'
  ==⟨ refl _ ⟩
    +-elim (isDec l l') (λ p -> s l) (λ _ -> s l')
  ==⟨ +-elim {Z = λ z -> +-elim z (λ p → s l) (λ _ → s l') == s l'}
             (isDec l l')
             (λ p -> app-cong {f = s} p)
             (λ _ -> refl (s l')) ⟩
    s l'
  ∎

eq1-aux : {X : Set}
       -> (l : Loc)
       -> (c : State X)
       -> (s : Store)
       -> (get l λ v -> put l v c) s == c s
eq1-aux l c s =
    (get l λ v -> put l v c) s
  ==⟨ refl _ ⟩
    c (upd s l (s l))
  ==⟨ app-cong {f = c} (fun-ext (λ l' -> eq1-aux' l c s l')) ⟩
    c s
  ∎

eq1 : {X : Set}
   -> (l : Loc)
   -> (c : State X)
   -> get l (λ v -> put l v c) == c
eq1 l c =
    get l (λ v -> put l v c)
  ==⟨ fun-ext (λ s -> eq1-aux l c s) ⟩
    c
  ∎
  

{- Second global state equation -}

eq2-aux' : (l : Loc)
        -> (v : Val)
        -> (s : Store)
        -> upd s l v l == v
eq2-aux' l v s =
    upd s l v l
  ==⟨ refl _ ⟩
    +-elim (isDec l l) (λ p -> v) (λ _ -> s l)
  ==⟨ (+-elim {Z = λ z -> +-elim z (λ p -> v) (λ _ -> s l) == v}
              (isDec l l)
              (λ _ -> refl v)
              (λ p -> zero-elim {X = λ _ -> s l == v} (p (refl l)))) ⟩
    v
  ∎

eq2-aux : {X : Set}
       -> (l : Loc)
       -> (v : Val)
       -> (c : Val -> State X)
       -> (s : Store)
       -> (put l v (get l (λ v' -> c v'))) s == (put l v (c v)) s
eq2-aux l v c s =
    (put l v (get l (λ v' -> c v'))) s
  ==⟨ refl _ ⟩
    c ((upd s l v) l) (upd s l v)
  ==⟨ app-cong {f = λ w -> c w (upd s l v)} (eq2-aux' l v s) ⟩
    c v (upd s l v)
  ==⟨ refl _ ⟩
    (put l v (c v)) s
  ∎
  
eq2 : {X : Set}
   -> (l : Loc)
   -> (v : Val)
   -> (c : Val -> State X)
   -> put l v (get l (λ v' -> c v')) == put l v (c v)
eq2 l v c =
    put l v (get l (λ v' -> c v'))
  ==⟨ fun-ext (λ s -> eq2-aux l v c s) ⟩
    put l v (c v)
  ∎


{- Third global state equation -}

eq3-aux'' : (l : Loc)
         -> (v : Val)
         -> (s : Store)
         -> (l' : Loc)
         -> (p : l == l' -> Zero)
         -> upd s l v l' == s l'
eq3-aux'' l v s l' p =
    upd s l v l'
  ==⟨ refl _ ⟩
    +-elim (isDec l l') (λ p -> v) (λ _ -> s l')  
  ==⟨ +-elim {Z = λ z -> +-elim z (λ p₁ -> v) (λ _ -> s l') == s l'}
             (isDec l l')
             (λ q -> zero-elim (p q))
             (λ _ -> refl (s l')) ⟩
    s l'
  ∎

eq3-aux' : (l : Loc)
        -> (v : Val)
        -> (v' : Val)
        -> (s : Store)
        -> (l' : Loc)
        -> upd (upd s l v) l v' l' == upd s l v' l'
eq3-aux' l v v' s l' =
    upd (upd s l v) l v' l'
  ==⟨ refl _ ⟩
    +-elim (isDec l l') (λ p -> v') (λ _ -> (upd s l v) l')
  ==⟨ +-elim {Z = λ z -> +-elim z (λ p -> v') (λ _ -> upd s l v l') == +-elim z (λ p -> v') (λ _ -> s l')}
             (isDec l l')
             (λ p -> refl v')
             (λ p -> eq3-aux'' l v s l' p) ⟩
    +-elim (isDec l l') (λ p -> v') (λ _ -> s l')
  ==⟨ refl _ ⟩
    upd s l v' l'
  ∎

eq3-aux : {X : Set}
       -> (l : Loc)
       -> (v : Val)
       -> (v' : Val)
       -> (c : State X)
       -> (s : Store)
       -> (put l v (put l v' c)) s == (put l v' c) s
eq3-aux l v v' c s =
    (put l v (put l v' c)) s
  ==⟨ refl _ ⟩
    c (upd (upd s l v) l v')
  ==⟨ app-cong {f = c} (fun-ext (λ l' -> eq3-aux' l v v' s l')) ⟩
    c (upd s l v')
  ==⟨ refl _ ⟩
    (put l v' c) s
  ∎

eq3 : {X : Set}
   -> (l : Loc)
   -> (v : Val)
   -> (v' : Val)
   -> (c : State X)
   -> put l v (put l v' c) == put l v' c
eq3 l v v' c =
    put l v (put l v' c)
  ==⟨ fun-ext (λ s -> eq3-aux l v v' c s) ⟩
    put l v' c
  ∎


{- Fourth global state equation -}

eq4-aux : {X : Set}
       -> (l : Loc)
       -> (l' : Loc)
       -> (c : Val × Val -> State X)
       -> (s : Store)
       ->    (get l (λ v -> get l' (λ v' -> c (v , v')))) s
          == +-elim {Z = λ _ -> State X} (isDec l l') (λ _ -> get l (λ v -> get l' (λ v' -> c (v , v')))) (λ _ -> get l' (λ v' -> get l (λ v -> c (v , v')))) s
eq4-aux {X} l l' c s =
    (get l (λ v -> get l' (λ v' -> c (v , v')))) s
  ==⟨ +-elim {Z = λ z ->     (get l (λ v -> get l' (λ v' -> c (v , v')))) s
                          == +-elim {Z = λ _ -> State X} z (λ _ -> get l (λ v -> get l' (λ v' -> c (v , v')))) (λ _ -> get l' (λ v' -> get l (λ v -> c (v , v')))) s }
              (isDec l l')
              (λ _ -> refl _)
              (λ _ -> refl _) ⟩
    +-elim {Z = λ _ -> State X} (isDec l l') (λ _ -> get l (λ v -> get l' (λ v' -> c (v , v')))) (λ _ -> get l' (λ v' -> get l (λ v -> c (v , v')))) s
  ∎

eq4 : {X : Set}
   -> (l : Loc)
   -> (l' : Loc)
   -> (c : Val × Val -> State X)
   ->    (get l (λ v -> get l' (λ v' -> c (v , v'))))
      == +-elim (isDec l l') (λ _ -> get l (λ v -> get l' (λ v' -> c (v , v')))) (λ _ -> get l' (λ v' -> get l (λ v -> c (v , v'))))
eq4 l l' c =
    get l (λ v -> get l' (λ v' -> c (v , v')))
  ==⟨ fun-ext (λ s -> eq4-aux l l' c s) ⟩
    +-elim (isDec l l') (λ _ -> get l (λ v -> get l' (λ v' -> c (v , v')))) (λ _ -> get l' (λ v' -> get l (λ v -> c (v , v'))))
  ∎


{- Fifth global state equation -}

eq5-aux'' : (l : Loc)
         -> (l' : Loc)
         -> (v : Val)
         -> (v' : Val)
         -> (s : Store)
         -> (p : l == l' -> Zero)
         -> (l'' : Loc)
         -> upd (upd s l v) l' v' l'' == upd (upd s l' v') l v l''
eq5-aux'' l l' v v' s p l'' =
    upd (upd s l v) l' v' l''
  ==⟨ refl _ ⟩
    +-elim (isDec l' l'') (λ q -> v') (λ _ -> upd s l v l'')
  ==⟨ refl _ ⟩
    +-elim (isDec l' l'') (λ q -> v') (λ _ -> +-elim (isDec l l'') (λ q -> v) (λ _ -> s l''))
  ==⟨ +-elim {Z = λ z ->    +-elim z (λ q -> v') (λ _ -> +-elim (isDec l l'') (λ q -> v) (λ _ -> s l''))
                        == +-elim (isDec l l'') (λ q -> v) (λ _ -> +-elim z (λ q -> v') (λ _ -> s l''))}
             (isDec l' l'')
             (λ q -> +-elim {Z = λ z ->   v'
                                       == +-elim z (λ r -> v) (λ _ -> v')}
                            (isDec l l'')
                            (λ r -> zero-elim (p (trans r (sym q))))
                            (λ r -> refl v' ))
             (λ q -> refl _) ⟩
    +-elim (isDec l l'') (λ q -> v) (λ _ -> +-elim (isDec l' l'') (λ q -> v') (λ _ -> s l''))
  ==⟨ refl _ ⟩
    +-elim (isDec l l'') (λ q -> v) (λ _ -> upd s l' v' l'')
  ==⟨ refl _ ⟩
    upd (upd s l' v') l v l''
  ∎

eq5-aux' : {X : Set}
        -> (l : Loc)
        -> (l' : Loc)
        -> (v : Val)
        -> (v' : Val)
        -> (c : State X)
        -> (s : Store)
        -> (p : l == l' -> Zero)
        -> put l v (put l' v' c) s == put l' v' (put l v c) s
eq5-aux' l l' v v' c s p =
    put l v (put l' v' c) s
  ==⟨ refl _ ⟩
    c (upd (upd s l v) l' v')
  ==⟨ app-cong {f = c} (fun-ext (λ l'' -> eq5-aux'' l l' v v' s p l'')) ⟩
    c (upd (upd s l' v') l v)
  ==⟨ refl _ ⟩
    put l' v' (put l v c) s
  ∎

eq5-aux : {X : Set}
       -> (l : Loc)
       -> (l' : Loc)
       -> (v : Val)
       -> (v' : Val)
       -> (c : State X)
       -> (s : Store)
       ->    (put l v (put l' v' c)) s
          == +-elim {Z = λ _ -> State X} (isDec l l') (λ _ -> put l v (put l' v' c)) (λ _ -> put l' v' (put l v c)) s
eq5-aux {X} l l' v v' c s =
    (put l v (put l' v' c)) s
  ==⟨ +-elim {Z = λ z ->   put l v (put l' v' c) s
                        == +-elim {Z = λ z' -> State X} z (λ _ -> put l v (put l' v' c)) (λ _ -> put l' v' (put l v c)) s} (isDec l l')
             (λ _ -> refl _)
             (λ p -> eq5-aux' l l' v v' c s p) ⟩
    +-elim {Z = λ _ -> State X} (isDec l l') (λ _ -> put l v (put l' v' c)) (λ _ -> put l' v' (put l v c)) s
  ∎

eq5 : {X : Set}
   -> (l : Loc)
   -> (l' : Loc)
   -> (v : Val)
   -> (v' : Val)
   -> (c : State X)
   ->    put l v (put l' v' c)
      == +-elim (isDec l l') (λ _ -> put l v (put l' v' c)) (λ _ -> put l' v' (put l v c))
eq5 l l' v v' c =
    put l v (put l' v' c)
  ==⟨ fun-ext (λ s -> eq5-aux l l' v v' c s) ⟩
    +-elim (isDec l l') (λ _ -> put l v (put l' v' c)) (λ _ -> put l' v' (put l v c))
  ∎
