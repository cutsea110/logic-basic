module deep where

open import Data.Bool using (Bool; true; false) renaming (_∧_ to _&&_; _∨_ to _||_; not to !_)
open import Data.Nat

infixl 0 _==_
infixr 2 _⟹_
infixr 3 _⊃_
infixl 5 _∨_
infixl 6 _∧_
infixr 8 ¬_
infixl 9 _╲_

data Form : Set where
  Atom : ℕ → Form
  ⊥ : Form
  ¬_ : Form → Form
  _∨_ : Form → Form → Form
  _∧_ : Form → Form → Form
  _⊃_ : Form → Form → Form

_==_ : Form → Form → Bool
(Atom m) == (Atom n) = eqℕ m n
  where
    eqℕ : ℕ → ℕ → Bool
    eqℕ zero zero = true
    eqℕ zero (suc n) = false
    eqℕ (suc m) zero = false
    eqℕ (suc m) (suc n) = eqℕ m n
¬ P == ¬ P' = P == P'
P ∨ Q == P' ∨ Q' = (P == P') || (Q == Q')
P ∧ Q == P' ∧ Q' = (P == P') && (Q == Q')
P ⊃ Q == P' ⊃ Q' = (P == P') && (Q == Q')
_ == _ = false

ev : Form → (ℕ → Bool) → Bool
ev (Atom n) φ = φ n
ev ⊥ φ = false
ev (¬ P) φ = ! (ev P φ)
ev (P ∨ Q) φ = (ev P φ) || (ev Q φ)
ev (P ∧ Q) φ = (ev P φ) && (ev Q φ)
ev (P ⊃ Q) φ = (! (ev P φ)) || (ev Q φ)

open import Data.List

_╲_ : List Form → Form → List Form
[] ╲ Q = []
(P ∷ Ps) ╲ Q with P == Q
... | true = Ps ╲ Q
... | false = P ∷ (Ps ╲ Q)

data _⟹_ : List Form → Form → Set where
  Assume : (P : Form) → (P ∷ []) ⟹ P
  ⊥Elim : {fs : List Form}{P : Form} →
          fs ⟹ ⊥ → fs ⟹ P
  ¬Intro : {fs : List Form}{P : Form} →
           fs ⟹ ⊥ → fs ╲ P ⟹ ¬ P
  ¬Elim : {fs gs : List Form}{P : Form} →
          fs ⟹ P → gs ⟹ ¬ P → (fs ++ gs) ⟹ ⊥
  ∧Intro : {fs gs : List Form}{P Q : Form} →
           fs ⟹ P → gs ⟹ Q → (fs ++ gs) ⟹ P ∧ Q
  ∧Elim₁ : {fs : List Form}{P Q : Form} →
           fs ⟹ P ∧ Q → fs ⟹ P
  ∧Elim₂ : {fs : List Form}{P Q : Form} →
           fs ⟹ P ∧ Q → fs ⟹ Q
  ∨Intro₁ : {fs : List Form}{P Q : Form} →
            fs ⟹ P → fs ⟹ P ∨ Q
  ∨Intro₂ : {fs : List Form}{P Q : Form} →
            fs ⟹ Q → fs ⟹ P ∨ Q
  ∨Elim : {fs gs hs : List Form}{P Q R : Form} →
          fs ⟹ P ∨ Q → gs ⟹ R → hs ⟹ R → (fs ++ gs ╲ P ++ hs ╲ Q) ⟹ R
  ⊃Intro : {fs : List Form}{P Q : Form} →
           fs ⟹ Q → fs ╲ P ⟹ P ⊃ Q
  ⊃Elim : {fs gs : List Form}{P Q : Form} →
          fs ⟹ P → gs ⟹ P ⊃ Q → (fs ++ gs) ⟹ Q
  -- for Classical logic, if you expect intuition, then you comment out below LEM
  LEM : (P : Form) → [] ⟹ P ∨ ¬ P

-- proof DNE
A : Form
A = Atom 0
DNE0 : [] ⟹ (¬ ¬ A ⊃ A)
DNE0 = ⊃Intro (∨Elim (LEM A) (Assume A) (⊥Elim (¬Elim (Assume (¬ A)) (Assume (¬ ¬ A)))))
