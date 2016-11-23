module deep where

open import Data.Bool using (Bool; true; false) renaming (_∧_ to _&&_; _∨_ to _||_; not to !_)
open import Data.Nat

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
(¬ P) == (¬ P') = P == P'
(P ∨ Q) == (P' ∨ Q') = (P == P') || (Q == Q')
(P ∧ Q) == (P' ∧ Q') = (P == P') && (Q == Q')
(P ⊃ Q) == (P' ⊃ Q') = (P == P') && (Q == Q')
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

infixr 3 _⊃_
infixl 5 _∨_
infixl 6 _∧_
infixr 8 ¬_

data Proof : List Form → Form → Set where
  Assume : (P : Form) → Proof (P ∷ []) P
  ⊥Elim : {fs : List Form}{P : Form} →
          Proof fs ⊥ → Proof fs P
  ¬Intro : {fs : List Form}{P : Form} →
           Proof fs ⊥ → Proof (fs ╲ P) (¬ P)
  ¬Elim : {fs gs : List Form}{P : Form} →
          Proof fs P → Proof gs (¬ P) → Proof (fs ++ gs) ⊥
  ∧Intro : {fs gs : List Form}{P Q : Form} →
           Proof fs P → Proof gs Q → Proof (fs ++ gs) (P ∧ Q)
  ∧Elim₁ : {fs : List Form}{P Q : Form} →
           Proof fs (P ∧ Q) → Proof fs P
  ∧Elim₂ : {fs : List Form}{P Q : Form} →
           Proof fs (P ∧ Q) → Proof fs Q
  ∨Intro₁ : {fs : List Form}{P Q : Form} →
            Proof fs P → Proof fs (P ∨ Q)
  ∨Intro₂ : {fs : List Form}{P Q : Form} →
            Proof fs Q → Proof fs (P ∨ Q)
  ∨Elim : {fs gs hs : List Form}{P Q R : Form} →
          Proof fs (P ∨ Q) → Proof gs R → Proof hs R → Proof (fs ++ (gs ╲ P) ++ (hs ╲ Q)) R
  ⊃Intro : {fs : List Form}{P Q : Form} →
           Proof fs Q → Proof (fs ╲ P) (P ⊃ Q)
  ⊃Elim : {fs gs : List Form}{P Q : Form} →
          Proof fs P → Proof gs (P ⊃ Q) → Proof (fs ++ gs) Q
  -- for Classical logic, if you expect intuition, then you comment out below LEM
  LEM : (P : Form) → Proof [] (P ∨ (¬ P))

-- proof DNE
A : Form
A = Atom 0
DNE0 : Proof [] (¬ ¬ A ⊃ A)
DNE0 = ⊃Intro (∨Elim (LEM A) (Assume A) (⊥Elim (¬Elim (Assume (¬ A)) (Assume (¬ ¬ A)))))
