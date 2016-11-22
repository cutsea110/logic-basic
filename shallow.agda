module shallow where

data ⊥ : Set where

⊥Elim : {P :  Set} → ⊥ → P
⊥Elim ()

-- propositional logic

-- conjunction
record _∧_ (P Q : Set) : Set where
  field
    Elim₁ : P
    Elim₂ : Q

∧Intro : {P Q : Set} → P → Q → P ∧ Q
∧Intro p q = record { Elim₁ = p ; Elim₂ = q }

-- disjunction
data _∨_ (P Q : Set) : Set where
  ∨Intro₁ : P → P ∨ Q
  ∨Intro₂ : Q → P ∨ Q

∨Elim : {P Q R : Set} → P ∨ Q → (P → R) → (Q → R) → R
∨Elim (∨Intro₁ a) prfP _    = prfP a
∨Elim (∨Intro₂ b) _    prfQ = prfQ b

-- imply
data _⊃_ (P Q : Set) : Set where
  ⊃Intro : (P → Q) → P ⊃ Q

⊃Elim : {P Q : Set} → P ⊃ Q → P → Q
⊃Elim (⊃Intro f) a = f a

_!_ : {P Q : Set} → P ⊃ Q → P → Q
_!_ = ⊃Elim

-- negation
¬_ : Set → Set
¬ P = P ⊃ ⊥

¬Intro : (P : Set) → (P → ⊥) → ¬ P
¬Intro P prf = ⊃Intro prf

¬Elim : (P : Set) → P → ¬ P → ⊥
¬Elim P prf₁ (⊃Intro prf₂) = prf₂ prf₁

-- predicate logic

-- forall
data ∀' (P : Set) (Q : P → Set) : Set where
  ∀'Intro : ((a : P) → Q a) → ∀' P Q

∀'Elim : {P : Set}{Q : P → Set} → ∀' P Q → (a : P) → Q a
∀'Elim (∀'Intro f) a = f a

-- exists
record ∃' (P : Set) (Q : P → Set) : Set where
  field
    evidence : P
    Elim     : Q evidence

∃'Intro : {P : Set}{Q : P → Set} → (a : P) → Q a → ∃' P Q
∃'Intro e prf = record { evidence = e ; Elim = prf }

-- proof tautologies
p1 : (A B : Set) → (A ∧ B) ⊃ (A ∨ B)
p1 A B = ⊃Intro (λ x → ∨Intro₁ (_∧_.Elim₁ x))

p2 : (A B : Set) → (A ∧ B) ⊃ (A ∨ B)
p2 A B = ⊃Intro (λ x → ∨Intro₂ (_∧_.Elim₂ x))

p3 : (A B : Set) → (P : A → B → Set) →
     (∃' A (λ (x : A) → ∀' B (λ (y : B) → P x y))) ⊃
     (∀' B (λ (y : B) → ∃' A (λ (x : A) → P x y)))
p3 A B P = ⊃Intro (λ pr → ∀'Intro (λ b → record { evidence = ∃'.evidence pr
                                                ; Elim = ∀'Elim (∃'.Elim pr) b
                                                }))


-- classical logic
postulate
  LEM : (P : Set) → P ∨ (¬ P)

DNE : {A : Set} → (¬ ¬ A) ⊃ A
DNE {A} = ⊃Intro (λ y → ∨Elim (LEM A) (λ w → w) (λ z → ⊥Elim (⊃Elim y z)))
