{-# OPTIONS --cubical-compatible #-}
module AgdaStage.PropositionAsTypes where

open import AgdaStage.nat
open import AgdaStage.prova

data Even : ℕ → Set where
    even-zero : Even zero -- Base case
    even-suc  : ∀ {n} → Even n → Even (succ (succ n)) -- Being even means that n = 2k for some k

data Odd : ℕ → Set where
  base-odd : Odd one
  step-odd : {n : ℕ} → Odd n → Odd (succ (succ n))

data isZero : ℕ → Set where
    isZero-zero : isZero zero

data ⊥ : Set where

infixr 3 ¬_
¬_ : Set → Set
¬ A = A → ⊥

one-not-even : Even one → ⊥
one-not-even () 

⊥-elim : ⊥ → {A : Set} → A
⊥-elim () {A} 

dni : {A : Set} → A → ¬ ¬ A
dni x = λ k → k x



