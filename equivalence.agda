{-# OPTIONS --cubical-compatible #-}
module AgdaStage.equivalence where

open import AgdaStage.nat
open import AgdaStage.PropositionAsTypes

infix 4 _≡_
data _≡_ {X : Set} : X → X → Set where
  refl : {a : X} → a ≡ a

data _≡'_ {X : Set} : X → X → Set where
  refl    : {x   : X} → x ≡' x
  bailout : {x y : X} → x ≡' y

zero-equals-zero : zero ≡ zero
zero-equals-zero = refl

grande-teorema : two + two ≡ four
grande-teorema = refl

trivial : (b : ℕ) → zero + b ≡ b
trivial b = refl

outrageous' : one ≡' zero
outrageous' = bailout

