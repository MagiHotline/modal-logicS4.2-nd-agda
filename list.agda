{-# OPTIONS --cubical-compatible #-}
module AgdaStage.list where

open import AgdaStage.nat

infixr 5 _::_
data List (A : Set) : Set where
    []  : List A
    _::_ : A → List A → List A

sum : List ℕ → ℕ
sum []       = zero
sum (x :: xs) = x + sum xs