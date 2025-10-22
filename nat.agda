{-# OPTIONS --cubical-compatible #-}
module AgdaStage.nat where

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

one : ℕ
one = succ zero

two : ℕ
two = succ one

three : ℕ
three = succ two

four : ℕ
four = succ three

twice : ℕ → ℕ
twice zero = zero   
twice (succ n) = succ (succ (twice n))
 
infixl 6 _+_
_+_ : ℕ → ℕ → ℕ
zero + m = m
succ n + m = succ (n + m)

half : ℕ → ℕ
half zero = zero
half (succ zero) = zero
half (succ (succ n)) = succ (half n)

infixl 6 _-_
_-_ : ℕ → ℕ → ℕ
a - zero = a
zero - (succ m) = zero
succ n - (succ m) = n - m

_*_ : ℕ → ℕ → ℕ
zero * m = zero
succ n * m = m + (n * m)

max : ℕ → ℕ → ℕ
max zero m = m
max (succ n) zero = succ n
max (succ n) (succ m) = succ (max n m)

