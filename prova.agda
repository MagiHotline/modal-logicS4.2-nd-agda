{-# OPTIONS --cubical-compatible #-}
module AgdaStage.prova where

open import AgdaStage.nat

data Bool : Set where
    true  : Bool
    false : Bool

idBool : Bool → Bool
idBool b = b

not : Bool → Bool
not true  = false
not false = true

even? : ℕ → Bool
even? zero            = true
even? (succ zero)     = false
even? (succ (succ a)) = even? a

odd? : ℕ → Bool
odd? n = not (even? n)

and : Bool → Bool → Bool
and false false = false
and false true  = false
and true  false = false
and true  true  = true

example-usage : Bool
example-usage = and false (and true false)
-- example-usage evaluates to false

infixr 6 _&&_
_&&_ : Bool → Bool → Bool
false && false = false
false && true  = false
true  && false = false
true  && true  = true
