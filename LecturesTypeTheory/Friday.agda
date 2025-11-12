{-# OPTIONS --without-K #-}

{-
Equality 
-}

data _≡_ {A : Set} : A → A → Set where
  refl : {a : A} → a ≡ a

infix 4 _≡_

variable A B C : Set

sym : (a b : A) → a ≡ b → b ≡ a
sym a .a refl = refl

trans : (a b c : A) → a ≡ b → b ≡ c → a ≡ c
trans a .a c refl q = q

cong : (f : A → B)(a b : A) → a ≡ b → f a ≡ f b
cong f a .a refl = refl

-- pattern matching => combinators
-- J (Per Martin-Löf) , path induction
-- intensional type theory 

J : (M : (a b : A) → a ≡ b → Set)
    → ((a : A) → M a a refl)
    → (a b : A)(p : a ≡ b) → M a b p
J M m a .a refl = m a

sym-j : (a b : A) → a ≡ b → b ≡ a
-- sym a .a refl = refl
sym-j = J (λ a b p → b ≡ a) (λ a → refl)

trans-j : (a b c : A) → a ≡ b → b ≡ c → a ≡ c
-- trans a .a c refl q = q
trans-j a b c = J (λ a b _ → b ≡ c → a ≡ c) (λ a q → q) a b
-- can we prove trans-j without functions?

cong-j : (f : A → B)(a b : A) → a ≡ b → f a ≡ f b
cong-j = {!   !}

J' : (M : (a b : A) → Set)
    → ((a : A) → M a a)
    → (a b : A) → a ≡ b → M a b 
J' M m a .a refl = m a

-- reprove sym, trans, cong using only J'
-- what can we say about equality non provable with J'?

-- uip : (a b : A)(p q : a ≡ b) → p ≡ q
-- uip a .a refl refl = refl

-- K : (M : (a : A) → a ≡ a → Set)
--     → ((a : A) → M a refl)
--     → (a : A)(p : a ≡ a) → M a p
-- K M m a refl = m a

-- uip-j : (a b : A)(p q : a ≡ b) → p ≡ q
-- uip-j a b p q = J (λ a b p → (q : a ≡ b) → p ≡ q) 
--         (K (λ a q → refl ≡ q) (λ a₁ → refl)) a b p q

-- 1990 it seems that we cannot prove uip without K ?
-- can we show this ?

-- what can we prove with J?
-- yes, equality behaves like a group, actually a groupoid.
-- (ℤ , + , 0 , -(_))
-- (_≡_, trans, refl, sym) is a groupoid

lneutr≡ : (a b : A)(p : a ≡ b) → trans a a b refl p ≡ p
lneutr≡ a b p = refl

rneutr≡ : (a b : A)(p : a ≡ b) → trans a b b p refl ≡ p
rneutr≡ a .a refl = refl

assoc≡ : (a b c d : A)(p : a ≡ b)(q : b ≡ c)(r : c ≡ d)
  → trans _ _ _ (trans _ _ _ p q) r ≡ trans _ _ _ p (trans _ _ _ q r)
assoc≡ a .a c d refl q r = refl

lsym≡ : (a b : A)(p : a ≡ b) → trans _ _ _ (sym _ _ p) p ≡ refl
lsym≡ a .a refl = refl

rsym≡ : (a b : A)(p : a ≡ b) → trans _ _ _ p (sym _ _ p) ≡ refl
rsym≡ a .a refl = refl

-- show that all these can be proven using J
-- using J we can show that equality is a groupoid 
-- Hofmann-Streicher : using the laws groupoid justifies J
-- if we just assume that equality is a groupoid we get J
-- the groupoid model of Type Theory
-- using any groupoid (eg ℤ) we can show that K cannot be derivable.

rneutr≡-j : (a b : A)(p : a ≡ b) → trans a b b p refl ≡ p
rneutr≡-j = J (λ a b p → trans a b b p refl ≡ p) (λ a → refl)

-- I thought: OK we need K. I was wrong. 
-- extensionality ? 
-- Coq never implemented K (now called Rocq)

open import Data.Nat
f : ℕ → ℕ
f x = x + 0
g : ℕ → ℕ
g x = 0 + x

lem : (x : ℕ) → f x ≡ g x 
lem zero = refl
lem (suc x) = cong suc _ _ (lem x)

fg : f ≡ g 
fg = ?