{-# OPTIONS --cubical-compatible --safe #-}

module System.Modal where

open import Data.Nat as Nat using (ℕ; zero; suc; _+_; _<_; _≤_)
open import Data.List as List using (List; []; _∷_; map; concat; _++_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Relation.Nullary.Decidable using (does)
open import Data.Fin using (Fin; zero; suc; fromℕ; toℕ; _≟_)
open import Data.List.Membership.Propositional as Mem using (_∈_; _∉_)
-- open import Data.Fin.Subset as Subset

data mf : Set where 
    BOT : mf
    TOP : mf
    _⇒_ : mf → mf → mf
    ¬_ : mf → mf
    _∧_ : mf → mf → mf
    _∨_ : mf → mf → mf
    □_ : mf → mf
    ◇_ : mf → mf

-- precedenze e associatività degli operatori
infixr 10 _⇒_  
infixr 15 _∨_  
infixr 20 _∧_  
infix  30 □_  
infix  30 ◇_   
infix  30 ¬_

Token : ℕ → Set
Token n = Fin n

-- definizione delle positions come liste di token (Fin n)
position : {n : ℕ} → Set
position {n} = List (Token n)

-- position senza token, vuota
∅ : {n : ℕ} → position {n}
∅ = []

-- Funzione Ausiliaria "Smart Cons" (_∷?_)
-- Inserisce x nella lista SOLO SE non è già presente.
infixr 5 _∷?_
_∷?_ : {n : ℕ} → Token n → position {n} → position {n}
x ∷? [] = x ∷ []
x ∷? (y ∷ ys) = if does (x ≟ y) then (y ∷ ys) else (y ∷ (x ∷? ys))

-- UNIONE
infix 6 _∪_
_∪_ : {n : ℕ} → position {n} → position {n} → position {n}
[] ∪ t = t
(x ∷ s) ∪ t = s ∪ (x ∷? t)

-- per inserire un singolo token nella position
⁅_⁆ : {n : ℕ} → Token n → position {n}
⁅ x ⁆ = x ∷ ∅

infix 6 _^_ 
record pf {n : ℕ} : Set where 
   constructor _^_ 
   field 
    A : mf
    s : position {n}

-- La nuova funzione fresh controlla che un token x non appartenga 
-- alla lista delle formule in Γ

-- Given a predicate P, then Any P xs means that at least one element
-- in xs satisfies P. See `Relation.Unary` for an explanation of
-- predicates.

-- Quindi ci chiediamo se un elemento x appartiene a una lista di elementi xs
-- _∈_ : A → List A → Set _
-- x ∈ xs = Any (x ≈_) xs
-- E qua se un elemento x non appartiene a una lista di elementi xs
-- _∉_ : A → List A → Set _
-- x ∉ xs = ¬ x ∈ xs

fresh : {n : ℕ} → Token n → List (pf {n}) → Set
fresh x Γ = x ∉ (concat (map pf.s Γ))