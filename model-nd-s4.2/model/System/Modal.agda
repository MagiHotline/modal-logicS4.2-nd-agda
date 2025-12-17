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

fresh : {n : ℕ} → Token n → List (pf {n}) → Set
fresh x Γ = x ∉ (concat (map pf.s Γ))

-- Equivalenza logica
-- A ⇔ B significa semplicemente (A implica B) E (B implica A)
infix 3 _⇔_
_⇔_ : Set → Set → Set
A ⇔ B = (A → B) × (B → A)

-- Definizione di Equivalenza Insiemistica
-- Due posizioni sono equivalenti se contengono gli stessi elementi.
infix 4 _≈_
_≈_ : {n : ℕ} → position {n} → position {n} → Set
s ≈ t = ∀ {x} → (x ∈ s) ⇔ (x ∈ t)

-- Quindi ci chiediamo se un elemento x appartiene a una lista di elementi xs
-- _∈_ : A → List A → Set _
-- x ∈ xs = Any (x ≈_) xs
