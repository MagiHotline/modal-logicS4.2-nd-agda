{-# OPTIONS --cubical-compatible --safe #-}

module System.Modal where

open import Data.Nat as Nat using (ℕ; zero; suc; _+_; _<_; _≤_)
open import Data.List as List using (List; []; _∷_; map; concat; _++_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import Data.Fin using (Fin; zero; suc; fromℕ; toℕ)
open import Data.List.Membership.Propositional as Mem using (_∈_; _∉_)
-- open import Data.Fin.Subset as Subset

-- We first define modal formulas 
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

-- definizione delle positions come liste di token (Fin n)
position : {n : ℕ} → Set
position {n} = List (Fin n)

-- position senza token, vuota
∅ : {n : ℕ} → position {n}
∅ = []

-- unire due positions
infix 6 _∪_
_∪_ : {n : ℕ} → position {n} → position {n} → position {n}
s ∪ t = s ++ t

-- per inserire un singolo token nella position
⁅_⁆ : {n : ℕ} → Fin n → position {n}
⁅ x ⁆ = x ∷ []

-- DA CAMBIARE
-- RICERCA COME SONO IMPLEMENTATI GLI INSIEMI IN AGDA
-- Alternativa: usare liste per le positions (duplication and contraction)
-- Posizione come funzione () insieme come funzioni nei Proof 

infix 6 _^_ 
record pf {n : ℕ} : Set where 
   constructor _^_ 
   field 
    A : mf
    s : position {n}

-- La nuova funzione fresh controlla che un token x non appartenga 
-- alla lista delle formule in Γ
fresh : {n : ℕ} → Fin n → List (pf {n}) → Set
fresh x Γ = x ∉ (concat (map pf.s Γ))