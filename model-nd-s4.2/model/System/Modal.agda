{-# OPTIONS --cubical-compatible --safe #-}

module System.Modal where

open import Data.Nat as Nat using (ℕ; zero; suc; _+_; _<_; _≤_)
open import Data.List as List using (List; []; _∷_; map)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import Data.Fin using (Fin; zero; suc; fromℕ; toℕ)
open import Data.Fin.Subset as Subset 

-- We first define modal formulas 
data mf : Set where 
    atom : String → mf
    BOT : mf
    TOP : mf
    _⇒_ : mf → mf → mf
    ¬_ : mf → mf
    _∧_ : mf → mf → mf
    _∨_ : mf → mf → mf
    □_ : mf → mf
    ◇_ : mf → mf

-- Next, we define position formulas where a Position formula is an expression A^s 
-- where A is a modal formula and s is a position.
-- A position is a finite set of tokens where the empty set denotes the empty position 
-- and s,t denotes the union of positions s ∪ t and s,x denotes the position s ∪ {x}

-- A token is defined in the proof assistant as a term of Fin n. 
-- In STD Agda, Fin n is the type of natural numbers less than n.
-- where n determines the size of the set. 
-- A position si defined as Subset n. The type Subset n represents a subset of Fin n 
position : {n : ℕ} → Set
position {n} = Subset n 

infix 6 _^_ 
record pf {n : ℕ} : Set where 
   constructor _^_
   field 
    A : mf
    s : position {n}

-- I won't redefine the Fin n as token but I will just say that the tokens are elements of Fin n.
fresh : {n : ℕ} → Fin n → List (pf) → Set
fresh x Γ = x ∉ (⋃ (map (pf.s) Γ))


