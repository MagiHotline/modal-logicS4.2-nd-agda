{-# OPTIONS --cubical-compatible --safe #-}

module System.Derivation where

open import Data.Nat as Nat using (ℕ; zero; suc)
open import Data.List as List using (List; []; _∷_; _++_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import Data.Fin using (Fin; zero; suc; fromℕ; toℕ)
open import Data.Fin.Subset as Subset
open import System.Modal
open import Data.List.Membership.Propositional as Mem using (_∈_)

infix 4 _⊢_
data _⊢_ : {n : ℕ} → List (pf {n}) → pf {n} → Set where
    ----------- REGOLE PROPOSIZIONALI -----------
    -- (P_B : (A ^ s) ∷ Γ ⊢ B ^ s) 
    -- dove A ^ s L'assunzione specifica che si sta aggiungendo (e che verrà scaricata).
    -- L'operatore ∷ indica che A ^ s viene aggiunta al contesto Γ.
    -- Γ sono le altre assunzioni attive 
    -- (A ^ s) ∷ Γ è il contesto esteso 
    -- B ^ s La conclusione che si vuole dimostrare.
    --  Γ ⊢ (A ⇒ B) ^ s quando abbiamo questa prova l'elemento A ^ s è stato rimosso e quindi scaricato

    -- Assunzione: P è derivabile da Γ se P è in Γ.
    Ass : {n : ℕ} {P : pf {n}} {Γ : List (pf {n})} → P Mem.∈ Γ → Γ ⊢ P
    ⇒I : {A B : mf} {n : ℕ} {s : position {n}} → (P_B : (A ^ s) ∷ Γ ⊢ B ^ s) → Γ ⊢ (A ⇒ B) ^ s
    ⇒E : {A B : mf} {n : ℕ} {s : position {n}} → (P₁ : Γ ⊢ (A ⇒ B) ^ s) → (P₂ : Γ ⊢ A ^ s) → Γ ⊢ B ^ s  
    ∧I : {A B : mf} {n : ℕ} {s : position {n}} → (P₁ : Γ ⊢ A ^ s) → (P₂ : Γ ⊢ B ^ s) → Γ ⊢ (A ∧ B) ^ s  
    ∧E₁ : {A B : mf} {n : ℕ} {s : position {n}} → (P : Γ ⊢ (A ∧ B) ^ s) → Γ ⊢ A ^ s
    ∧E₂ : {A B : mf} {n : ℕ} {s : position {n}} → (P : Γ ⊢ (A ∧ B) ^ s) → Γ ⊢ B ^ s 
    ∨I₁ : {A B : mf} {n : ℕ} {s : position {n}} → (P : Γ ⊢ A ^ s) → Γ ⊢ (A ∨ B) ^ s
    ∨I₂ : {A B : mf} {n : ℕ} {s : position {n}} → (P : Γ ⊢ B ^ s) → Γ ⊢ (A ∨ B) ^ s
    ∨E : {A B C : mf} {n : ℕ} {s : position {n}} → (P₁ : Γ ⊢ (A ∨ B) ^ s) →
          (P₂ : (A ^ s) ∷ Γ ⊢ C ^ s) → (P₃ : (B ^ s) ∷ Γ ⊢ C ^ s) → Γ ⊢ C ^ s
    ¬∧ : {A : mf} {n : ℕ} {Γ : List (pf {n})} {s : position {n}} → (P₁ : Γ ⊢ (¬ A) ^ s) → (P₂ : Γ ⊢ A ^ s) → Γ ⊢ BOT ^ s
    ¬I : {A : mf} {n : ℕ} {Γ : List (pf {n})} {s : position {n}} → (P : (A ^ s) ∷ Γ ⊢ BOT ^ s) → Γ ⊢ (¬ A) ^ s
    ----------- REGOLE MODALI -----------
    -- Introduzione del box
                                            -- ↓↓↓↓↓↓↓↓ Dove token {n} è un elemento di Fin n
    □I : {A : mf} {n : ℕ} {s : position {n}} {x : Fin n} 
        → fresh x Γ -- x non appare in una assunzione aperta di Γ 
        → (P_A : (A ^ (s ∪ ⁅ x ⁆)) ∷ Γ ⊢ A ^ (s ∪ ⁅ x ⁆))
        → Γ ⊢ (□ A) ^ s
    -- Eliminazione del box
    □E : {A : mf} {n : ℕ} {s : position {n}} {x : Fin n} 
        → (P_boxA : Γ ⊢ (□ A) ^ s)
        → Γ ⊢ A ^ (s ∪ ⁅ x ⁆)
    -- Introduzione del diamond
    ◇I : {A : mf} {n : ℕ} {s : position {n}} {x : Fin n} → (P_A : Γ ⊢ A ^ (s ∪ ⁅ x ⁆)) → Γ ⊢ (◇ A) ^ s
    ◇E : {A C : mf} {n : ℕ} {s t : position {n}} {x : Fin n} {Γ Δ : List (pf {n})} 
         → fresh x Γ 
         → fresh x Δ 
         → (P_diamondA : Γ ⊢ (◇ A) ^ s)          
         → (P_C_dep : (A ^ (s ∪ ⁅ x ⁆)) ∷ Δ ⊢ C ^ t) 
         -- I need to combine the two contexts Γ and Δ
         → (Γ ++ Δ) ⊢ C ^ t




