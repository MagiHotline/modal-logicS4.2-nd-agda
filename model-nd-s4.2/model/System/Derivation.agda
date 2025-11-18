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

-- Con contesto iniziale Γ (una lista di formule posizionate) e una formula posizionata P,
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
    Ax : ∀ {n A} {s : position {n}} {Γ : List (pf {n})} → (A ^ s) ∷ Γ ⊢ (A ^ s)
    Wk : ∀ {n A B} {s : position {n}} {Γ : List (pf {n})}
        → (P_B : Γ ⊢ B ^ s) 
        → (B ^ s) ∷ Γ ⊢ (A ⇒ B) ^ s
    ⇒I : ∀ {n A B} {s : position {n}} {Γ : List (pf {n})}
        → (P_B : (A ^ s) ∷ Γ ⊢ B ^ s) 
        → Γ ⊢ (A ⇒ B) ^ s
    ⇒E : ∀ {n A B} {s : position {n}} {Γ : List (pf {n})}
        → (P₁ : Γ ⊢ (A ⇒ B) ^ s) 
        → (P₂ : Γ ⊢ A ^ s) 
        → Γ ⊢ B ^ s  
    ∧I : ∀ {n A B} {s : position {n}} {Γ : List (pf {n})}
        → (P₁ : Γ ⊢ A ^ s) 
        → (P₂ : Γ ⊢ B ^ s) 
        → Γ ⊢ (A ∧ B) ^ s  
    ∧E₁ : ∀ {n A B} {s : position {n}} {Γ : List (pf {n})}
        → (P : Γ ⊢ (A ∧ B) ^ s) 
        → Γ ⊢ A ^ s
    ∧E₂ : ∀ {n A B} {s : position {n}} {Γ : List (pf {n})}
        → (P : Γ ⊢ (A ∧ B) ^ s) 
        → Γ ⊢ B ^ s 
    ∨I₁ : ∀ {n A B} {s : position {n}} {Γ : List (pf {n})}
        → (P : Γ ⊢ A ^ s) 
        → Γ ⊢ (A ∨ B) ^ s
    ∨I₂ : ∀ {n A B} {s : position {n}} {Γ : List (pf {n})}
        → (P : Γ ⊢ B ^ s) 
        → Γ ⊢ (A ∨ B) ^ s
    ∨E : ∀ {n A B C} {s : position {n}} {Γ : List (pf {n})}
        → (P₁ : Γ ⊢ (A ∨ B) ^ s) 
        → (P₂ : (A ^ s) ∷ Γ ⊢ C ^ s) 
        → (P₃ : (B ^ s) ∷ Γ ⊢ C ^ s) 
        → Γ ⊢ C ^ s
    ¬∧ : ∀ {n A} {s : position {n}} {Γ : List (pf {n})}
        → (P₁ : Γ ⊢ (¬ A) ^ s) 
        → (P₂ : Γ ⊢ A ^ s) 
        → Γ ⊢ BOT ^ s
    ¬I : ∀ {n A} {s : position {n}} {Γ : List (pf {n})}
        → (P : (A ^ s) ∷ Γ ⊢ BOT ^ s) 
        → Γ ⊢ (¬ A) ^ s
    ----------- REGOLE MODALI -----------
    -- Introduzione del box
                                            -- ↓↓↓↓↓↓↓↓ Dove token {n} è un elemento di Fin n
    □I : ∀ {n A x} {s : position {n}} {Γ : List (pf {n})}
        → fresh x Γ -- x non appare in una assunzione aperta di Γ 
        → (P_A : (A ^ (s ∪ ⁅ x ⁆)) ∷ Γ ⊢ A ^ (s ∪ ⁅ x ⁆))
        → Γ ⊢ (□ A) ^ s
    -- Eliminazione del box
    □E : ∀ {n A x} {s : position {n}} {Γ : List (pf {n})}
        → (P_boxA : Γ ⊢ (□ A) ^ s)
        → Γ ⊢ A ^ (s ∪ ⁅ x ⁆)
    -- Introduzione del diamond
    ◇I : ∀ {n A x} {s : position {n}} {Γ : List (pf {n})}
        → (P_A : Γ ⊢ A ^ (s ∪ ⁅ x ⁆)) 
        → Γ ⊢ (◇ A) ^ s
    ◇E : ∀ {n A C x} {s t : position {n}} {Γ Δ : List (pf {n})}
         → fresh x Γ 
         → fresh x Δ 
         → (P_diamondA : Γ ⊢ (◇ A) ^ s)          
         → (P_C_dep : (A ^ (s ∪ ⁅ x ⁆)) ∷ Δ ⊢ C ^ t) 
         -- Devo combinare i contesti Γ e Δ
         → (Γ ++ Δ) ⊢ C ^ t
    




