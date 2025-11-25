{-# OPTIONS --cubical-compatible --safe #-}

module System.NaturalDeduction where

-- Include some useful STD Agda libraries
open import Data.Nat as Nat using (ℕ; zero; suc)
open import Data.Vec as Vec using (here; there)
open import Data.List as List using (List; []; _∷_; _++_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import Data.Fin using (Fin; zero; suc; fromℕ; toℕ)
open import Data.List.Membership.Propositional as Mem using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any as Any

open import System.Modal 

variable 
    n : ℕ
    s t : position {n}
    A B : mf 
    Q T P : pf 
    Γ : List (pf {n})

-- Definizione delle regole di inferenza del sistema di deduzione naturale
infix 4 _⊢_
data _⊢_ : {n : ℕ} → List (pf {n}) → pf {n} → Set where

    -- REGOLE STRUTTURALI 

    -- ASSUNZIONE: Mi serve per introddure ipotesi all'interno della derivazione
    Ass : ∀ {A Γ} → (A ^ s) ∷ Γ ⊢ (A ^ s)
    -- WEAKENING: Se posso provare P da Γ, posso provarlo anche se aggiungo un'altra ipotesi 
    Wk : ∀ {P Q} 
        → (Π : Γ ⊢ P)
        → (Q ∷ Γ) ⊢ P

    -- EXCHANGE 
    Exch : ∀ {Q T Γ}
        → (Π : Q ∷ T ∷ Γ ⊢ P)
        → T ∷ Q ∷ Γ ⊢ P

    -- REGOLE PROPOSIZIONALI 

    -- IMPLICAZIONE INTRODUZIONE
    ⇒I : ∀ {A B} 
        → (P_B : (A ^ s) ∷ Γ ⊢ B ^ s) 
        → Γ ⊢ (A ⇒ B) ^ s

    -- IMPLICAZIONE ELIMINAZIONE (Modus Ponens)
    ⇒E : ∀ {A B s}
        → (P_A⇒B : Γ ⊢ (A ⇒ B) ^ s) 
        → (P_A : Γ ⊢ A ^ s) 
        → Γ ⊢ B ^ s  
    -- CONGIUNZIONE
    ∧I : ∀ {A B s}
        → Γ ⊢ A ^ s 
        → Γ ⊢ B ^ s 
        → Γ ⊢ (A ∧ B) ^ s  
    ∧E₁ : ∀ {A B s} 
        → Γ ⊢ (A ∧ B) ^ s 
        → Γ ⊢ A ^ s
    ∧E₂ : ∀ {A B s} 
        → Γ ⊢ (A ∧ B) ^ s 
        → Γ ⊢ B ^ s 
    -- DISGIUNZIONE
    ∨I₁ : ∀ {A B s} 
        → Γ ⊢ A ^ s 
        → Γ ⊢ (A ∨ B) ^ s
    ∨I₂ : ∀ {A B s} 
        → Γ ⊢ B ^ s 
        → Γ ⊢ (A ∨ B) ^ s
    -- DISGIUNZIONE ELIMINAZIONE
    ∨E : ∀ {A B C s} 
        → (P_AB : Γ ⊢ (A ∨ B) ^ s) 
        → (P_C₁ : (A ^ s) ∷ Γ ⊢ C ^ s) 
        → (P_C₂ : (B ^ s) ∷ Γ ⊢ C ^ s) 
        → Γ ⊢ C ^ s

    -- Questa è solo MP ? 
    -- ¬E : ∀ {n A s} {Γ : List (pf {n})}
    --    → Γ ⊢ (¬ A) ^ s 
    --    → Γ ⊢ A ^ s 
    --    → Γ ⊢ BOT ^ s

    -- RAA
    RAA : ∀ {A s}
        → (P_bot : (A ^ s) ∷ Γ ⊢ BOT ^ s) 
        → Γ ⊢ (¬ A) ^ s                  
    -- Ex-falso quod libet
    Ex-falso : ∀ {A s} 
        → (P_bot : Γ ⊢ BOT ^ s) 
        → Γ ⊢ A ^ s
        
    -- REGOLE MODALI 

    -- BOX INTRODUZIONE 
    □I : ∀ {A x s} 
        → x ∉ s
        → fresh x Γ                       
        → (P : Γ ⊢ A ^ (s ∪ ⁅ x ⁆))   
        → Γ ⊢ (□ A) ^ s 
    -- BOX ELIMINAZIONE
    □E : ∀ {A}
        → (P_box : Γ ⊢ (□ A) ^ s)
        → Γ ⊢ A ^ (s ∪ t)
    -- DIAMOND INTRODUZIONE
    ◇I : ∀ {A t s} 
        → (P_A : Γ ⊢ A ^ (s ∪ t)) 
        → Γ ⊢ (◇ A) ^ s
    -- DIAMOND ELIMINAZIONE
    ◇E : ∀ {A C x s t} 
         → x ∉ s
         → x ∉ t
         → fresh x Γ                        
         → (P_diamond : Γ ⊢ (◇ A) ^ s)     
         → (P_C : (A ^ (s ∪ ⁅ x ⁆)) ∷ Γ ⊢ C ^ t) 
         → Γ ⊢ C ^ t     
    -- NEC 
    NEC : ∀ {A} 
        → (P_A : Γ ⊢ A ^ ∅) 
        → Γ ⊢ (□ A) ^ ∅                   
