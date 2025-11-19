{-# OPTIONS --cubical-compatible --safe #-}

module System.NaturalDeduction where

open import Data.Nat as Nat using (ℕ)
open import Data.List as List using (List; []; _∷_; _++_)
open import Data.Product using (_×_; _,_)
open import Data.Fin using (Fin)
open import Data.Fin.Subset as Subset using (_∪_; ⁅_⁆; _∉_)
open import System.Modal
open import Data.List.Membership.Propositional as Mem using (_∈_)

-- Definizione di derivazione del tipo : Γ ⊢ A^s
infix 4 _⊢_
data _⊢_ : {n : ℕ} → List (pf {n}) → pf {n} → Set where

    -- REGOLE STRUTTURALI --

    -- ASSUNZIONE: Mi serve per introddure ipotesi all'interno della derivazione
    -- Se A^s è presente in un punto qualsiasi di Γ, possiamo derivarlo.
    Ass : ∀ {n A s} {Γ : List (pf {n})} 
        → (A ^ s) ∈ Γ  -- Prova che la formula è nel contesto
        → Γ ⊢ (A ^ s)
    -- New: Se posso provare P da Γ, posso provarlo anche se aggiungo un'altra ipotesi 
    New : ∀ {n P Q} {Γ : List (pf {n})}
        → (Π : Γ ⊢ P)
        → (Q ∷ Γ) ⊢ P
    
    -- REGOLE PROPOSIZIONALI --

    -- IMPLICAZIONE INTRODUZIONE
    -- Per provare A ⇒ B, assumo A (aggiungendolo a Γ) e provo B.
    -- L'assunzione A viene "scaricata" (rimossa dal contesto della conclusione).
    ⇒I : ∀ {n A B} {Γ : List (pf {n})} {s : position {n}}
        → (P_B : (A ^ s) ∷ Γ ⊢ B ^ s) 
        → Γ ⊢ (A ⇒ B) ^ s
    -- IMPLICAZIONE ELIMINAZIONE (Modus Ponens)
    ⇒E : ∀ {n A B s} {Γ : List (pf {n})}
        → (P_A⇒B : Γ ⊢ (A ⇒ B) ^ s) 
        → (P_A : Γ ⊢ A ^ s) 
        → Γ ⊢ B ^ s  
    -- CONGIUNZIONE
    ∧I : ∀ {n A B s} {Γ : List (pf {n})}
        → Γ ⊢ A ^ s 
        → Γ ⊢ B ^ s 
        → Γ ⊢ (A ∧ B) ^ s  
    ∧E₁ : ∀ {n A B s} {Γ : List (pf {n})}
        → Γ ⊢ (A ∧ B) ^ s 
        → Γ ⊢ A ^ s
    ∧E₂ : ∀ {n A B s} {Γ : List (pf {n})}
        → Γ ⊢ (A ∧ B) ^ s 
        → Γ ⊢ B ^ s 
    -- DISGIUNZIONE
    ∨I₁ : ∀ {n A B s} {Γ : List (pf {n})}
        → Γ ⊢ A ^ s 
        → Γ ⊢ (A ∨ B) ^ s
    ∨I₂ : ∀ {n A B s} {Γ : List (pf {n})}
        → Γ ⊢ B ^ s 
        → Γ ⊢ (A ∨ B) ^ s
    -- DISGIUNZIONE ELIMINAZIONE
    -- Se ho A ∨ B, e so che A implica C e B implica C, allora ho C.
    -- Si scaricano due assunzioni diverse in due rami diversi.
    ∨E : ∀ {n A B C s} {Γ : List (pf {n})}
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
    RAA : ∀ {n A s} {Γ : List (pf {n})}
        → (P_bot : (A ^ s) ∷ Γ ⊢ BOT ^ s) 
        → Γ ⊢ (¬ A) ^ s                  
    -- Ex-falso quod libet
    Ex-falso : ∀ {n A s} {Γ : List (pf {n})}
        → (P_bot : Γ ⊢ BOT ^ s) 
        → Γ ⊢ A ^ s

    -- REGOLE MODALI 

    -- BOX INTRODUZIONE 
    □I : ∀ {n A x s} {Γ : List (pf {n})}
        → x ∉ s
        → fresh x Γ                       
        → (P : Γ ⊢ A ^ (s ∪ ⁅ x ⁆))   
        → Γ ⊢ (□ A) ^ s
    -- BOX ELIMINAZIONE
    □E : ∀ {n A t s} {Γ : List (pf {n})}
        → (P_box : Γ ⊢ (□ A) ^ s)
        → Γ ⊢ A ^ (s ∪ t)
    -- DIAMOND INTRODUZIONE
    ◇I : ∀ {n A t s} {Γ : List (pf {n})}
        → (P_A : Γ ⊢ A ^ (s ∪ t)) 
        → Γ ⊢ (◇ A) ^ s
    -- DIAMOND ELIMINAZIONE
    ◇E : ∀ {n A C x s t} {Γ : List (pf {n})}
         → x ∉ s
         → x ∉ t
         → fresh x Γ                        
         → (P_diamond : Γ ⊢ (◇ A) ^ s)     
         → (P_C : (A ^ (s ∪ ⁅ x ⁆)) ∷ Γ ⊢ C ^ t) 
         → Γ ⊢ C ^ t                        