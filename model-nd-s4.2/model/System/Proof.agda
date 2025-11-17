{-# OPTIONS --cubical-compatible --safe #-}

module System.Proof where

open import Data.Nat as Nat using (ℕ; zero; suc)
open import Data.List as List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import Data.Fin using (Fin; zero; suc; fromℕ; toℕ)
open import Data.Fin.Subset as Subset
open import System.Modal

-- Il tipo di una Prova è una Prova di una specifica Formula Posizionata (pf).
-- Le assunzioni (il contesto) saranno gestite come parametri chiusi (assunzioni scaricabili) nelle regole di introduzione.
data Proof {n : ℕ} : pf {n} → Set where
    -- Implica-Introduzione (scarica un'assunzione [A^s] per ottenere (A⇒B)^s)
    -- L'assunzione scaricata A^s è un parametro del costruttore.
    -- (Per semplicità, non sto includendo qui il meccanismo di gestione del contesto di Agda,
    -- ma l'idea è che A^s non deve essere una premessa non scaricata di P_B)
    -- In una formalizzazione 'pura' ND in Agda, questo è gestito da una funzione.
    -- Qui lo semplifichiamo, assumendo che sia corretto in linea di principio.

    -- Se hai una prova P_B di B^s che dipende da un'assunzione A^s,
    -- allora puoi concludere una prova di (A⇒B)^s (senza dipendere da A^s).
    ----------- REGOLE PROPOSIZIONALI -----------
    Ax : {A : mf} {s : position {n}} → Proof (A ^ s) → Proof (A ^ s)
    -- Weakening
    Wk : {A B : mf} {s : position {n}} → Proof (A ^ s) → Proof ((B ⇒ A) ^ s)
    -- Introduizione dell'implicazione
    ⇒I : {A B : mf} {s : position {n}} → (P_B : Proof (B ^ s)) → Proof ((A ⇒ B) ^ s)
    -- Eliminazione dell'implicazione
    ⇒E : {A B : mf} {s : position {n}} → (P_A : Proof (A ^ s)) → (P_A⇒B : Proof ((A ⇒ B) ^ s)) → Proof (B ^ s)
    -- Introduzione dell'and
    ∧I : {A B : mf} {s : position {n}} → (P_A : Proof (A ^ s)) → (P_B : Proof (B ^ s)) → Proof ((A ∧ B) ^ s)
    -- Eliminazione dell'and
    ∧E₁ : {A B : mf} {s : position {n}} → (P_A∧B : Proof ((A ∧ B) ^ s)) → Proof (A ^ s)
    ∧E₂ : {A B : mf} {s : position {n}} → (P_A∧B : Proof ((A ∧ B) ^ s)) → Proof (B ^ s)
    -- Introduzione dell'or
    ∨I₁ : {A B : mf} {s : position {n}} → (P_A : Proof (A ^ s)) → Proof ((A ∨ B) ^ s)
    ∨I₂ : {A B : mf} {s : position {n}} → (P_B : Proof (B ^ s)) → Proof ((A ∨ B) ^ s)
    -- Eliminazione dell'or
    ∨E : {A B C : mf} {s : position {n}} → (P_A∨B : Proof ((A ∨ B) ^ s)) →
          (P_A_to_C : Proof (C ^ s)) → (P_B_to_C : Proof (C ^ s)) → Proof (C ^ s)
    -- Contradiction
    ¬∧ : {A : mf} {s : position {n}} → (P_notA : Proof ((¬ A) ^ s)) → (P_A : Proof (A ^ s)) → Proof (BOT ^ s)
    ¬I : {A : mf} {s : position {n}} → (P_⊥ : Proof (BOT ^ s)) → Proof ((¬ A) ^ s)

    ----------- REGOLE MODALI -----------
    -- Introduzione del box
                                   -- ↓↓↓↓↓↓↓↓ Dove token {n} è un elemento di Fin n
    □I : {A : mf} {s : position {n}} {x : Fin n} {Γ : List (pf {n})} 
     → fresh x Γ -- x non appare in una assunzione aperta di Γ 
     → (P_A : Proof (A ^ (s ∪ ⁅ x ⁆)))
     → Proof ((□ A) ^ s)
    -- Eliminazione del box
    □E : {A : mf} {s : position {n}} {x : Fin n}
     → (P_boxA : Proof ((□ A) ^ s))
     → Proof (A ^ (s ∪ ⁅ x ⁆))
    -- Introduzione del diamond
    ◇I : {A : mf} {s : position {n}} {x : Fin n}
     → (P_A : Proof (A ^ (s ∪ ⁅ x ⁆)))
     → Proof ((◇ A) ^ s)
    -- Eliminazione del diamond
    ◇E : {A C : mf} {s t : position {n}} {x : Fin n} {Γ Δ : List (pf {n})} 
     → fresh x Γ -- x non appare in una assunzione aperta di Γ 
     → fresh x Δ -- x non appare in una assunzione aperta di Δ
     → (P_A : Proof (A ^ (s ∪ ⁅ x ⁆)))
     → (P_diamondA : Proof ((◇ A) ^ s)) 
     → (P_C : Proof (C ^ t))
     -- If from A^s∪{x} and Δ we can prove C^t then ...
     → Proof (C ^ t)

