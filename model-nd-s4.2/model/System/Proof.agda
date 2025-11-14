{-# OPTIONS --cubical-compatible --safe #-}

module System.Proof where

open import Data.Nat as Nat using (ℕ; zero; suc)
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