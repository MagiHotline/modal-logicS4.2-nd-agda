{-

  This file is the entry point to the formalization of my work on 
  S4.2 Modal Logic using a deductive system such as Natural Deduction
  by Paolo Imbriani

  It has been tested with
  - Agda version 2.8.0

-}

{-# OPTIONS --cubical-compatible --safe #-}

module index where 

-- Include some useful STD Agda libraries
open import Data.Nat as Nat using (ℕ; zero; suc)
open import Data.List as List using (List; []; _∷_; _++_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import Data.Fin using (Fin; zero; suc; fromℕ; toℕ)
open import Data.Fin.Subset as Subset
open import Data.List.Membership.Propositional as Mem using (_∈_)
open import Data.List.Relation.Unary.Any as Any

{- Overview dei moduli -}
open import System.Modal
-- open import System.Derivation
open import System.NaturalDeduction

-- S4.2 è il più piccolo insieme X di formule che contiene tutte le istanze dei seguenti assiomi: 

{- §0. MP: A , A→B → B -}
-- Modus Ponens -- A ∷ [] , A ⇒ B ∷ [] ⊢ B
mp : ∀ {n A B} → ( [] ⊢ A ^ ⊥ ) → ( [] ⊢ (A ⇒ B) ^ ⊥ ) → ( [] ⊢ B ^ ⊥ )
mp P_A P_A⇒B = ⇒E P_A⇒B P_A

{- §1. P1: A → (B → A) ^ ⊥ -}

-- 1. Aggiungitamo tra le assunzioni A 
-- 2. Usiamo New per aggiungere B al contesto di Γ e provare A da [B, A]
-- 3. Usiamo ⇒I per scaricare l'assunzione B e provare B ⇒ A da [A]
-- 4. Usiamo ⇒I per scaricare l'assunzione A e provare A ⇒ (B ⇒ A) da []

-- Implies -- B ∷ A  -- A ∷ [] ⊢ A
axiom1 : ∀ {n A B} → [] ⊢ (A ⇒ (B ⇒ A)) ^ ⊥
axiom1 = ⇒I ( ⇒I ( Wk ( Ass ) ) )

{- §2. P2: (A → (B → C)) → ((A → B) → (A → C)) -}


{- §3. P3: ((¬ B → ¬A) → ((¬ B → A) → B)  -}

{- §4. K: □(A → B) → (□A → □B) -}

{- §5. T: □A → A -}

axiomT : ∀ {n A} → [] ⊢(□ A ⇒ A) ^ ⊥
axiomT = ⇒I (□E ( Ass ))

{- §6. 4: □A → □□A -}

{- §7. C: ◇□A → □◇A -}

{- §8. NEC: A → □A -}

