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
open import Data.Empty using (⊥)
open import Data.List as List using (List; []; _∷_; _++_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; _≢_; sym; cong)
open import Data.Fin using (Fin; zero; suc; fromℕ; toℕ; _≟_)
open import Data.List.Membership.Propositional as Mem using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any as Any

{- Overview dei moduli -}
open import System.Modal
-- open import System.Derivation
open import System.NaturalDeduction

-- § TATTICHE / LEMMI AUSILIARI

zero≢suc-zero : ∀ {n} → zero ≡ suc zero → ⊥
zero≢suc-zero ()

∉-singleton : ∀ {n} {x y : Token n} → (x ≡ y → ⊥) → x ∉ ⁅ y ⁆
∉-singleton x≢y (here p) = x≢y p

fresh-[] : ∀ {n} {x : Token n} → fresh x []
fresh-[] ()

x∉∅ : ∀ {n} {x : Token n} → x ∉ (∅ {n})
x∉∅ ()

-- Prova: x non appartiene mai a ∅
∉⊥ : ∀ {n} {x : Token n} → x ∉ ∅
∉⊥ ()

prova : (A ^ s) ∷ (B ^ s) ∷ [] ⊢ B ^ s
prova = Wk Ass

-- S4.2 è il più piccolo insieme X di formule che contiene tutte le istanze dei seguenti assiomi:

{- §0. MP: A , A→B → B -}

mp : ∀ {n A B} → ( [] ⊢ A ^ (∅ {n}) ) → ( [] ⊢ (A ⇒ B) ^ (∅ {n}) ) → ( [] ⊢ B ^ (∅ {n}) )
mp P_A P_A⇒B = ⇒E P_A⇒B P_A

{- §1. P1: A → (B → A) ^ ∅ -}

-- axiom1 : ∀ {n A B} → [] ⊢ (A ⇒ (B ⇒ A)) ^ ∅
axiom1 : ∀ {n A B} → [] ⊢ (A ⇒ (B ⇒ A)) ^ (∅ {n})
axiom1 {n} {A} {B} = ⇒I ( ⇒I ( Wk Ass ) )

{- §2. P2: (A → (B → C)) → ((A → B) → (A → C)) -}

axiom2 : ∀ {n A B C} → [] ⊢ ((A ⇒ (B ⇒ C)) ⇒ ((A ⇒ B) ⇒ (A ⇒ C))) ^ (∅ {n})
axiom2 {n} {A} {B} {C} =
  ⇒I {A = (A ⇒ (B ⇒ C))} {B = ((A ⇒ B) ⇒ (A ⇒ C))} (
    ⇒I {A = (A ⇒ B)} {B = (A ⇒ C)} (
      ⇒I {A = A} {B = C} (
         ⇒E -- C
           (⇒E -- B ⇒ C
             (Wk (Wk Ass)) -- A ⇒ (B ⇒ C)
             Ass -- A
           )
           (⇒E -- B
             (Wk Ass) -- A ⇒ B
             Ass -- A
           )
      )
    )
  )


{- §3. P3: ((¬ B → ¬A) → ((¬ B → A) → B) ^ ∅ -}

axiom3 : ∀ {n : ℕ} {A B} → [] ⊢ ((¬ B ⇒ ¬ A) ⇒ ((¬ B ⇒ A) ⇒ B)) ^ (∅ {n})
axiom3 {n} {A} {B} =
  ⇒I {A = ¬ B ⇒ ¬ A} {B = (¬ B ⇒ A) ⇒ B} (
    ⇒I {A = ¬ B ⇒ A} {B = B} (
       RAA {A = B} (
          ¬E (
             ⇒E (Wk (Wk Ass)) Ass
          )
          (
             ⇒E (Wk Ass) Ass
          )
       )
    )
  )

{- §4. K: □(A → B) → (□A → □B) -}

-- Assioma K: □(A → B) → (□A → □B)
-- Richiede un universo con almeno 1 token (suc n) per poter fare il "salto" nel mondo x.
axiomK : ∀ {n A B} → [] ⊢ (□ (A ⇒ B) ⇒ (□ A ⇒ □ B)) ^ (∅ {suc n})
axiomK {n} {A} {B} = 
  let 
      x = zero
      t = ⁅ x ⁆ 
  in
  ⇒I {A = □ (A ⇒ B)} {B = □ A ⇒ □ B} ( -- Scarica □(A → B)
    ⇒I {A = □ A} {B = □ B} ( -- Scarica □A     
       -- Ho bisogno di due prove 
       -- PROVA DI FRESHNESS 1: x non è nell'insieme vuoto. banalmente vero.
       -- PROVA DI FRESHNESS 2: x non è in Γ (fresh x Γ)
          -- Γ contiene solo formule posizionate in ∅. Quindi la lista dei token usati è vuota.
          -- x ∉ [] è banalmente vero per ogni formula in Γ.
       □I {x = zero} (∉⊥) (∉⊥) -- Introduciamo il box per avere (□ B)^∅
          (
             ⇒E -- A questo punto abbiamo B^x
                (
                  -- Abbiamo (A → B)^x
                  -- Prendiamo □(A → B) dall'assunzione (Wk Ass) che è a livello ∅
                  -- Usiamo □E con t=⁅x⁆ per portarla qui.
                   □E {t = ⁅ x ⁆} (Wk Ass)
                ) 
                (
                  -- Abbiamo A^x
                  -- Prendiamo □A dall'assunzione (Ass) che è a livello ∅
                  -- Usiamo □E con t= ⁅x⁆ per portarla qui.
                   □E {t = ⁅ x ⁆} Ass
                )
          )
    )
  )

{- §5. T: □A → A -}

axiomT : ∀ {n A} → ([] ⊢ ((□ A) ⇒ A) ^ (∅ {n}))
axiomT {n} {A} = ⇒I {A = □ A} {B = A} (□E {t = ∅} ( Ass ))

{- §6. 4: □A → □□A -}

-- Richiede che esistano almeno 2 token (suc (suc n))

axiom4 : ∀ {n A} → [] ⊢ (□ A ⇒ □ (□ A)) ^ (∅ {suc (suc n)})
axiom4 =
  ⇒I (
    □I {x = zero}
       x∉∅
       fresh-[]
       (
         □I {x = suc zero}
            (∉-singleton zero≢suc-zero)
            fresh-[]
            (
              □E Ass
            )
       )
  )



{- §7. 4: (□A → ◇A) ^ ∅ -}

axiomD : ∀ {n A} → [] ⊢ (□ A ⇒ ◇ A) ^ (∅ {n})
axiomD {n} {A} =
    ⇒I
    (
      ◇I {t = ∅}

      (
        □E {t = ∅} Ass
      )
    )

{- §8. C: ◇□A → □◇A -}

geachAxiom : ∀ {n A} → ([] ⊢ ((◇ (□ A))⇒ (□ (◇ A)) ^ (∅ {suc (suc n)})))
geachAxiom {A = A} = {!!}