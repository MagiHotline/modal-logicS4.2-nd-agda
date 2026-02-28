{-

  This file is the entry point to the formalization of my work on
  S4.2 Modal Logic using a deductive system such as Natural Deduction
  by Paolo Imbriani

  It has been tested with
  - Agda version 2.8.0

-}

module index where

open import Data.Nat as Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.List as List using (List; []; _∷_; _++_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; _≢_; sym; cong)
open import Data.Fin using (Fin; zero; suc; fromℕ; toℕ; _≟_)
open import Data.List.Membership.Propositional as Mem using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any as Any

open import System.Modal
open import System.NaturalDeduction

-- § TATTICHE / LEMMI AUSILIARI

-- fresh-[] : Una formula posizionata in x è sempre fresh da una lista vuota.
fresh-[] : ∀ {n} {x : Token n} → fresh x []
fresh-[] ()

-- var ∉∅ : Prova che var non appartiene all'insieme vuoto
∉∅ : ∀ {n} {x : Token n} → x ∉ (∅ {n})
∉∅ ()

-- Definiamo esplicitamente che suc zero non è (zero).
suc-zero≢zero : ∀ {n} → Fin.suc (Fin.zero {n}) ≢ Fin.zero
suc-zero≢zero () 

-- ∉-singleton : Se x ed y sono distinti, allora x non appartiene alla lista contenente solo y.
∉-singleton : ∀ {a} {A : Set a} {x y : A} → x ≢ y → x ∉ (y ∷ [])
∉-singleton x≢y (Any.here p) = x≢y p
∉-singleton x≢y (Any.there ())

-- I postulate in Agda ci permettono di dichiarare assiomi che assumiamo veri senza doverli dimostrare.
postulate
  -- Lemma insiemistico: {x, y} è uguale a {y, x}.
  -- È vero per definizione di unione insiemistica.
  comm-lemma : ∀ {n} {x y : Token n} → (⁅ x ⁆ ∪ ⁅ y ⁆) ≈ (⁅ y ⁆ ∪ ⁅ x ⁆)

prova : (A ^ s) ∷ (B ^ s) ∷ [] ⊢ B ^ s
prova = Wk Ass

-- S4.2 è il più piccolo insieme X di formule che contiene tutte le istanze dei seguenti assiomi:

{- §0. MP: A , A→B → B -}

mp : ∀ {n A B} → ( [] ⊢ A ^ (∅ {n}) ) → ( [] ⊢ (A ⇒ B) ^ (∅ {n}) ) → ( [] ⊢ B ^ (∅ {n}) )
mp P_A P_A⇒B = ⇒E P_A⇒B P_A

{- §1. P1: A → (B → A) ^ ∅ -}

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
          ¬E 
          (
             ⇒E (Wk (Wk Ass)) Ass
          )
          (
             ⇒E (Wk Ass) Ass
          )
       )
    )
  )

{- §4. K: □(A → B) → (□A → □B) -}

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
       □I {x = zero} (∉∅) (∉∅) -- Introduciamo il box per avere (□ B)^∅
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
axiom4 {n} {A} =
  let 
    x = Fin.zero 
    y = Fin.suc Fin.zero
  in
  ⇒I {A = □ A} {B = □ (□ A)} ( -- Scarico □A ^ ∅ 
    □I {x = x} -- Rimuovi x
       ∉∅ -- x non appartiene alla lista vuota
       fresh-[] -- x è sempre fresco in una lista vuota
       ( 
         □I {x = y} -- Rimuovi y
            (∉-singleton (suc-zero≢zero {n})) -- Un elemento x non appartiene alla lista di y se x e y sono diversi
            fresh-[]                          -- Un elemento è sempre fresh da una lista vuota
            (
              □E Ass -- Assumption □ A ^ ∅
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

-- TENTATIVO DI TRADUZIONE (FALLISCE SENZA CASTING DA LISTA A INSIEME)
{-
geachAttempt : ∀ {n A} → [] ⊢ ((◇ (□ A)) ⇒ (□ (◇ A))) ^ (∅ {suc (suc n)})
geachAttempt {n} {A} = 
  let 
    x = zero
    y = suc zero
  in
  -- Agda riesce con successo a costruire ◇ (□ A)) ⇒ (□ (◇ A)) 
  -- se si prova a dare ad A e B valori diversi, l'assioma doesn't hold
  ⇒I {A = ◇ (□ A)} {B = (□ (◇ A))} (
    -- 1. Eliminiamo ◇(□ A) ^ ∅. Otteniamo x e (□ A) ^ x.
    ◇E {x = x} 
       (∉∅) -- x ∉ ∅ (s)
       (∉∅) -- x ∉ ∅ (t)
       (fresh-[]) -- fresh x (banale, contesto vuoto)
       (
        Ass -- -- L'ipotesi ◇(□ A)
       )    
       (
         -- 2. Introduciamo □(◇ A) ^ ∅.
         -- Qui siamo nel mondo ∅. Creiamo il mondo y.
         □I {x = y}
            (∉∅)    -- y ∉ ∅ (Banale)
            y∉x     -- fresh y Γ (Γ contiene x, quindi serve la prova y≠x)
            (
              -- 3. Obiettivo: ◇ A ^ y.
              -- Per la Diamond Introduction come l'abbiamo definita noi:

              {- 

                -- DIAMOND INTRODUZIONE
                ◇I : ∀ {A t s} 
                    → (P_A : Γ ⊢ A ^ (s ∪ t)) <--- in questo caso abbiamo y,x 
                    → Γ ⊢ (◇ A) ^ s <--- E ora ◇ A ^ y
              
              -}
              ◇I {t = ⁅ x ⁆} 
              (  
                  {- 
                  
                  Notice the role the interpretation of positions as a set plays
                  in the derivation, allowing to manipulating tokens independently from the position in the sequence.
                  Moving to a more structured (lists) notion of position, we can not derive the Geach’s Axioms

                  -- BorsettoZorzi Paper
                  -}
                  (□E {t = ⁅ y ⁆} Ass) -- <-- ERRORE!!! 
                  {- 
                  
                    Agda v2.8.0
                    238 => error: [UnequalTerms]
                    y != x of type Fin (suc (suc n))
                    when checking that the inferred type of an application
                      □ A ^ (∅ ∪ ⁅ x ⁆) ∷ ◇ (□ A) ^ ∅ ∷ [] ⊢ A ^ ((∅ ∪ ⁅ x ⁆) ∪ ⁅ y ⁆)
                    matches the expected type
                      □ A ^ (∅ ∪ ⁅ x ⁆) ∷ ◇ (□ A) ^ ∅ ∷ [] ⊢ A ^ ((∅ ∪ ⁅ y ⁆) ∪ ⁅ x ⁆)

                      ------------------- PERCHé LA COSTRUZIONE DELL'ASSIOMA FALLISCE -------------------

                      Il tipo position nel codice è definito come una List. 
                      Per Agda, una lista è una sequenza ordinata di elementi. 
                      [A, B] ≠ [B, A]
                      Guardiamo i due termini che Agda sta confrontando nel messaggio di errore                    

                      Agda calcola le due liste fino alla loro forma normale e vede:

                      - A: suc zero ∷ zero ∷ [] (La lista [1, 0])
                      - B: zero ∷ suc zero ∷ [] (La lista [0, 1])

                      Per Agda, queste due strutture sono diverse.
                      L'errore y != x  (y != x of type Fin...) 

                        - Guarda la testa della prima lista: trova y.
                        - Guarda la testa della seconda lista: trova x.

                      In informatica e matematica, la confluenza (Assioma di Geach) è una proprietà di riscrittura dei sistemi,
                      che descrive quali termini in tale sistema possono essere riscritti in più modi,
                      per produrre lo stesso risultato.

                      L'assioma di Geach (◇□ A ⇒ □◇A) è ciò che distingue la logica S4.2 dalla semplice S4
                      A differenza di K, T e 4, l'assioma di Geach non è derivabile sintatticamente 
                      usando solo le regole di introduzione ed eliminazione standard di □ e ◇ 
                      Geach richiede la proprietà di Confluenza (Directedness) del frame:
                      ∀ u, v, w. (uRv ∧ uRw) → ∃z.(vRz ∧ wRz)

                      -- BLOCCO LOGICO --
                      Hai due posizioni x e y. 
                      Per provare ◇A in y, ti serve un mondo z accessibile da y. 
                      Ma tu sai che A vale solo nei mondi accessibili da x. Senza una regola che dica
                      "esiste un z accessibile sia da x che da y" (Confluenza), non puoi unire i due "rami".
                  -}

              )
            )
       )
  )
  where
  -- Definiamo la prova che y (1) non appartiene a {x} (0)
  -- Questa serve per soddisfare il requisito 'fresh' di □I
  y∉x : suc zero ∉ ⁅ zero ⁆
  y∉x (Any.here ())   -- 1 != 0
  -- Devo fare Any.here poiché Fin n è un Setoid
-}

geachAxiom : ∀ {n A} → [] ⊢ ((◇ (□ A)) ⇒ (□ (◇ A))) ^ (∅ {suc (suc n)})
geachAxiom {n} {A} = 
  let 
    x = zero
    y = suc zero
  in
  -- Agda riesce con successo a costruire ◇ (□ A)) ⇒ (□ (◇ A)) 
  -- se si prova a dare ad A e B valori diversi, l'assioma doesn't hold
  ⇒I {A = ◇ (□ A)} {B = (□ (◇ A))} (
    -- 1. Eliminiamo ◇(□ A) ^ ∅. Otteniamo x e (□ A) ^ x.
    ◇E {x = x} 
       (∉∅) -- x ∉ ∅ (s)
       (∉∅) -- x ∉ ∅ (t)
       (fresh-[]) -- fresh x (banale, contesto vuoto)
       (
        Ass -- L'ipotesi ◇(□ A)
       )    
       (
         -- 2. Introduciamo □(◇ A) ^ ∅.
         -- Qui siamo nel mondo ∅. Creiamo il mondo y.
         □I {x = y}
            (∉∅)    -- y ∉ ∅ 
            y∉x     -- fresh y Γ (Γ contiene x, quindi serve la prova y≠x)
            (
              -- 3. Obiettivo: ◇ A ^ y.
              -- Per la Diamond Introduction come l'abbiamo definita noi:
              {- 

                -- DIAMOND INTRODUZIONE
                ◇I : ∀ {A t s} 
                    → (P_A : Γ ⊢ A ^ (s ∪ t)) <--- in questo caso abbiamo y,x 
                    → Γ ⊢ (◇ A) ^ s <--- E ora ◇ A ^ y
              
              -}
              ◇I {t = ⁅ x ⁆} 
              (
                -- Obiettivo: A ^ (y ∪ x)
                -- 4. Scambiamo (x ∪ y) con (y ∪ x) usando Cast
                -- Scambiare questi due elementi ci permette di poter interagire con 
                -- la lista di Token come se fossero un insieme e di conseguenza ci permette
                -- di provare la confluenza e l'assioma di Geach.
                Cast (comm-lemma {x = x} {y = y}) (□E {t = ⁅ y ⁆} Ass)
              )
            )
       )
  )
  where
    -- Definiamo la prova che y (1) non appartiene a {x} (0)
    -- Questa serve per soddisfare il requisito 'fresh' di □I
    -- per inserire un singolo token nella position
    -- ⁅_⁆ : {n : ℕ} → Token n → position {n}
    -- ⁅ x ⁆ = x ∷ ∅
    y∉x : suc zero ∉ ⁅ zero ⁆
    y∉x (Any.here ()) -- 1 != 0
    y∉x (Any.there ())   
    -- Devo fare Any.here () e non () poiché Fin n è un
    -- Setoid e lo sto confrontando con una lista 