{-
Introduction to Type Theory (3)

-}

open import Data.Nat hiding (_≤_ ; _≤?_)
open import Data.Empty 
open import Data.Unit  
open import Data.Product
open import Data.Bool hiding (_≤_ ; _≤?_)

Prop = Set
¬_ : Set → Set
¬ P = P → ⊥
infix 0 _⇔_
_⇔_ : Set → Set → Set
P ⇔ Q = (P → Q) × (Q → P)
infixr 1 _⇒_
_⇒_ : Prop → Prop → Prop
P ⇒ Q = P → Q

variable A B C : Set

-- \equiv
data _≡_ {A : Set} : A → A → Set where
    refl : (a : A) → a ≡ a

infix 4 _≡_

-- 2 + 3 = 5
-- 2 + 3 ≡ 5
-- f x = x + 0
-- g x = 0 + x
-- f ≡ g ?
-- intensional type theory

-- reflex, symmetric, transitive
-- equivalence relation

sym : {a b : A} → a ≡ b → b ≡ a
sym (refl a) = refl a

trans : {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans (refl _) q = q

-- equality is a congruence

cong : (f : A → B){a b : A} → a ≡ b → f a ≡ f b
cong f (refl a) = refl (f a)

-- uncong : (f : A → B){a b : A} → f a ≡ f b → a ≡ b
-- uncong f (refl (f a)) = refl a

-- (ℕ , + , 0 ) \bN 
-- is a commutative monoid
{-
_+_ : Nat → Nat → Nat
zero  + m = m
suc n + m = suc (n + m)
-} 
_+'_ : ℕ → ℕ → ℕ
m +' zero = m
m +' suc n = suc (m +' n)

-- m +' n = n + m

lneutr : (n : ℕ) → 0 + n ≡ n
lneutr n = refl n

rneutr : (n : ℕ) → n + 0 ≡ n
rneutr zero = refl _
rneutr (suc n) = cong suc (rneutr n)

-- induction = recursion with dependent types
-- induction = pattern matching and recursion

assoc : (l m n : ℕ) → l + (m + n) ≡ (l + m) + n
assoc zero m n = refl _
assoc (suc l) m n = cong suc (assoc l m n)

suc-plus : (m n : ℕ) → m + suc n ≡ suc (m + n)
suc-plus zero n = refl _
suc-plus (suc m) n = cong suc (suc-plus m n)

comm : (m n : ℕ) → m + n ≡ n + m
comm zero n = sym (rneutr _)
comm (suc m) n = trans (cong suc (comm m n)) (sym (suc-plus _ _))

-- suc (m + n) ≡ 
-- suc (n + m) ≡
-- n + suc m

-- (ℕ , + , 0 , * , 1) commutative semiring
-- (ℕ , *, 1) is a commutative monoid
-- (l + m) * n = l * m + l * n
-- 0 * n = 0
-- exercise : prove this 

-- (a + b)^2 = a^2 + 2ab + b^2
-- ring tactic 

-- programming with dependent (Vec, Fin,...)
-- logic PaT, induction = recursion

eqnat : ℕ → ℕ → Bool
eqnat zero zero = true
eqnat zero (suc n) = false
eqnat (suc m) zero = false
eqnat (suc m) (suc n) = eqnat m n

-- m ≡ n 

data Dec (A : Set) : Set where
    yes : A → Dec A
    no : ¬ A → Dec A

-- TND A 
-- A is decided 
-- P ̸= NP is undecided 
-- P : A → Prop
-- P is decidable : (a : A) → Dec (P a)
-- Halt : ℕ → Prop : not decidable

no-conf : (m : ℕ) → ¬ (zero ≡ suc m)
no-conf m ()

inj-suc : (m n : ℕ) → suc m ≡ suc n → m ≡ n
inj-suc m .m (refl .(suc m)) = refl _

-- _≡?_ : (m n : ℕ) → Dec (m ≡ n)
-- zero ≡? zero = yes (refl _)
-- zero ≡? suc n = no (no-conf _)
-- suc m ≡? zero = no (λ p → no-conf _ (sym p))
-- suc m ≡? suc n with m ≡? n
-- ... | yes p = yes (cong suc p)
-- ... | no np = no (λ p → np (inj-suc _ _ p))

_≡?_ : (m n : ℕ) → Dec (m ≡ n)
zero ≡? zero = yes (refl _)
zero ≡? suc n = no (λ ())
suc m ≡? zero = no (λ ())
suc m ≡? suc n with m ≡? n
... | yes p = yes (cong suc p )
... | no np = no (λ {(refl n) → np (refl _)})

data BT : Set where
    l : BT
    n : BT → BT → BT

_≡BT?_ : (t u : BT) → Dec (t ≡ u)
t ≡BT? u = {!   !}

--- Metalogic

-- Minimal logic : propositional logic with ⇒ 
-- natural deduction 
open import Data.String

data Form : Set where
 atom : String → Form
 _[⇒]_ : Form → Form → Form

data Con : Set where
  • : Con -- \bu
  _▷_ : Con → Form → Con
-- nameless, deBruijn 

infix 5 _⊢_
infix 8 _▷_
infixr 10 _[⇒]_

variable φ ψ : Form
variable Γ Δ : Con 

data _⊢_ : Con → Form → Set where

           ----------
    zero : Γ ▷ φ ⊢ φ

    suc : Γ ⊢ ψ →
          -----------
          Γ ▷ φ ⊢ ψ

    lam : Γ ▷ φ ⊢ ψ →
          ------------
          Γ ⊢ φ [⇒] ψ

    app : Γ ⊢ φ [⇒] ψ → 
          Γ ⊢ φ →
          --------------
          Γ ⊢ ψ 

I : • ⊢ (atom "P") [⇒] (atom "P")
-- λ x → x
I = lam zero

sw : • ⊢ ((atom "P") [⇒] (atom "Q") [⇒] (atom "R"))
         [⇒] ((atom "Q") [⇒] (atom "P") [⇒] (atom "R"))
sw = lam (lam (lam (app (app (suc (suc zero)) zero) (suc zero))))
    
-- bad : ¬ (• ⊢ (atom "P" [⇒] atom "Q") [⇒] (atom "Q" [⇒] atom "P"))
-- bad (lam (suc d)) = {!   !}
-- bad (lam (lam (suc d))) = {!   !}
-- bad (lam (lam (app d d₁))) = {!   !}
-- bad (lam (app d d₁)) = {!   !}
-- bad (app d e) = {!   !}

-- (P → Q) → (Q → P)
-- P = ⊥ , Q = ⊤ 

Env = String → Prop

⟦_⟧ : Form → Env → Prop
⟦ atom x ⟧ ρ = ρ x
⟦ φ [⇒] ψ ⟧ ρ = ⟦ φ ⟧ ρ → ⟦ ψ ⟧ ρ

env : Env 
env "P" = ⊥
env "Q" = ⊤
env _ = ⊥

variable ρ : Env

⟦_⟧* : Con → Env → Prop
⟦ • ⟧* ρ = ⊤
⟦ Γ ▷ φ ⟧* ρ = ⟦ Γ ⟧* ρ × ⟦ φ ⟧ ρ

sound : Γ ⊢ ψ → ⟦ Γ ⟧* ρ → ⟦ ψ ⟧ ρ
sound zero (_ , p) = p
sound (suc d) (γ , _) = sound d γ
sound (lam d) γ p = sound d (γ , p)
sound (app d e) γ = sound d γ (sound e γ)

bad : ¬ (• ⊢ (atom "P" [⇒] atom "Q") [⇒] (atom "Q" [⇒] atom "P"))
bad d = sound {ρ = env} d tt (λ _ → tt) tt

-- to prove unprovability we need semantics 
-- is there another way (more syntactic) ?

-- ((P → Q) → P) → P
-- Peirce formula

compl : ({ρ : Env} → ⟦ Γ ⟧* ρ → ⟦ ψ ⟧ ρ) → Γ ⊢ ψ 
compl = {!   !}

no-pierce : 
    ¬ (• ⊢ ((atom "P" [⇒] atom "Q") [⇒] atom "P") [⇒] atom "P")
no-pierce = {!   !}