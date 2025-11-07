{-
Introduction to Type Theory (2)

Logic via PaT
-}

Prop = Set

variable P Q R : Prop

infixr 1 _⇒_
_⇒_ : Prop → Prop → Prop
P ⇒ Q = P → Q

swap : (P ⇒ Q ⇒ R) ⇒ (Q ⇒ P ⇒ R)
swap pqr q p = pqr p q

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B

open _×_

variable A B C : Set

-- _,_ : A → B → A × B
-- proj₁ (a , b) = a
-- proj₂ (a , b) = b

infix 3 _∧_
_∧_ : Prop → Prop → Prop
P ∧ Q = P × Q

infix 0 _⇔_
_⇔_ : Prop → Prop → Prop
P ⇔ Q = (P ⇒ Q) ∧ (Q ⇒ P)

assoc : P ∧ (Q ∧ R) ⇔ (P ∧ Q) ∧ R
proj₁ assoc (p , (q , r)) = (p , q) , r
proj₂ assoc ((p , q) , r) = p , (q , r)

-- disjoint union, coproduct, sum (+)

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

infix 2 _∨_
_∨_ : Prop → Prop → Prop
P ∨ Q = P ⊎ Q -- uplus

-- Distributivity
distrib : P ∧ (Q ∨ R) ⇔ (P ∧ Q) ∨ (P ∧ R)
proj₁ distrib (p , inj₁ q) = inj₁ (p , q) 
proj₁ distrib (p , inj₂ r) = inj₂ (p , r)
proj₂ distrib (inj₁ (p , q)) = p , inj₁ q
proj₂ distrib (inj₂ (p , r)) = p , inj₂ r

data ⊥ : Set where

record ⊤ : Set where

¬ : Prop → Prop
¬ P = P ⇒ ⊥

efq : ⊥ ⇒ P
efq () -- impossible pattern

dm1 : ¬ (P ∨ Q) ⇔ (¬ P) ∧ (¬ Q)
dm1 = {!!}

-- I don't have dogs and cats
-- I don't have dogs or I don't have cats 

-- tertium non datur
tnd : Prop → Prop
tnd P = P ∨ ¬ P

dm2 : tnd P → ¬ (P ∧ Q) ⇔ (¬ P) ∨ (¬ Q)
proj₁ (dm2 (inj₁ p)) npq = inj₂ (λ q → npq (p , q))
proj₁ (dm2 (inj₂ np)) npq = inj₁ np
proj₂ (dm2 tnd) = {!!}

-- reductio ad absurdum, indirect proof
raa : Prop → Prop
raa P = (¬ (¬ P)) ⇒ P

tnd→raa : (tnd P) ⇒ raa P
tnd→raa (inj₁ p) nnp = p
tnd→raa (inj₂ np) nnp = efq (nnp np) 

nntnd : (¬ (¬  (P ∨ ¬ P))) 
nntnd f = f (inj₂ (λ p → f (inj₁ p)))

raa→tnd : raa (tnd P) → tnd P
raa→tnd h = h nntnd
-- Thus, raa and tnd are equivalent principles
-- both are based truth interpretation of Prop L

CLASS = {P : Prop} → raa P

-- ∀ 
All : (A : Set) → (A → Prop) → Prop
All A P = (x : A) → P x

syntax All A (λ x → P) = ∀[ x ∈ A ] P

variable PP QQ : A → Prop

all-and : ∀[ x ∈ A ] (PP x ∧ QQ x) ⇔ 
    (∀[ x ∈ A ](PP x)) ∧ (∀[ x ∈ A ](QQ x))
proj₁ all-and f  = (λ x →  proj₁ (f x)) , (λ x →  proj₂ (f x))
proj₂ all-and  (f , g) = λ x → (f x)  , (g x)

-- ∃

record Σ (A : Set) (P : A → Prop) : Set where
  constructor _,_
  field
    witness : A
    proof   : P witness

Ex : (A : Set) → (A → Prop) → Prop
Ex A P = Σ A P

syntax Ex A (λ x → P) = ∃[ x ∈ A ] P

-- ex-or : ∃[ x ∈ A ] (PP x ∨ QQ x) ⇔ 
--    (∃[ x ∈ A ] PP x) ∨ (∃[ x ∈ A ] QQ x)
-- proj₁ ex-or (a, inj₁ pa) = inj₁ (a , pa)
-- proj₁ ex-or (a, inj₂ qa) = inj₂ (a , qa)
-- proj₂ ex-or (inj₁ (a , pa)) = a , inj₁ pa
-- proj₂ ex-or (inj₂ (a , qa)) = a , inj₂ qa

variable RR : A → B → Prop

-- Axiom of Choice says 
-- if for every x in A there exists a y in B such that R x y
-- then there exists a function f from A to B such that for every x in A R x (f x)
ac : (∀[ x ∈ A ] ∃[ y ∈ B ] RR x y) ⇒ 
     (∃[ f ∈ (A → B) ] ∀[ x ∈ A ] RR x (f x))
ac h = (λ x → Σ.witness (h x)) , (λ x → Σ.proof (h x))

-- I have proven the axiom of choice
-- Diaconescu : AC ⇒ TND
-- Prop = Sets with at most one inhabitant
-- HoTT definition of Prop, redefine ∨ and ∃ using prop truncation