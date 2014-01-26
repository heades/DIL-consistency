module utl where

open import Data.Nat
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Data.List
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

proj1 = proj₁ 
proj2 = proj₂
proj3 : ∀{A B C : Set}(a : A × B × C) → C
proj3 = λ a → proj2 (proj2 a)

inj1 : {A : Set}{B : Set}(x : A) → A ⊎ B
inj1  = inj₁
inj2 : {A : Set}{B : Set}(x : B) → A ⊎ B
inj2 = inj₂

True = Data.Unit.⊤
False = Data.Empty.⊥

-- Facts about Lists.
InList : {A : Set} → A → List A → Set
InList {A} e [] = False
InList {A} e (a ∷ L) = e ≡ a ⊎ InList e L

_∈_ : ∀{A : Set} → A → List A → Set
e ∈ L = InList e L

_∉_ : ∀{A : Set} → A → List A → Set
e ∉ L = e ∈ L → Data.Empty.⊥

inEq : ∀{A : Set}(a : A)(l : List A) → InList a (a ∷ l)
inEq {A} a l = inj1 refl

inCons : ∀{A : Set}(a b : A)(l : List A) → InList b l -> InList b (a ∷ l)
inCons {A} a b l inPF = inj2 inPF

inNil : ∀{A : Set}{a : A} → InList a [] → False
inNil {A}{a} inPF = inPF

inSplit : ∀{A : Set}{x : A}(l : List A) → InList x l -> ∃ λ l1 → ∃ λ l2 → l ≡ l1 ++ x ∷ l2
inSplit {A}{x} [] inPF = ⊥-elim inPF
inSplit {A}{x} (a ∷ L) (inj₁ eq) = [] , (L , (subst {A = A} (λ a → a ∷ L ≡ x ∷ L) {x}{a} eq refl))
inSplit {A}{x} (a ∷ L) (inj₂ inPF) = (a ∷ proj1 (inSplit L inPF)) , (proj1 (proj2 (inSplit L inPF)) , 
                                     subst {A = List A} (λ L' → a ∷ L ≡ a ∷ L') (proj2 (proj2 (inSplit L inPF))) refl)

inApp : ∀{A : Set}{L1 L2 : List A}{a : A} → InList a (L1 ++ L2) → (InList a L1) ⊎ (InList a L2)
inApp {A}{[]}{L2}{a} inPF = inj2 inPF
inApp {A}{a' ∷ L1}{L2}{a} (inj₁ eqPF) = inj1 (inj1 eqPF)
inApp {A}{a' ∷ L1}{L2}{a} (inj₂ inPF) with inApp {A} {L1}{L2}{a} inPF 
inApp {A}{a' ∷ L1}{L2}{a} (inj₂ inPF) | inj₁ P = inj1 (inj2 P)
inApp {A}{a' ∷ L1}{L2}{a} (inj₂ inPF) | inj₂ P = inj2 P

inApp2 : ∀{A : Set}{L1 L2 : List A}{a : A} → (InList a L1) ⊎ (InList a L2) → InList a (L1 ++ L2)
inApp2 {A}{[]}{L2}{a} (inj₁ inPF) = ⊥-elim inPF
inApp2 {A}{[]}{L2}{a} (inj₂ inPF) = inPF
inApp2 {A}{a' ∷ L1}{L2}{a} (inj₁ inPF) with inPF 
... | inj₁ P = inj1 P
... | inj₂ P = inj2 (inApp2 {A}{L1}{L2}{a} (inj1 P))
inApp2 {A}{a' ∷ L1}{L2}{a} (inj₂ inPF) = inj2 (inApp2 {A}{L1}{L2}{a} (inj2 inPF))

inLinSU : ∀{A : Set}{L1 L2 : List A}{n n2 : A} 
  → InList n (L1 ++ L2) 
  → InList n L1 ⊎ n ≡ n2 ⊎ InList n L2
inLinSU {A}{L1}{L2}{n}{n2} inPF with inApp {A}{L1} inPF
... | inj₁ P = inj1 P
... | inj₂ P = inj2 (inj2 P)

-- Facts about compare.
compareEqEq : ∀ n → compare n n ≡ equal n
compareEqEq 0 = refl
compareEqEq (suc n) rewrite compareEqEq n = refl

compareGrEq : ∀ m1 m2 → compare (suc (m1 + m2)) m1 ≡ greater m1 m2
compareGrEq 0 m1 = refl
compareGrEq (suc n) m1 rewrite compareGrEq n m1 = refl

compareLeEq : ∀ m1 m2 → compare m1 (suc (m1 + m2)) ≡ less m1 m2
compareLeEq 0 m2 = refl
compareLeEq (suc n) m2 rewrite compareLeEq n m2 = refl

-- Facts about nats.
is0 : ℕ → Set
is0 0 = True
is0 _ = False

isSuc : ℕ → Set
isSuc 0 = False
isSuc _ = True

sucInj : ∀ a b → suc a ≡ suc b → a ≡ b
sucInj a b = cong pred

sucPlusNEq : ∀ n1 n2 → n1 ≡ suc (n1 + n2) → False
sucPlusNEq 0 0 eqPF = subst (λ x → is0 x) {0}{1} eqPF tt 
sucPlusNEq (suc n1) 0 eqPF = sucPlusNEq n1 0 (cong pred eqPF)
sucPlusNEq 0 (suc n1) eqPF = sucPlusNEq _ _ (cong pred eqPF)
sucPlusNEq (suc n1) (suc n2) eqPF = sucPlusNEq n1 (suc n2) (cong pred eqPF)

sucPlusNEq' : ∀ n1 n2 → suc (n1 + n2) ≡ n1 → False
sucPlusNEq' 0 0 eqPF = subst (λ x → isSuc x) {1}{0} eqPF tt  
sucPlusNEq' (suc n1) 0 eqPF = sucPlusNEq' n1 0 (cong pred eqPF)
sucPlusNEq' 0 (suc n1) eqPF = sucPlusNEq' _ _ (cong pred eqPF)
sucPlusNEq' (suc n1) (suc n2) eqPF = sucPlusNEq' n1 (suc n2) (cong pred eqPF)

-- Some convenient substitution and congruence functions.
subst2 : ∀{A B : Set}(P : A → B → Set){a a' : A}{b b' : B}
  → a ≡ a' 
  → b ≡ b'
  → P a b
  → P a' b'
subst2 {A}{B} P {a}{a'}{b}{b'} aEq bEq PPf = 
       subst (λ x₁ → P x₁ b') aEq (subst (λ x → P a x) bEq PPf)

subst3 : ∀{A B C : Set}(P : A → B → C → Set){a a' : A}{b b' : B}{c c' : C} 
  → a ≡ a' 
  → b ≡ b'
  → c ≡ c'
  → P a b c
  → P a' b' c'
subst3 {A}{B}{C} P {a}{a'}{b}{b'}{c}{c'} aEq bEq cEq PPf = 
       subst (λ x₁ → P x₁ b' c') aEq (subst (λ x → P a x c') bEq (subst (λ x → P a b x) cEq PPf))
