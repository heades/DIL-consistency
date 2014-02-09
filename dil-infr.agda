module dil-infr where

open import utl
open import dil-syntax
open import dil-graph

open import Data.List
open import Data.Product
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

ctxEl = polarity × form × Node
Context = List ctxEl

Γ∣_∣ : Context → List Node
Γ∣ Γ ∣ = Data.List.map proj3 Γ

-- In case we need any monoid laws in the proofs.
open import Algebra
ctxMonoid = monoid (polarity × form × Node)
open Monoid

data inferCF (G : Graph) (Γ : Context) (p : polarity) : Node → form → Set where
  ifrAx : ∀ {A : form}{n n' : Node} → G ⊢ n reaches n' heading p → (p , A , n) ∈ Γ  → inferCF G Γ p n' A
  ifrUnit : ∀ {n : Node} → inferCF G Γ p n ⟨ p ⟩
  ifrAnd : ∀ {n : Node}{A B : form} → inferCF G Γ p n A → inferCF G Γ p n B → inferCF G Γ p n (And p A B)
  ifrAndBarL : ∀ {n : Node}{A B : form} → inferCF G ((bar p , B , n) ∷ Γ) p n A → inferCF G Γ p n (And (bar p) A B)
  ifrAndBarR : ∀ {n : Node}{A B : form} → inferCF G ((bar p , A , n) ∷ Γ) p n B → inferCF G Γ p n (And (bar p) A B)  
  ifrImp : ∀{n n' : Node}{A B : form} → n' ∉ ∣ G ∣
                                      → n' ∉ Γ∣ Γ ∣
                                      → inferCF ((n , p , n') ∷ G) ((p , A , n') ∷ Γ) p n' B 
                                      → inferCF G Γ p n (Implies p A B)
  ifrImpBar : ∀{n n' : Node}{A B : form} → G ⊢ n reaches n' heading (bar p)
                                         → inferCF G Γ (bar p) n' A 
                                         → inferCF G Γ p n' B
                                         → inferCF G Γ p n (Implies (bar p) A B)
  ifrAxCut : ∀{n n' : Node}{A B : form} → (p , B , n') ∈ Γ 
                                        → inferCF G ((bar p , A , n) ∷ Γ) (bar p) n' B
                                        → inferCF G Γ p n A
  ifrAxCutBar : ∀{n n' : Node}{A B : form} → (bar p , B , n') ∈ Γ 
                                           → inferCF G ((bar p , A , n) ∷ Γ)  p n' B
                                           → inferCF G Γ p n A

data infer (G : Graph) (Γ : Context) (p : polarity) : Node → form → Set where
  ifrBase : ∀{n : Node}{A : form} → inferCF G Γ p n A → infer G Γ p n A
  
  ifrCut : ∀{n n' : Node}{A B : form} → infer G ((bar p , A , n) ∷ Γ) p+ n' B
                                      → infer G ((bar p , A , n) ∷ Γ) p- n' B
                                      → infer G Γ p n A
