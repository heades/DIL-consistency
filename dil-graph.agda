module dil-graph where

open import utl
open import dil-syntax
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.List
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

Node = ℕ

-- Finally, a graph consists of list of edges.
Graph = List (Node × polarity × Node)

-- The nodes of a graph.

∣_∣ : Graph → List Node
∣ G ∣ = (Data.List.map proj1 G)++(Data.List.map proj3 G)

node∉DomNeq : ∀ n' G → n' ∉ ∣ G ∣ → ∀ n → n ∈ ∣ G ∣ → (n ≡ n' → False)
node∉DomNeq n' G n'∉G n n∈G eqpf rewrite eqpf = n'∉G n∈G

-- Reachability.
_reaches_heading_ : Node → Node → polarity → Node × polarity × Node
n1 reaches n2 heading p = (n1 , p , n2)

infix 5 _⊢_
data _⊢_ (G : Graph) : Node × polarity × Node → Set where
   RelRefl : ∀{ n : Node}{p : polarity} → G ⊢ n reaches n heading p
   RelAx : ∀{n n' : Node}{p : polarity} → (n , p , n') ∈ G → G ⊢ n reaches n' heading p
   RelTrans : ∀{n1 n2 n3 : Node}{p : polarity} → 
                   G ⊢ n1 reaches n2 heading p →
                   G ⊢ n2 reaches n3 heading p →
                   G ⊢ n1 reaches n3 heading p
   RelFlip : ∀{n1 n2 n3 : Node}{p : polarity} → 
                   G ⊢ n1 reaches n2 heading (bar p) →
                   G ⊢ n2 reaches n1 heading p


