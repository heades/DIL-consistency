module dil-semantics where

open import utl
open import dil-syntax
open import dil-graph
open import dil-infr

open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.List
import Data.Empty
import Data.Unit
import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

record model  : Set1 where
  field W     : Set                    
        R     : W -> W -> Set 
        V     : W → ℕ → Set
        mmono  : ∀ { w w' i } → R w w' → V w i → V w' i
        mrefl  : ∀ { w } → R w w
        mtrans : ∀ { w1 w2 w3 } → R w1 w2 → R w2 w3 → R w1 w3

open model

_⟦_⟧_ : ∀ ( k : model ) → form → W k → Set
k ⟦ ⟨ p+ ⟩ ⟧ w = True
k ⟦ ⟨ p- ⟩ ⟧ w = False
k ⟦ $ i ⟧ w = V k w i  
k ⟦ (And p+) f1 f2 ⟧ w = k ⟦ f1 ⟧ w × k ⟦ f2 ⟧ w
k ⟦ (And p-) f1 f2 ⟧ w = k ⟦ f1 ⟧ w ⊎ k ⟦ f2 ⟧ w
k ⟦ (Implies p+) f1 f2 ⟧ w = ∀ w' → R k w w' → k ⟦ f1 ⟧ w' → k ⟦ f2 ⟧ w'
k ⟦ (Implies p-) f1 f2 ⟧ w = ∃ (λ w' → R k w' w × ( (k ⟦ f1 ⟧ w') → False) × k ⟦ f2 ⟧ w')

interp_mono : ∀ {k : model}{w w' : W k} → R k w w' → ∀ (f : form) → k ⟦ f ⟧ w → k ⟦ f ⟧ w'
interp_mono {k} {w} {w'} r ⟨ p+ ⟩ p = Data.Unit.tt
interp_mono {k} {w} {w'} r ⟨ p- ⟩ p = p
interp_mono {k} {w} {w'} r ($ i) p = mmono k r p
interp_mono {k} {w} {w'} r (And p+ f1 f2) (p1 , p2) = (interp_mono {k} {w} {w'} r f1 p1) ,′ (interp_mono {k} {w} {w'} r f2 p2)
interp_mono {k} {w} {w'} r (And p- f1 f2) (inj₁ p1) = inj₁ (interp_mono {k} {w} {w'} r f1 p1)
interp_mono {k} {w} {w'} r (And p- f1 f2) (inj₂ p1) = inj₂ (interp_mono {k} {w} {w'} r f2 p1)
interp_mono {k} {w} {w'} r (Implies p+ f1 f2) p = λ w'' r' p' → {!p w'' (mtrans k r r') p'!}
interp_mono {k} {w} {w'} r (Implies p- f1 f2) ( w'' , ( r' , p1 , p2 ) ) = record { proj₁ = w'' ; proj₂ = ( mtrans k r' r , p1 , p2 ) }

-- This is needed to prove consistency of Cut.
postulate lem : ∀ { k f w } → Relation.Nullary.Dec (k ⟦ f ⟧ w)

E→P : ∀(k : model)(N→W : Node → W k) → (Node × polarity × Node) → Set
E→P k N→W (n , p+ , n') = R k (N→W n) (N→W n')
E→P k N→W (n , p- , n') = R k (N→W n') (N→W n)

G⟦_⟧_,_ : (G : Graph)(k : model)(N→W : Node → W k) → Set
G⟦ [] ⟧ k , N→W = True 
G⟦ n ∷ G ⟧ k , N→W = (E→P k N→W n) × G⟦ G ⟧ k , N→W 

expand⟦G⟧ : ∀{k : model}{N→W : Node → W k}{G G1 G2 : Graph}{e : Node × polarity × Node} → G⟦ G ⟧ k , N→W  → e ∈ G → G ≡ G1 ++ (e ∷ G2) → G⟦ G1 ++ (e ∷ G2) ⟧ k , N→W 
expand⟦G⟧ {k}{N→W}{G} Gpf inPF eqPf = subst (λ G' → G⟦ G' ⟧ k , N→W) eqPf Gpf

split⟦G⟧ : ∀{k : model}{N→W : Node → W k}{G1 G2 : Graph} → G⟦ G1 ++ G2 ⟧ k , N→W  → G⟦ G1 ⟧ k , N→W  × G⟦ G2 ⟧ k , N→W 
split⟦G⟧ {k}{N→W}{[]}{G2} GPF = Data.Unit.tt , GPF
split⟦G⟧ {k}{N→W}{(n1 , p+ , n2) ∷ G1}{G2} GPF = (((proj1 GPF , proj1 (split⟦G⟧ {k}{N→W}{G1}{G2} (proj2 GPF)))) , proj2 (split⟦G⟧ {k}{N→W}{G1}{G2} (proj2 GPF)))
split⟦G⟧ {k}{N→W}{(n1 , p- , n2) ∷ G1}{G2} GPF = ((proj1 GPF , proj1 (split⟦G⟧ {k}{N→W}{G1}{G2} (proj2 GPF))) , proj2 (split⟦G⟧ {k}{N→W}{G1}{G2} (proj2 GPF)))

R-prop : ∀(k : model)(w1 w2 : W k)(p : polarity) → Set
R-prop k w1 w2 p+ = R k w1 w2
R-prop k w1 w2 p- = R k w2 w1
R→R : ∀{k : model}{N→W : Node → W k}{G : Graph}{n1 n2 : Node}{p : polarity} → G⟦ G ⟧ k , N→W → G ⊢ (n1 , p , n2) → R-prop k (N→W n1) (N→W n2) p
R→R {k}{N→W}{p = p+} _ RelRefl = mrefl k
R→R {k}{N→W}{p = p-} _ RelRefl = mrefl k
R→R {k}{N→W}{G}{n1}{n2}{p+} GPF (RelAx inPF) = proj1 (proj2 (split⟦G⟧ {k}{N→W}{proj1 (inSplit G inPF)}{(n1 , p+ , n2) ∷ proj1 (proj2 (inSplit G inPF))} (expand⟦G⟧ {k}{N→W}{G}{proj1 (inSplit G inPF)}{proj1 (proj2 (inSplit G inPF))}{(n1 , p+ , n2)} GPF inPF (proj2 (proj2 (inSplit G inPF))))))
R→R {k}{N→W}{G}{n1}{n2}{p-} GPF (RelAx inPF) = proj1 (proj2 (split⟦G⟧ {k}{N→W}{proj1 (inSplit G inPF)}{(n1 , p- , n2) ∷ proj1 (proj2 (inSplit G inPF))} (expand⟦G⟧ {k}{N→W}{G}{proj1 (inSplit G inPF)}{proj1 (proj2 (inSplit G inPF))}{(n1 , p- , n2)} GPF inPF (proj2 (proj2 (inSplit G inPF))))))
R→R {k}{N→W}{G}{n1}{n2}{p+} GPF (RelTrans H1 H2) = mtrans k (R→R GPF H1) (R→R GPF H2)
R→R {k}{N→W}{G}{n1}{n2}{p-} GPF (RelTrans H1 H2) = mtrans k (R→R GPF H2) (R→R GPF H1)
R→R {k}{N→W}{G}{n1}{n2}{p+} GPF (RelFlip H) = R→R GPF H
R→R {k}{N→W}{G}{n1}{n2}{p-} GPF (RelFlip H) = R→R GPF H

Γ⟦_⟧_,_ : (Γ : Context)(k : model)(N→W : Node → W k) → Set
Γ⟦ [] ⟧ k , N→W = True
Γ⟦ (p+ , A , n) ∷ Γ ⟧ k , N→W = k ⟦ A ⟧ (N→W n) × Γ⟦ Γ ⟧ k , N→W
Γ⟦ (p- , A , n) ∷ Γ ⟧ k , N→W = (k ⟦ A ⟧ (N→W n) → False) × Γ⟦ Γ ⟧ k , N→W

expand⟦Γ⟧ : ∀{Γ Γ1 Γ2 : Context}{k : model}{N→W : Node → W k}{e : polarity × form × Node} → Γ⟦ Γ ⟧ k , N→W → e ∈ Γ → Γ ≡ Γ1 ++ (e ∷ Γ2) → Γ⟦ Γ1 ++ (e ∷ Γ2) ⟧ k , N→W 
expand⟦Γ⟧ {Γ}{k = k}{N→W} Γpf inPF eqPf = subst (λ Γ' → Γ⟦ Γ' ⟧ k , N→W) eqPf Γpf

split⟦Γ⟧ : ∀{k : model}{N→W : Node → W k}{Γ1 Γ2 : Context} → Γ⟦ Γ1 ++ Γ2 ⟧ k , N→W → Γ⟦ Γ1 ⟧ k , N→W  × Γ⟦ Γ2 ⟧ k , N→W 
split⟦Γ⟧ {k}{N→W}{[]}{Γ2} ΓPF = (Data.Unit.tt , ΓPF)
split⟦Γ⟧ {k}{N→W}{(p+ , A , n) ∷ Γ1}{Γ2} ΓPF = (((proj1 ΓPF , proj1 (split⟦Γ⟧ {k}{N→W}{Γ1}{Γ2} (proj2 ΓPF)))) , proj2 (split⟦Γ⟧ {k}{N→W}{Γ1}{Γ2} (proj2 ΓPF)))
split⟦Γ⟧ {k}{N→W}{(p- , A , n) ∷ Γ1}{Γ2} ΓPF = ((proj1 ΓPF , proj1 (split⟦Γ⟧ {k}{N→W}{Γ1}{Γ2} (proj2 ΓPF))) , proj2 (split⟦Γ⟧ {k}{N→W}{Γ1}{Γ2} (proj2 ΓPF)))

