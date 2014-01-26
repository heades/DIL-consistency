module dil-soundness where

open import Data.List
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Data.Bool
open import Relation.Nullary.Core
open import Relation.Binary.PropositionalEquality
open import Algebra.FunctionProperties
open import Function

open import utl
open import dil-syntax
open import dil-graph
open import dil-infr
open import dil-semantics

open ≡-Reasoning
open model

definedOn : {k : model}(N→W : Node → W k)(G : Graph) → Set
definedOn {k} N→W G = ∀ n → n ∈ ∣ G ∣ → (∃ λ w → (N→W n ≡ w))

extendN→W : ∀{k : model}(N→W : Node → W k)(n : Node)(w : W k)→ (Node → W k)
extendN→W {k} N→W n w n' with compare n n'
extendN→W {k} N→W .m w .m | equal m  = w
extendN→W {k} N→W n w n' | _  = N→W n'

extendDF : {k : model}(N→W : Node → W k)(G : Graph)(n n' : Node)(w : W k) 
  → definedOn {k} N→W G 
  → definedOn {k} (extendN→W {k} N→W n' w) ((n , p+ , n') ∷ G)
extendDF {k} N→W G n n' w DFPF n'' ∃PF with compare n' n''
extendDF {k} N→W G n .m w DFPF .m ∃PF | equal m rewrite compareEqEq m = w , refl
extendDF {k} N→W G n .m1 w DFPF .(suc (m1 + m2)) ∃PF | less m1 m2 = N→W (suc (m1 + m2)) , refl
extendDF {k} N→W G n .(suc (m1 + m2)) w DFPF .m1 ∃PF | greater m1 m2 = (N→W m1) , refl

extNEqN→W : {k : model}{N→W : Node → W k}{w : W k} 
  → ∀ n n' 
  → (n ≡ n' → False) 
  → extendN→W {k} N→W n' w n ≡ N→W n
extNEqN→W {k}{N→W} n n' ⊥PF with compare n n'
extNEqN→W {k}{N→W} .m .m ⊥PF | equal m =  ⊥-elim (⊥PF refl)
extNEqN→W {k}{N→W} .m1 .(suc (m1 + m2)) ⊥PF | less m1 m2 rewrite compareGrEq m1 m2 = refl
extNEqN→W {k}{N→W} .(suc (m1 + m2)) .m1 ⊥PF | greater m1 m2 rewrite compareLeEq m1 m2 = refl

extEq : {k : model}{N→W : Node → W k}{w : W k} 
  → ∀ n → extendN→W {k} N→W n w n ≡ w
extEq {k}{N→W}{w} n rewrite (compareEqEq n) = refl 

definedOnDown : ∀{k : model}{G : Graph}{N→W : Node → W k}{e : Node × polarity × Node}
  → definedOn {k} N→W (e ∷ G) 
  → definedOn {k} N→W G
definedOnDown {k}{G}{N→W}{(n1 , p , n2)} DFPF n WPF = (N→W n) , refl

extendINTGr : {k : model}(G : Graph)(N→W : Node → W k)(n : Node)(w' : W k) 
  → definedOn {k} N→W G 
  → n ∉ ∣ G ∣ → G⟦ G ⟧ k , N→W 
  → G⟦ G ⟧ k , extendN→W {k} N→W n w' 
extendINTGr {k} [] N→W n w' DFPF ∉PF IPF = tt       
extendINTGr {k} ((n1 , p+ , n2) ∷ G) N→W n w' DFPF ∉PF IPF =  
  (subst {A = W k} (λ w → R k w (extendN→W N→W n w' n2)) 
                  (sym (extNEqN→W {k}{N→W}{w'} n1 n (node∉DomNeq n ((n1 , p+ , n2) ∷ G) ∉PF n1 (inj1 refl)))) 
                  (subst {A = W k} 
                         (λ w → R k (N→W n1) w) 
                         (sym (extNEqN→W {k}{N→W}{w'} n2 n 
                           (node∉DomNeq n ((n1 , p+ , n2) ∷ G) ∉PF n2 
                              (inj2 (inApp2 {L1 = Data.List.map proj1 G}
                                            {n2 ∷ Data.List.map (λ a₁ → proj₂ (proj₂ a₁)) G} 
                                            (inj2 (inEq n2 
                                                        (Data.List.map (λ a₁ → proj₂ (proj₂ a₁)) G))))))))
                                   (proj1 IPF) ) , 
   extendINTGr {k} G N→W n w' (definedOnDown {k} {G} {N→W} {n1 , p+ , n2} DFPF) 
                               (λ H1 → ∉PF (inj2 (inApp2 {L1 = Data.List.map proj₁ G} 
                               (inLinSU H1)))) (proj2 IPF))

extendINTGr {k} ((n1 , p- , n2) ∷ G) N→W n w' DFPF ∉PF IPF = 
  subst {A = W k} (λ w → R k w (extendN→W N→W n w' n1)) 
                  (sym (extNEqN→W {k}{N→W}{w'} n2 n 
                    (node∉DomNeq n ((n1 , p- , n2) ∷ G) 
                         ∉PF 
                         n2 
                         (inj2 (inApp2 {L1 = Data.List.map proj₁ G} (inj2 (inj1 refl))))))) 
                  (subst {A = W k} 
                         (λ w → R k (N→W n2) w) 
                         (sym (extNEqN→W {k}{N→W}{w'} n1 n (node∉DomNeq n ((n1 , p- , n2) ∷ G) ∉PF n1 (inj1 refl))))
                         (proj1 IPF) ) , 
  extendINTGr {k} G N→W n w' 
    (definedOnDown {k} {G} {N→W} {n1 , p- , n2} DFPF)
    (λ H1 → ∉PF (inj2 (inApp2 {L1 = Data.List.map proj₁ G} (inLinSU H1))))
    (proj2 IPF)

extendINTΓ : {k : model}(G : Graph)(Γ : Context)(N→W : Node → W k)(n' : Node)(w' : W k) 
  → definedOn {k} N→W G 
  → n' ∉ Γ∣ Γ ∣ → Γ⟦ Γ ⟧ k , N→W 
  → Γ⟦ Γ ⟧ k , extendN→W {k} N→W n' w' 
extendINTΓ {k} G [] N→W n w' DFPF ∉PF IPF = tt
extendINTΓ {k} G ((p+ , A , n) ∷ Γ) N→W n' w' DFPF ∉PF IPF with compare n' n
extendINTΓ {k} G ((p+ , A , .m) ∷ Γ) N→W .m w' DFPF ∉PF IPF | equal m  =  
  ⊥-elim (∉PF (inj1 refl))
extendINTΓ {k} G (( p+ , A , .(suc (m1 + m2))) ∷ Γ) N→W .m1 w' DFPF ∉PF IPF | less m1 m2 = 
  (proj1 IPF , -- The use of IPF here is the reason I had to case split over the polarity.
   extendINTΓ G Γ N→W m1 w' DFPF (λ x → ∉PF (inj2 x)) (proj2 IPF))
extendINTΓ {k} G (( p+ , A , .m1) ∷ Γ) N→W .(suc (m1 + m2)) w' DFPF ∉PF IPF | greater m1 m2 = 
  (proj1 IPF) , (extendINTΓ G Γ N→W (suc (m1 + m2)) w' DFPF (λ x → ∉PF (inj2 x)) (proj2 IPF))

extendINTΓ {k} G ((p- , A , n) ∷ Γ) N→W n' w' DFPF ∉PF IPF with compare n' n
extendINTΓ {k} G (( p- , A , .m) ∷ Γ) N→W .m w' DFPF ∉PF IPF | equal m = 
  ⊥-elim (∉PF (inj1 refl))
extendINTΓ {k} G (( p- , A , .(suc (m1 + m2))) ∷ Γ) N→W .m1 w' DFPF ∉PF IPF | less m1 m2 = 
  (proj1 IPF , -- The use of IPF here is the reason I had to case split over the polarity.
   extendINTΓ G Γ N→W m1 w' DFPF (λ x → ∉PF (inj2 x)) (proj2 IPF))
extendINTΓ {k} G (( p- , A , .m1) ∷ Γ) N→W .(suc (m1 + m2)) w' DFPF ∉PF IPF | greater m1 m2 = 
  (proj1 IPF) , (extendINTΓ G Γ N→W (suc (m1 + m2)) w' DFPF (λ x → ∉PF (inj2 x)) (proj2 IPF))

soundness-prop : (G : Graph)(Γ : Context)(p : polarity)(n : Node)(A : form)(k : model)(N→W : Node → W k) → Set

soundness-prop G Γ p+ n A k N→W = definedOn {k} N→W G → G⟦ G ⟧ k , N→W → Γ⟦ Γ ⟧ k , N→W → k ⟦ A ⟧ (N→W n)

soundness-prop G Γ p- n A k N→W = definedOn {k} N→W G
               → G⟦ G ⟧ k , N→W → Γ⟦ Γ ⟧ k , N→W → (k ⟦ A ⟧ (N→W n) → False)

soundCF : ∀{G : Graph}{Γ : Context}{p : polarity}{n : Node}{A : form} 
              → inferCF G Γ p n A  → ∀(k : model)(N→W : Node → W k) → soundness-prop G Γ p n A k N→W

soundCF {G}{Γ}{p+}{n} (ifrImp {n' = n'}{A}{B} n'InG n'∉Γ H) k N→W with compare n n'    
soundCF {G}{Γ}{p+}{.n} (ifrImp {n' = .n}{A}{B} n'InG n'∉Γ H) k N→W | equal n = 
  λ DFPF GPF ΓPF w' HR AINT → 
    subst {A = W k} 
          (λ w → k ⟦ B ⟧ w) 
          {extendN→W {k} N→W n w' n} {w'} 
          (extEq n)
          (soundCF H k (extendN→W {k} N→W n w') 
                     (λ j x → extendDF {k} N→W G n n w' DFPF j x) 
                     (mrefl k , extendINTGr {k} G N→W n w' DFPF n'InG GPF) 
                     ((subst {A = W k} (λ w → k ⟦ A ⟧ w) {w'} {extendN→W N→W n w' n} (sym (extEq n)) AINT) , 
                      (extendINTΓ {k} G Γ N→W n w' DFPF n'∉Γ ΓPF))) 

soundCF {G}{Γ}{p+}{.m1} (ifrImp {n' = .(suc (m1 + m2))}{A}{B} n'InG n'∉Γ H) k N→W | less m1 m2 = 
  λ DFPF GPF ΓPF w' HR AINT → subst {A = W k} 
                                           (λ w → k ⟦ B ⟧ w)
                                           {extendN→W {k} N→W (suc (m1 + m2)) w' (suc (m1 + m2))} 
                                           {w'} 
                                           (extEq (suc (m1 + m2))) 
                                           (soundCF H k (extendN→W {k} N→W (suc (m1 + m2)) w')
                                             (extendDF {k} N→W G m1 (suc (m1 + m2)) w' DFPF) 
                                             (subst2 {W k} {W k} (λ w1 w2 → R k w1 w2) {N→W m1}
                                                {extendN→W N→W (suc (m1 + m2)) w' m1} {w'}
                                                {extendN→W N→W (suc (m1 + m2)) w' (suc (m1 + m2))} 
                                                (sym (extNEqN→W {k} {N→W} {w'} m1 (suc (m1 + m2)) (sucPlusNEq m1 m2))) 
                                                (sym (extEq (suc (m1 + m2)))) 
                                                HR , 
                                                extendINTGr {k} G N→W (suc (m1 + m2)) w' DFPF n'InG GPF) 
                                             (subst {A = W k} (λ w → k ⟦ A ⟧ w) {w'}
                                                {extendN→W {k} N→W (suc (m1 + m2)) w' (suc (m1 + m2))} 
                                                (sym (extEq (suc (m1 + m2)))) 
                                                AINT , 
                                              extendINTΓ {k} G Γ N→W (suc (m1 + m2)) w' DFPF n'∉Γ ΓPF))

soundCF {G}{Γ}{p+}{.(suc (m1 + m2))} (ifrImp {n' = .m1}{A}{B} n'InG n'∉Γ H) k N→W | greater m1 m2 = 
  λ DFPF GPF ΓPF w' HR AINT → subst {A = W k} 
                                           (λ w → k ⟦ B ⟧ w)
                                           {extendN→W {k} N→W m1 w' m1} 
                                           {w'} 
                                           (extEq m1) 
                                           (soundCF H k (extendN→W {k} N→W m1 w')
                                             (extendDF {k} N→W G (suc (m1 + m2)) m1 w' DFPF)
                                             (subst2 {W k} {W k} (λ w1 w2 → R k w1 w2) {N→W (suc (m1 + m2))}
                                               {extendN→W N→W m1 w' (suc (m1 + m2))} {w'}
                                               {extendN→W N→W m1 w' m1} 
                                               (sym (extNEqN→W {k} {N→W} {w'} (suc (m1 + m2)) m1 (sucPlusNEq' m1 m2)))
                                               (sym (extEq m1)) 
                                               HR , 
                                               extendINTGr {k} G N→W m1 w' DFPF n'InG GPF)
                                             (subst {A = W k} (λ w → k ⟦ A ⟧ w) {w'}
                                               {extendN→W {k} N→W m1 w' m1} 
                                               (sym (extEq m1)) 
                                               AINT , 
                                               extendINTΓ {k} G Γ N→W m1 w' DFPF n'∉Γ ΓPF))

soundCF {G}{Γ}{p-}{n} (ifrImp {n' = n'}{A}{B} n'InG n'∉Γ H) k N→W with compare n n'    
soundCF {G}{Γ}{p-}{.n} (ifrImp {n' = .n}{A}{B} n'InG n'∉Γ H) k N→W | equal n = λ DFPF GPF ΓPF ∃PF → 
  soundCF H k (extendN→W {k} N→W n (proj1 ∃PF)) 
            (extendDF N→W G n n (proj1 ∃PF) DFPF) 
            (mrefl k , extendINTGr G N→W n (proj1 ∃PF) DFPF n'InG GPF) 
            ((λ H' → proj1 (proj2 (proj2 ∃PF)) 
               (subst {A = W k} 
                      (λ w → k ⟦ A ⟧ w) 
                      {extendN→W {k} N→W n (proj1 ∃PF) n}
                      {proj1 ∃PF} (extEq n) H')) , 
            extendINTΓ {k} G Γ N→W n (proj1 ∃PF) DFPF n'∉Γ ΓPF) 
            (subst {A = W k} (λ w → k ⟦ B ⟧ w) {proj1 ∃PF}
               {extendN→W {k} N→W n (proj1 ∃PF) n} (sym (extEq n)) (proj2 (proj2 (proj2 ∃PF)))) 

soundCF {G}{Γ}{p-}{.m1} (ifrImp {n' = .(suc (m1 + m2))}{A}{B} n'InG n'∉Γ H) k N→W | less m1 m2 = 
  λ DFPF GPF ΓPF ∃PF → 
    soundCF H k (extendN→W {k} N→W (suc (m1 + m2)) (proj1 ∃PF))
              (extendDF N→W G m1 (suc (m1 + m2)) (proj1 ∃PF) DFPF) 
              (subst2 
                 (λ w1 w2 → R k w1 w2) 
                 {proj1 ∃PF}
                 {extendN→W N→W (suc (m1 + m2)) (proj₁ ∃PF) (suc (m1 + m2))}
                 {N→W m1} 
                 {extendN→W N→W (suc (m1 + m2)) (proj₁ ∃PF) m1} 
                 (sym (extEq (suc (m1 + m2)))) 
                 (sym (extNEqN→W {k} {N→W} {proj1 ∃PF} m1 (suc (m1 + m2)) (sucPlusNEq m1 m2)))
                 (proj1 (proj2 ∃PF)) , 
               extendINTGr {k} G N→W (suc (m1 + m2)) (proj1 ∃PF) DFPF n'InG GPF)
              ((λ H' → 
                (proj1 (proj2 (proj2 ∃PF))) (subst 
                                                {A = W k} 
                                                (λ w → k ⟦ A ⟧ w) 
                                                {extendN→W {k} N→W (suc (m1 + m2)) 
                                                                    (proj1 ∃PF) 
                                                                    (suc (m1 + m2))}
                                                {proj1 ∃PF}
                                                (extEq (suc (m1 + m2))) 
                                                H')) , 
               (extendINTΓ {k} G Γ N→W (suc (m1 + m2)) (proj1 ∃PF) DFPF n'∉Γ ΓPF))
              (subst {A = W k} 
                     (λ w → k ⟦ B ⟧ w) 
                     {proj1 ∃PF}
                     {extendN→W {k} N→W (suc (m1 + m2)) (proj1 ∃PF) (suc (m1 + m2))}
                     (sym (extEq (suc (m1 + m2)))) 
                     (proj2 (proj2 (proj2 ∃PF))))

soundCF {G}{Γ}{p-}{.(suc (m1 + m2))} (ifrImp {n' = .m1}{A}{B} n'InG n'∉Γ H) k N→W | greater m1 m2 = 
  λ DFPF GPF ΓPF ∃PF →  
    soundCF H k (extendN→W {k} N→W m1 (proj1 ∃PF))
              (extendDF N→W G (suc (m1 + m2)) m1 (proj1 ∃PF) DFPF) 
              (subst2 
                 (λ w1 w2 → R k w1 w2) 
                 {proj1 ∃PF}
                 {extendN→W N→W m1 (proj₁ ∃PF) m1}
                 {N→W (suc (m1 + m2))} 
                 {extendN→W N→W m1 (proj₁ ∃PF) (suc (m1 + m2))} 
                 (sym (extEq m1)) 
                 (sym (extNEqN→W {k} {N→W} {proj1 ∃PF} (suc (m1 + m2)) m1 (sucPlusNEq' m1 m2)))
                 (proj1 (proj2 ∃PF)) , 
               extendINTGr {k} G N→W m1 (proj1 ∃PF) DFPF n'InG GPF)
              ((λ H' → 
                (proj1 (proj2 (proj2 ∃PF))) (subst 
                                                {A = W k} 
                                                (λ w → k ⟦ A ⟧ w) 
                                                {extendN→W {k} N→W m1(proj1 ∃PF) m1}
                                                {proj1 ∃PF}
                                                (extEq m1) 
                                                H')) , 
               (extendINTΓ {k} G Γ N→W m1 (proj1 ∃PF) DFPF n'∉Γ ΓPF))
              (subst {A = W k} 
                     (λ w → k ⟦ B ⟧ w) 
                     {proj1 ∃PF}
                     {extendN→W {k} N→W m1 (proj1 ∃PF) m1}
                     (sym (extEq m1)) 
                     (proj2 (proj2 (proj2 ∃PF))))

soundCF {G}{Γ}{p+}{n} (ifrImpBar {n' = n'}{A}{B} HR Hinfr1 Hinfr2) k N→W = 
   λ DFPF GPF ΓPF → (N→W n') , 
                           (R→R GPF HR) , 
                           (soundCF {G}{Γ}{p-}{n'} Hinfr1 k N→W DFPF GPF ΓPF) , 
                           (soundCF {G}{Γ}{p+}{n'} Hinfr2 k N→W DFPF GPF ΓPF)

soundCF {G}{Γ}{p-}{n} (ifrImpBar {n' = n'}{A}{B} HR Hinfr1 Hinfr2) k N→W = 
   λ DFPF GPF ΓPF H → soundCF {G} {Γ} {p-} {n'} Hinfr2 k 
                                   N→W DFPF GPF ΓPF 
                                   (H (N→W n') 
                                      (R→R GPF HR) 
                                      (soundCF {G}{Γ}{p+}{n'} Hinfr1 k N→W DFPF GPF ΓPF))


soundCF {G}{Γ}{p+}{n}{A} (ifrAx rPF inPF) k N→W = 
   λ DFPF GPF ΓPF → 
     interp R→R GPF rPF mono A ((proj1 (proj2 ((split⟦Γ⟧ {k}{N→W}{proj1 (inSplit Γ inPF)} 
                                                                  (expand⟦Γ⟧ {Γ}
                                                                             {proj1 (inSplit Γ inPF)}
                                                                             {proj1 (proj2 (inSplit Γ inPF))} 
                                                                             ΓPF inPF 
                                                                             (proj2 
                                                                               (proj2 
                                                                                 (inSplit Γ inPF)))))))))

soundCF {G}{Γ}{p-}{n}{A} (ifrAx rPF inPF) k N→W = 
   λ DFPF GPF ΓPF H → 
     (proj1 (proj2 ((split⟦Γ⟧ {k}{N→W}{proj1 (inSplit Γ inPF)} 
                                       (expand⟦Γ⟧ {Γ}{proj1 (inSplit Γ inPF)}
                                                     {proj1 (proj2 (inSplit Γ inPF))} 
                                                     ΓPF inPF 
                                                     (proj2 
                                                       (proj2 
                                                         (inSplit Γ inPF)))))))) 
     (interp_mono (R→R GPF rPF) A H) 

soundCF {G}{Γ}{p+}{n} ifrUnit k N→W = λ DFPF GPF ΓPF → tt
soundCF {G}{Γ}{p-}{n} ifrUnit k N→W = λ DFPF GPF ΓPF H → H

soundCF {G}{Γ}{p+}{n} (ifrAnd H1 H2) k N→W = 
  λ DFPF GPF ΓPF →  (soundCF H1 k N→W DFPF GPF ΓPF , soundCF H2 k N→W DFPF GPF ΓPF) 

soundCF {G}{Γ}{p-}{n} (ifrAnd {A = A}{B = B} H1 H2) k N→W =
  λ DFPF GPF ΓPF H → [ (λ AINT → (soundCF H1 k N→W DFPF GPF ΓPF) AINT) , (λ BINT → (soundCF H2 k N→W DFPF GPF ΓPF) BINT) ]′ H

soundCF {G}{Γ}{p+}{n} (ifrAndBarL {A = A}{B} H) k N→W with (lem {k}{B}{N→W n}) 
... | yes H' = λ DFPF GPF ΓPF →  inj2 H' 
... |  no H' = λ DFPF GPF ΓPF →  inj1 (soundCF H k N→W DFPF GPF (H' , ΓPF))

soundCF {G}{Γ}{p+}{n} (ifrAndBarR {A = A}{B} H) k N→W with (lem {k}{A}{N→W n})
... | yes H' = λ DFPF GPF ΓPF →  inj1 H' 
... |  no H' = λ DFPF GPF ΓPF →  inj2 (soundCF H k N→W DFPF GPF (H' , ΓPF)) 

soundCF {G}{Γ}{p-}{n} (ifrAndBarL H) k N→W = 
  λ DFPF GPF ΓPF H' → (soundCF H k N→W DFPF GPF (proj2 H' , ΓPF)) (proj1 H') 

soundCF {G}{Γ}{p-}{n} (ifrAndBarR H) k N→W = 
  λ DFPF GPF ΓPF → λ H' → (soundCF H k N→W DFPF GPF (proj1 H' , ΓPF)) (proj2 H')  

soundCF {G}{Γ}{p+}{n} (ifrAxCut {n' = n'}{A}{B} inΓ H) k N→W with (lem {k}{A}{N→W n})
... | yes H' = λ DFPF GPF ΓPF → H' 
... | no H'  = λ DFPF GPF ΓPF → 
    ⊥-elim (soundCF H k N→W DFPF GPF (H' , ΓPF) 
             (let split = inSplit Γ inΓ in 
                let Γ1 = proj1 split in 
                     let Γ2 = proj1 (proj2 split) in
                       proj1 (proj2 (split⟦Γ⟧ {k}{N→W}{Γ1}{(p+ , B , n') ∷ Γ2} 
                                       (expand⟦Γ⟧ {Γ} {Γ1}{Γ2}{k}{N→W}{(p+ , B , n')} 
                                                  ΓPF inΓ (proj2 (proj2 split)))))))

soundCF {G}{Γ}{p-}{n} (ifrAxCut {n' = n'}{A}{B} inΓ H) k N→W = λ DFPF GPF ΓPF H' →
  (let split = inSplit Γ inΓ in 
     let Γ1 = proj1 split in 
       let Γ2 = proj1 (proj2 split) in
         proj1 (proj2 (split⟦Γ⟧ {k}{N→W}{Γ1}{(p- , B , n') ∷ Γ2} 
                        (expand⟦Γ⟧ {Γ} {Γ1}{Γ2}{k}{N→W}{(p- , B , n')} 
                          ΓPF inΓ (proj2 (proj2 split)))))) 
  (soundCF H k N→W DFPF GPF (H' , ΓPF))

soundCF {G}{Γ}{p+}{n} (ifrAxCutBar {n' = n'}{A}{B} inΓ H) k N→W with (lem {k}{A}{N→W n})
... | yes H' = λ DFPF GPF ΓPF → H'
... |  no H' = λ DFPF GPF ΓPF →   
  ⊥-elim
    ((let split = inSplit Γ inΓ in 
        let Γ1 = proj1 split in 
          let Γ2 = proj1 (proj2 split) in 
            proj1
               (proj2
                (split⟦Γ⟧ {k} {N→W} {Γ1} {(p- , B , n') ∷ Γ2}
                 (expand⟦Γ⟧ {Γ} {Γ1} {Γ2} {k} {N→W} {p- , B , n'} ΓPF inΓ
                  (proj2 (proj2 split))))))
     (soundCF H k N→W DFPF GPF (H' , ΓPF)))

soundCF {G}{Γ}{p-}{n} (ifrAxCutBar {n' = n'}{A}{B} inΓ H) k N→W = 
  λ DFPF GPF ΓPF H' → 
    (soundCF H k N→W DFPF GPF (H' , ΓPF)) 
      (let split = inSplit Γ inΓ in 
         let Γ1 = proj1 split in 
           let Γ2 = proj1 (proj2 split) in 
             proj1
               (proj2
                (split⟦Γ⟧ {k} {N→W} {Γ1} {(p+ , B , n') ∷ Γ2}
                 (expand⟦Γ⟧ {Γ} {Γ1} {Γ2} {k} {N→W} {p+ , B , n'} ΓPF inΓ
                  (proj2 (proj2 split))))))
      

sound : ∀{G : Graph}{Γ : Context}{p : polarity}{n : Node}{A : form} 
             → infer G Γ p n A  
             → ∀(k : model)(N→W : Node → W k) → soundness-prop G Γ p n A k N→W

sound {G}{Γ}{p}{n} (ifrBase {A = A} H) k N→W = soundCF H k N→W
sound {G}{Γ}{p+}{n} (ifrCut {n' = n'}{A}{B} H1 H2) k N→W with (lem {k}{A}{N→W n})
... | yes H' = λ DFPF GPF ΓPF → H'
... |  no H' = λ DFPF GPF ΓPF → ⊥-elim ((sound H2 k N→W DFPF GPF (H' , ΓPF))
                                         (sound H1 k N→W DFPF GPF (H' , ΓPF)))

sound {G}{Γ}{p-}{n} (ifrCut {n' = n'}{A}{B} H1 H2) k N→W = 
  λ DFPF GPF ΓPF H' → ⊥-elim ((sound H1 k N→W DFPF GPF (H' , ΓPF))
                               (sound H2 k N→W DFPF GPF (H' , ΓPF)))
