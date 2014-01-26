module dil-syntax where

open import Data.Nat

data polarity : Set where
  p+ : polarity
  p- : polarity

bar : polarity → polarity
bar p+ = p-
bar p- = p+

data form : Set where 
  ⟨_⟩ : polarity → form
  Implies : polarity → form -> form -> form
  And : polarity → form -> form -> form  
  $_ : ℕ → form
  -- At first lets just prove completeness without fixed points.
  -- μ : ℕ → form → form

infixr 5 _⇒+_
infixr 5 _⇒-_
infixr 6 _∧_
infixr 6 _∨_

_⇒+_ : form → form → form
f1 ⇒+ f2 = (Implies p+) f1 f2

_⇒-_ : form → form → form
f1 ⇒- f2 = (Implies p-) f1 f2

_∧_ : form → form → form
f1 ∧ f2 = (And p+) f1 f2

_∨_ : form → form → form
f1 ∨ f2 = (And p-) f1 f2

⊤ : form
⊤ = ⟨ p+ ⟩

⊥ : form
⊥ = ⟨ p- ⟩ 

¬ : form → form
¬ f = f ⇒+ ⊥

∼ : form → form
∼ f = f ⇒- ⊤

Non : form → form
Non f = f ⇒- ⊤

Not : form → form
Not f = f ⇒+ ⊥


