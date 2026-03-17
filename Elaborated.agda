{-# OPTIONS --type-in-type --with-K #-}

-- I hope this file can tell the difference between Russell's and Girard/Hurkens/Reynolds' paradox
-- If the construction of a paradox can be fit into `NaiveSetTheory`, we can call it Russell's
-- If can be fit into `NonnaiveSetTheory` (or `RefinedNonnaive`), it should be Girard/Hurkens/Reynolds'.

open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Empty

P : Set → Set 
P A = A → Set 

record NaiveSetTheory 
    (V : Set)
    (intro : P V → V)
    (match : V → P V) : Set where 

  _∈_ : V → V → Set 
  x ∈ y = match y x

  field 
    prop  : (u : P V) (v : V) → v ∈ (intro u) → u v
    prop' : (u : P V) (v : V) → u v           → v ∈ (intro u)
    -- or (V-β : (u : P V) (v : V) → match (intro u) v ≡ u v) 
  
  R : V 
  R = intro λ x → ¬ x ∈ x  

  R-prop : (x : V) → x ∈ R → ¬ x ∈ x 
  R-prop = λ x p → prop (λ x → ¬ x ∈ x) x p

  R∉R : ¬ R ∈ R 
  R∉R R∈R = R-prop R R∈R R∈R 

  R∈R : R ∈ R 
  R∈R = prop' (λ x → ¬ (x ∈ x)) R R∉R

  bot : ⊥ 
  bot = R∉R R∈R

transp : {A B : Set} → A ≡ B → A → B 
transp refl x = x

transp-eq : {A : Set} (x : A) (eq : A ≡ A) → transp eq x ≡ x 
transp-eq x refl = refl

module SetTheorySigma where 

  V : Set 
  V = Σ[ A ∈ Set ] (A → Set)

  intro : (V → Set) → V
  intro = V ,_ 

  _∈_ : (a : V) (s : V) → Set
  _∈_ a s = Σ[ eq ∈ V ≡ proj₁ s ] proj₂ s (transp eq a)

  Paradox : NaiveSetTheory V intro (flip _∈_)
  Paradox = record 
          { prop  = λ { u v (eq , h) → subst (proj₂ (intro u)) (transp-eq v eq) h } 
          ; prop' = λ u v p → refl , p }

-- Ref: Naïm Camille Favier. [https://gist.github.com/ncfavier/79f4fbcfee068d8a59af0e0332ac963d]
module SetTheoryPi where 
  
  V : Set
  V = (A : Set) → A → Set

  intro : (V → Set) → V
  intro p A x = (eq : A ≡ V) → p (transp eq x)

  _∈_ : V → V → Set
  a ∈ s = s V a

  Paradox : NaiveSetTheory V intro (flip _∈_)
  Paradox = record 
          { prop  = λ u v x → x refl 
          ; prop' = λ u v x eq → subst u (sym (transp-eq v eq)) x }

module SetTheoryTree where 

  data V : Set where
    set : (A : Set) → (A → V) → V

  intro : P V → V 
  intro p = set (Σ[ x ∈ V ] p x) proj₁

  _∈_ : V → V → Set 
  x ∈ set A f = Σ[ i ∈ A ] f i ≡ x 

  Paradox : NaiveSetTheory V intro (flip _∈_) 
  Paradox = record 
          { prop  = λ { u v ((s , x) , eq) → J (λ v _ → u v) eq x }  
          ; prop' = λ u v p → (v , p) , refl }

module SetTheoryDataType where 
  
  {-# NO_POSITIVITY_CHECK #-}
  data V : Set where 
    intro : (V → Set) → V
  
  match : V → V → Set 
  match (intro p) x = p x 

  Paradox : NaiveSetTheory V intro match
  Paradox = record 
          { prop  = λ u v z → z    
          ; prop' = λ u v z → z } 

----------------------------------------------------------------------------------------------
-- Using T V instead of P V
-- Ref: Thierry Coquand. A variation of Reynolds-Hurkens Paradox [https://arxiv.org/pdf/2308.16726]
----------------------------------------------------------------------------------------------------

T : Set → Set 
T A = P (P A)

Tmap : {A B : Set} → (A → B) → (T A → T B)
Tmap f ta p = ta (λ x → p (f x))

Tmap-law : {A B C : Set} (f : A → B) (g : B → C) → Tmap (g ∘ f) ≡ Tmap g ∘ Tmap f 
Tmap-law f g = refl

record NonnaiveSetTheory 
    (V : Set) 
    (intro : T V → V) 
    (match : V → T V) : Set where 
  -- match : (set : V) (element : V → Set) → Set
  field
    prop  : (u : T V) (v : P V) → match (intro u) v → u v
    prop' : (u : T V) (v : P V) → u v               → match (intro u) v

  -- in naive set theory, we construct V by [ x ∈ V ∣ p x ]
  -- in here, we [ p : P V ∣ p' p ] where p' : P (P V)

  C : P V → V → Set
  C p x = p x → ¬ match x p -- x in p and p in x is impossible, or say, x and p are not mutual included.

  p₀ : P V
  p₀ x = (p : P V) → C p x -- p₀ = { x | all p are not mutual included with x }

  X₀ : T V
  X₀ p = (x : V) → C p x -- in set theory, this is exactly as same as p₀

  x₀ : V
  x₀ = intro λ p → ∀ (x : V) → C p x -- x₀ = intro X₀ 
    
  l₁ : (x : V) → C p₀ x -- Forall x, p₀ are not mutual with x
  l₁ x h = h p₀ h       -- Proof.
                        --  assume x ∈ p₀ and p₀ ∈ x  [p₀ x and match x p₀]
                        --  we have that x is not mutual with any p by the property of p₀.
                        --  let p be p₀, we have x ∈ p₀ ∧ p­₀ ∈ x → ⊥
                        --  contradiction is easy to see.
                        -- Qed. 

  l₂ : p₀ x₀            -- In set theory, l₂ is exactly as same as l₁
  l₂ p h h₁ = prop X₀ p h₁ x₀ h h₁ 

  bot : ⊥               -- p₀ is in p₀, because l₁ shows that p₀ are not mutual with anyone, which matches p₀'s property.
                        -- hence we can get a paradox.
  bot = l₂ p₀ l₂ (prop' X₀ p₀ l₁) 

module DataType where
  
  {-# NO_POSITIVITY_CHECK #-}
  data V : Set where 
    intro : T V → V 
  
  match : V → T V
  match (intro p) q = p q

  Paradox : NonnaiveSetTheory V intro match 
  Paradox = record 
          { prop  = λ u v z → z   
          ; prop' = λ u v z → z } 

-- Follow Coquand 1.2
record RefinedNonnaive
    (V : Set) 
    (intro : T V → V) 
    (match : V → T V) : Set where 
  
  δ : V → V 
  δ = intro ∘ match

  field 
    match-intro : match ∘ intro ≡ Tmap δ
    -- It would be good if this is judgemental
  
  -- blabla

module Reynolds where
  V : Set 
  V = (X : Set) → (T X → X) → X 

  ι : (X : Set) → (T X → X) → (V → X)
  ι X f a = a X f 

  intro : T V → V 
  intro u X f = f (Tmap (ι X f) u)

  match : V → T V
  match = ι _ (Tmap intro)

  δ = intro ∘ match

  match-intro : match ∘ intro ≡ Tmap δ
  match-intro = refl

  p₀ : P V 
  p₀ x = (p : P V) → p (δ x) → ¬ (match x p)

  X₀ : T V 
  X₀ p = (x : V) → p x → ¬ (match x p)

  x₀ : V 
  x₀ = intro X₀

  s₁ : (x : V) → p₀ x → p₀ (δ x)
  s₁ x h p = h (p ∘ δ)

  s₂ : (p : P V) → X₀ p → X₀ (p ∘ δ)
  s₂ p h x = h (δ x)

  l₀ : (p : P V) → p x₀ → ¬ X₀ p 
  l₀ p h h₀ = h₀ x₀ h (s₂ p h₀)

  l₁ : X₀ p₀
  l₁ x h = h p₀ (s₁ x h)

  l₂ : p₀ x₀ 
  l₂ p = l₀ (p ∘ δ)
  
module Hurkens where  

  V : Set
  V = (X : Set) → (T X → X) → T X 

  ι : {X : Set} → (T X → X) → V → X 
  ι {X} f b = f (b X f)

  intro : T V → V 
  intro v X f = Tmap (ι f) v

  match : V → T V 
  match b v = b V intro v
  
  δ = intro ∘ match

  match-intro : match ∘ intro ≡ Tmap δ
  match-intro = refl

  p₀ : P V 
  p₀ x = (p : P V) → p (δ x) → ¬ (match x p)

  X₀ : T V 
  X₀ p = (x : V) → p x → ¬ (match x p)

  x₀ : V 
  x₀ = intro X₀

  s₁ : (x : V) → p₀ x → p₀ (δ x)
  s₁ x h p = h (p ∘ δ)

  s₂ : (p : P V) → X₀ p → X₀ (p ∘ δ)
  s₂ p h x = h (δ x)

  l₀ : (p : P V) → p x₀ → ¬ X₀ p 
  l₀ p h h₀ = h₀ x₀ h (s₂ p h₀)

  l₁ : X₀ p₀
  l₁ x h = h p₀ (s₁ x h)

  l₂ : p₀ x₀ 
  l₂ p = l₀ (p ∘ δ)
  
