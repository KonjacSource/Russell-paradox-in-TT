{-# OPTIONS --type-in-type --with-K #-}

open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Empty
 
transp : {A B : Set} → A ≡ B → A → B
transp refl x = x

transp-eq : {A : Set} (x : A) (eq : A ≡ A) → transp eq x ≡ x
transp-eq x refl = refl

V : Set
V = Σ[ A ∈ Set ] (A → Set)

_∈_ : V → V → Set
_∈_ a s = Σ[ eq ∈ V ≡ proj₁ s ] proj₂ s (transp eq a)

set-syntax : (V → Set) → V
set-syntax = V ,_

syntax set-syntax (λ x → N) = [ x ∣ N ]

R : V
R = [ x ∣ ¬ x ∈ x ]

R∉R : ¬ R ∈ R
R∉R (h , p) = p (subst (λ x → x ∈ x) {! (sym (transp-eq R h))  !} (h , p))

R∈R : R ∈ R
R∈R = refl , R∉R

bot : ⊥
bot = R∉R R∈R
