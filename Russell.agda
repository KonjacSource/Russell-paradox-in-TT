{-# OPTIONS --type-in-type #-}

open import Data.Product 
open import Relation.Binary.PropositionalEquality  
open import Relation.Nullary 
open import Data.Empty

V : Set 
V = Σ[ A ∈ Set ] (A → Set)

set-syntax : (V → Set) → V
set-syntax = V ,_ 

syntax set-syntax (λ x → N) = [ x ∣ N ]

transp : {A B : Set} → A ≡ B → A → B 
transp refl x = x

trasnp-eq : {A : Set} (x : A) (eq : A ≡ A) → transp eq x ≡ x 
trasnp-eq x refl = refl

_∈_ : {A : Set} (a : A) (s : V) → Set 
_∈_ {A} a s = Σ[ eq ∈ A ≡ proj₁ s ] proj₂ s (transp eq a)

R : V 
R = [ x ∣ ¬ x ∈ x ]

R∉R : ¬ R ∈ R
R∉R R∈R = proj₂ R∈R (subst (λ x → x ∈ x) (sym (trasnp-eq R (proj₁ R∈R))) R∈R) 

R∈R : R ∈ R 
R∈R = refl , R∉R

bot : ⊥ 
bot = R∉R R∈R