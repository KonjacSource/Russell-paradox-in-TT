{-# OPTIONS --type-in-type #-}

open import Data.Product 
open import Relation.Binary.PropositionalEquality  
open import Relation.Nullary
open import Data.Empty
open import Data.Unit

V : Set
V = Σ[ A ∈ Set ] (A → Set)

transp : {A B : Set} → A ≡ B → A → B 
transp refl x = x

trasnp-eq : {A : Set} (x : A) (eq : A ≡ A) → transp eq x ≡ x 
trasnp-eq x refl = refl

set-syntax : (V → Set) → V
set-syntax = V ,_ 

syntax set-syntax (λ x → N) = [ x ∣ N ]

_∈_ : {A : Set} (a : A) (s : V) → Set 
_∈_ {A} a s = Σ[ eq ∈ A ≡ proj₁ s ] proj₂ s (transp eq a)

module FixPoint {A : Set} (g : A → A) where 

  R : V 
  R = [ x ∣ ((x ∈ x) → A) ]

  R∉R : R ∈ R → A 
  R∉R R∈R = g (proj₂ R∈R (subst (λ x → x ∈ x) (sym (trasnp-eq R (proj₁ R∈R))) R∈R))

  R∉R' : R ∈ R → A
  R∉R' (h , p) = p (subst (λ x → x ∈ x) (sym (trasnp-eq R h)) (h , p)) 

  R∈R : R ∈ R
  R∈R = refl , R∉R

  fixpoint : A
  fixpoint = R∉R R∈R

  -- This will stuck the type checker
  -- fixpoint-eq : fixpoint ≡ g fixpoint
  -- fixpoint-eq = refl 
