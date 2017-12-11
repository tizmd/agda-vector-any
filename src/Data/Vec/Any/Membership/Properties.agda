module Data.Vec.Any.Membership.Properties where

open import Relation.Binary
open import Data.Vec

module SingleSetoid {a ℓ} (S : Setoid a ℓ) where
    open Setoid S renaming (Carrier to A)
    open import Data.Vec.Any
    open import Data.Vec.Any.Membership S
    open import Function using (flip)
    open import Data.Vec.Equality using (module Equality)
    open Equality S renaming (_≈_ to _≋_; trans to ≋-trans)  
    ⊆-reflexive : ∀ {n m} {xs : Vec A n} {ys : Vec A m} →
      xs ≋ ys → xs ⊆ ys
    ⊆-reflexive []-cong ()
    ⊆-reflexive (x₁≈x₂ ∷-cong eq) (here x≈x₁) = here (trans x≈x₁ x₁≈x₂)
    ⊆-reflexive (_ ∷-cong eq) (there p) = there (⊆-reflexive eq p)  

    ∈′-resp-≈ : ∀ {x} → (x ≈_) Respects _≈_
    ∈′-resp-≈ = flip trans

    ∈′-resp-≋ : ∀ {n₁ n₂ x}{xs₁ : Vec A n₁}{xs₂ : Vec A n₂} →
      xs₁ ≋ xs₂ → x ∈′ xs₁ → x ∈′ xs₂  
    ∈′-resp-≋ {xs₁ = .[]} {.[]} []-cong ()
    ∈′-resp-≋ {xs₁ = .(_ ∷ _)} {.(_ ∷ _)} (x¹≈x² ∷-cong eq) (here x≈x₁) = here (trans x≈x₁ x¹≈x²)
    ∈′-resp-≋ {xs₁ = .(_ ∷ _)} {.(_ ∷ _)} (x¹≈x² ∷-cong eq) (there p) =
       there (∈′-resp-≋ eq p)

open SingleSetoid public

module DoubleSetoid {a₁ a₂ ℓ₁ ℓ₂}
  (S₁ : Setoid a₁ ℓ₁) (S₂ : Setoid a₂ ℓ₂) where
      open import Data.Vec.Any.Properties
      import Data.Vec.Any as Any
      open import Data.Product hiding (map)
      open Setoid S₁ renaming (Carrier to A₁; _≈_ to _≈₁_; refl to refl₁)
      open Setoid S₂ renaming (Carrier to A₂; _≈_ to _≈₂_)

      open import Data.Vec.Any.Membership S₁ renaming (_∈′_ to _∈′₁_) using (find′)
      open import Data.Vec.Any.Membership S₂ renaming (_∈′_ to _∈′₂_) using ()      

      ∈′-map⁺  : ∀ {n x}{xs : Vec A₁ n} {f} →
        f Preserves _≈₁_ ⟶ _≈₂_ → 
          x ∈′₁ xs → f x ∈′₂ map f xs
      ∈′-map⁺ pres x∈′xs = map⁺ (Any.map pres x∈′xs)
   

      ∈′-map⁻  : ∀ {n y}{xs : Vec A₁ n} {f} → y ∈′₂ map f xs →
        ∃ λ x → x ∈′₁ xs × y ≈₂ f x
      ∈′-map⁻ y∈′map with find′ (map⁻ y∈′map)
      ... | _ , x∈xs , px = , x∈xs , px
open DoubleSetoid public
