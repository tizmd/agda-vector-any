module Data.Vec.Any.Membership.Propositional.Properties where

open import Algebra
open import Data.Vec as Vec 
open import Data.Vec.Any
open import Data.Vec.Any.Membership.Propositional
open import Data.Vec.Any.Properties
import Data.Vec.Any.Membership.Properties as Membershipᵖ
open import Function
open import Function.Inverse as Inv using (_↔_)
import Function.Related as Related
open import Function.Related.TypeIsomorphisms
open import Relation.Binary.PropositionalEquality as P
import Relation.Binary.Sigma.Pointwise as Σ
open import Relation.Unary using (_⟨×⟩_)
open import Data.Product 

private
  module ×⊎ {k ℓ} = CommutativeSemiring (×⊎-CommutativeSemiring k ℓ)

  
-- map

module _ {a b} {A : Set a} {B : Set b} {f : A → B} where
  ∈′-map⁺ : ∀ {n x}{xs : Vec A n} → x ∈′ xs → f x ∈′ Vec.map f xs
  ∈′-map⁺ = Membershipᵖ.∈′-map⁺ (P.setoid _) (P.setoid _) (P.cong f)

  ∈′-map⁻ : ∀ {n y}{xs : Vec A n} → y ∈′ Vec.map f xs → ∃ λ x → x ∈′ xs × y ≡ f x
  ∈′-map⁻ = Membershipᵖ.∈′-map⁻ (P.setoid _) (P.setoid _) 

  map-∈′↔ : ∀ {n y}{xs : Vec A n} →
    (∃ λ x → x ∈′ xs × y ≡ f x) ↔ y ∈′ Vec.map f xs
  map-∈′↔ {n}{y}{xs} =
    (∃ λ x → x ∈′ xs × y ≡ f x) ↔⟨ Any↔ ⟩
    Any (λ x → y ≡ f x)   xs    ↔⟨ map↔ ⟩
    y ∈′ Vec.map f xs       ∎
    where open Related.EquationalReasoning 
  

