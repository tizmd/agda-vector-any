open import Relation.Binary using (Setoid)

module Data.Vec.Any.Membership {a ℓ} (S : Setoid a ℓ) where
  open import Level using (_⊔_)
  open Setoid S renaming (Carrier to A; refl to ≈-refl; trans to ≈-trans )
  open import Relation.Nullary
  open import Relation.Binary
  open import Data.Fin
  open import Data.Nat as ℕ hiding (_⊔_)
  open import Data.Product as Prod hiding (map) 
  open import Data.Vec as Vec hiding (map)
  open import Data.Vec.Equality 
  open import Data.Vec.Any as Any
  open import Function using (_∘_; id; flip)
  open Equality S renaming (_≈_ to _≋_; trans to ≋-trans)

  infix 4 _∈′_ _∉′_
  _∈′_ : ∀ {n} → A → Vec A n → Set (a ⊔ ℓ)
  x ∈′ xs = Any (x ≈_) xs
  
  _∉′_ : ∀ {n} → A → Vec A n → Set (a ⊔ ℓ) 
  x ∉′ xs = ¬ (x ∈′ xs)

  infix 4 _⊆_ _⊈_

  _⊆_  : ∀ {n m} → Vec A n → Vec A m → Set _
  xs ⊆ ys = ∀ {x} → x ∈′ xs → x ∈′ ys
  _⊈_  : ∀ {n m} → Vec A n → Vec A m → Set _
  xs ⊈ ys = ¬ (xs ⊆ ys)

  -- A variant of Vec.map.

  map-with-∈′ : ∀ {n b} {B : Set b}
             (xs : Vec A n) → (∀ {x} → x ∈′ xs → B) → Vec B n
  map-with-∈′ []       f = []
  map-with-∈′ (x ∷ xs) f = f (here ≈-refl)  ∷ map-with-∈′ xs (f ∘ there)
  
  -- Finds an element satisfying the predicate.

  find′ : ∀ {p n} {P : A → Set p} {xs : Vec A n} →
         Any P xs → ∃ λ x → x ∈′ xs × P x
  find′ (here px) = , here ≈-refl  , px
  find′ (there pxs) = Prod.map id (Prod.map there id) (find′ pxs) 

  lose′ : ∀ {p n} {P : A → Set p} {x}{xs : Vec A n} →
         P Respects _≈_ → x ∈′ xs → P x → Any P xs
  lose′ resp x∈′xs  px = map (flip resp px) x∈′xs




