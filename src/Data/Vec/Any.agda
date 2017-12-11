module Data.Vec.Any {a} {A : Set a} where
  open import Level using (_⊔_)
  open import Relation.Nullary
  open import Data.Fin
  open import Data.Nat as ℕ hiding (_⊔_)
  open import Data.Vec as Vec using (Vec; _∷_; [])
  open import Relation.Unary renaming (_⊆_ to _⋐_) using (Decidable)
  open import Function.Inverse using (_↔_)
  open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
  import Relation.Binary.PropositionalEquality as P
  open import Relation.Nullary using (¬_; yes; no)
  import Relation.Nullary.Decidable as Dec
  open import Data.Empty using (⊥-elim)
  open import Data.Product using (∃ ; ,_ ) 
  import Data.List.Any as ListAny
  
  data Any {p}(P : A → Set p) : ∀ {n} → Vec A n → Set (a ⊔ p) where
    here  : ∀ {n x}{xs : Vec A n} → P x → Any P (x ∷ xs)
    there : ∀ {n x}{xs : Vec A n} → Any P xs → Any P (x ∷ xs)
  open Any public
  
  map : ∀ {p q} {P : A → Set p} {Q : A → Set q} {n} {xs : Vec A n} → 
    P ⋐ Q → Any P xs → Any Q xs
  map g (here px) =   here (g px)
  map g (there pxs) = there (map g pxs)   

  tail : ∀ {p} {P : A → Set p}{x n} {xs : Vec A n} → ¬ P x → Any P (x ∷ xs) → Any P xs
  tail ¬px (here px) = ⊥-elim (¬px px)
  tail ¬px (there pxs) = pxs

  any :  ∀ {p} {P : A → Set p} → Decidable P → ∀ {n} → Decidable (Any P {n})
  any p [] = no λ()
  any p (x ∷ xs) with p x
  any p (x ∷ xs) | yes px = yes (here px)
  any p (x ∷ xs) | no ¬px = Dec.map′ there (tail ¬px) (any p xs)

  index : ∀ {p}{P : A → Set p}{n}{xs : Vec A n} → Any P xs → Fin n
  index (here px) = zero
  index (there pxs) = suc (index pxs)

  satisfied : ∀ {p}{P : A → Set p}{n}{xs : Vec A n} → Any P xs → ∃ P
  satisfied (here px) = , px
  satisfied (there pxs) = satisfied pxs


  Any↔ListAny : ∀ {p}{P : A → Set p}{n}{xs : Vec A n} →
    Any P xs ↔ ListAny.Any P (Vec.toList xs)
  Any↔ListAny {P = P} = record {
        to = P.→-to-⟶ to
      ; from =  P.→-to-⟶ from
      ; inverse-of = record {
            left-inverse-of = left-inverse
          ; right-inverse-of = right-inverse
        }
    }
    where
      to : ∀ {n}{xs : Vec A n} → Any P xs → ListAny.Any P (Vec.toList xs)
      to (here px) = ListAny.here px
      to (there pxs) = ListAny.there (to pxs)

      from : ∀ {n}{xs : Vec A n} → ListAny.Any P (Vec.toList xs) → Any P xs
      from {xs = []} ()
      from {xs = x ∷ xs} (ListAny.here px) = here px
      from {xs = x ∷ xs} (ListAny.there pxs) = there (from pxs)


      left-inverse : ∀ {n}{xs : Vec A n}(p : Any P xs) → from (to p) P.≡ p
      left-inverse (here px) = P.refl
      left-inverse (there pxs) = P.cong there (left-inverse pxs)

      right-inverse : ∀ {n}{xs : Vec A n}(p : ListAny.Any P (Vec.toList xs)) → to (from p) P.≡ p
      right-inverse {xs = []} ()
      right-inverse {xs = x ∷ xs} (ListAny.here px) = P.refl
      right-inverse {xs = x ∷ xs} (ListAny.there pxs) = P.cong ListAny.there (right-inverse pxs)

