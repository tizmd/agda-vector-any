module Data.Vec.Membership where

open import Data.Vec as Vec
open import Data.Vec.Any
open import Data.Vec.Any.Membership.Propositional
open import Data.Product as Prod hiding (map)
open import Function using (_∘_; id)

find : ∀ {a p}{A : Set a}{P : A → Set p}{n}{xs : Vec A n} →
  Any P xs → ∃ λ x → x ∈ xs × P x
-- find = Prod.map id (Prod.map ∈′→∈ id) ∘ find′
find (here px) = , here , px
find (there p) = Prod.map id (Prod.map there id) (find p)

lose : ∀ {a p}{A : Set a}{P : A → Set p}{n x}{xs : Vec A n} →
  x ∈ xs → P x → Any P xs
lose = lose′ ∘ ∈→∈′

open import Function.Related as Related public using (Kind; Symmetric-kind)
            renaming (implication to subset
              ;  reverse-implication to superset
              ;  equivalence to set
              ;  injection to subbag
              ;  reverse-injection to superbag
              ;  bijection to bag)
   
_∼[_]_ : ∀ {a m n}{A : Set a} → Vec A m → Kind → Vec A n → Set _
xs ∼[ k ] ys = ∀ {x} → (x ∈ xs) Related.∼[ k ] (x ∈ ys)


