module Data.Vec.Any.Membership.Propositional  where
  open import Relation.Binary.PropositionalEquality 
  open import Data.Vec
  open import Data.Vec.Any hiding (map)   
  open import Function.Inverse using (_↔_)
  open import Function using (_∘_)
  open import Data.Nat  
  open import Data.Product hiding (map)
  import Data.Vec.Any.Membership as Mem
  open import Function.Related using (↔⇒)
  module _ {a} {A : Set a} where
    private module M = Mem (setoid A)
    open M public hiding (lose′)

    ∈′→∈ : ∀ {n x}{xs : Vec A n} → x ∈′ xs → x ∈ xs
    ∈′→∈ {xs = .(_ ∷ _)} (here refl) = here
    ∈′→∈ {xs = .(_ ∷ _)} (there p) = there (∈′→∈ p)

    ∈→∈′ : ∀ {n x}{xs : Vec A n} → x ∈ xs → x ∈′ xs
    ∈→∈′ {xs = .(_ ∷ _)} here = here refl
    ∈→∈′ {xs = .(_ ∷ _)} (there p) = there (∈→∈′ p)
  
    ∈↔∈′ : ∀ {n x}{xs : Vec A n} → x ∈ xs ↔ x ∈′ xs
    ∈↔∈′ = record {
         to = →-to-⟶ ∈→∈′
         ; from =  →-to-⟶ ∈′→∈
         ; inverse-of = record {
             left-inverse-of = left-inverse
           ; right-inverse-of = right-inverse
         }
         }
         where
           left-inverse : ∀ {n x}{xs : Vec A n}(p : x ∈ xs) → ∈′→∈ (∈→∈′ p) ≡ p 
           left-inverse {xs = .(_ ∷ _)} here = refl
           left-inverse {xs = .(_ ∷ _)} (there p) = cong there (left-inverse p)

           right-inverse : ∀ {n x}{xs : Vec A n}(p : x ∈′ xs) → ∈→∈′ (∈′→∈ p) ≡ p
           right-inverse {xs = .(_ ∷ _)} (here refl) = refl
           right-inverse {xs = .(_ ∷ _)} (there p) = cong there (right-inverse p)

    ∈′→∈-there : ∀ {n x}{xs : Vec A n}(x∈′xs : x ∈′ xs) → ∈′→∈ (there {x = x} x∈′xs) ≡ there (∈′→∈ x∈′xs)
    ∈′→∈-there (here refl) = refl
    ∈′→∈-there (there p) rewrite ∈′→∈-there p = refl
    
    lose′ : ∀ {p}{P : A → Set p} {n x} {xs : Vec A n} →
      x ∈′ xs → P x → Any P xs
    lose′ {P = P} = M.lose′ (subst P) 

  open import Function.Related as Related public using (Kind; Symmetric-kind)
              renaming (implication to subset
                     ;  reverse-implication to superset
                     ;  equivalence to set
                     ;  injection to subbag
                     ;  reverse-injection to superbag
                     ;  bijection to bag)
  infix 4 _∼[_]_
  _∼[_]_ : ∀ {a m n}{A : Set a} → Vec A m → Kind → Vec A n → Set _
  xs ∼[ k ] ys = ∀ {x} → (x ∈′ xs) Related.∼[ k ] (x ∈′ ys)
    
  bag-=⇒ : ∀ {k a m n} {A : Set a} {xs : Vec A m} {ys : Vec A n} →
           xs ∼[ bag ] ys → xs ∼[ k ] ys
  bag-=⇒ xs≈ys = ↔⇒ xs≈ys
