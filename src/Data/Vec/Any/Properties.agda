module Data.Vec.Any.Properties where

open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≢_; inspect; refl)
open import Relation.Unary renaming (_⊆_ to _⋐_) using ()
open import Data.Product as Prod hiding (map; swap)
open import Data.Vec as Vec 
open import Data.Vec.Any as Any
open import Data.Vec.Any.Membership.Propositional
--open import Data.Vec.Membership
open import Data.Bool.Base using (Bool; false; true; T)
open import Data.Bool.Properties
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Empty
open import Data.Sum as Sum hiding (map)
open import Function using (_∘_; _$_; id; flip; const)
open import Function.Inverse as Inv using (_↔_)
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence as Eq using (_⇔_ ; module Equivalence)
open import Function.Related as Related using (Related)
open Related.EquationalReasoning
open import Relation.Binary.Sum

map-id : ∀ {a p n}  {A : Set a} {P : A → Set p} (f : P ⋐ P) {xs : Vec A n} →
         (∀ {x} (p : P x) → f p ≡ p) →
         (p : Any P xs) → Any.map f p ≡ p
map-id f hyp (here px) = P.cong here $ hyp px
map-id f hyp (there p) = P.cong there $ map-id f hyp p

map-∘  : ∀ {a p q r n}{A : Set a}{P : A → Set p}{Q : A → Set q}{R : A → Set r}
         (f : Q ⋐ R)(g : P ⋐ Q) {xs : Vec A n}(p : Any P xs) →
         Any.map (f ∘ g) p ≡ Any.map f (Any.map g p)

map-∘ f g (here px) = P.refl
map-∘ f g (there p) = P.cong there $ map-∘ f g p

map∘find′ : ∀ {a n p}{A : Set a} {P : A → Set p}{xs : Vec A n} (p : Any P xs) →
         let (x , x∈xs , px) = find′ p in
           {f : (x ≡_) ⋐ P } →
           f P.refl ≡ px     →
           Any.map f x∈xs ≡ p
map∘find′ (here px) hyp = P.cong here hyp
map∘find′ (there pxs) hyp = P.cong there $ map∘find′ pxs hyp

find′∘map : ∀ {a n p q}{A : Set a}{P : A → Set p}{Q : A → Set q}{xs : Vec A n}(p : Any P xs)(f : P ⋐ Q) →
           find′ (Any.map f p) ≡ Prod.map id (Prod.map id f) (find′ p)
find′∘map (here px) f = P.refl
find′∘map (there pxs) f rewrite find′∘map pxs f = P.refl
    
find′-∈′ : ∀ {a n}{A : Set a}{x}{xs : Vec A n}(x∈xs : x ∈′ xs) →
  find′ x∈xs ≡ (x , x∈xs , P.refl)
find′-∈′ (here P.refl) = P.refl
find′-∈′ (there x∈xs) rewrite find′-∈′ x∈xs = P.refl

lose′∘find′ : ∀ {a n p}{A : Set a} {P : A → Set p}{xs : Vec A n} (p : Any P xs) →
  uncurry′ lose′ (proj₂ (find′ p)) ≡ p
lose′∘find′ (here px) = P.refl
lose′∘find′ (there p) = P.cong there $ lose′∘find′ p

find′∘lose′ : ∀ {a n p}{A : Set a} (P : A → Set p){x}{xs : Vec A n} (x∈xs : x ∈′ xs)(px : P x) →
  find′ {P = P} (lose′ x∈xs px) ≡ (x , x∈xs , px)
find′∘lose′ P x∈xs px rewrite find′∘map x∈xs (flip (P.subst P) px) | find′-∈′ x∈xs = P.refl


∃∈-Any : ∀ {a p n}{A : Set a} {P : A → Set p}{xs : Vec A n} →
         (∃ λ x → x ∈′ xs × P x) → Any P xs
∃∈-Any = uncurry′ lose′ ∘ proj₂

Any↔  : ∀ {a p n}{A : Set a} {P : A → Set p}{xs : Vec A n} →
  (∃ λ x → x ∈′ xs × P x) ↔ Any P xs
  
Any↔ {P = P}{xs} = record {
     to = P.→-to-⟶ ∃∈-Any
   ; from = P.→-to-⟶ (find′ {P = P})
   ; inverse-of = record {
         left-inverse-of = λ { (x , x∈xs , px) → find′∘lose′ P x∈xs px}
       ; right-inverse-of = lose′∘find′
     }
  }

Any-cong : ∀ {k a p m n} {A : Set a} {P₁ P₂ : A → Set p} {xs₁ : Vec A m} {xs₂ : Vec A n} →
           (∀ x → Related k (P₁ x) (P₂ x)) → xs₁ ∼[ k ] xs₂ → Related k (Any P₁ xs₁) (Any P₂ xs₂)
Any-cong {P₁ = P₁}{P₂}{xs₁}{xs₂} P₁∼P₂ xs₁∼xs₂ =
  Any P₁ xs₁ ↔⟨ sym $ Any↔ {P = P₁} ⟩ (∃ λ x → x ∈′ xs₁ × P₁ x)
               ∼⟨ Σ.cong Inv.id (xs₁∼xs₂ ×-cong P₁∼P₂ _) ⟩(∃ λ x → x ∈′ xs₂ × P₂ x)
             ↔⟨ Any↔ {P = P₂} ⟩  Any P₂ xs₂ ∎
  where
    open import Relation.Binary.Product.Pointwise
    import Relation.Binary.Sigma.Pointwise as Σ    

swap : ∀ {a b p}{A : Set a}{B : Set b}{P : A → B → Set p}
  {m n}{xs : Vec A m}{ys : Vec B n} → Any (λ x → Any (P x) ys) xs → Any (λ y → (Any (flip P y) xs)) ys
swap (here pys) = Any.map here pys
swap (there pxys) = Any.map there $ swap pxys


swap-there : ∀ {a b p}{A : Set a}{B : Set b}{P : A → B → Set p}
    {m n x}{xs : Vec A m}{ys : Vec B n}(any : Any (λ x → Any (P x) ys) xs) →
    swap (Any.map (there {x = x}) any) ≡ there (swap any)
swap-there (here pys) = P.refl
swap-there (there pxys) = P.cong (Any.map there) $ swap-there pxys
    
swap-invol : ∀ {a b p}{A : Set a}{B : Set b}{P : A → B → Set p}
    {m n}{xs : Vec A m}{ys : Vec B n}(any : Any (λ x → Any (P x) ys) xs) →
      swap (swap any) ≡ any
swap-invol (here (here px)) = P.refl
swap-invol (here (there pys)) = P.cong (Any.map there) $ swap-invol (here pys)
swap-invol (there pxys) = P.trans (swap-there (swap pxys)) $ P.cong there $ swap-invol pxys

swap↔ : ∀ {a b p}{A : Set a}{B : Set b}{P : A → B → Set p}
    {m n}{xs : Vec A m}{ys : Vec B n} →
    Any (λ x → Any (P x) ys) xs ↔  Any (λ y → (Any (flip P y) xs)) ys
swap↔ = record {
    to = P.→-to-⟶ swap
  ; from = P.→-to-⟶ swap
  ; inverse-of = record {
     left-inverse-of = swap-invol
   ; right-inverse-of = swap-invol
  }
  }

⊥↔Any⊥ : ∀ {a n}{A : Set a}{xs : Vec A n} → ⊥ ↔ Any (const ⊥) xs   
⊥↔Any⊥ {A = A} = record {
    to = P.→-to-⟶ λ()
  ; from = P.→-to-⟶ (λ p → from p)
  ; inverse-of = record {
      left-inverse-of = λ()
    ; right-inverse-of = λ p → from p
  }
  }
  where
    from : ∀ {n}{xs : Vec A n} → Any (const ⊥) xs → ∀ {b} {B : Set b} → B
    from (here ())
    from (there p) = from p

⊥↔Any[] : ∀ {a}{A : Set a}{P : A → Set}  → ⊥ ↔ Any P []
⊥↔Any[] = record { 
    to = P.→-to-⟶ λ()
  ; from = P.→-to-⟶ λ()
  ; inverse-of = record {
      left-inverse-of = λ()
    ; right-inverse-of = λ()
  }
  }

-- any⇔

module _ {a p q}{A : Set a}{P : A → Set p}{Q : A → Set q} where
  Any-⊎⁺ : ∀{n}{xs : Vec A n} → Any P xs ⊎ Any Q xs → Any (λ x → P x ⊎ Q x) xs
  Any-⊎⁺ = [ Any.map inj₁  , Any.map inj₂ ]′

  Any-⊎⁻ : ∀{n}{xs : Vec A n} → Any (λ x → P x ⊎ Q x) xs → Any P xs ⊎ Any Q xs 
  Any-⊎⁻ (here (inj₁ px)) = inj₁ (here px)
  Any-⊎⁻ (here (inj₂ qx)) = inj₂ (here qx)
  Any-⊎⁻ (there p) = Sum.map there there (Any-⊎⁻ p) 

  
  ⊎↔ : ∀ {n}{xs : Vec A n} → (Any P xs ⊎ Any Q xs) ↔ Any (λ x → P x ⊎ Q x) xs
  ⊎↔ = record
    { to         = P.→-to-⟶ Any-⊎⁺
    ; from       = P.→-to-⟶ Any-⊎⁻
    ; inverse-of = record
      { left-inverse-of  = from∘to
      ; right-inverse-of = to∘from
      }
    }
    where

    from∘to : ∀ {n}{xs : Vec A n} (p : Any P xs ⊎ Any Q xs) → Any-⊎⁻ (Any-⊎⁺ p) ≡ p
    from∘to (inj₁ (here  p)) = P.refl
    from∘to (inj₁ (there p)) rewrite from∘to (inj₁ p) = P.refl
    from∘to (inj₂ (here  q)) = P.refl
    from∘to (inj₂ (there q)) rewrite from∘to (inj₂ q) = P.refl

    to∘from : ∀ {n}{xs : Vec A n} (p : Any (λ x → P x ⊎ Q x) xs) →
              Any-⊎⁺ (Any-⊎⁻ p) ≡ p
    to∘from (here (inj₁ p)) = P.refl
    to∘from (here (inj₂ q)) = P.refl
    to∘from (there p) with Any-⊎⁻ p | to∘from p
    to∘from (there .(Any.map inj₁ p)) | inj₁ p | P.refl = P.refl
    to∘from (there .(Any.map inj₂ q)) | inj₂ q | P.refl = P.refl

module _ {a b p q} {A : Set a} {B : Set b}
         {P : A → Set p} {Q : B → Set q} where

  Any-×⁺ : ∀ {m n}{xs : Vec A m} {ys : Vec B n} → Any P xs × Any Q ys →
           Any (λ x → Any (λ y → P x × Q y) ys) xs
  Any-×⁺ (p , q) = Any.map (λ p → Any.map (λ q → (p , q)) q) p

  Any-×⁻ : ∀ {m n} {xs : Vec A m}{ys : Vec B n} → Any (λ x → Any (λ y → P x × Q y) ys) xs →
           Any P xs × Any Q ys
  Any-×⁻ pq with Prod.map id (Prod.map id find′) (find′ pq)
  ... | (x , x∈xs , y , y∈ys , p , q) = (lose′ x∈xs p , lose′ y∈ys q)

  ×↔ : ∀ {m n} {xs : Vec A m}{ys : Vec B n} →
       (Any P xs × Any Q ys) ↔ Any (λ x → Any (λ y → P x × Q y) ys) xs
  ×↔ {m}{n}{xs} {ys} = record
    { to         = P.→-to-⟶ Any-×⁺
    ; from       = P.→-to-⟶ Any-×⁻
    ; inverse-of = record
      { left-inverse-of  = from∘to
      ; right-inverse-of = to∘from
      }
    }
    where
      from∘to : ∀ (pq : Any P xs × Any Q ys)
        → Any-×⁻ (Any-×⁺ pq) ≡ pq
      from∘to (p , q)
        rewrite find′∘map {Q = λ x → Any (λ y → P x × Q y) ys}
                       p (λ px → Any.map (λ q → (px , q)) q)
              | find′∘map {Q = λ y → P (proj₁ (find′ p)) × Q y}
                         q (λ q → proj₂ (proj₂ (find′ p)) , q)
              | lose′∘find′ p
              | lose′∘find′ q
              = P.refl

      to∘from : ∀ (pq :  Any (λ x → Any (λ y → P x × Q y) ys) xs) → Any-×⁺ (Any-×⁻ pq) ≡ pq
      to∘from pq  with find′ pq
              | (λ (f : (proj₁ (find′ pq) ≡_) ⋐ _) → map∘find′ pq {f})
      ... | (x , x∈xs , pq′) | lem₁
        with find′ pq′
          | (λ (f : (proj₁ (find′ pq′) ≡_) ⋐ _) → map∘find′ pq′ {f})
      ... | (y , y∈ys , p , q) | lem₂
        rewrite P.sym $ map-∘ {R = λ x → Any (λ y → P x × Q y) ys}
                              (λ p → Any.map (λ q → p , q) (lose′ y∈ys q))
                              (λ y → P.subst P y p)
                              x∈xs
                = lem₁ _ helper
        where
          helper : Any.map (λ q → p , q) (lose′ y∈ys q) ≡ pq′
          helper rewrite P.sym $ map-∘ {R = λ y → P x × Q y}
                                     (λ q → p , q)
                                     (λ y → P.subst Q y q)
                                     y∈ys                                       
                 = lem₂ _ P.refl


module _ {a b} {A : Set a} {B : Set b} where
  map⁺ : ∀ {p} {P : B → Set p} {f : A → B}{n}{xs : Vec A n} →
         Any (P ∘ f) xs → Any P (Vec.map f xs)
  map⁺ (here pfx) = here pfx
  map⁺ (there p) = there (map⁺ p)

  map⁻ : ∀ {p} {P : B → Set p} {f : A → B} {n}{xs : Vec A n} →
         Any P (Vec.map f xs) → Any (P ∘ f) xs
  map⁻ {xs = []}     ()
  map⁻ {xs = x ∷ xs} (here p)  = here p
  map⁻ {xs = x ∷ xs} (there p) = there $ map⁻ p

  map⁺∘map⁻ : ∀ {p} {P : B → Set p} {f : A → B}{n}{xs : Vec A n} →
              (p : Any P (Vec.map f xs)) → map⁺ (map⁻ p) ≡ p
  map⁺∘map⁻ {xs = []}     ()
  map⁺∘map⁻ {xs = x ∷ xs} (here  p) = P.refl
  map⁺∘map⁻ {xs = x ∷ xs} (there p) = P.cong there (map⁺∘map⁻ p)

  map⁻∘map⁺ : ∀ {p} (P : B → Set p) {f : A → B}{n} {xs : Vec A n} →
              (p : Any (P ∘ f) xs) → map⁻ {P = P} (map⁺ p) ≡ p
  map⁻∘map⁺ P (here  p) = P.refl
  map⁻∘map⁺ P (there p) = P.cong there (map⁻∘map⁺ P p)

  map↔ : ∀ {p} {P : B → Set p} {f : A → B} {n}{xs : Vec A n} →
         Any (P ∘ f) xs ↔ Any P (Vec.map f xs)
  map↔ {P = P} {f = f} = record
    { to         = P.→-to-⟶ $ map⁺ {P = P} {f = f}
    ; from       = P.→-to-⟶ $ map⁻ {P = P} {f = f}
    ; inverse-of = record
      { left-inverse-of  = map⁻∘map⁺ P
      ; right-inverse-of = map⁺∘map⁻
      }
    }
------------------------------------------------------------------------

-- _++_

module _ {a p} {A : Set a} {P : A → Set p} where

  ++⁺ˡ : ∀ {m n}{xs : Vec A m} {ys : Vec A n} → Any P xs → Any P (xs ++ ys)
  ++⁺ˡ (here p)  = here p
  ++⁺ˡ (there p) = there (++⁺ˡ p)

  ++⁺ʳ : ∀ {m n} (xs : Vec A m) {ys : Vec A n} → Any P ys → Any P (xs ++ ys)
  ++⁺ʳ []       p = p
  ++⁺ʳ (x ∷ xs) p = there (++⁺ʳ xs p)

  ++⁻ : ∀ {m n} (xs : Vec A m) {ys : Vec A n} → Any P (xs ++ ys) → Any P xs ⊎ Any P ys
  ++⁻ []       p         = inj₂ p
  ++⁻ (x ∷ xs) (here p)  = inj₁ (here p)
  ++⁻ (x ∷ xs) (there p) = Sum.map there id (++⁻ xs p)

  ++⁺∘++⁻ : ∀{m n} (xs : Vec A m) {ys : Vec A n} (p : Any P (xs ++ ys)) →
            [ ++⁺ˡ , ++⁺ʳ xs ]′ (++⁻ xs p) ≡ p
  ++⁺∘++⁻ []       p         = refl
  ++⁺∘++⁻ (x ∷ xs) (here  p) = refl
  ++⁺∘++⁻ (x ∷ xs) (there p) with ++⁻ xs p | ++⁺∘++⁻ xs p
  ++⁺∘++⁻ (x ∷ xs) (there p) | inj₁ p′ | ih = P.cong there ih
  ++⁺∘++⁻ (x ∷ xs) (there p) | inj₂ p′ | ih = P.cong there ih

  ++⁻∘++⁺ : ∀{m n} (xs : Vec A m) {ys : Vec A n} (p : Any P xs ⊎ Any P ys) →
            ++⁻ xs ([ ++⁺ˡ , ++⁺ʳ xs ]′ p) ≡ p
  ++⁻∘++⁺ []            (inj₁ ())
  ++⁻∘++⁺ []            (inj₂ p)         = refl
  ++⁻∘++⁺ (x ∷ xs)      (inj₁ (here  p)) = refl
  ++⁻∘++⁺ (x ∷ xs) {ys} (inj₁ (there p)) rewrite ++⁻∘++⁺ xs {ys} (inj₁ p) = refl
  ++⁻∘++⁺ (x ∷ xs)      (inj₂ p)         rewrite ++⁻∘++⁺ xs      (inj₂ p) = refl

  ++↔ : ∀{m n} {xs : Vec A m}{ys : Vec A n} → (Any P xs ⊎ Any P ys) ↔ Any P (xs ++ ys)
  ++↔ {xs = xs} = record
    { to         = P.→-to-⟶ [ ++⁺ˡ , ++⁺ʳ xs ]′
    ; from       = P.→-to-⟶ $ ++⁻ xs
    ; inverse-of = record
      { left-inverse-of  = ++⁻∘++⁺ xs
      ; right-inverse-of = ++⁺∘++⁻ xs
      }
    }

  ++-comm : ∀ {m n} (xs : Vec A m) (ys : Vec A n) → Any P (xs ++ ys) → Any P (ys ++ xs)
  ++-comm xs ys = [ ++⁺ʳ ys , ++⁺ˡ ]′ ∘ ++⁻ xs

  ++-comm∘++-comm : ∀{m n} (xs : Vec A m) {ys : Vec A n} (p : Any P (xs ++ ys)) →
                    ++-comm ys xs (++-comm xs ys p) ≡ p
  ++-comm∘++-comm [] {ys} p
    rewrite ++⁻∘++⁺ ys {ys = []} (inj₁ p) = P.refl
  ++-comm∘++-comm (x ∷ xs) {ys} (here p)
    rewrite ++⁻∘++⁺ ys {ys = x ∷ xs} (inj₂ (here p)) = P.refl
  ++-comm∘++-comm (x ∷ xs)      (there p) with ++⁻ xs p | ++-comm∘++-comm xs p
  ++-comm∘++-comm (x ∷ xs) {ys} (there .([ ++⁺ʳ xs , ++⁺ˡ ]′ (++⁻ ys (++⁺ʳ ys p))))
    | inj₁ p | P.refl
    rewrite ++⁻∘++⁺ ys (inj₂                 p)
            | ++⁻∘++⁺ ys (inj₂ $ there {x = x} p) = P.refl
  ++-comm∘++-comm (x ∷ xs) {ys} (there .([ ++⁺ʳ xs , ++⁺ˡ ]′ (++⁻ ys (++⁺ˡ p))))
    | inj₂ p | P.refl
    rewrite ++⁻∘++⁺ ys {ys =     xs} (inj₁ p)
            | ++⁻∘++⁺ ys {ys = x ∷ xs} (inj₁ p) = P.refl

  ++↔++ : ∀{m n} (xs : Vec A m) (ys : Vec A n) → Any P (xs ++ ys) ↔ Any P (ys ++ xs)
  ++↔++ xs ys = record
    { to         = P.→-to-⟶ $ ++-comm xs ys
    ; from       = P.→-to-⟶ $ ++-comm ys xs
    ; inverse-of = record
      { left-inverse-of  = ++-comm∘++-comm xs
      ; right-inverse-of = ++-comm∘++-comm ys
      }
    }

------------------------------------------------------------------------

-- tabulate

module _ {a p} {A : Set a} {P : A → Set p} where
  tabulate⁺ : ∀ {n} {f : Fin n → A} i → P (f i) → Any P (tabulate f)
  tabulate⁺ fzero    p = here p
  tabulate⁺ (fsuc i) p = there (tabulate⁺ i p)

  tabulate⁻ : ∀ {n} {f : Fin n → A} →
              Any P (tabulate f) → ∃ λ i → P (f i)
  tabulate⁻ {zero}  ()
  tabulate⁻ {suc n} (here p)   = fzero , p
  tabulate⁻ {suc n} (there p) = Prod.map fsuc id (tabulate⁻ p)

------------------------------------------------------------------------
-- map-with-∈.

module _ {a b p} {A : Set a} {B : Set b} {P : B → Set p} where

  map-with-∈′⁺ : ∀ {n}{xs : Vec A n} (f : ∀ {x} → x ∈′ xs → B) →
                (∃₂ λ x (x∈xs : x ∈′ xs) → P (f x∈xs)) →
                Any P (map-with-∈′ xs f)
  map-with-∈′⁺ f (_ , here refl  , p) = here p
  map-with-∈′⁺ f (_ , there x∈xs , p) =
    there $ map-with-∈′⁺ (f ∘ there) (_ , x∈xs , p)

  map-with-∈′⁻ : ∀ {n} (xs : Vec A n) (f : ∀ {x} → x ∈′ xs → B) →
                Any P (map-with-∈′ xs f) →
                ∃₂ λ x (x∈xs : x ∈′ xs) → P (f x∈xs)
  map-with-∈′⁻ []       f ()
  map-with-∈′⁻ (y ∷ xs) f (here  p) = (y , here refl , p)
  map-with-∈′⁻ (y ∷ xs) f (there p) =
    Prod.map id (Prod.map there id) $ map-with-∈′⁻ xs (f ∘ there) p

  map-with-∈′↔ : ∀{n}{xs : Vec A n} {f : ∀ {x} → x ∈′ xs → B} →
    (∃₂ λ x (x∈xs : x ∈′ xs) → P (f x∈xs)) ↔ Any P (map-with-∈′ xs f)
  map-with-∈′↔ = record
    { to         = P.→-to-⟶ (map-with-∈′⁺ _)
    ; from       = P.→-to-⟶ (map-with-∈′⁻ _ _)
    ; inverse-of = record
      { left-inverse-of  = from∘to _
      ; right-inverse-of = to∘from _ _
      }
    }
    where

    from∘to : ∀ {n} {xs : Vec A n} (f : ∀ {x} → x ∈′ xs → B)
              (p : ∃₂ λ x (x∈xs : x ∈′ xs) → P (f x∈xs)) →
              map-with-∈′⁻ xs f (map-with-∈′⁺ f p) ≡ p
    from∘to f (_ , here refl  , p) = refl
    from∘to f (_ , there x∈xs , p)
      rewrite from∘to (f ∘ there) (_ , x∈xs , p) = refl

    to∘from : ∀ {n}(xs : Vec A n) (f : ∀ {x} → x ∈′ xs → B)
              (p : Any P (map-with-∈′ xs f)) →
              map-with-∈′⁺ f (map-with-∈′⁻ xs f p) ≡ p
    to∘from []       f ()
    to∘from (y ∷ xs) f (here  p) = refl
    to∘from (y ∷ xs) f (there p) =
      P.cong there $ to∘from xs (f ∘ there) p

------------------------------------------------------------------------
module _ {a p} {A : Set a} {P : A → Set p} where
  return⁺ : ∀ {x} → P x → Any P ([ x ])
  return⁺ = here

  return⁻ : ∀ {x} → Any P ([ x ]) → P x
  return⁻ (here p)   = p
  return⁻ (there ())

  return⁺∘return⁻ : ∀ {x} (p : Any P [ x ]) →
                    return⁺ (return⁻ p) ≡ p
  return⁺∘return⁻ (here p)   = refl
  return⁺∘return⁻ (there ())

  return⁻∘return⁺ : ∀ {x} (p : P x) → return⁻ (return⁺ p) ≡ p
  return⁻∘return⁺ p = refl

  return↔ : ∀ {x} → P x ↔ Any P ([ x ])
  return↔ = record
    { to         = P.→-to-⟶ $ return⁺
    ; from       = P.→-to-⟶ $ return⁻
    ; inverse-of = record
      { left-inverse-of  = return⁻∘return⁺
      ; right-inverse-of = return⁺∘return⁻
      }
    }

-- _∷_.

∷↔ : ∀ {a p n} {A : Set a} (P : A → Set p) {x} {xs : Vec A n} →
     (P x ⊎ Any P xs) ↔ Any P (x ∷ xs)
∷↔ P {x} {xs} =
  (P x         ⊎ Any P xs)  ↔⟨ return↔ {P = P} ⊎-cong (Any P xs ∎) ⟩
  (Any P [ x ] ⊎ Any P xs)  ↔⟨ ++↔ {P = P} {xs = [ x ]} ⟩
  Any P (x ∷ xs)            ∎


