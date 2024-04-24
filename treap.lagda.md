```agda
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS --prop #-}

open import Level using () renaming (zero to lzero)
open import Relation.Binary

module treap where


open import Data.Nat hiding (compare)
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum

open import Data.Maybe using (Maybe; nothing; just) renaming (map to mapMaybe)
open import Agda.Builtin.Bool 
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; sym)
open import Relation.Nullary
import Calf

variable
  A B C : Set
  x y z : A
  k l m n : ℕ

it : {{x : A}} → A
it {{x}} = x

open import Data.Unit using (⊤)
open import Data.Empty using (⊥)

_≢_ : A → A → Set
x ≢ y = ¬(x ≡ y)
So : Bool → Set
So false = ⊥
So true = ⊤

instance    
  ≤-dec : {p : So (m <ᵇ suc n)} → m ≤ n
  ≤-dec {m = zero} {n = n} = z≤n
  ≤-dec {m = suc m} {n = suc n} {p = p} = s≤s (≤-dec {p = p})

instance    
  <-dec : {p : So (m <ᵇ n)} → m < n
  <-dec {m = zero} {n = suc n} = s≤s z≤n
  <-dec {m = suc m} {n = suc n} {p} = s≤s (<-dec {p = p})





module TreapModule (Carrier : Set) (_<_ : Carrier → Carrier → Set) (IsSTO : IsStrictTotalOrder _≡_ _<_) where
  open IsStrictTotalOrder IsSTO

  data Treap (lower : Carrier) (prio : ℕ) (upper : Carrier) : Set where
    empty : {{lower < upper }} → Treap lower prio upper
    node : (p : ℕ) → {{p ≤ prio}} → (k : Carrier) → Treap lower p k → Treap k p upper → Treap lower prio upper

  
  data _∈_ {lower} {p : ℕ} {upper} (x : Carrier) : (t : Treap lower p upper) → Set where
    here : ∀ {p' h l r} → x ≡ y  → x ∈ node p' {{h}} y l r
    left : ∀ {p' h l r} → x ∈ l → x ∈ node p' {{h}} y l r
    right : ∀ {p' h l r} → x ∈ r → x ∈ node p' {{h}} y l r

  -- _tri∈_ : Tri 
  _∉_ : ∀ {lower} {p : ℕ} {upper} (x : Carrier) (t : Treap lower p upper) → Set
  x ∉ t = ¬ (x ∈ t)

  lemmaOrder : ∀ { lower p upper } → (t : Treap lower p upper) → lower < upper
  lemmaOrder empty = it
  lemmaOrder (node p k l r) = trans (lemmaOrder l) (lemmaOrder r)

  lemmaLeft : ∀ {lower p upper} → (t : Treap lower p upper) → (x : Carrier) → (x < lower ⊎ x ≡ lower) → x ∉ t
  lemmaLeft empty x x≤lower = λ ()
  lemmaLeft (node p k l r) x x≤lower with compare x k
  ... | tri< x<k ¬x≡k ¬k<x = λ { (here x≡k) → ¬x≡k x≡k
                               ; (left x∈l) → lemmaLeft l x x≤lower x∈l
                               ; (right x∈r) → lemmaLeft r x (inj₁ x<k) x∈r }
  ... | tri≈ ¬x<k x≡k ¬k<x = λ { (here x≡k) → [ (λ x<lower → ¬x<k (trans x<lower (lemmaOrder l))) , (λ x≡lower → ¬x<k (Eq.subst (_< k) (sym x≡lower) (lemmaOrder l)) )] x≤lower
                               ; (left x∈l) → lemmaLeft l x x≤lower x∈l
                               ; (right x∈r) → lemmaLeft r x (inj₂ x≡k) x∈r }
  ... | tri> ¬x<k ¬x≡k k<x = λ { (here x≡k) → ¬x≡k x≡k
                               ; (left x∈l) → lemmaLeft l x x≤lower x∈l
                               ; (right x∈r) → [ (λ x<lower → ¬x<k (trans x<lower (lemmaOrder l))) , (λ x≡lower → ¬x<k (Eq.subst (_< k) (sym x≡lower) (lemmaOrder l))) ] x≤lower}
  
  lemmaRight : ∀ {lower p upper} → (t : Treap lower p upper) → (x : Carrier) → (upper < x ⊎ x ≡ upper) → x ∉ t
  lemmaRight empty x x≥upper = λ ()
  lemmaRight (node p k l r) x x≥upper with compare x k
  ... | tri< x<k ¬x≡k ¬k<x = λ { (here x≡k) → ¬x≡k x≡k
                               ; (left x∈l) → lemmaRight l x ([ (λ upper<x → inj₁ (trans (lemmaOrder r) upper<x)) , (λ x≡upper → inj₁ (Eq.subst (k <_) (sym x≡upper) (lemmaOrder r))) ] x≥upper) x∈l
                               ; (right x∈r) → lemmaRight r x x≥upper x∈r }
  ... | tri≈ ¬x<k x≡k ¬k<x = λ _ → ¬k<x ([ trans (lemmaOrder r) , (λ x≡upper → Eq.subst (k <_) (sym x≡upper) (lemmaOrder r)) ] x≥upper)
  ... | tri> ¬x<k ¬x≡k k<x = λ { (here x≡k) → ¬x≡k x≡k
                               ; (left x∈l) → lemmaRight l x (inj₁ k<x) x∈l
                               ; (right x∈r) → lemmaRight r x x≥upper x∈r }
  
  lookup : ∀ { lower p upper } → (x : Carrier) → (t : Treap lower p upper) → Dec (x ∈ t)
  lookup x empty = no (λ ())
  lookup x (node p k l r) with compare x k
  lookup x (node p k l r) | tri≈ _ x≡k _ = yes (here x≡k)
  lookup x (node p k l r) | tri< x<k ¬x≡k ¬k<x with lookup x l
  ... | no x∉l = no (λ { (here x≡k) → ¬x≡k x≡k
                       ; (left x∈l) → x∉l x∈l
                       ; (right x∈r) → lemmaLeft r x (inj₁ x<k) x∈r })
  ... | yes x∈l = yes (left x∈l)
  lookup x (node p k l r) | tri> ¬x<k ¬x≡k k<x with lookup x r
  ... | no x∉r = no (λ { (here x≡k) → ¬x≡k x≡k
                       ; (left x∈l) → lemmaRight l x (inj₁ k<x) x∈l
                       ; (right x∈r) → x∉r x∈r })
  ... | yes x∈r = yes (right x∈r)
```


Let's test the `Treap` module:

```agda

module _ where
  open TreapModule ℕ _<_ <-isStrictTotalOrder

  ΣTreap : ℕ → Set
  ΣTreap prio = ∃[ lower ] ∃[ upper ] Treap lower prio upper

  _ : ΣTreap 10
  _ = 0 , 1 , empty

  _ : ΣTreap 10
  _ = 0 , 2 , node 0 1 empty empty

  _ : ΣTreap 15
  _ = 0 , 9001 , node 15 42 (node 3 6 empty empty) (node 2 9000 empty empty)

```

 
 Lookup

```agda

-- module Lookup {{STO : StrictTotalOrder lzero lzero lzero}} where
--   open StrictTotalOrder STO


          
  
```       