```agda
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS --prop #-}

open import Level using () renaming (zero to lzero)
open import Relation.Binary.Bundles using (DecTotalOrder)

module treap where


open import Data.Nat.Base using (ℕ; zero; suc; _⊓_) hiding (module ℕ)
module ℕ where
  open import Data.Nat.Base public
  open import Data.Nat.Properties public

open import Data.Integer.Base using (ℤ) hiding (module ℤ)
module ℤ where
  open import Data.Integer.Base public
  open import Data.Integer.Properties public

open import Data.Maybe using (Maybe; nothing; just) renaming (map to mapMaybe)
open import Agda.Builtin.Bool public
open import Agda.Builtin.Nat
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
import Calf

variable
  A B C : Set
  x y z : A
  k l m n : ℕ

it : {{x : A}} → A
it {{x}} = x

record ⊤ : Set where
  constructor tt
data ⊥ : Set where
module ℕ-≤ where
  data _≤_ : ℕ → ℕ → Set where
    ≤-zero : zero ≤ n
    ≤-suc : m ≤ n → suc m ≤ suc n

  ≤-refl : n ≤ n
  ≤-refl {n = zero} = ≤-zero
  ≤-refl {n = suc k} = ≤-suc ≤-refl

  ≤-trans : k ≤ l → l ≤ m → k ≤ m
  ≤-trans ≤-zero l≤m = ≤-zero
  ≤-trans (≤-suc k≤l) (≤-suc l≤m) = ≤-suc (≤-trans k≤l l≤m)

  ≤-antisym : k ≤ l → l ≤ k → k ≡ l
  ≤-antisym ≤-zero ≤-zero = Eq.refl
  ≤-antisym (≤-suc k≤l) (≤-suc l≤k) = Eq.cong suc (≤-antisym k≤l l≤k)

  So : Bool → Set
  So false = ⊥
  So true = ⊤

  instance    
    ≤-dec : {p : So (m < suc n)} → m ≤ n
    ≤-dec {m = zero} {n = n} = ≤-zero
    ≤-dec {m = suc m} {n = suc n} {p = p} = ≤-suc (≤-dec {p = p})

record Ord (A : Set) : Set₁ where
  field
    _≤_ : A → A → Set
    
    ≤-refl : x ≤ x
    ≤-trans : x ≤ y → y ≤ z → x ≤ z
    ≤-antisym : x ≤ y → y ≤ x → x ≡ y

  _≥_ : A → A → Set
  x ≥ y = y ≤ x

open Ord {{...}} 

instance
  Ord-ℕ : Ord ℕ
  _≤_ {{Ord-ℕ}} = ℕ-≤._≤_
  ≤-refl {{Ord-ℕ}} = ℕ-≤.≤-refl
  ≤-trans {{Ord-ℕ}} = ℕ-≤.≤-trans
  ≤-antisym {{Ord-ℕ}} = ℕ-≤.≤-antisym

  Ord-ℤ : Ord ℤ
  _≤_ {{Ord-ℤ}} = ℤ._≤_
  ≤-refl {{Ord-ℤ}} = ℤ.≤-refl
  ≤-trans {{Ord-ℤ}} = ℤ.≤-trans
  ≤-antisym {{Ord-ℤ}} = ℤ.≤-antisym

data Tri {{_ : Ord A}} : A → A → Set where
  less    : {{ x≤y : x ≤ y }} → Tri x y
  equal   : {{x≡y : x ≡ y}} → Tri x y
  greater : {{ x≥y : x ≥ y }} → Tri x y

record TDO (A : Set) : Set₁ where
  field
    {{Ord-A}} : Ord A
    tri : (x y : A) → Tri x y

open TDO {{...}} public

triNat : (x y : ℕ) → Tri x y
triNat zero zero = equal
triNat zero (suc y) = less
triNat (suc x) zero = greater
triNat (suc x) (suc y) with triNat x y
... | less  {{x≤y}} = less {{x≤y = ℕ-≤.≤-suc x≤y}}
... | equal {{x≡y}} = equal {{x≡y = Eq.cong ℕ.suc x≡y}}
... | greater {{x≥y}} = greater {{x≥y = ℕ-≤.≤-suc x≥y}}

-- triℤ : (x y : ℤ) → Tri x y
-- triℤ (ℤ.+_ zero) (ℤ.+_ zero) = equal
-- triℤ (ℤ.+_ zero) (ℤ.+_ (suc n₁)) = {! less  !}
-- triℤ (ℤ.+_ (suc n)) (ℤ.+_ n₁) = {!   !}
-- triℤ (ℤ.+_ n) (ℤ.-[1+_] n₁) = {!   !}
-- triℤ (ℤ.-[1+_] n) y = {!   !}
instance
  TDO-Nat : TDO ℕ
  Ord-A {{TDO-Nat}} = Ord-ℕ
  tri {{TDO-Nat}} = triNat

data Tree : Set where
  Empty : Tree
  Node : (l : Tree) → (k : ℕ) → (p : ℤ) → (r : Tree) → Tree

data [_]∞ (A : Set) : Set where
  -∞ : [ A ]∞
  [_] : A → [ A ]∞
  +∞ : [ A ]∞

module Ord-[]∞ {A : Set} {{ A-≤ : Ord A }} where 
  data _≤∞_ : [ A ]∞ → [ A ]∞ → Set where
    -∞-≤ : -∞ ≤∞ y
    []-≤ : x ≤ y → [ x ] ≤∞ [ y ]
    +∞-≤ : x ≤∞ +∞

  []∞-refl : x ≤∞ x
  []∞-refl {x = -∞} = -∞-≤
  []∞-refl {x = [ x ]} = []-≤ (≤-refl {A = A})
  []∞-refl {x = +∞} = +∞-≤

  []∞-trans : x ≤∞ y → y ≤∞ z → x ≤∞ z
  []∞-trans -∞-≤ _ = -∞-≤
  []∞-trans ([]-≤ x≤y) ([]-≤ y≤z) = []-≤ (≤-trans {A = A} x≤y y≤z)
  []∞-trans _ +∞-≤ = +∞-≤

  []∞-antisym : x ≤∞ y → y ≤∞ x → x ≡ y
  []∞-antisym -∞-≤ -∞-≤ = Eq.refl
  []∞-antisym ([]-≤ x≤y) ([]-≤ y≤x) = Eq.cong [_] (≤-antisym {A = A} x≤y y≤x)
  []∞-antisym +∞-≤ +∞-≤ = Eq.refl

  instance
    Ord-[]∞ : {{_ : Ord A}} → Ord [ A ]∞
    _≤_ {{Ord-[]∞}} = _≤∞_
    ≤-refl {{Ord-[]∞}} = []∞-refl
    ≤-trans {{Ord-[]∞}} = []∞-trans
    ≤-antisym {{Ord-[]∞}} = []∞-antisym
    
open Ord-[]∞ public



module _ {{_ : Ord A}} where
  instance
    -∞-≤-I : {y : [ A ]∞} → -∞ ≤ y
    -∞-≤-I = -∞-≤

    +∞-≤-I : {x : A} → [ x ] ≤ +∞
    +∞-≤-I = +∞-≤

    []-≤-I : {x y : A} {{x≤y : x ≤ y}} → [ x ] ≤ [ y ]
    []-≤-I {{x≤y = x≤y}} = []-≤ x≤y

data Treap (A : Set) {{_ : Ord A}} (lower : [ A ]∞) (prio : [ ℕ ]∞) (upper : [ A ]∞) : Set where
  empty : {{ lower ≤ upper }} → Treap A lower prio upper
  node : (p : ℕ) → {{[ p ]  ≤ prio}} → (k : A) → Treap A lower [ p ] [ k ] → Treap A [ k ] [ p ] upper → Treap A lower prio upper
```


Let's test the `Treap` module:

```agda

_ : Treap ℕ -∞ -∞ +∞
_ = empty

_ : Treap ℕ -∞ [ 0 ] +∞
_ = node 0 0 empty empty

_ : Treap ℕ -∞ ([ 15 ]) +∞
_ = node 15 42 (node 3 6 empty empty) (node 2 9000 empty empty)
```

 
 Lookup

```agda

module Lookup {{_ : TDO A}} where
  data _∈_ {lower} {p : ℕ} {upper} (x : A) : (t : Treap A lower [ p ] upper) → Set where
    here : ∀ {t₁ t₂} → x ≡ y → x ∈ node p y t₁ t₂
    left : ∀ {t₁ t₂} → x ∈ t₁ → x ∈ node p y t₁ t₂
    right : ∀ {t₁ t₂} → x ∈ t₂ → x ∈ node p y t₁ t₂

  lookup : ∀ { lower p upper } → (x : A) → (t : Treap A lower [ p ] upper) → Maybe (x ∈ t)
  lookup x empty = nothing
  lookup x (node p y l r) with tri x y
  ... | less = mapMaybe left (lookup x l)
  ... | equal = just (here it)
  ... | greater = mapMaybe right (lookup x r)

  

```