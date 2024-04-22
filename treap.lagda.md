```agda
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS --prop #-}

open import Level using () renaming (zero to lzero)
open import Relation.Binary.Bundles using (DecTotalOrder)

module treap (O : DecTotalOrder lzero lzero lzero) where

module O = DecTotalOrder O
open O
  using    (_≤_; total)
  renaming (Carrier to 𝕂)

open import Data.Nat.Base using (ℕ; zero; suc; _⊓_) hiding (module ℕ)
module ℕ where
  open import Data.Nat.Base public
  open import Data.Nat.Properties public

open import Data.Integer.Base using (ℤ) hiding (module ℤ)
module ℤ where
  open import Data.Integer.Base public
  open import Data.Integer.Properties public

open import Data.Maybe using (Maybe; nothing; just)

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
import Calf

variable
  A B C : Set
  x y z : A
  k l m n : ℕ

it : {{x : A}} → A
it {{x}} = x

record Ord (A : Set) : Set₁ where
  field
    _≤_ : A → A → Set
    
    ≤-refl : x ≤ x
    ≤-trans : x ≤ y → y ≤ z → x ≤ z
    ≤-antisym : x ≤ y → y ≤ x → x ≡ y


data Tree : Set where
  Empty : Tree
  Node : (l : Tree) → (k : ℕ) → (p : ℤ) → (r : Tree) → Tree


ℤ-∞ = Maybe ℤ
pattern -∞ = nothing


```


Invariants we need at every node:
p(parent) >= p(children)
Left < k < Right (keys are binary searched)
