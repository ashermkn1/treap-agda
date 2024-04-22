
```agda

data ⊥ : Set where

record ⊤ : Set where
  constructor ⟨⟩

data Bool : Set where
  tt ff : Bool

So : Bool → Set
So tt = ⊤
So ff = ⊥

record ⌜_⌝ (P : Set) : Set where
  constructor !
  field {{prf}} : P


```