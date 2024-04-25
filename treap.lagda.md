In this file, we are providing an implementation of the `Treap` data structure with packaged proofs that the ordering and priority invariants are met.
At a high level, the `Treap` datatype consists of an `empty` constructor and a `node` constructor that contains a key, priority, and two child trees.
We will discuss the specifics of the verification in the report; for now, let's get into the code!

We start off with some boilerplate imports and some basic utilities needed for our instance types to work (more about this in the report):

```agda
module Treap where
  -- relations
  open import Relation.Binary
  open import Relation.Nullary
  open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; sym)
  
  -- datatypes
  open import Data.Product
  open import Data.Sum
  open import Data.Nat hiding (compare)
  open import Data.Nat.Properties
  open import Data.Unit using (⊤ ; tt)
  open import Data.Empty using (⊥ ; ⊥-elim)
  open import Agda.Builtin.Bool 
  open import Data.Bool.Base using (T)
  open import Function.Base using (_∘_)
  
  variable A : Set

  -- grab the instance value into an actual value
  it : {{x : A}} → A
  it {{x}} = x
  
  -- allow ≤ and < on the ℕs to be automatically derivable through instances
  instance    
    ≤-dec : ∀ {m n} → {p : T (m <ᵇ suc n)} → m ≤ n
    ≤-dec {m = zero} {n = n} = z≤n
    ≤-dec {m = suc m} {n = suc n} {p = p} = s≤s (≤-dec {p = p})

    <-dec : ∀ {m n} → {p : T (m <ᵇ n)} → m < n
    <-dec {m = zero} {n = suc n} = s≤s z≤n
    <-dec {m = suc m} {n = suc n} {p} = s≤s (<-dec {p = p})
```

Now, we are good to go for implementing `Treap`s!
We define our structure where the keys are an abstract `Carrier` type that supports a strict total ordering based on equality (≡) and a given ordering function (<):

```agda
  module TreapBase (Carrier : Set) (_<_ : Carrier → Carrier → Set) (IsSTO : IsStrictTotalOrder _≡_ _<_) where
    open IsStrictTotalOrder IsSTO

    data Treap (lower : Carrier) (prio : ℕ) (upper : Carrier) : Set where
      empty : {{lower < upper }} → Treap lower prio upper
      node  : (p : ℕ) → {{p ≤ prio}} → (k : Carrier) → Treap lower p k → Treap k p upper → Treap lower prio upper
    
    -- wrapper type to represent any `Treap` with priority at most `prio`
    ΣTreap : (prio : ℕ) → Set
    ΣTreap prio = ∃[ lower ] ∃[ upper ] Treap lower prio upper
```

We also define a notion of "is in" for `Treap`s:

```agda 
    data _∈_ {lower p upper} (x : Carrier) : (t : Treap lower p upper) → Set where
      here  : ∀ {p' h y l r} → x ≡ y → x ∈ node p' {{h}} y l r
      left  : ∀ {p' h y l r} → x ∈ l → x ∈ node p' {{h}} y l r
      right : ∀ {p' h y l r} → x ∈ r → x ∈ node p' {{h}} y l r

    _∉_ : ∀ {lower p upper} (x : Carrier) (t : Treap lower p upper) → Set
    x ∉ t = ¬ (x ∈ t)
```

And that's it! To show off the power of our cool new ✨ verified ✨ data structure, let's write some tests to show off its power:

```agda
  module _ where
    open TreapBase ℕ _<_ <-isStrictTotalOrder

    _ : ΣTreap 10
    _ = 0 , 1 , empty

    _ : ΣTreap 10
    _ = 0 , 2 , node 0 1 empty empty

    _ : ΣTreap 15
    _ = 0 , 9001 , node 15 42 (node 3 6 empty empty) (node 2 9000 empty empty)

    -- this correctly doesn't typecheck due to the top-level priority being wrong
    -- _ : ΣTreap 9
    -- _ = 0 , 10 , node 10 5 empty empty

    -- this correctly doesn't typecheck due to the right child containing a duplicate of the top node
    -- _ : ΣTreap 10
    -- _ = 0 , 11 , node 9 9 empty (node 4 10 (node 3 9 empty empty) empty)
```

Now, we define a method to `lookup` keys in a `Treap`, returning either a proof of existence or a proof of non-existence.
We make use of 3 lemmas:
  `lemmaOrder` to show that the `lower` bound of a `Treap` is less than its `upper` bound,
  `lemmaLeft` to show that given some `Treap t` and a key `x` that is less than or equal to `lower`, `x ∉ t`, and
  `lemmaRight` to show that given some `Treap t` and a key `x` where `upper` is less than or equal to `x`, `x ∉ t`.

```agda
  module Lookup (Carrier : Set) (_<_ : Carrier → Carrier → Set) (IsSTO : IsStrictTotalOrder _≡_ _<_) where
    open IsStrictTotalOrder IsSTO
    open TreapBase Carrier _<_ IsSTO
    
    lemmaOrder : ∀ {lower p upper} → (t : Treap lower p upper) → lower < upper
    lemmaOrder empty = it
    lemmaOrder (node p k l r) = trans (lemmaOrder l) (lemmaOrder r)

    lemmaLeft : ∀ {lower p upper} → (t : Treap lower p upper) → (x : Carrier) → (x < lower ⊎ x ≡ lower) → x ∉ t
    lemmaLeft empty x x≤lower = λ ()
    lemmaLeft (node p k l r) x x≤lower with compare x k
    ... | tri< x<k ¬x≡k ¬k<x = λ { (here x≡k) → ¬x≡k x≡k
                                ; (left x∈l) → lemmaLeft l x x≤lower x∈l
                                ; (right x∈r) → lemmaLeft r x (inj₁ x<k) x∈r }
    ... | tri≈ ¬x<k x≡k ¬k<x = λ { (here x≡k) → ¬x<k ([ (λ x<lower → trans x<lower (lemmaOrder l)) , (λ x≡lower → Eq.subst (_< k) (sym x≡lower) (lemmaOrder l) )] x≤lower)
                                ; (left x∈l) → lemmaLeft l x x≤lower x∈l
                                ; (right x∈r) → lemmaLeft r x (inj₂ x≡k) x∈r }
    ... | tri> ¬x<k ¬x≡k k<x = λ { (here x≡k) → ¬x≡k x≡k
                                ; (left x∈l) → lemmaLeft l x x≤lower x∈l
                                ; (right x∈r) → ¬x<k ([ (λ x<lower → trans x<lower (lemmaOrder l)) , (λ x≡lower → Eq.subst (_< k) (sym x≡lower) (lemmaOrder l)) ] x≤lower) }
    
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
  
Now, we can test some lookup proofs on a sample `Treap`:

```agda
  module _ where
    open TreapBase ℕ _<_ <-isStrictTotalOrder
    open Lookup ℕ _<_ <-isStrictTotalOrder

    treap : Treap 0 15 30
    treap = node 15 22 (node 15 15 (node 3 8 empty (node 0 10 empty empty)) (node 11 20 (node 10 18 empty empty) (node 11 21 empty empty))) (node 6 29 empty empty)

    15∈treap : 15 ∈ treap
    15∈treap = invert (proof (lookup 15 treap))

    16∉treap : 16 ∉ treap
    16∉treap = invert (proof (lookup 16 treap))

    21∈treap : 21 ∈ treap
    21∈treap = invert (proof (lookup 21 treap))

    45∉treap : 45 ∉ treap
    45∉treap = invert (proof (lookup 45 treap))

    -- cannot refine since 22 is in `treap`
    -- 22∉treap : 22 ∉ treap
    -- 22∉treap = invert (proof (lookup 22 {! treap  !}))

    -- cannot refine since 0 is not in `treap`
    -- 0∈treap : 0 ∈ treap
    -- 0∈treap = invert (proof (lookup 0 {! treap  !}))
```


```agda
  module Join (Carrier : Set) (_<_ : Carrier → Carrier → Set) (IsSTO : IsStrictTotalOrder _≡_ _<_) where
    open IsStrictTotalOrder IsSTO
    open TreapBase Carrier _<_ IsSTO
    

    priority : ∀ { lower prio upper } → Treap lower prio upper → ℕ
    priority empty = 0
    priority (node p k t t₁) = p
    
    treapCoerce : ∀ { lower prio upper p } → (t : Treap lower prio upper) → {{priority t ≤ p}} → Treap lower p upper
    treapCoerce empty = empty
    treapCoerce {p = p} (node p₁ k l r) {{p₁≤p}} = node p₁ {{p₁≤p}} k l r

    {-# TERMINATING #-}
    join : ∀ { lower prio upper } → (k : Carrier) → (p : ℕ) → Treap lower prio k → {{h : p ≤ prio}} → Treap k prio upper → ∃[ t' ] k ∈ t'
    join k p empty {{h}} empty = node p {{h}} k empty empty , here _≡_.refl
    join k p empty {{h}} (node p₁ {{h₁}} k₁ r r₁) with ≤-total p p₁
    ... | inj₁ p≤p₁ = 
      let l , k∈l = join k p empty {{p≤p₁}} r
      in node p₁ {{h₁}} k₁ l r₁ , left k∈l
    ... | inj₂ p₁≤p = node p {{h}} k empty (node p₁ {{p₁≤p}} k₁ r r₁) , here _≡_.refl
    join k p (node p₁ {{h₁}} k₁ l l₁) {{h}} empty with ≤-total p p₁
    ... | inj₁ p≤p₁ = 
      let r , k∈r = join k p l₁ {{p≤p₁}} empty
      in node p₁ {{h₁}} k₁ l r , right k∈r
    ... | inj₂ p₁≤p = node p {{h}} k (node p₁ {{p₁≤p}} k₁ l l₁) empty , here _≡_.refl
    join k p (node p₁ {{h₁}} k₁ l l₁) {{h}} (node p₂ {{h₂}} k₂ r r₁) with ≤-total p p₁ | ≤-total p p₂
    ... | inj₂ p₁≤p | inj₂ p₂≤p = node p {{h}} k (node p₁ {{p₁≤p}} k₁ l l₁) (node p₂ {{p₂≤p}} k₂ r r₁) , here _≡_.refl
    ... | inj₂ p₁≤p | inj₁ p≤p₂ = 
      let l' , k∈l' = join k p (node p₁ {{≤-trans p₁≤p p≤p₂}} k₁ l l₁) {{p≤p₂}} r
      in node p₂ {{h₂}} k₂ l' r₁ , left k∈l'
    ... | inj₁ p≤p₁ | inj₂ p₂≤p = 
      let r' , k∈r' = join k p l₁ {{p≤p₁}} (node p₂ {{≤-trans p₂≤p p≤p₁}} k₂ r r₁) 
      in node p₁ {{h₁}} k₁ l r' , right k∈r'
    ... | inj₁ p≤p₁ | inj₁ p≤p₂ with ≤-total p₁ p₂
    ... | inj₁ p₁≤p₂ = 
      let l' , k∈l' = join k p (node p₁ {{p₁≤p₂}} k₁ l l₁) {{p≤p₂}} r
      in node p₂ {{h₂}} k₂ l' r₁ , left k∈l'
    ... | inj₂ p₂≤p₁ = 
      let r' , k∈r' = join k p l₁ {{p≤p₁}} (node p₂ {{p₂≤p₁}} k₂ r r₁)
      in node p₁ {{h₁}} k₁ l r' , right k∈r'

    join' : ∀ { lower prio upper } → (k : Carrier) → (p : ℕ) → Treap lower prio k → {{h : p ≤ prio}} → Treap k prio upper → Treap lower prio upper
    join' k p l {{h}} r = proj₁ (join k p l {{h = h}} r)
```

```agda
  module Split (Carrier : Set) (_<_ : Carrier → Carrier → Set) (IsSTO : IsStrictTotalOrder _≡_ _<_) where
    open IsStrictTotalOrder IsSTO
    open TreapBase Carrier _<_ IsSTO
    open Lookup Carrier _<_ IsSTO
    open Join Carrier _<_ IsSTO

    coercePrio : ∀ { lower prio upper prio' } → { h : prio ≤ prio' } → Treap lower prio upper → Treap lower prio' upper
    coercePrio empty = empty
    coercePrio {prio' = prio'} {h = h} (node p {{p≤prio}} k l r) = node p {{≤-trans p≤prio h}} k l r
    
    coerceUpper : ∀ { lower prio upper upper' } → { h : upper < upper' } → Treap lower prio upper → Treap lower prio upper'
    coerceUpper {h = h} (empty {{lower<upper}}) = empty {{trans lower<upper h}}
    coerceUpper {h = h} (node p {{p≤prio}} k l r) = node p {{p≤prio}} k l (coerceUpper {h = h} r)
    
    coerceLower : ∀ { lower prio upper lower' } → {h : lower' < lower } → Treap lower prio upper → Treap lower' prio upper
    coerceLower {h = h} (empty {{lower<upper}}) = empty {{trans h lower<upper}}
    coerceLower {h = h} (node p {{p≤prio}} k l r ) = node p {{p≤prio}} k (coerceLower {h = h} l) r
    
    split : ∀ { lower prio upper } → (t : Treap lower prio upper) → (k : Carrier) → {{ lower < k }} → {{ k < upper }} → Treap lower prio k × Dec (k ∈ t) × Treap k prio upper
    split empty k = empty , no (λ ()) , empty
    split {lower = lower} {prio = prio} {upper = upper} T@(node p {{p≤prio}} k₁ l r) k with compare k k₁
    ... | tri< k<k₁ ¬k≡k₁ ¬k₁<k = 
      let (L₁ , _ , L₂) = split l k {{it}} {{k<k₁}} 
      in coercePrio {h = p≤prio} L₁ , lookup k T , coercePrio {h = p≤prio} (join' k₁ p L₂ {{h = ≤-refl}} r)
    ... | tri≈ ¬k<k₁ k≡k₁ ¬k₁<k = 
      Eq.subst (λ x → Treap lower prio x) (sym k≡k₁) (coercePrio {h = p≤prio} l) , 
        (yes (here k≡k₁)) , 
      Eq.subst (λ x → Treap x prio upper) (sym k≡k₁) (coercePrio {h = p≤prio} r)
    ... | tri> ¬k<k₁ ¬k≡k₁ k₁<k = 
      let (R₁ , _ , R₂) = split r k {{k₁<k}} {{it}} 
      in  coercePrio {h = p≤prio} (join' k₁ p l {{h = ≤-refl}} R₁) , (lookup k T) , coercePrio {h = p≤prio} R₂
```

```agda
  module Insert (Carrier : Set) (_<_ : Carrier → Carrier → Set) (IsSTO : IsStrictTotalOrder _≡_ _<_) where
    open IsStrictTotalOrder IsSTO
    open TreapBase Carrier _<_ IsSTO
    open Lookup Carrier _<_ IsSTO
    open Split Carrier _<_ IsSTO
    open Join Carrier _<_ IsSTO

    insert : ∀ { lower prio upper } → (x : Carrier) → (p : ℕ) → { h : p ≤ prio }  → (t : Treap lower prio upper) → {{ lower < x }} → {{ x < upper }} → x ∉ t → ∃[ t' ] x ∈ t' 
    insert x p {h = h} t x∉t = 
      let 
        (L , dec , R) = split t x
      in join x p L {{h = h}} R

    insert' : ∀ { lower prio upper } → (x : Carrier) → (p : ℕ) → { h : p ≤ prio }  → (t : Treap lower prio upper) → {{ lower < x }} → {{ x < upper }} → x ∉ t → Treap lower prio upper
    insert' x p {h} t x∉t = proj₁ (insert x p {h = h} t x∉t)
    
    insertSound : ∀ { lower prio upper k } → (x : Carrier) → (p : ℕ) → { h : p ≤ prio }  → (t : Treap lower prio upper) → {{ h₁ : lower < x }} → {{ h₂ : x < upper }} → (x∉t : x ∉ t) → k ∈ t → k ∈ (insert' x p {h = h} t {{h₁}} {{h₂}} x∉t)
    insertSound {k = k} x p {h} t x∉t k∈t with insert x p {h = h} t x∉t 
    ... | node p₁ k₁ l r , x∈t' with k∈t | compare k k₁ 
    ... | here x₁ | bar = {!   !}
    ... | left foo | bar = {!   !}
    ... | right foo | bar = {!   !}
``` 