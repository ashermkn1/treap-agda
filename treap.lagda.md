In this file, we are providing an implementation of the `Treap` data structure (as detailed in 15-210) with packaged proofs that the ordering and priority invariants are met.
At a high level, a `Treap` can either be `empty` or a `node` constructor that contains a key, priority, and two child trees.
`Treap`s are an extension of BSTs with priorities for each key, with the additional invariant that the priorities of child nodes must be less than or equal to the current priority.
When priorities are assigned to keys at random, it can be proven that the height of the tree is logarithmic in the number of nodes with high probability, and all of the standard tree complexities can then be derived in expectation.

Here, we provide a verified implementation of the `Treap` datatype, along with verified implementations of several primitive operations.
Specifically, we have implemented `lookup`, `_∈_`, `join`, `split`, `insert`, and `delete` --- all with some level of correctness proofs.

We start off with some boilerplate imports and some basic utilities needed for our instance types to work (more about this in the report):

```agda
module Treap where
  -- relations
  open import Relation.Binary hiding (_⇔_)
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
  open import Function.Bundles
  open import Function.Properties.Equivalence using (⇔⇒⟶ ; ⇔⇒⟵)
  
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
      empty : {{lower < upper}} → Treap lower prio upper
      node  : (p : ℕ) → {{p ≤ prio}} → (k : Carrier) → Treap lower p k → Treap k p upper → Treap lower prio upper
    
    variable
      k : Carrier
      p prio : ℕ
      lower upper lower' upper' : Carrier
      t₁ t₂ : Treap lower prio upper
      
    -- wrapper type to represent any `Treap` with priority at most `prio`
    ΣTreap : (prio : ℕ) → Set
    ΣTreap prio = ∃[ lower ] ∃[ upper ] Treap lower prio upper

    -- returns lowest valid priority of a `Treap`
    priority : Treap lower prio upper → ℕ
    priority empty = 0
    priority (node p k t t₁) = p

    -- returns an explicit inequality that the `Treap`'s priority is a lower bound on the type's priority
    validPriority : (t : Treap lower prio upper) → priority t ≤ prio
    validPriority empty = z≤n
    validPriority (node p {{p≤prio}} k t t₁) = p≤prio
    
    -- changes the type of a `Treap` into any type that involves a valid priority for that `Treap`
    coercePrio : (t : Treap lower prio upper) → {{priority t ≤ p}} → Treap lower p upper
    coercePrio empty = empty
    coercePrio {p = p} (node p₁ k l r) {{p₁≤p}} = node p₁ {{p₁≤p}} k l r

    -- changes the type of a `Treap` into any type that involves a looser upper bound for that `Treap`
    coerceUpper : { h : upper < upper' } → Treap lower prio upper → Treap lower prio upper'
    coerceUpper {h = h} (empty {{lower<upper}}) = empty {{trans lower<upper h}}
    coerceUpper {h = h} (node p {{p≤prio}} k l r) = node p {{p≤prio}} k l (coerceUpper {h = h} r)
    
    -- changes the type of a `Treap` into any type that involves a looser lower bound for that `Treap`
    coerceLower : {h : lower' < lower } → Treap lower prio upper → Treap lower' prio upper
    coerceLower {h = h} (empty {{lower<upper}}) = empty {{trans h lower<upper}}
    coerceLower {h = h} (node p {{p≤prio}} k l r ) = node p {{p≤prio}} k (coerceLower {h = h} l) r

    -- extract bounds well-formedness from `Treap`
    lemmaOrder : (t : Treap lower p upper) → lower < upper
    lemmaOrder empty = it
    lemmaOrder (node p k l r) = trans (lemmaOrder l) (lemmaOrder r)
```

We also define a notion of "is in", and some corresponding lemmas for `Treap`s:

```agda 
    data _∈_ {lower p upper} (x : Carrier) : (t : Treap lower p upper) → Set where
      here  : ∀ {p' h y l r} → x ≡ y → x ∈ node p' {{h}} y l r
      left  : ∀ {p' h y l r} → x ∈ l → x ∈ node p' {{h}} y l r
      right : ∀ {p' h y l r} → x ∈ r → x ∈ node p' {{h}} y l r

    _∉_ : (x : Carrier) (t : Treap lower p upper) → Set
    x ∉ t = ¬ (x ∈ t)

    -- given a `Treap` and evidence that a key `k` is in it, we can derive `lower < k < upper`
    lemmaContains : { t : Treap lower prio upper } → k ∈ t → lower < k × k < upper
    lemmaContains {lower = lower} {upper = upper} {t = node p k₁ l r} (here k≡k₁) = 
      (Eq.subst (lower <_) (sym k≡k₁) (lemmaOrder l)) , Eq.subst (_< upper) (sym k≡k₁) (lemmaOrder r)
    lemmaContains {t = node p k₁ l r} (left k∈l) = 
      let lower<k , k<k₁ = lemmaContains k∈l 
      in lower<k , (trans k<k₁ (lemmaOrder r))
    lemmaContains {t = node p k₁ l r} (right k∈r) = 
      let k₁<k , k<upper = lemmaContains k∈r
      in trans (lemmaOrder l) k₁<k , k<upper

    -- given a `Treap` and some key that is ≤ the `lower` bound, we can derive that it is not in the `Treap`
    lemmaLeft : (t : Treap lower p upper) → (x : Carrier) → (x < lower ⊎ x ≡ lower) → x ∉ t
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
    
    -- given a `Treap` and some key that is > the `upper` bound, we can derive that it is not in the `Treap`
    lemmaRight : (t : Treap lower p upper) → (x : Carrier) → (upper < x ⊎ x ≡ upper) → x ∉ t
    lemmaRight empty x x≥upper = λ ()
    lemmaRight (node p k l r) x x≥upper with compare x k
    ... | tri< x<k ¬x≡k ¬k<x = λ { (here x≡k) → ¬x≡k x≡k
                                ; (left x∈l) → lemmaRight l x ([ (λ upper<x → inj₁ (trans (lemmaOrder r) upper<x)) , (λ x≡upper → inj₁ (Eq.subst (k <_) (sym x≡upper) (lemmaOrder r))) ] x≥upper) x∈l
                                ; (right x∈r) → lemmaRight r x x≥upper x∈r }
    ... | tri≈ ¬x<k x≡k ¬k<x = λ _ → ¬k<x ([ trans (lemmaOrder r) , (λ x≡upper → Eq.subst (k <_) (sym x≡upper) (lemmaOrder r)) ] x≥upper)
    ... | tri> ¬x<k ¬x≡k k<x = λ { (here x≡k) → ¬x≡k x≡k
                                ; (left x∈l) → lemmaRight l x (inj₁ k<x) x∈l
                                ; (right x∈r) → lemmaRight r x x≥upper x∈r }
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

Next, we define a method to `lookup` keys in a `Treap`, returning either a proof of existence or a proof of non-existence.

```agda
  module Lookup (Carrier : Set) (_<_ : Carrier → Carrier → Set) (IsSTO : IsStrictTotalOrder _≡_ _<_) where
    open IsStrictTotalOrder IsSTO
    open TreapBase Carrier _<_ IsSTO
    
    lookup : (x : Carrier) → (t : Treap lower p upper) → Dec (x ∈ t)
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
  
Let's test some lookup proofs on a sample `Treap`!
We can make use of the `invert` function in the standard library to extract the actual proof value from its wrapped `Decidable` type.
Because this all works at the type level, we can set the type of the value to be whether we expect a value to be in `treap` or not, and if the proof inversion typechecks, it worked as expected!

```agda
  module _ where
    open TreapBase ℕ _<_ <-isStrictTotalOrder
    open Lookup ℕ _<_ <-isStrictTotalOrder

    treap : Treap 0 15 30
    treap = node 15 22 (node 15 15 (node 3 8 empty (node 0 10 empty empty)) (node 11 20 (node 10 18 empty empty) (node 11 21 empty empty))) (node 6 29 empty empty)

    _ : 15 ∈ treap
    _ = invert (proof (lookup 15 treap))

    _ : 16 ∉ treap
    _ = invert (proof (lookup 16 treap))

    _ : 21 ∈ treap
    _ = invert (proof (lookup 21 treap))

    _ : 45 ∉ treap
    _ = invert (proof (lookup 45 treap))

    -- cannot refine since 22 is in `treap`
    -- _ : 22 ∉ treap
    -- _ = invert (proof (lookup 22 {! treap  !}))

    -- cannot refine since 0 is not in `treap`
    -- _ : 0 ∈ treap
    -- _ = invert (proof (lookup 0 {! treap  !}))
```

Finally, `Treap` is starting to take a familiar shape!
But we still have a few utilities we need to define before we can really say we have a useful data structure.
First on the list is `join`ing `Treap`s.
We define `join` that takes in `Treap`s `l` and `r` as well as a key `k` and priority `p`, with the builtin requirement that `l < k < r` (in shorthand), and returns both the joined `Treap` and a proof that `k` is in the result.

```agda
  module Join (Carrier : Set) (_<_ : Carrier → Carrier → Set) (IsSTO : IsStrictTotalOrder _≡_ _<_) where
    open IsStrictTotalOrder IsSTO
    open TreapBase Carrier _<_ IsSTO

    {-# TERMINATING #-}
    join : (k : Carrier) → (p : ℕ) → Treap lower prio k → {{h : p ≤ prio}} → Treap k prio upper → ∃[ t' ] k ∈ t'
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

    -- start of a correctness proof for join
    joinCorrect : ∀ { x : Carrier } → {k : Carrier} → {p : ℕ} → {{h : p ≤ prio}} → { t₁ : Treap lower prio k } → { t₂ : Treap k prio upper } → ((x ∈ t₁ ⊎ x ≡ k ⊎ x ∈ t₂) → x ∈ (proj₁ (join k p t₁ {{h}} t₂))) × (x ∈ (proj₁ (join k p t₁ {{h}} t₂)) → (x ∈ t₁ ⊎ x ≡ k ⊎ x ∈ t₂))
    joinCorrect = {!   !} , {!   !}
    
    -- removes the proof for situations where it is not needed
    join' : (k : Carrier) → (p : ℕ) → Treap lower prio k → {{h : p ≤ prio}} → Treap k prio upper → Treap lower prio upper
    join' k p l {{h}} r = proj₁ (join k p l {{h = h}} r)

    -- joins two `Treap`s without a middle key/priority pair
    {-# TERMINATING #-}
    joinPair : (t₁ : Treap lower prio k) → (t₂ : Treap k prio upper) → Treap lower prio upper
    joinPair t₁ empty = coerceUpper {h = it} t₁
    joinPair empty t₂@(node p k₁ l r) = coerceLower {h = it} t₂
    joinPair t₁@(node p₁ {{p₁≤prio}} k₁ l₁ r₁) t₂@(node p₂ {{p₂≤prio}} k₂ l₂ r₂) with ≤-total p₁ p₂
    ... | inj₁ p₁≤p₂ = node p₂ {{p₂≤prio}} k₂ (joinPair (coercePrio t₁ {{p₁≤p₂}}) l₂) r₂
    ... | inj₂ p₂≤p₁ = node p₁ {{p₁≤prio}} k₁ l₁ (joinPair r₁ (coercePrio t₂ {{p₂≤p₁}}))

    -- start of a correctness proof for `joinPair`
    joinPairCorrect : ∀ { x : Carrier } → { t₁ : Treap lower prio k } → { t₂ : Treap k prio upper } → (((x ∈ t₁) ⊎ (x ∈ t₂)) → x ∈ (joinPair t₁ t₂)) × (x ∈ (joinPair t₁ t₂) → ((x ∈ t₁) ⊎ (x ∈ t₂)))
    joinPairCorrect = {!   !} , {!   !}
```

Next (and last!) on the list is `split`ting a Treap into 2 pieces `l` and `r` based on some key `k`, such that `l < k < r`.
`split` also decides whether the split key was in the input `Treap` or not.

```agda
  module Split (Carrier : Set) (_<_ : Carrier → Carrier → Set) (IsSTO : IsStrictTotalOrder _≡_ _<_) where
    open IsStrictTotalOrder IsSTO
    open TreapBase Carrier _<_ IsSTO
    open Lookup Carrier _<_ IsSTO
    open Join Carrier _<_ IsSTO
    
    split : (t : Treap lower prio upper) → (k : Carrier) → {{ lower < k }} → {{ k < upper }} → Treap lower prio k × Dec (k ∈ t) × Treap k prio upper
    split empty k = empty , no (λ ()) , empty
    split {lower = lower} {prio = prio} {upper = upper} T@(node p {{p≤prio}} k₁ l r) k with compare k k₁
    ... | tri< k<k₁ ¬k≡k₁ ¬k₁<k = 
      let (L₁ , _ , L₂) = split l k {{it}} {{k<k₁}} in
      let R₂ = join' k₁ p L₂ {{h = ≤-refl}} r in
      coercePrio L₁ {{≤-trans (validPriority L₁) p≤prio}}, lookup k T , coercePrio R₂ {{≤-trans (validPriority R₂) p≤prio}}
    ... | tri≈ ¬k<k₁ k≡k₁ ¬k₁<k = 
      Eq.subst (λ x → Treap lower prio x) (sym k≡k₁) (coercePrio l {{≤-trans (validPriority l) p≤prio}}) , 
        (yes (here k≡k₁)) , 
      Eq.subst (λ x → Treap x prio upper) (sym k≡k₁) (coercePrio r {{≤-trans (validPriority r) p≤prio}})
    ... | tri> ¬k<k₁ ¬k≡k₁ k₁<k = 
      let (R₁ , _ , R₂) = split r k {{k₁<k}} {{it}} in
      let L₂ = join' k₁ p l {{h = ≤-refl}} R₁ in
      coercePrio L₂ {{≤-trans (validPriority L₂) p≤prio}} , (lookup k T) , coercePrio R₂ {{≤-trans (validPriority R₂) p≤prio}}
```

At long last, we can insert things into our `Treap`!
Making good use of our `join` and `split` functions, this is almost trivial, and we also get a proof that our result contains the desired element for free!

```agda
  module Insert (Carrier : Set) (_<_ : Carrier → Carrier → Set) (IsSTO : IsStrictTotalOrder _≡_ _<_) where
    open IsStrictTotalOrder IsSTO
    open TreapBase Carrier _<_ IsSTO
    open Lookup Carrier _<_ IsSTO
    open Split Carrier _<_ IsSTO
    open Join Carrier _<_ IsSTO

    insert : (x : Carrier) → (p : ℕ) → { h : p ≤ prio }  → (t : Treap lower prio upper) → {{ lower < x }} → {{ x < upper }} → ∃[ t' ] x ∈ t' 
    insert x p {h = h} t = 
      let L , dec , R = split t x in
      join x p L {{h = h}} R

    -- removes the proof for situations where it is not needed
    insert' : (x : Carrier) → (p : ℕ) → { h : p ≤ prio }  → (t : Treap lower prio upper) → {{ lower < x }} → {{ x < upper }} → Treap lower prio upper
    insert' x p {h} t = proj₁ (insert x p {h = h} t)
    
    -- start of a partial proof that insert is correct
    insertSound : (x : Carrier) → (p : ℕ) → { h : p ≤ prio }  → (t : Treap lower prio upper) → {{ h₁ : lower < x }} → {{ h₂ : x < upper }} → k ∈ t → k ∈ (insert' x p {h = h} t {{h₁}} {{h₂}})
    insertSound {k = k} x p {h} t k∈t with insert x p {h = h} t
    ... | node p₁ k₁ l r , x∈t' with k∈t | compare k k₁ 
    ... | here x₁ | bar = {!   !}
    ... | left foo | bar = {!   !}
    ... | right foo | bar = {!   !}
```

But wait, with these primitives we also get an implementation of `delete` for free!
We need a few more utilities 

```agda
  module Delete (Carrier : Set) (_<_ : Carrier → Carrier → Set) (IsSTO : IsStrictTotalOrder _≡_ _<_) where
    open IsStrictTotalOrder IsSTO
    open TreapBase Carrier _<_ IsSTO
    open Lookup Carrier _<_ IsSTO
    open Split Carrier _<_ IsSTO
    open Join Carrier _<_ IsSTO
    
    delete : (t : Treap lower prio upper) → (k : Carrier) → {{h₁ : lower < k}} → {{ h₂ : k < upper }} → Σ[ t' ∈ Treap lower prio upper ] k ∉ t'
    delete t k = 
      let 
        (L , _ , R) = split t k {{it}} {{it}}
        _ , from = joinPairCorrect {x = k} {t₁ = L} {t₂ = R}
      in joinPair L R , 
         contraposition from (λ {(inj₁ k∈L) → lemmaRight L k (inj₂ _≡_.refl) k∈L
                               ; (inj₂ k∈R) → lemmaLeft R k (inj₂ _≡_.refl) k∈R})

    -- start of a partial proof that delete is correct
    deleteSound : 
      (t : Treap lower prio upper) → (k : Carrier) → {{h₁ : lower < k}} → {{ h₂ : k < upper }} → 
      {k' : Carrier} → {h₃ : k' Eq.≢ k} → k' ∈ t → k' ∈ (proj₁ (delete t k))
    deleteSound t k k'∈t = {!   !}
```

```agda
  module Misc (Carrier : Set) (_<_ : Carrier → Carrier → Set) (IsSTO : IsStrictTotalOrder _≡_ _<_) where
    open IsStrictTotalOrder IsSTO
    open TreapBase Carrier _<_ IsSTO

    minElem : Treap lower prio upper → Carrier × ℕ → Carrier × ℕ
    minElem empty kp = kp
    minElem (node p k l _) _ = minElem l (k , p)
    
    minKey : Treap lower prio upper → Carrier → Carrier
    minKey empty k = k
    minKey (node _ k l _) _ = minKey l k
    
    minKeySound : ∀ { x } → (t : Treap lower prio upper) → x ∈ t → (minKey t k < x ⊎ minKey t k ≡ x)
    minKeySound (node p k empty r) (here x≡k) = inj₂ (sym x≡k)
    minKeySound (node p k L@(node p₁ k₁ l r₁) r) (here x≡k) with minKeySound {k = k} {x = k₁} L (here _≡_.refl)
    ... | inj₁ min< = inj₁ (trans min< (Eq.subst (k₁ <_) (sym x≡k) (lemmaOrder r₁)))
    ... | inj₂ min≡ = inj₁ (Eq.subst₂ _<_ (sym min≡) (sym x≡k) (lemmaOrder r₁))
    minKeySound (node p k l r) (left x∈l) = minKeySound {k = k} l x∈l
    minKeySound (node p k empty r) (right x∈r) = inj₁ (proj₁ (lemmaContains x∈r))
    minKeySound {x = x} (node p k L@(node p₁ k₁ l₁ r₁) r) (right x∈r) with minKeySound {k = k} {x = k₁} L (here _≡_.refl)
    ... | inj₁ min< = 
      let k<x , _ = lemmaContains x∈r
      in inj₁ (trans min< (trans (lemmaOrder r₁) k<x))
    ... | inj₂ min≡ = 
      let k<x , _ = lemmaContains x∈r
      in inj₁ (Eq.subst (_< x) (sym min≡) (trans (lemmaOrder r₁) k<x))
```