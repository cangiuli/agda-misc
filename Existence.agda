--------------------------------------------------------------------------------
-- The existence assumption.
-- See pastebin.com/XygqzAdj
--------------------------------------------------------------------------------

module Existence where

--------------------------------------------------------------------------------
-- Positive integers (ℕ⁺)
--------------------------------------------------------------------------------

data ℕ⁺ : Set where
  one : ℕ⁺
  suc : ℕ⁺ → ℕ⁺

pred : ℕ⁺ → ℕ⁺
pred one = one
pred (suc n) = n

_+_ : ℕ⁺ → ℕ⁺ → ℕ⁺
one + m = suc m
(suc n) + m = suc (n + m)

_×_ : ℕ⁺ → ℕ⁺ → ℕ⁺
one × m = m
(suc n) × m = (n × m) + m

_² : ℕ⁺ → ℕ⁺
n ² = n × n

--------------------------------------------------------------------------------
-- Logic
--------------------------------------------------------------------------------

data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

data _∨_ (A B : Set) : Set where
  inl : A → A ∨ B
  inr : B → A ∨ B

data Σ {A : Set} (B : A → Set) : Set where
  _,_ : (x : A) → (B x) → Σ {A} B

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 5 _≡_

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

infix 5 _≢_

data _>_ : ℕ⁺ → ℕ⁺ → Set where
  >one : ∀ {n} → (suc n > one)
  >suc : ∀ {n m} → (n > m) → (suc n > suc m)

infix 10 _>_

_≥_ : ℕ⁺ → ℕ⁺ → Set
n ≥ m = (n ≡ m) ∨ (n > m)

infix 10 _≥_

--------------------------------------------------------------------------------
-- Lemmas
--------------------------------------------------------------------------------

≡-cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
≡-cong f refl = refl

≡-resp : {A : Set} (P : A → Set) {x y : A} → x ≡ y → P x → P y
≡-resp _ refl Px = Px

>-irrefl : {n m : ℕ⁺} → (n > m) → (m ≢ n)
>-irrefl >one ()
>-irrefl (>suc p) sm≡sn = >-irrefl p (≡-cong pred sm≡sn)

>-antisym : {n m : ℕ⁺} → (n > m) → (m > n) → ⊥
>-antisym >one ()
>-antisym (>suc p) (>suc q) = >-antisym p q

decidable-≡ : (n m : ℕ⁺) → (n ≡ m) ∨ (n ≢ m)
decidable-≡ one     one     = inl refl
decidable-≡ one     (suc n) = inr (λ ())
decidable-≡ (suc n) one     = inr (λ ())
decidable-≡ (suc n) (suc m) with decidable-≡ n m
... | inl eq  = inl (≡-cong suc eq)
... | inr neq = inr (λ s-eq → neq (≡-cong pred s-eq))

one-or-not : (n : ℕ⁺) → (n ≡ one) ∨ (n ≢ one)
one-or-not n = decidable-≡ n one

suc-> : {n m : ℕ⁺} → (n > m) → (suc n > m)
suc-> {one}   {one}   _ = >one
suc-> {suc n} {one}   _ = >one
suc-> {one}   {suc m} ()
suc-> {suc n} {suc m} (>suc n>m) = >suc (suc-> n>m)

sucn>n : {n : ℕ⁺} → suc n > n
sucn>n {one}   = >one
sucn>n {suc n} = >suc sucn>n

+-> : (n m : ℕ⁺) → (n + m > m)
+-> one     one     = >one
+-> (suc n) one     = >one
+-> one     (suc m) = sucn>n
+-> (suc n) (suc m) = suc-> (+-> n (suc m))

²-embiggens-≢-one : {n : ℕ⁺} → (n ≢ one) → (n ² > n)
²-embiggens-≢-one {one}   n≢one = ⊥-elim (n≢one refl)
²-embiggens-≢-one {suc m} _     = +-> (m × suc m) (suc m)

--------------------------------------------------------------------------------
-- Existence theorem
--------------------------------------------------------------------------------

is-maximal : ℕ⁺ → Set
is-maximal N = (m : ℕ⁺) → N ≥ m

refute-maximal : {N : ℕ⁺} → Σ (λ m → m > N) → is-maximal N → ⊥
refute-maximal (m , m>N) N≥ with N≥ m
... | inl N≡m = >-irrefl m>N N≡m
... | inr N>m = >-antisym m>N N>m

one-is-maximal : Σ is-maximal → is-maximal one
one-is-maximal (N , N≥) with one-or-not N
... | inl N≡one = ≡-resp is-maximal N≡one N≥
... | inr N≢one = ⊥-elim (refute-maximal N²-counterexample N≥)
  where N²-counterexample = (N ² , ²-embiggens-≢-one N≢one)

