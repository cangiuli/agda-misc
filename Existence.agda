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

data _≥_ : ℕ⁺ → ℕ⁺ → Set where
  ≥one : ∀ {n} → (n ≥ one)
  ≥suc : ∀ {n m} → (n ≥ m) → (suc n ≥ suc m)

infix 10 _≥_

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
  >pf : ∀ {n m} → (n ≢ m) → (n ≥ m) → (n > m)

infix 10 _>_

--------------------------------------------------------------------------------
-- Lemmas
--------------------------------------------------------------------------------

≡-cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
≡-cong f refl = refl

≡-resp : {A : Set} {P : A → Set} {x y : A} → x ≡ y → P x → P y
≡-resp refl Px = Px

≡-sym : {n m : ℕ⁺} → n ≡ m → m ≡ n
≡-sym refl = refl

≥-antisym : {n m : ℕ⁺} → (n ≥ m) → (m ≥ n) → (n ≡ m)
≥-antisym {one}   {one}   _ _ = refl
≥-antisym {one}   {suc m} () _
≥-antisym {suc n} {one}   _ ()
≥-antisym {suc n} {suc m} (≥suc p₁) (≥suc p₂) = ≡-cong suc (≥-antisym p₁ p₂)

inl-lemma : {A B : Set} → A ∨ B → (B → ⊥) → A
inl-lemma (inl a) f = a
inl-lemma (inr b) f = ⊥-elim (f b)

decidable-≡ : (n m : ℕ⁺) → (n ≡ m) ∨ (n ≢ m)
decidable-≡ one     one     = inl refl
decidable-≡ one     (suc n) = inr (λ ())
decidable-≡ (suc n) one     = inr (λ ())
decidable-≡ (suc n) (suc m) with decidable-≡ n m
... | inl eq  = inl (≡-cong suc eq)
... | inr neq = inr (λ s-eq → neq (≡-cong pred s-eq))

one-or-not : (n : ℕ⁺) → (n ≡ one) ∨ (n ≢ one)
one-or-not n = decidable-≡ n one

+-suc : {n m : ℕ⁺} → n + suc m ≡ suc n + m
+-suc {one} = refl
+-suc {suc n} = ≡-cong suc +-suc

sucn≥n : {n : ℕ⁺} → suc n ≥ n
sucn≥n {one}   = ≥one
sucn≥n {suc n} = ≥suc sucn≥n

+-> : (n m : ℕ⁺) → (n + m > m)
+-> _       one     = >pf (λ ()) ≥one
+-> one     (suc m) = >pf (λ ()) sucn≥n
+-> (suc n) (suc m) with +-> (suc n) m
... | >pf _ n+m≥m = >pf (λ ()) (≥suc (≥-cong +-suc n+m≥m))
  where ≥-cong : {n n' m : ℕ⁺} → n' ≡ n → n ≥ m → n' ≥ m
        ≥-cong refl p = p

²-fixpoint : (n : ℕ⁺) → Set
²-fixpoint n = n ² ≡ n

²-fixpoint-is-one : (n : ℕ⁺) → ²-fixpoint n → n ≡ one
²-fixpoint-is-one one _ = refl
²-fixpoint-is-one (suc n) ()

²-embiggens-≢-one : {n : ℕ⁺} → (n ≢ one) → (n ² > n)
²-embiggens-≢-one {one}   n≢one = ⊥-elim (n≢one refl)
²-embiggens-≢-one {suc m} _     = +-> (m × suc m) (suc m)

--------------------------------------------------------------------------------
-- Existence theorem
--------------------------------------------------------------------------------

is-maximal : ℕ⁺ → Set
is-maximal N = (m : ℕ⁺) → N ≥ m

refute-maximal : {N : ℕ⁺} → Σ (λ m → m > N) → is-maximal N → ⊥
refute-maximal (m , >pf m≢N m≥N) N≥ = m≢N (≥-antisym m≥N (N≥ m))

one-is-maximal : Σ is-maximal → is-maximal one
one-is-maximal (N , N≥) with one-or-not N
... | inl N≡one = ≡-resp N≡one N≥
... | inr N≢one = ⊥-elim (refute-maximal N²-counterexample N≥)
  where N²-counterexample = (N ² , ²-embiggens-≢-one N≢one)


--------------------------------------------------------------------------------
-- Bonus lemmas
--------------------------------------------------------------------------------

+-comm : {n m : ℕ⁺} → n + m ≡ m + n
+-comm {one}   {one}   = refl
+-comm {one}   {suc m} = +-suc
+-comm {suc n} {one}   = +-suc
+-comm {suc n} {suc m} = ≡-cong suc +-comm

