module AtLeast where

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + m = suc m
(suc n) + m = suc (n + m)

data _≤_ : ℕ → ℕ → Set where
  z≤ : (n : ℕ) → zero ≤ n
  s≤ : {n m : ℕ} → (n ≤ m) → (suc n ≤ suc m)

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

--------------------------------------------------------------------------------
-- suc is a bijection on upper sets
--------------------------------------------------------------------------------

AtLeast : ℕ → Set
AtLeast n = Σ (λ m → (n ≤ m))

f : {n : ℕ} → AtLeast n → AtLeast (suc n)
f (m , pf) = (suc m , s≤ pf)

g : {n : ℕ} → AtLeast (suc n) → AtLeast n
g (m , pf) = _

{-
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
-}
