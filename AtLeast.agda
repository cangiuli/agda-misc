module AtLeast where

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + m = m
(suc n) + m = suc (n + m)

_-_ : ℕ → ℕ → ℕ
n - zero = n
zero - m = zero
(suc n) - (suc m) = n - m

data _≤_ : ℕ → ℕ → Set where
  z≤ : (n : ℕ) → zero ≤ n
  s≤ : {n m : ℕ} → (n ≤ m) → (suc n ≤ suc m)

--------------------------------------------------------------------------------
-- Logic
--------------------------------------------------------------------------------

data Σ {A : Set} (B : A → Set) : Set where
  _,_ : (x : A) → (B x) → Σ {A} B

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 5 _≡_

≡-cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
≡-cong f refl = refl

≡-resp : {A : Set} (P : A → Set) {x y : A} → x ≡ y → P x → P y
≡-resp _ refl Px = Px

Σ-eq : {A : Set} {a c : A} {B : A → Set} {b : B a} {d : B c} →
       Σ (λ (p : a ≡ c) → ≡-resp B p b ≡ d) → ((a , b) ≡ (c , d))
Σ-eq (refl , refl) = refl

--------------------------------------------------------------------------------
-- Lemmas
--------------------------------------------------------------------------------

≤-+ : (n m : ℕ) → n ≤ (n + m)
≤-+ zero m = z≤ m
≤-+ (suc n) m = s≤ (≤-+ n m)

+-- : (n m : ℕ) → (n + m) - n ≡ m
+-- zero m = refl 
+-- (suc n) m = +-- n m

≤-lem : (n m : ℕ) → (n ≤ m) → n + (m - n) ≡ m
≤-lem zero m pf = refl
≤-lem (suc n) (suc m) (s≤ pf) = ≡-cong suc (≤-lem n m pf)

≤-prop : {n m : ℕ} (p q : n ≤ m) → p ≡ q
≤-prop = _

--------------------------------------------------------------------------------
-- Every upper set is isomorphic to Nat
--------------------------------------------------------------------------------

AtLeast : ℕ → Set
AtLeast n = Σ (λ m → (n ≤ m))

f : {n : ℕ} → AtLeast n → ℕ
f {n} (m , pf) = m - n

g : {n : ℕ} → ℕ → AtLeast n
g {n} m = ((n + m) , ≤-+ n m)

fg-id : {n : ℕ} (m : ℕ) → f {n} (g {n} m) ≡ m
fg-id {n} m = +-- n m

gf-id : {n : ℕ} (m,p : AtLeast n) → g {n} (f {n} m,p) ≡ m,p
gf-id {n} (m , pf) = Σ-eq (≤-lem n m pf , _) --(≤-prop pf (≤-+ n (n + (m - n))))

{-
--------------------------------------------------------------------------------
-- suc is a bijection on upper sets
--------------------------------------------------------------------------------

f : {n : ℕ} → AtLeast n → AtLeast (suc n)
f (m , pf) = (suc m , s≤ pf)

g : {n : ℕ} → AtLeast (suc n) → AtLeast n
g (m , pf) = _
-}
