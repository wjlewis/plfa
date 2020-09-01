module plfa.part1.≤-Reasoning where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
open import plfa.part1.Relations using (_≤_; z≤n; s≤s; ≤-trans)

infix  1 begin_
infixr 2 _≤⟨⟩_ _≤⟨_⟩_
infix  3 _∎

-- We can't prove an analagous `cong` for `_≤_` in general, but
-- we can for a limited collection of functions, like `suc`:
cong-suc : {m n : ℕ}
        → m ≤ n
          --------------
        → suc m ≤ suc n
cong-suc m≤n = s≤s m≤n

≡-⊆-≤ : {m n : ℕ}
       → m ≡ n
         ------
       → m ≤ n
≡-⊆-≤ {zero} _ = z≤n
≡-⊆-≤ {suc m} {suc n} refl = s≤s (≡-⊆-≤ {m} {n} refl)

begin_ : {m n : ℕ}
      → m ≤ n
        ------
      → m ≤ n
begin m≤n = m≤n

_≤⟨⟩_ : (m : ℕ) {n : ℕ}
     → m ≤ n
       ------
     → m ≤ n
m ≤⟨⟩ m≤n = m≤n

_≤⟨_⟩_ : (m : ℕ) {n p : ℕ}
      → m ≤ n
      → n ≤ p
        ------
      → m ≤ p
m ≤⟨ m≤n ⟩ n≤p = ≤-trans m≤n n≤p

_∎ : (m : ℕ)
    ------
  → m ≤ m
m ∎ = ≡-⊆-≤ refl


≤-monoʳ-+ : (n p q : ℕ)
         → p ≤ q
           --------------
         → n + p ≤ n + q
≤-monoʳ-+ zero    p q p≤q = p≤q
≤-monoʳ-+ (suc n) p q p≤q =
  begin
    suc n + p
  ≤⟨⟩
    suc (n + p)
  ≤⟨ cong-suc (≤-monoʳ-+ n p q p≤q) ⟩
    suc (n + q)
  ≤⟨⟩
    suc n + q
  ∎

≤-monoˡ-+ : (m n p : ℕ)
         → m ≤ n
           --------------
         → m + p ≤ n + p
≤-monoˡ-+ m n p m≤n =
  begin
    m + p
  ≤⟨ ≡-⊆-≤ (+-comm m p) ⟩
    p + m
  ≤⟨ ≤-monoʳ-+ p m n m≤n ⟩
    p + n
  ≤⟨ ≡-⊆-≤ (+-comm p n) ⟩
    n + p
  ∎

≤-mono-+ : (m n p q : ℕ)
        → m ≤ n
        → p ≤ q
          --------------
        → m + p ≤ n + q
≤-mono-+ m n p q m≤n p≤q =
  begin
    m + p
  ≤⟨ ≤-monoˡ-+ m n p m≤n ⟩
    n + p
  ≤⟨ ≤-monoʳ-+ n p q p≤q ⟩
    n + q
  ∎
