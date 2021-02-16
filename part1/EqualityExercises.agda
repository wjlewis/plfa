module plfa.part1.EqualityExercises where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)

infix 4 _≤_
data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n}
        --------
      → zero ≤ n

  s≤s : ∀ {m n}
      → m ≤ n
        -------------
      → suc m ≤ suc n

≤-trans : {m n p : ℕ}
        → m ≤ n
        → n ≤ p
          -----
        → m ≤ p
≤-trans z≤n _ = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

module ≤-Reasoning where
  infix  1 begin_
  infixr 2 _≤⟨⟩_ _≤⟨_⟩_
  infix  3 _∎

  begin_ : {m n : ℕ}
         → m ≤ n
           -----
         → m ≤ n
  begin m≤n = m≤n

  _≤⟨⟩_ : (m : ℕ) → {n : ℕ}
        → m ≤ n
          -----
        → m ≤ n
  m ≤⟨⟩ m≤n = m≤n

  _≤⟨_⟩_ : (m : ℕ) → {n p : ℕ}
         → m ≤ n
         → n ≤ p
           -----
         → m ≤ p
  m ≤⟨ m≤n ⟩ n≤p = ≤-trans m≤n n≤p

  _∎ : (m : ℕ)
       -----
     → m ≤ m
  zero ∎ = z≤n
  (suc m) ∎ = s≤s (m ∎)

open ≤-Reasoning

+-monoʳ-≤ : (n p q : ℕ)
         → p ≤ q
           -------------
         → n + p ≤ n + q
+-monoʳ-≤ zero _ _ p≤q = p≤q
+-monoʳ-≤ (suc n) p q p≤q =
  begin
    suc n + p
  ≤⟨⟩
    suc (n + p)
  ≤⟨ s≤s (+-monoʳ-≤ n p q p≤q) ⟩
    suc (n + q)
  ≤⟨⟩
    suc n + q
  ∎

+-monoˡ-≤ : (m n p : ℕ)
         → m ≤ n
           -------------
         → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n rewrite +-comm m p | +-comm n p = +-monoʳ-≤ p m n m≤n

+-mono-≤ : (m n p q : ℕ)
         → m ≤ n
         → p ≤ q
         → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q =
  begin
    m + p
  ≤⟨ +-monoˡ-≤ m n p m≤n ⟩
    n + p
  ≤⟨ +-monoʳ-≤ n p q p≤q ⟩
    n + q
  ∎
