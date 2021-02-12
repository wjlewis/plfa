module plfa.part1.InductionExercises where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)
open import Data.Nat.Properties using (+-assoc; +-comm; +-identityʳ; +-suc)
open import plfa.part1.NaturalsExercises using (Bin; ⟨⟩; _O; _I; inc; to; from)

+-swap : (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p =
  begin
    m + (n + p)
  ≡⟨ sym (+-assoc m n p) ⟩
    (m + n) + p
  ≡⟨ cong (_+ p) (+-comm m n) ⟩
    (n + m) + p
  ≡⟨ +-assoc n m p ⟩
    n + (m + p)
  ∎

+-swap' : (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap' m n p rewrite sym (+-assoc m n p) | cong (_+ p) (+-comm m n) | +-assoc n m p = refl

*-distrib-+ : (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p =
  begin
    (suc m + n) * p
  ≡⟨⟩
    suc (m + n) * p
  ≡⟨⟩
    p + (m + n) * p
  ≡⟨ cong (p +_) (*-distrib-+ m n p) ⟩
    p + (m * p + n * p)
  ≡⟨ sym (+-assoc p (m * p) (n * p)) ⟩
    p + m * p + n * p
  ≡⟨⟩
    suc m * p + n * p
  ∎

*-assoc : (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p =
  begin
    (suc m * n) * p
  ≡⟨⟩
    (n + m * n) * p
  ≡⟨ *-distrib-+ n (m * n) p ⟩
    n * p + (m * n) * p
  ≡⟨ cong ((n * p) +_) (*-assoc m n p) ⟩
    n * p + m * (n * p)
  ≡⟨⟩
    suc m * (n * p)
  ∎

*-zero : (m : ℕ) → m * zero ≡ zero
*-zero zero = refl
*-zero (suc m) rewrite *-zero m = refl

*-suc : (m n : ℕ) → m * suc n ≡ m + m * n
*-suc zero n = refl
*-suc (suc m) n =
  begin
    suc m * suc n
  ≡⟨⟩
    suc n + m * suc n
  ≡⟨ cong (suc n +_) (*-suc m n) ⟩
    suc n + (m + m * n)
  ≡⟨ sym (+-assoc (suc n) m (m * n)) ⟩
    suc n + m + m * n
  ≡⟨⟩
    suc (n + m + m * n)
  ≡⟨ cong suc (+-rearrange n m (m * n)) ⟩
    suc (m + n + m * n)
  ≡⟨⟩
    suc m + n + m * n
  ≡⟨ +-assoc (suc m) n (m * n) ⟩
    suc m + (n + m * n)
  ≡⟨⟩
    suc m + suc m * n
  ∎
  where
    +-rearrange : (m n p : ℕ) → m + n + p ≡ n + m + p
    +-rearrange m n p rewrite +-comm m n = refl

*-comm : (m n : ℕ) → m * n ≡ n * m
*-comm m zero = *-zero m
*-comm m (suc n) =
  begin
    m * suc n
  ≡⟨ *-suc m n ⟩
    m + m * n
  ≡⟨ cong (m +_) (*-comm m n) ⟩
    m + (n * m)
  ≡⟨⟩
    suc n * m
  ∎

0∸n≡0 : (n : ℕ) → 0 ∸ n ≡ 0
0∸n≡0 zero = refl
0∸n≡0 (suc n) = refl

∸-+-assoc : (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc m zero p = refl
∸-+-assoc zero (suc n) p = 0∸n≡0 p
∸-+-assoc (suc m) (suc n) p rewrite ∸-+-assoc m n p = refl

twice≡double : (m : ℕ) → 2 * m ≡ m + m
twice≡double m =
  begin
    2 * m
  ≡⟨⟩
    suc (suc zero) * m
  ≡⟨⟩
    m + (suc zero) * m
  ≡⟨⟩
    m + (m + zero * m)
  ≡⟨⟩
    m + (m + zero)
  ≡⟨ cong (m +_) (+-identityʳ m) ⟩
    m + m
  ∎

_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
f ∘ g = λ x → f (g x)

from-homo : (b : Bin) → from (inc b) ≡ suc (from b)
from-homo ⟨⟩ = refl
from-homo (b O) =
  begin
    from (inc (b O))
  ≡⟨⟩
    from (b I)
  ≡⟨⟩
    1 + 2 * from b
  ≡⟨⟩
    1 + from (b O)
  ≡⟨⟩
    suc (from (b O))
  ∎
from-homo (b I) =
  begin
    from (inc (b I))
  ≡⟨⟩
    from ((inc b) O)
  ≡⟨⟩
    2 * from (inc b)
  ≡⟨ cong (2 *_) (from-homo b) ⟩
    2 * suc (from b)
  ≡⟨ twice≡double (suc (from b)) ⟩
    suc (from b) + suc (from b)
  ≡⟨⟩
    suc (from b + suc (from b))
  ≡⟨ cong suc (+-suc (from b) (from b)) ⟩
    suc (suc (from b + from b))
  ≡⟨ cong (suc ∘ suc) (sym (twice≡double (from b))) ⟩
    suc (from (b I))
  ∎

-- to (from b) ‌‌≢ b
-- Consider:
-- ```
-- to (from (⟨⟩ O)) ≡ to 0 ≡ ⟨⟩ ≢ ⟨⟩ O
-- ```

from-to-inv : (m : ℕ) → from (to m) ≡ m
from-to-inv zero = refl
from-to-inv (suc m) =
  begin
    from (to (suc m))
  ≡⟨⟩
    from (inc (to m))
  ≡⟨ from-homo (to m) ⟩
    suc (from (to m))
  ≡⟨ cong suc (from-to-inv m) ⟩
    suc m
  ∎
