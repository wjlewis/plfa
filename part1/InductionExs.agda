module plfa.part1.InductionExs where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (refl; _≡_; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _*_; _^_)
open import plfa.part1.Induction using (+-assoc; +-comm; +-identityʳ)

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
    (p + m * p) + n * p
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

*-zeroʳ : (m : ℕ) → m * zero ≡ zero
*-zeroʳ zero = refl
*-zeroʳ (suc m) =
  begin
    suc m * zero
  ≡⟨⟩
    zero + m * zero
  ≡⟨⟩
    m * zero
  ≡⟨ *-zeroʳ m ⟩
    zero
  ∎

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
    suc (n + m) + m * n
  ≡⟨ cong (_+ (m * n)) (cong suc (+-comm n m)) ⟩
    suc (m + n) + m * n
  ≡⟨⟩
    suc m + n + m * n
  ≡⟨ +-assoc (suc m) n (m * n) ⟩
    suc m + (n + m * n)
  ≡⟨⟩
    suc m + suc m * n
  ∎

*-comm : (m n : ℕ) → m * n ≡ n * m
*-comm m zero =
  begin
    m * zero
  ≡⟨ *-zeroʳ m ⟩
    zero
  ≡⟨⟩
    zero * m
  ∎
*-comm m (suc n) =
  begin
    m * suc n
  ≡⟨ *-suc m n ⟩
    m + m * n
  ≡⟨ cong (m +_) (*-comm m n) ⟩
    m + n * m
  ≡⟨⟩
    suc n * m
  ∎

0∸n≡0 : (m : ℕ) → zero ∸ m ≡ zero
0∸n≡0 zero = refl
0∸n≡0 (suc m) = refl

∸-+-assoc : (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc m zero p = refl
∸-+-assoc zero (suc n) p =
  begin
    zero ∸ suc n ∸ p
  ≡⟨ cong (_∸ p) (0∸n≡0 (suc n)) ⟩
    zero ∸ p
  ≡⟨ 0∸n≡0 p ⟩
    zero
  ≡⟨ sym (0∸n≡0 (suc n + p)) ⟩
    zero ∸ (suc n + p)
  ∎
∸-+-assoc (suc m) (suc n) p =
  begin
    suc m ∸ suc n ∸ p
  ≡⟨⟩
    m ∸ n ∸ p
  ≡⟨ ∸-+-assoc m n p ⟩
    m ∸ (n + p)
  ≡⟨⟩
    suc m ∸ suc (n + p)
  ≡⟨⟩
    suc m ∸ (suc n + p)
  ∎

*-identity : (m : ℕ) → 1 * m ≡ m
*-identity zero = refl
*-identity (suc m) =
  begin
    1 * suc m
  ≡⟨⟩
    suc m + zero * suc m
  ≡⟨ +-identityʳ (suc m) ⟩
    suc m
  ∎

^-distribˡ-+-* : (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distribˡ-+-* m zero p =
  begin
    m ^ (zero + p)
  ≡⟨⟩
    m ^ p
  ≡⟨ sym (*-identity (m ^ p)) ⟩
    1 * m ^ p
  ≡⟨⟩
    m ^ zero * m ^ p
  ∎
^-distribˡ-+-* m (suc n) p =
  begin
    m ^ (suc n + p)
  ≡⟨⟩
    m ^ suc (n + p)
  ≡⟨⟩
    m * m ^ (n + p)
  ≡⟨ cong (m *_) (^-distribˡ-+-* m n p) ⟩
    m * (m ^ n * m ^ p)
  ≡⟨ sym (*-assoc m (m ^ n) (m ^ p)) ⟩
    m * m ^ n * m ^ p
  ≡⟨⟩
    m ^ suc n * m ^ p
  ∎

*-rearrange : (m n p q : ℕ) → (m * n) * (p * q) ≡ (m * p) * (n * q)
*-rearrange m n p q =
  begin
    (m * n) * (p * q)
  ≡⟨ *-assoc m n (p * q) ⟩
    m * (n * (p * q))
  ≡⟨ cong (m *_) (sym (*-assoc n p q)) ⟩
    m * ((n * p) * q)
  ≡⟨ cong (m *_) (cong (_* q) (*-comm n p)) ⟩
    m * ((p * n) * q)
  ≡⟨ sym (*-assoc m (p * n) q) ⟩
    (m * (p * n)) * q
  ≡⟨ cong (_* q) (sym (*-assoc m p n)) ⟩
    ((m * p) * n) * q
  ≡⟨ *-assoc (m * p) n q ⟩
    (m * p) * (n * q)
  ∎

^-distribʳ-* : (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distribʳ-* m n zero = refl
^-distribʳ-* m n (suc p) =
  begin
    (m * n) ^ suc p
  ≡⟨⟩
    (m * n) * (m * n) ^ p
  ≡⟨ cong ((m * n) *_) (^-distribʳ-* m n p) ⟩
    (m * n) * ((m ^ p) * (n ^ p))
  ≡⟨ *-rearrange m n (m ^ p) (n ^ p) ⟩
    (m * m ^ p) * (n * n ^ p)
  ≡⟨⟩
    (m ^ suc p) * (n ^ suc p)
  ∎

^-*-assoc : (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
^-*-assoc m n zero =
  begin
    (m ^ n) ^ zero
  ≡⟨⟩
    1
  ≡⟨⟩
    m ^ zero
  ≡⟨ cong (m ^_) (sym (*-zeroʳ n)) ⟩
    m ^ (n * zero)
  ∎
^-*-assoc m n (suc p) =
  begin
    (m ^ n) ^ suc p
  ≡⟨⟩
    m ^ n * (m ^ n) ^ p
  ≡⟨ cong (m ^ n *_) (^-*-assoc m n p) ⟩
    m ^ n * m ^ (n * p)
  ≡⟨ sym (^-distribˡ-+-* m n (n * p)) ⟩
    m ^ (n + n * p)
  ≡⟨ cong (m ^_) (sym (*-suc n p)) ⟩
    m ^ (n * suc p)
  ∎
