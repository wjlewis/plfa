module plfa.part1.Rewrite where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning using (begin_; _∎; _≡⟨⟩_; _≡⟨_⟩_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ; +-suc)

+-comm : (m n : ℕ) → m + n ≡ n + m
+-comm m zero with  m + zero | +-identityʳ m
...              | .m        | refl          = refl
+-comm m (suc n) with   m + n  | +-comm m n |  m + suc n     | +-suc m n
...                 | .(n + m) | refl       | .(suc (n + m)) | refl      = refl

+-comm₁ : (m n : ℕ) → m + n ≡ n + m
+-comm₁ m zero    rewrite +-identityʳ m = refl
-- Why does the order of these two clauses matter?
+-comm₁ m (suc n) rewrite +-suc m n | +-comm₁ m n = refl
