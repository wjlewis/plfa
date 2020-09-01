module plfa.part1.DotPatterns where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)

data Square : (m : ℕ) → Set where
  sq : (m : ℕ) → Square (m * m)

root : (n : ℕ)
     → Square n
       --------
     → ℕ
-- By matching `(sq m)` against `Square n`, we are able to determine
-- that `n` must have the form `m * m`.
root .(m * m) (sq m) = m
