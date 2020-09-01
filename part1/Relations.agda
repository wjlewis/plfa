module plfa.part1.Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm; +-identityʳ)

-- Does `_≤_` capture our notion of "less than or equal"?
-- Our definition says the following:
-- 1. We have evidence that zero is less than or equal to any number
-- 2. If `m` and `n` are numbers, given evidence that `m` is leq to
--    `n`, we have evidence that `m + 1` is leq to `n + 1`.
infix 4 _≤_
data _≤_ : (m n : ℕ) → Set where
  z≤n : ∀ {n}
       ---------
     → zero ≤ n

  s≤s : ∀ {m n}
     → m ≤ n
       --------------
     → suc m ≤ suc n

-- `_≤_` is reflexive since
--
-- -----------
-- zero ≤ zero
--
-- And
--
-- m ≤ m
-- -------------
-- suc m ≤ suc m
≤-refl : {m : ℕ}
         ------
       → m ≤ m
≤-refl {zero} = z≤n
≤-refl {suc m} = s≤s (≤-refl {m})

-- `_≤_` is transitive since
--
-- zero ≤ n
-- n ≤ p
-- --------
-- zero ≤ p
--
-- And
--
-- m ≤ n
-- n ≤ p
-- -------------
-- suc m ≤ suc p
≤-trans : {m n p : ℕ}
        → m ≤ n
        → n ≤ p
          ------
        → m ≤ p
≤-trans z≤n       n≤p       = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

≤-antisym : {m n : ℕ}
          → m ≤ n
          → n ≤ m
            -------
          → m ≡ n
≤-antisym z≤n       z≤n       = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)

data ≤-Total (m n : ℕ) : Set where
  forward : m ≤ n
           ------------
         → ≤-Total m n

  flipped : n ≤ m
           ------------
         → ≤-Total m n

≤-total : (m n : ℕ) → ≤-Total m n
≤-total zero _ = forward z≤n
≤-total _ zero = flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
...                        | forward m≤n = forward (s≤s m≤n)
...                        | flipped n≤m = flipped (s≤s n≤m)

+-monoʳ-≤ : (n p q : ℕ)
         → p ≤ q
           --------------
         → n + p ≤ n + q
+-monoʳ-≤ zero    p q p≤q = p≤q
+-monoʳ-≤ (suc n) p q p≤q = s≤s (+-monoʳ-≤ n p q p≤q)

+-monoˡ-≤ : (m n p : ℕ)
         → m ≤ n
           --------------
         → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n rewrite (+-comm m p) | (+-comm n p) = +-monoʳ-≤ p m n m≤n

+-mono-≤ : (m n p q : ℕ)
         → m ≤ n
         → p ≤ q
           --------------
         → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q = let m+p≤n+p = +-monoˡ-≤ m n p m≤n
                               n+p≤n+q = +-monoʳ-≤ n p q p≤q
                           in ≤-trans m+p≤n+p n+p≤n+q

infix 4 _<_
data _<_ : ℕ → ℕ → Set where
  z<s : {n : ℕ}
       -------------
     → zero < suc n

  s<s : {m n : ℕ}
     → m < n
       --------------
     → suc m < suc n

data even : ℕ → Set
data odd : ℕ → Set

data even where
        -----------
  zero : even zero

  suc : {n : ℕ}
     → odd n
       -------------
     → even (suc n)

data odd where
  suc : {n : ℕ}
     → even n
       ------------
     → odd (suc n)

e+e≡e : {m n : ℕ}
      → even m
      → even n
        -------------
      → even (m + n)

o+e≡o : {m n : ℕ}
      → odd m
      → even n
      → odd (m + n)

e+e≡e zero      en = en
e+e≡e (suc om) en = suc (o+e≡o om en)

o+e≡o (suc em) en = suc (e+e≡e em en)
