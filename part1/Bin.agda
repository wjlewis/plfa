module plfa.part1.Bin where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩    = ⟨⟩ I
inc (n O) = n I
inc (n I) = (inc n) O

to : ℕ → Bin
to zero    = ⟨⟩ O
to (suc m) = inc (to m)

from : Bin → ℕ
from ⟨⟩ = zero
from (n O) = 2 * from n
from (n I) = 1 + 2 * from n

-- `from` is a homomorphism from `Bin` to `ℕ`
from-homo : (b : Bin) → from (inc b) ≡ suc (from b)
from-homo ⟨⟩ = refl
from-homo (b O) = refl
from-homo (b I) = {!!}

-- `to` is an inverse for `from`
to-inv-from : (b : Bin) → to (from b) ≡ b
to-inv-from = {!!}

-- `from` is an inverse for `to`
from-inv-to : (n : ℕ) → from (to n) ≡ n
from-inv-to = {!!}

-- Testing `inc` (0-4)
_ : inc ⟨⟩ ≡ ⟨⟩ I
_ = refl

_ : inc (⟨⟩ I) ≡ ⟨⟩ I O
_ = refl

_ : inc (⟨⟩ I O) ≡ ⟨⟩ I I
_ = refl

_ : inc (⟨⟩ I I) ≡ ⟨⟩ I O O
_ = refl

_ : inc (⟨⟩ I O O) ≡ ⟨⟩ I O I
_ = refl

-- Testing `to` (0-4)
_ : to 0 ≡ ⟨⟩ O
_ = refl

_ : to 1 ≡ ⟨⟩ I
_ = refl

_ : to 2 ≡ ⟨⟩ I O
_ = refl

_ : to 3 ≡ ⟨⟩ I I
_ = refl

_ : to 4 ≡ ⟨⟩ I O O
_ = refl

-- Testing `from` (0-4)
_ : from ⟨⟩ ≡ 0
_ = refl

_ : from (⟨⟩ I) ≡ 1
_ = refl

_ : from (⟨⟩ I O) ≡ 2
_ = refl

_ : from (⟨⟩ I I) ≡ 3
_ = refl

_ : from (⟨⟩ I O O) ≡ 4
_ = refl
