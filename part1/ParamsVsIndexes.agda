module plfa.part1.ParamsVsIndexes where

open import Data.Nat using (ℕ; zero; suc)

infixr 4 _∷_

-- Here is a type for polymorphic lists:
data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

-- We could create a similar type for lists of length zero:
data List0 (A : Set) : Set where
  []  : List0 A

-- And one for lists of length one:
data List1 (A : Set) : Set where
  [] : List1 A
  _∷_ : A → List0 A → List1 A

-- And one for lists of length two:
data List2 (A : Set) : Set where
  [] : List2 A
  _∷_ : A → List1 A → List2 A

-- for instance:
l1 : List2 ℕ
l1 = 1 ∷ 2 ∷ []

-- but not
-- l2 : List2 ℕ
-- l2 = 1 ∷ 2 ∷ 3 ∷ []

-- We could continue to create these closely related types,
-- `List3`, `List4`, etc.
-- However, we can also recognize that these types form a
-- "family" of sorts: `List2` is just like `List1`, except
-- its `_∷_` adds an element to the from of a `List1`, and
-- not a `List0`. We can express this as follows:
data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  _∷_ : {l : ℕ} → A → Vec A l → Vec A (suc l)
