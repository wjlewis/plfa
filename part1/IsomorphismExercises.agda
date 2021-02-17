module plfa.part1.IsomorphismExercises where

open import Data.Nat using (ℕ)
open import plfa.part1.Isomorphism using (_≃_; _≲_; _∘_)
open import plfa.part1.NaturalsExercises renaming (from to from-Bin; to to to-Bin)
open import plfa.part1.InductionExercises hiding (_∘_)

open _≃_
open _≲_

≃-implies-≲ : {A B : Set}
             → A ≃ B
               ------
             → A ≲ B
≃-implies-≲ A≃B =
  record
    { to = to A≃B
    ; from = from A≃B
    ; from∘to = from∘to A≃B
    }

record _⇔_ (A B : Set) : Set where
  field
    to : A → B
    from : B → A
open _⇔_

⇔-refl : {A : Set}
         -----
       → A ⇔ A
⇔-refl =
  record
    { to = λ x → x
    ; from = λ y → y
    }

⇔-sym : {A B : Set}
      → A ⇔ B
        -----
      → B ⇔ A
⇔-sym A⇔B =
  record
    { to = from A⇔B
    ; from = to A⇔B
    }

⇔-trans : {A B C : Set}
        → A ⇔ B
        → B ⇔ C
          -----
        → A ⇔ C
⇔-trans A⇔B B⇔C =
  record
    { to = to B⇔C ∘ to A⇔B
    ; from = from A⇔B ∘ from B⇔C
    }

ℕ≲Bin : ℕ ≲ Bin
ℕ≲Bin =
  record
    { to = to-Bin
    ; from = from-Bin
    ; from∘to = from-to-inv
    }
