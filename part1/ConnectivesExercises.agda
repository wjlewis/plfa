module plfa.part1.ConnectivesExercises where

open import Relation.Binary.PropositionalEquality using (refl)
open import plfa.part1.Isomorphism using (_≃_)
open plfa.part1.Isomorphism.≃-Reasoning
open import plfa.part1.IsomorphismExercises using (_⇔_)
open import plfa.part1.Connectives using (_×_; ⟨_,_⟩; _⊎_; injₗ; injᵣ; case-⊎; ⊥)

open _⇔_

⇔≃× : ∀ {A B}
     → A ⇔ B
       ---------------
     → (A → B) × (B → A)
⇔≃× A⇔B = ⟨ to A⇔B , from A⇔B ⟩

⊎-comm : ∀ {A B}
         -------------
       → A ⊎ B ≃ B ⊎ A
⊎-comm =
  record
    { to = λ{ (injₗ a) → injᵣ a
            ; (injᵣ b) → injₗ b
            }
    ; from = λ{ (injᵣ a) → injₗ a
              ; (injₗ b) → injᵣ b
              }
    ; from∘to = λ{ (injₗ a) → refl
                 ; (injᵣ b) → refl
                 }
    ; to∘from = λ{ (injᵣ a) → refl
                 ; (injₗ b) → refl
                 }
    }

⊎-assoc : ∀ {A B C}
          -------------------------
        → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc =
  record
    { to = λ{ (injₗ (injₗ a)) → injₗ a
            ; (injₗ (injᵣ b)) → injᵣ (injₗ b)
            ; (injᵣ c) → injᵣ (injᵣ c)
            }
    ; from = λ{ (injₗ a) → injₗ (injₗ a)
              ; (injᵣ (injₗ b)) → injₗ (injᵣ b)
              ; (injᵣ (injᵣ c)) → injᵣ c
              }
    ; from∘to = λ{ (injₗ (injₗ a)) → refl
                 ; (injₗ (injᵣ b)) → refl
                 ; (injᵣ c) → refl
                 }
    ; to∘from = λ{ (injₗ a) → refl
                 ; (injᵣ (injₗ b)) → refl
                 ; (injᵣ (injᵣ c)) → refl
                 }
    }

⊥-identityˡ : ∀ {A}
             ---------
           → ⊥ ⊎ A ≃ A
⊥-identityˡ =
  record
    { to = λ{ (injₗ ())
            ; (injᵣ a) → a
            }
    ; from = injᵣ
    ; from∘to = λ{ (injₗ ())
                 ; (injᵣ a) → refl
                 }
    ; to∘from = λ a → refl
    }

⊥-identityʳ : ∀ {A}
             ---------
           → A ⊎ ⊥ ≃ A
⊥-identityʳ {A} =
  ≃-begin
    (A ⊎ ⊥)
  ≃⟨ ⊎-comm ⟩
    (⊥ ⊎ A)
  ≃⟨ ⊥-identityˡ ⟩
    A
  ≃-∎

⊎-weak-× : {A B C : Set}
         → (A ⊎ B) × C
           -----------
         → A ⊎ (B × C)
⊎-weak-× ⟨ injₗ a , c ⟩ = injₗ a
⊎-weak-× ⟨ injᵣ b , c ⟩ = injᵣ ⟨ b , c ⟩

⊎×-implies-×⊎ : {A B C D : Set}
              → (A × B) ⊎ (C × D)
                -----------------
              → (A ⊎ C) × (B ⊎ D)
⊎×-implies-×⊎ (injₗ ⟨ a , b ⟩) = ⟨ injₗ a , injₗ b ⟩
⊎×-implies-×⊎ (injᵣ ⟨ c , d ⟩) = ⟨ injᵣ c , injᵣ d ⟩

×⊎-not-implies-⊎× : {A B C D : Set}
                  → (A ⊎ C) × (B ⊎ D)
                  → (A × B) ⊎ (C × D)
                    -----------------
                  → ⊥
×⊎-not-implies-⊎× f = {!!}
