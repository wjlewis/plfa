module plfa.part1.Connectives where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import plfa.part1.Isomorphism using (_≃_; _≲_; extensionality)
open plfa.part1.Isomorphism.≃-Reasoning

infixr 2 _×_
data _×_ (A B : Set) : Set where
  ⟨_,_⟩ : A
        → B
          -----
        → A × B

proj₁ : ∀ {A B}
      → A × B
        -----
      → A
proj₁ ⟨ M , _ ⟩ = M

proj₂ : ∀ {A B}
      → A × B
        -----
      → B
proj₂ ⟨ _ , N ⟩ = N

η-× : ∀ {A B}
    → (w : A × B)
      -------------------------
    → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ M , N ⟩ = refl

×-comm : ∀ {A B}
         --------------
       → A × B ≃ B × A
×-comm =
  record
    { to = λ{ ⟨ x , y ⟩ → ⟨ y , x ⟩ }
    ; from = λ{ ⟨ y , x ⟩ → ⟨ x , y ⟩ }
    ; from∘to = λ{ ⟨ x , y ⟩ → refl }
    ; to∘from = λ{ ⟨ y , x ⟩ → refl }
    }

×-assoc : ∀ {A B C}
          -------------------------
        → (A × B) × C ≃ A × (B × C)
×-assoc =
  record
    { to = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩ }
    ; from = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩ }
    ; from∘to = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → refl }
    ; to∘from = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → refl }
    }

data ⊤ : Set where
  tt : ⊤

η-⊤ : (w : ⊤) → tt ≡ w
η-⊤ tt = refl

⊤-identityˡ : ∀ {A}
             ----------
           → ⊤ × A ≃ A
⊤-identityˡ =
  record
    { to = λ{ ⟨ tt , y ⟩ → y }
    ; from = λ y → ⟨ tt , y ⟩
    ; from∘to = λ{ ⟨ tt , y ⟩ → refl }
    ; to∘from = λ y → refl
    }

⊤-identityʳ : ∀ {A}
             ---------
           → A × ⊤ ≃ A
⊤-identityʳ {A} =
  ≃-begin
    (A × ⊤)
  ≃⟨ ×-comm ⟩
    (⊤ × A)
  ≃⟨ ⊤-identityˡ ⟩
    A
  ≃-∎

infixr 1 _⊎_
data _⊎_ (A B : Set) : Set where
  injₗ : A
        -----
      → A ⊎ B

  injᵣ : B
        -----
      → A ⊎ B

case-⊎ : {A B C : Set}
       → (A → C)
       → (B → C)
       → A ⊎ B
         -----
       → C
case-⊎ A→C _ (injₗ A) = A→C A
case-⊎ _ B→C (injᵣ B) = B→C B

η-⊎ : ∀ {A B}
    → (w : A ⊎ B)
      ---------------------
    → case-⊎ injₗ injᵣ w ≡ w
η-⊎ (injₗ A) = refl
η-⊎ (injᵣ B) = refl

uniq-⊎ : {A B C : Set} (h : A ⊎ B → C)
       → (w : A ⊎ B)
       → case-⊎ (h ∘ injₗ) (h ∘ injᵣ) w ≡ h w
uniq-⊎ h (injₗ A) = refl
uniq-⊎ h (injᵣ B) = refl

data ⊥ : Set where

⊥-elim : {A : Set}
       → ⊥
         --
       → A
⊥-elim ()

uniq-⊥ : {C : Set}
       → (h : ⊥ → C)
       → (w : ⊥)
         --------------
       → ⊥-elim w ≡ h w
uniq-⊥ h ()

→-elim : {A B : Set}
       → (A → B)
       → A
         --
       → B
→-elim a→b a = a→b a

η-→ : {A B : Set}
    → (f : A → B)
      -----------------
    → (λ (x : A) → f x) ≡ f
η-→ f = refl

currying : {A B C : Set}
           ---------------------------
         → (A → (B → C)) ≃ (A × B → C)
currying =
  record
    { to = λ f → λ{ ⟨ x , y ⟩ → f x y }
    ; from = λ g → λ a b → g ⟨ a , b ⟩
    ; from∘to = λ f → refl
    ; to∘from = λ g → extensionality λ{ ⟨ x , y ⟩ → refl }
    }

→-distrib-⊎ : {A B C : Set}
            → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ =
  record
    { to = λ f → ⟨ f ∘ injₗ , f ∘ injᵣ ⟩
    ; from = λ{ ⟨ a→c , b→c ⟩ → λ{ (injₗ a) → a→c a; (injᵣ b) → b→c b }
              }
    ; from∘to = λ f → extensionality λ{ (injₗ a) → refl; (injᵣ b) → refl }
    ; to∘from = λ{ ⟨ a→c , b→c ⟩ → refl }
    }

→-distrib-× : {A B C : Set}
              --------------------------------
            → (A → B × C) ≃ (A → B) × (A → C)
→-distrib-× =
  record
    { to = λ f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩
    ; from = λ{ ⟨ fb , fc ⟩ → λ a → ⟨ fb a , fc a ⟩ }
    ; from∘to = λ f → extensionality (λ x → η-× (f x))
    ; to∘from = λ{ ⟨ fa , fb ⟩ → refl }
    }

×-distrib-⊎ : {A B C : Set}
              ----------------------------
            → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
×-distrib-⊎ =
  record
    { to = λ{ ⟨ injₗ a , c ⟩ → injₗ ⟨ a , c ⟩
            ; ⟨ injᵣ b , c ⟩ → injᵣ ⟨ b , c ⟩
            }
    ; from = λ{ (injₗ ⟨ a , c ⟩) → ⟨ injₗ a , c ⟩
              ; (injᵣ ⟨ b , c ⟩) → ⟨ injᵣ b , c ⟩
              }
    ; from∘to = λ{ ⟨ injₗ a , c ⟩ → refl
                 ; ⟨ injᵣ b , c ⟩ → refl
                 }
    ; to∘from = λ{ (injₗ ⟨ a , c ⟩) → refl
                 ; (injᵣ ⟨ b , c ⟩) → refl
                 }
    }

⊎-distrib-× : {A B C : Set}
              -------------------------------
            → (A × B) ⊎ C ≲ (A ⊎ C) × (B ⊎ C)
⊎-distrib-× =
  record
    { to = λ{ (injₗ ⟨ a , b ⟩) → ⟨ injₗ a , injₗ b ⟩
            ; (injᵣ c) → ⟨ injᵣ c , injᵣ c ⟩
            }
    ; from = λ{ ⟨ injₗ a , injₗ b ⟩ → injₗ ⟨ a , b ⟩
              ; ⟨ injₗ a , injᵣ c ⟩ → injᵣ c
              ; ⟨ injᵣ c , _ ⟩ → injᵣ c
              }
    ; from∘to = λ{ (injₗ ⟨ a , b ⟩) → refl
                 ; (injᵣ c) → refl
                 }
    }
