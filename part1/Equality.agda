module plfa.part1.Equality where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)

infix 4 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

sym : ∀ {A} {x y : A}
    → x ≡ y
      -----
    → y ≡ x
sym refl = refl

trans : ∀ {A} {x y z : A}
      → x ≡ y
      → y ≡ z
        -----
      → x ≡ z
trans refl refl = refl

cong : ∀ {A B} → (f : A → B) → {x y : A}
     → x ≡ y
       -------------
     → f x ≡ f y
cong _ refl = refl

cong₂ : ∀ {A B C} → (f : A → B → C) → {u x : A} → {v y : B}
     → u ≡ x
     → v ≡ y
       -------------
     → f u v ≡ f x y
cong₂ _ refl refl = refl

cong-app : ∀ {A B} → {f g : A → B}
         → f ≡ g
           ---------------------
         → (x : A) → f x ≡ g x
cong-app refl = λ x → refl

subst : ∀ {A} → {x y : A} → (P : A → Set)
      → x ≡ y
      → P x
        -----
      → P y
subst P refl px = px

module ≡-Reasoning {A : Set} where

  infix  1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  3 _∎

  begin_ : {x y : A}
         → x ≡ y
           -----
         → x ≡ y
  begin_ x≡y = x≡y

  _≡⟨⟩_ : (x : A) {y : A}
        → x ≡ y
        → x ≡ y
  x ≡⟨⟩ x≡y = x≡y

  _≡⟨_⟩_ : (x : A) {y z : A}
         → x ≡ y
         → y ≡ z
           -----
         → x ≡ z
  x ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

  _∎ : (x : A)
       -----
     → x ≡ x
  x ∎ = refl

open ≡-Reasoning

trans' : {A : Set} {x y z : A}
       → x ≡ y
       → y ≡ z
         -----
       → x ≡ z
trans' {_} {x} {y} {z} x≡y y≡z =
  begin
    x
  ≡⟨ x≡y ⟩
    y
  ≡⟨ y≡z ⟩
    z
  ∎

_≐_ : {A : Set} → (x y : A) → Set₁
_≐_ {A} x y = (P : A → Set) → P x → P y

refl-≐ : {A : Set} {x : A} → x ≐ x
refl-≐ P Px = Px

trans-≐ : {A : Set} {x y z : A}
        → x ≐ y
        → y ≐ z
          -----
        → x ≐ z
trans-≐ x≐y y≐z P Px = y≐z P (x≐y P Px)

sym-≐ : {A : Set} {x y : A}
      → x ≐ y
        -----
      → y ≐ x
sym-≐ {A} {x} {y} x≐y P = Qy
  where
    Q : A → Set
    Q z = P z → P x

    Qx : Q x
    Qx = refl-≐ P

    Qy : Q y
    Qy = x≐y Q Qx

≡⇒≐ : {A : Set} {x y : A}
    → x ≡ y
      -----
    → x ≐ y
≡⇒≐ x≡y P = subst P x≡y

≐⇒≡ : {A : Set} {x y : A}
    → x ≐ y
      -----
    → x ≡ y
≐⇒≡ {A} {x} {y} x≐y = Qy
  where
    Q : A → Set
    Q z = x ≡ z

    Qx : Q x
    Qx = refl

    Qy : Q y
    Qy = x≐y Q Qx

data _≡′_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl′ : x ≡′ x

sym′ : ∀ {ℓ} {A : Set ℓ} {x y : A}
    → x ≡′ y
      ------
    → y ≡′ x
sym′ refl′ = refl′
