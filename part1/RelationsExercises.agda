module plfa.part1.RelationsExercises where

open import plfa.part1.Relations
open import plfa.part1.NaturalsExercises
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; *-comm)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)

*-monoʳ-≤ : (n p q : ℕ)
         → p ≤ q
           -------------
         → n * p ≤ n * q
*-monoʳ-≤ zero p q p≤q = z≤n
*-monoʳ-≤ (suc n) p q p≤q with *-monoʳ-≤ n p q p≤q
...                         | n*p≤n*q = +-mono-≤ p q (n * p) (n * q) p≤q n*p≤n*q

*-monoˡ-≤ : (m n p : ℕ)
         → m ≤ n
         → m * p ≤ n * p
*-monoˡ-≤ m n p m≤n rewrite *-comm m p | *-comm n p = *-monoʳ-≤ p m n m≤n

*-mono-≤ : (m n p q : ℕ)
         → m ≤ n
         → p ≤ q
           -------------
         → m * p ≤ n * q
*-mono-≤ m n p q m≤n p≤q = ≤-trans (*-monoˡ-≤ m n p m≤n) (*-monoʳ-≤ n p q p≤q)

<-trans : ∀ {m n p}
        → m < n
        → n < p
          -----
        → m < p
<-trans z<s (s<s _) = z<s
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)

data WeakTrichotomy : ℕ → ℕ → Set where
  lt : ∀ {m n}
     → m < n
       ------------------
     → WeakTrichotomy m n

  eq : ∀ {m n}
     → m ≡ n
       ------------------
     → WeakTrichotomy m n
  gt : ∀ {m n}
     → n < m
       ------------------
     → WeakTrichotomy m n

<-WeakTrichotomy : (m n : ℕ)
                 → WeakTrichotomy m n
<-WeakTrichotomy zero zero = eq refl
<-WeakTrichotomy zero (suc _) = lt z<s
<-WeakTrichotomy (suc _) zero = gt z<s
<-WeakTrichotomy (suc m) (suc n) with <-WeakTrichotomy m n
...                                 | lt m<n = lt (s<s m<n)
...                                 | eq m≡n = eq (cong suc m≡n)
...                                 | gt n<m = gt (s<s n<m)

+-monoʳ-< : (n p q : ℕ)
         → p < q
           -------------
         → n + p < n + q
+-monoʳ-< zero p q p<q = p<q
+-monoʳ-< (suc n) p q p<q = s<s (+-monoʳ-< n p q p<q)

+-monoˡ-< : (m n p : ℕ)
         → m < n
           -------------
         → m + p < n + p
+-monoˡ-< m n p m<n rewrite +-comm m p | +-comm n p = +-monoʳ-< p m n m<n

+-mono-< : (m n p q : ℕ)
         → m < n
         → p < q
           -------------
         → m + p < n + q
+-mono-< m n p q m<n p<q = <-trans (+-monoˡ-< m n p m<n) (+-monoʳ-< n p q p<q)

<⇒s≤ : ∀ {m n}
    → m < n
      -----
    → suc m ≤ n
<⇒s≤ z<s = s≤s z≤n
<⇒s≤ (s<s m<n) = s≤s (<⇒s≤ m<n)

s≤⇒< : ∀ {m n}
    → suc m ≤ n
      ---------
    → m < n
s≤⇒< {zero} {suc n} _ = z<s
s≤⇒< {suc m} (s≤s sm≤n) = s<s (s≤⇒< sm≤n)

<⇒≤ : ∀ {m n}
    → m < n
      -----
    → m ≤ n
<⇒≤ z<s = z≤n
<⇒≤ (s<s m<n) = s≤s (<⇒≤ m<n)

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

infix 2 _↔_
_↔_ : (A B : Set) → Set
p ↔ q = (p → q) × (q → p)

s≤-iff-< : ∀ {m n} → (suc m ≤ n ↔ m < n)
s≤-iff-< = s≤⇒< , <⇒s≤

<-trans' : ∀ {m n p}
       → m < n
       → n < p
         -----
       → m < p
<-trans' m<n n<p = s≤⇒< (≤-trans (<⇒s≤ m<n) (<⇒≤ n<p))

o+o≡e : ∀ {m n}
      → odd m
      → odd n
        ------------
      → even (m + n)

e+o≡o : ∀ {m n}
      → even m
      → odd n
        -----------
      → odd (m + n)

o+o≡e (suc em) on = suc (e+o≡o em on)

e+o≡o zero on = on
e+o≡o (suc om) on = suc (o+o≡e om on)

data One : Bin → Set where
  one :
       ----------
       One (⟨⟩ I)

  _O : ∀ {b}
       → One b
         -----
       → One (b O)

  _I : ∀ {b}
     → One b
       ---------
     → One (b I)

data Can : Bin → Set where
  zero : Can ⟨⟩

  lead : ∀ {b}
       → One b
         -----
       → Can b

inc-Can : ∀ {b}
        → Can b
          -----------
        → Can (inc b)
inc-Can zero = lead one
inc-Can (lead one-b) = {!!}
