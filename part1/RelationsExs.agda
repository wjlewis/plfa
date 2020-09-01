module plfa.part1.RelationsExs where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (*-comm; +-comm; +-identityʳ)
open import plfa.part1.Relations using ( _≤_; z≤n; s≤s
                                       ; ≤-trans; +-mono-≤
                                       ; _<_; z<s; s<s
                                       ; even; odd; zero; suc; e+e≡e; o+e≡o)

*-monoʳ-≤ : (n p q : ℕ)
         → p ≤ q
         → n * p ≤ n * q
*-monoʳ-≤ zero    p q p≤q = z≤n
*-monoʳ-≤ (suc n) p q p≤q = let n+p≤n+q = *-monoʳ-≤ n p q p≤q
                            in +-mono-≤ p q (n * p) (n * q) p≤q n+p≤n+q

*-monoˡ-≤ : (m n p : ℕ)
         → m ≤ n
         → m * p ≤ n * p
*-monoˡ-≤ m n p m≤n rewrite (*-comm m p) | (*-comm n p) = *-monoʳ-≤ p m n m≤n

*-mono-≤ : (m n p q : ℕ)
        → m ≤ n
        → p ≤ q
          --------------
        → m * p ≤ n * q
*-mono-≤ m n p q m≤n p≤q = let m*p≤n*p = *-monoˡ-≤ m n p m≤n
                               n*p≤n*q = *-monoʳ-≤ n p q p≤q
                           in ≤-trans m*p≤n*p n*p≤n*q

<-trans : {m n p : ℕ}
       → m < n
       → n < p
         ------
       → m < p
<-trans z<s       (s<s n<p) = z<s
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)

data <-Trichotomy : ℕ → ℕ → Set where
  lt : {m n : ℕ}
    → m < n
      -----------------
     → <-Trichotomy m n

  eq : {m n : ℕ}
    → m ≡ n
      -----------------
    → <-Trichotomy m n

  gt : {m n : ℕ}
    → n < m
      -----------------
    → <-Trichotomy m n

<-trichotomy : (m n : ℕ)
              -----------------
            → <-Trichotomy m n
<-trichotomy zero    zero    = eq refl
<-trichotomy zero    (suc n) = lt z<s
<-trichotomy (suc m) zero    = gt z<s
<-trichotomy (suc m) (suc n) with <-trichotomy m n
...                             | lt m<n = lt (s<s m<n)
...                             | eq m≡n = eq (cong suc m≡n)
...                             | gt n<m = gt (s<s n<m)

+-monoʳ-< : (n p q : ℕ)
         → p < q
           --------------
         → n + p < n + q
+-monoʳ-< zero    p q p<q = p<q
+-monoʳ-< (suc m) p q p<q = s<s (+-monoʳ-< m p q p<q)

+-monoˡ-< : (m n p : ℕ)
         → m < n
           --------------
         → m + p < n + p
+-monoˡ-< m n p m<n rewrite (+-comm m p) | (+-comm n p) = +-monoʳ-< p m n m<n

+-mono-< : (m n p q : ℕ)
        → m < n
        → p < q
          --------------
        → m + p < n + q
+-mono-< m n p q m<n p<q = let m+p<n+p = +-monoˡ-< m n p m<n
                               n+p<n+q = +-monoʳ-< n p q p<q
                           in <-trans m+p<n+p n+p<n+q

≤-if-< : {m n : ℕ}
      → m < n
        ------
      → suc m ≤ n
≤-if-< z<s = s≤s z≤n
≤-if-< (s<s m<n) = s≤s (≤-if-< m<n)

<-if-≤ : {m n : ℕ}
      → suc m ≤ n
        ------
      → m < n
<-if-≤ {zero}  {suc n} (s≤s z≤n) = z<s
<-if-≤ {suc m} {suc n} (s≤s m≤n) = s<s (<-if-≤ m≤n)

-- Is there a way to prove `<-trans-revisited` without this?
<-⊆-≤ : {m n : ℕ}
       → m < n
         ------
       → m ≤ n
<-⊆-≤ z<s       = z≤n
<-⊆-≤ (s<s m<n) = s≤s (<-⊆-≤ m<n)

<-trans-revisited : {m n p : ℕ}
                 → m < n
                 → n < p
                   ------
                 → m < p
<-trans-revisited m<n n<p = let sm≤n = ≤-if-< m<n
                                sn≤p = <-⊆-≤ n<p
                                sm≤p = ≤-trans sm≤n sn≤p
                            in  <-if-≤ sm≤p

o+o≡e : {m n : ℕ}
      → odd m
      → odd n
        -------------
      → even (m + n)

e+o≡o : {m n : ℕ}
      → even m
      → odd n
        ------------
      → odd (m + n)

o+o≡e (suc em) on = suc (e+o≡o em on)

e+o≡o zero     on = on
e+o≡o (suc om) on = suc (o+o≡e om on)
