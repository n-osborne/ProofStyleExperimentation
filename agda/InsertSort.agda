module InsertSort where

open import Data.Bool                                   using (Bool; true; false)
open import Data.Vec                                    using (Vec; []; _∷_)
open import Data.Nat                                    using (ℕ; zero; suc; _<ᵇ_; _≡ᵇ_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)


insert : {m : ℕ} → ℕ → Vec ℕ m → Vec ℕ (suc m)
insert n [] = n ∷ []
insert n (x ∷ xs) with n <ᵇ x
... | true  = n ∷ x ∷ xs
... | false = x ∷ (insert n xs)

insertsort : {m : ℕ} → Vec ℕ m → Vec ℕ m
insertsort []       = []
insertsort (x ∷ xs) = insert x (insertsort xs)

occurrences : {m : ℕ} → ℕ → Vec ℕ m → ℕ
occurrences n []    = zero
occurrences n (x ∷ xs) with n ≡ᵇ x
... | true  = suc (occurrences n xs)
... | false = occurrences n xs

-- Occurrences is a ternary relation between
-- 1. an element n (a nat here)
-- 2. a Vec
-- 3. the number of occurrences of n in the Vec 
data Occurrences : ∀ {m : ℕ} → ℕ → Vec ℕ m → ℕ → Set where
  empty : ∀ {n : ℕ} → Occurrences n [] zero

  same  : ∀ {o n m : ℕ}{xs : Vec ℕ m} →
          Occurrences n xs o →
          Occurrences n (n ∷ xs) (suc o)

  diff  : ∀ {o x n m : ℕ}{xs : Vec ℕ m} →
        (n ≡ᵇ x) ≡ false →
        Occurrences n xs o →
        Occurrences n (x ∷ xs) o 
