module InsertSort where

open import Data.Bool                                   using (Bool; true; false; T)
open import Data.Vec                                    using (Vec; []; _∷_)
open import Data.Nat                                    using (ℕ; zero; suc; _<ᵇ_; _≡ᵇ_; _<_; _<?_)
open import Data.Nat.Properties                         using (<ᵇ⇒<)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import Relation.Nullary                            using (Dec; yes; no)

-- *****************
-- * The algorithm *
-- *****************

-- We define a first version a insert sort algorithm using boolean lesser than function
insert_bool : {m : ℕ} → ℕ → Vec ℕ m → Vec ℕ (suc m)
insert_bool n [] = n ∷ []
insert_bool n (x ∷ xs) with n <ᵇ x
... | true  = n ∷ x ∷ xs
... | false = x ∷ (insert_bool n xs)

insertsort_bool : {m : ℕ} → Vec ℕ m → Vec ℕ m
insertsort_bool []       = []
insertsort_bool (x ∷ xs) = insert_bool x (insertsort_bool xs)

-- The we propose a second version using the Dec Relation
insert_Dec : {m : ℕ} → ℕ → Vec ℕ m → Vec ℕ (suc m)
insert_Dec n [] = n ∷ []
insert_Dec n (x ∷ xs) with n <? x
... | yes _ = n ∷ x ∷ xs
... | no _  = x ∷ (insert_Dec n xs)

insertsort_Dec : {m : ℕ} → Vec ℕ m → Vec ℕ m
insertsort_Dec []       = []
insertsort_Dec (x ∷ xs) = insert_Dec x (insertsort_Dec xs)

-- *************
-- * The proof *
-- *************

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

-- We define the Sorted predicate for nat vectors
data Sorted : ∀ {m : ℕ} → Vec ℕ m  → Set where
  empty_sorted     : Sorted []
  singleton_sorted : ∀ {n : ℕ} → Sorted (n ∷ [])
  cons_sorted      : ∀ {x y m : ℕ}{xs : Vec ℕ m} →
                     y < x →
                     Sorted (x ∷ xs) →
                     Sorted (y ∷ x ∷ xs)

-- And the Permutation relation
data Permutation : ∀ {m : ℕ} → Vec ℕ m → Vec ℕ m → Set where
  nil_perm   : Permutation [] []
  skip_perm  : ∀ {x m : ℕ}{xs ys : Vec ℕ m} →
               Permutation xs ys →
               Permutation (x ∷ xs) (x ∷ ys)
  swap_perm  : ∀ {x y m : ℕ}{xs ys : Vec ℕ m} →
               Permutation xs ys →
               Permutation (x ∷ y ∷ xs) (y ∷ x ∷ ys)
  trans_perm : ∀ {m : ℕ}{xs ys zs : Vec ℕ m} →
               Permutation xs ys →
               Permutation ys zs →
               Permutation xs zs



-- insert-sorted-in-out : ∀ {m : ℕ}(x : ℕ)(xs : Vec ℕ m) → Sorted xs → Sorted (insert x xs)
-- insert-sorted-in-out x [] sxs = singleton_sorted
-- insert-sorted-in-out x (x₁ ∷ xs) sxs with x <ᵇ x₁
-- ... | true  = cons_sorted (<ᵇ⇒< x x₁ (T (x <ᵇ x₁))) sxs
-- ... | false = {!!}
