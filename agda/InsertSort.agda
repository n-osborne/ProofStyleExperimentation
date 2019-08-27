module InsertSort where

open import Data.Bool                                   using (Bool; true; false)
open import Data.Vec                                    using (Vec; []; _∷_)
open import Data.Nat                                    using (ℕ; zero; suc; _<ᵇ_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)


insert : {m : ℕ} → ℕ → Vec ℕ m → Vec ℕ (suc m)
insert n [] = n ∷ []
insert n (x ∷ xs) with n <ᵇ x
... | true  = n ∷ x ∷ xs
... | false = x ∷ (insert n xs)

insertsort : {m : ℕ} → Vec ℕ m → Vec ℕ m
insertsort []       = []
insertsort (x ∷ xs) = insert x (insertsort xs)

