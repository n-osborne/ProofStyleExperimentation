module InsertSort where

open import Data.Bool                                   using (Bool; true; false; T)
open import Data.Vec                                    using (Vec; []; _∷_)
open import Data.Nat
open import Data.Nat.Properties                         using (<ᵇ⇒<; <⇒≤; ≤-trans)
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

insertsortBool : {m : ℕ} → Vec ℕ m → Vec ℕ m
insertsortBool []       = []
insertsortBool (x ∷ xs) = insert_bool x (insertsortBool xs)

-- The we propose a second version using the Dec Relation
insertDec : {m : ℕ} → ℕ → Vec ℕ m → Vec ℕ (suc m)
insertDec n [] = n ∷ []
insertDec n (x ∷ xs) with n <? x
... | yes _ = n ∷ x ∷ xs
... | no _  = x ∷ (insertDec n xs)

insertsortDec : {m : ℕ} → Vec ℕ m → Vec ℕ m
insertsortDec []       = []
insertsortDec (x ∷ xs) = insertDec x (insertsortDec xs)

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

{- We define the Sorted predicate for nat vectors

   Note that this definition will need us to use a functional induction
   that is an induction on the different values of the recursive call in 
   insertDec (see std-Coq version for example)
-}
data Sorted : ∀ {m : ℕ} → Vec ℕ m  → Set where
  empty-sorted     : Sorted []
  singleton-sorted : ∀ {n : ℕ} → Sorted (n ∷ [])
  cons-sorted      : ∀ {x y m : ℕ}{xs : Vec ℕ m} →
                     y ≤ x →
                     Sorted (x ∷ xs) →
                     Sorted (y ∷ x ∷ xs)

tail-sorted : ∀ {m x : ℕ}{xs : Vec ℕ m} → Sorted (x ∷ xs) → Sorted xs
tail-sorted singleton-sorted = empty-sorted
tail-sorted (cons-sorted x sxs) = sxs

{- Second definition for Sorted Predicate use the binary relation ≤* which means that 
the nat is lesser or equal to each of the elements of the Vec
-}
data _≤*_ : {m : ℕ} → ℕ → Vec ℕ m → Set where
  x≤*[]   : ∀ {x : ℕ} → x ≤* []
  x≤*xxs  : ∀ {x x₁ m : ℕ}{xs : Vec ℕ m} → x ≤ x₁ → x ≤* xs → x ≤* (x₁ ∷ xs)

{- In the process of the proof we will need the transitivity of ≤*
-}
≤*-trans : ∀ {x y m : ℕ}{ys : Vec ℕ m} → x ≤ y → y ≤* ys → x ≤* ys
≤*-trans {ys = []} x≤y y≤*ys                  = x≤*[]
≤*-trans {ys = x ∷ ys} x≤y (x≤*xxs y≤x y≤*ys) = x≤*xxs (≤-trans x≤y y≤x) (≤*-trans x≤y y≤*ys)


data Sorted₂ : ∀ {m : ℕ} → Vec ℕ m → Set where
  empty-sorted₂ : Sorted₂ []
  cons-sorted₁  : ∀ {x m : ℕ}{xs : Vec ℕ m} → x ≤* xs → Sorted₂ xs → Sorted₂ (x ∷ xs)
  
-- And the Permutation relation
data Permutation : ∀ {m : ℕ} → Vec ℕ m → Vec ℕ m → Set where
  nil-perm   : Permutation [] []
  skip-perm  : ∀ {x m : ℕ}{xs ys : Vec ℕ m} →
               Permutation xs ys →
               Permutation (x ∷ xs) (x ∷ ys)
  swap-perm  : ∀ {m : ℕ}{xs ys : Vec ℕ m}(x y : ℕ) →
               Permutation xs ys →
               Permutation (x ∷ y ∷ xs) (y ∷ x ∷ ys)
  trans-perm : ∀ {m : ℕ}{xs ys zs : Vec ℕ m} →
               Permutation xs ys →
               Permutation ys zs →
               Permutation xs zs

-- intermediate lemma that every Vec is its own Permutation
permutation-xs-xs : ∀ {m : ℕ}(xs : Vec ℕ m) → Permutation xs xs
permutation-xs-xs []       = nil-perm
permutation-xs-xs (x ∷ xs) = skip-perm (permutation-xs-xs xs)

{- 
  Proof that insertDec produces a permutation

  We proceed by induction on xs

  - Base case is trivial

  - Induction case split in two on x <? x₁
      yes -> skip-term 
      no  -> result is (x₁ ∷ (insertDec x xs))
             So the Goal is : Permutation (x ∷ x₁ ∷ xs) (x₁ ∷ (insertDec x xs))
             This is a work for trans-perm with:
               + (x ∷ x₁ ∷ xs) as xs
               + (x₁ ∷ x ∷ xs) as ys
               + (x₁ ∷ (insertDec x xs)) as zs
          So, there are two sub goals:
          1. Permutation (x ∷ x₁ ∷ xs) (x₁ ∷ x ∷ xs) => by swap-perm
          2. Permutation (x₁ ∷ x ∷ xs) (x₁ ∷ (insertDec x xs)) => by skip-perm and induction hypothesis
-}
insertDec-Permutation-cons : ∀ {m : ℕ}(x : ℕ)(xs : Vec ℕ m) → Permutation (x ∷ xs) (insertDec x xs)
insertDec-Permutation-cons x [] = skip-perm nil-perm
insertDec-Permutation-cons x (x₁ ∷ xs) with x <? x₁
... | yes _ = skip-perm (permutation-xs-xs (x₁ ∷ xs))
... | no  _ = trans-perm (swap-perm x x₁ (permutation-xs-xs xs)) (skip-perm (insertDec-Permutation-cons x xs))



{-
  Proof that insertDec preserves the Sorted Property

  This is the delicate part.

  We proceed by induction on the list
  Then we need some functional induction on the result of `insertDec x xs`

  The nil case is trivial
  The cons case need a case split on x <? x₁
  The yes case is obvious by inclusion of ≤ in <
  The no case need to know that x₁ is lesser than the head of (insertDec x xs)
  Pb: we don't know what is the head of (insertDec x xs) -- and we need to know
      in order to build a proof the cons-sorted

  At his point in the std-Coq version, we would use a `functional induction` on the
  `insertDec x xs`, but here, this expression is not in our environment
-}
insertDec-sorted-in-out : ∀ {m : ℕ}(x : ℕ)(xs : Vec ℕ m) → Sorted xs → Sorted (insertDec x xs)
insertDec-sorted-in-out x [] sxs = singleton-sorted
insertDec-sorted-in-out x (x₁ ∷ xs) sxs with x <? x₁
insertDec-sorted-in-out x (x₁ ∷ xs) sxs  | yes p = cons-sorted (<⇒≤ p) sxs
insertDec-sorted-in-out x (x₁ ∷ xs) sxs  | no ¬p with insertDec x xs
insertDec-sorted-in-out x (x₁ ∷ xs) sxs  | no ¬p | x₂ ∷ xs₂ = cons-sorted {!!} {!!} -- cons-sorted x₁≤x₂ (Sorted xs₂)
--insertDec-sorted-in-out x (x₁ ∷ []) sxs  | no ¬p   = {!!}
--insertDec-sorted-in-out x (x₁ ∷ x₂ ∷ xs) sxs  | no ¬p with insertDec x (x₂ ∷ xs)
--insertDec-sorted-in-out x (x₁ ∷ x₂ ∷ xs) sxs  | no ¬p | x ∷ x₂ ∷ xs           = ?
--insertDec-sorted-in-out x (x₁ ∷ x₂ ∷ xs) sxs  | no ¬p | x ∷ x₂ ∷ xs = ?
 
-- insert-sorted-in-out : ∀ {m : ℕ}(x : ℕ)(xs : Vec ℕ m) → Sorted xs → Sorted (insert x xs)
-- insert-sorted-in-out x [] sxs = singleton_sorted
-- insert-sorted-in-out x (x₁ ∷ xs) sxs with x <ᵇ x₁
-- ... | true  = cons_sorted (<ᵇ⇒< x x₁ (T (x <ᵇ x₁))) sxs
-- ... | false = {!!}


