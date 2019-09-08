module InsertSort where

open import Data.Bool                                   using (Bool; true; false; T)
open import Data.Vec                                    using (Vec; []; _∷_)
open import Data.Nat
open import Data.Nat.Properties                         using (<ᵇ⇒<; <⇒≤; ≤-trans; ≰⇒≥)
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
insertDec n (x ∷ xs) with n ≤? x
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

{- 
In order to avoid using functional induction, we use another definition of
the sorted property, one that contains explicitly more information.

This second definition for Sorted Predicate use the binary relation ≤* 
between a ℕ and a Vec ℕ
This relation means that the nat is lesser or equal to each of the elements 
of the Vec
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
  cons-sorted₂  : ∀ {x m : ℕ}{xs : Vec ℕ m} → x ≤* xs → Sorted₂ xs → Sorted₂ (x ∷ xs)

-- We will need some inversion functions on the cons-sorted₂ constructor
cons-sorted₂-inv₁ : ∀ {m x : ℕ}{xs : Vec ℕ m} → Sorted₂ (x ∷ xs) → x ≤* xs
cons-sorted₂-inv₁ (cons-sorted₂ x≤*xs _) = x≤*xs

cons-sorted₂-inv₂ : ∀ {m x : ℕ}{xs : Vec ℕ m} → Sorted₂ (x ∷ xs) → Sorted₂ xs
cons-sorted₂-inv₂ (cons-sorted₂ _ empty-sorted₂) = empty-sorted₂
cons-sorted₂-inv₂ (cons-sorted₂ _ sxs) = sxs

cons-sorted₂-inv₃ : ∀ {x₁ x₂ m : ℕ}{xs : Vec ℕ m} → Sorted₂ (x₁ ∷ x₂ ∷ xs) → x₁ ≤ x₂
cons-sorted₂-inv₃ (cons-sorted₂ (x≤*xxs x₁≤x₂ _) _) = x₁≤x₂

cons-sorted₂-inv₄ : ∀ {x₁ x₂ m : ℕ}{xs : Vec ℕ m} → Sorted₂ (x₁ ∷ x₂ ∷ xs) → x₁ ≤* xs
cons-sorted₂-inv₄ (cons-sorted₂ (x≤*xxs _ x₂≤*xs) _) = x₂≤*xs

cons-sorted₂-inv₅ : ∀ {m x₁ x₂ : ℕ}{xs : Vec ℕ m} → Sorted₂ (x₁ ∷ x₂ ∷ xs) → Sorted₂ (x₁ ∷ xs)
cons-sorted₂-inv₅ (cons-sorted₂ (x≤*xxs _ x₁≤*xs) (cons-sorted₂ _ sxs)) = cons-sorted₂ x₁≤*xs sxs

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
insertDec-Permutation-cons x (x₁ ∷ xs) with x ≤? x₁
... | yes _ = skip-perm (permutation-xs-xs (x₁ ∷ xs))
... | no  _ = trans-perm (swap-perm x x₁ (permutation-xs-xs xs)) (skip-perm (insertDec-Permutation-cons x xs))


-- *Proof that insertDec preserves the Sorted₂ property.*
{-
  We will need an auxiliary lemma to avoid that the proof in the recursive case became to big
-}
aux : ∀ {m x₁ x₂ : ℕ}{xs : Vec ℕ m} → x₂ ≤ x₁ → Sorted₂ (x₂ ∷ xs) → x₂ ≤* (insertDec x₁ xs)
aux {xs = []} x₂≤x₁ sx₂xs = x≤*xxs x₂≤x₁ x≤*[]
aux {x₁ = x₁}{xs = x ∷ xs} x₂≤x₁ sx₂xs with x₁ ≤? x
aux x₂≤x₁ sx₂xs | yes p = x≤*xxs x₂≤x₁ (x≤*xxs (≤-trans x₂≤x₁ p) (cons-sorted₂-inv₄ sx₂xs))
aux x₂≤x₁ sx₂xs | no ¬p = x≤*xxs
                          (cons-sorted₂-inv₃ sx₂xs) -- x₂ ≤ x
                          (aux x₂≤x₁ (cons-sorted₂-inv₅ sx₂xs)) -- x₂ ≤* insertDec x₁ xs

{-
  We procced by induction on the Vec

  the [] case is trivial.

  In the cons case, we procced by case analysis on x ≤? x₁
  The yes case : Goal is Sorted₂ (x ∷ x₁ ∷ xs)
                      x ≤* (x₁ ∷ xs) is build by transitivity of ≤*
                      Sorted₂ (x₁ ∷ xs) is given
  The no case : Goal is Sorted₂ (x₁ ∷ (insertDec x xs))
                     x₁ ≤* (insertDec x xs) is build using aux lemma
                     Sorted₂ (insertDec x xs) is build using the induction hypothesis.
-}
insertDec-Sorted₂-in-out : ∀ {m : ℕ}(x : ℕ)(xs : Vec ℕ m) → Sorted₂ xs → Sorted₂ (insertDec x xs)
insertDec-Sorted₂-in-out x [] sxs = cons-sorted₂ x≤*[] sxs
insertDec-Sorted₂-in-out x (x₁ ∷ xs) sxs with x ≤? x₁
insertDec-Sorted₂-in-out x (x₁ ∷ xs) sxs | yes p = cons-sorted₂
                                                   (x≤*xxs p (≤*-trans p (cons-sorted₂-inv₁ sxs)))
                                                   sxs
insertDec-Sorted₂-in-out x (x₁ ∷ xs) sxs | no ¬p = cons-sorted₂
                                                   (aux (≰⇒≥ ¬p) sxs)
                                                   (insertDec-Sorted₂-in-out x xs (cons-sorted₂-inv₂ sxs))
