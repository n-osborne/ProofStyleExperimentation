

Require Import Nat.
Require Import PeanoNat.
Require Import Lists.List.
Require Import Permutation.

Require Import FunInd.

Import ListNotations.


Fixpoint insert (n: nat) (l: list nat) : list nat :=
  match l with
  | []     => [n]
  | x :: xs => match leb n x with
           | true  => n :: x :: xs
           | false => x :: (insert n xs)
           end
  end.

Functional Scheme insert_ind := Induction for insert Sort Prop.

Fixpoint insert_sort (l: list nat) : list nat :=
  match l with
  | []     => []
  | x :: xs => insert x (insert_sort xs)
  end.

Fixpoint occurrences (n: nat) (l: list nat) : nat :=
  match l with
  | []     => O
  | x :: xs => match eqb n x with
             | true  => S (occurrences n xs)
             | false => occurrences n xs
             end
  end.

Inductive Occurrences (n: nat): list nat -> nat -> Prop :=
| empty : Occurrences n [] O
| same  : forall l o, Occurrences n l o -> Occurrences n (n :: l) (S o)
| diff  : forall l o x, Occurrences n l o -> x <> n -> Occurrences n (x :: l) o.

Inductive Sorted: list nat -> Prop :=
| nilSorted : Sorted []
| singleSorted: forall x, Sorted [x]
| consSorted : forall xs x n, Sorted (x :: xs) -> n <= x -> Sorted (n :: x :: xs).

Lemma Sorted_xxs_Sorted_xs: forall x xs, Sorted (x :: xs) -> Sorted xs.
Proof.
  intros x xs ant.
  inversion ant.
  - apply nilSorted.
  - assumption.
Qed.

Lemma Insert_Sorted: forall n l, Sorted l -> Sorted (insert n l).
Proof.
  intros n; induction l as [|x xs IH]; intro ant.
  - now apply singleSorted.
  - functional induction (insert n (x :: xs)).
    + apply singleSorted.
    + apply consSorted; trivial.
      now apply Nat.leb_le.
    + functional induction (insert n xs0).
      * apply consSorted.
        ** apply singleSorted.
        ** apply Nat.leb_gt in e0; now apply Nat.lt_le_incl.
      * apply consSorted.
        ** inversion ant.
           now apply IHl0 in H1.
        ** apply Nat.leb_gt in e0; now apply Nat.lt_le_incl.
      * apply consSorted.
        ** apply Sorted_xxs_Sorted_xs in ant.
           now apply IHl0 in ant.
        ** now inversion ant.
Qed.

        
