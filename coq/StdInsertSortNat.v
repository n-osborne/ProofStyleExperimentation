(**
   In this module, we prove that the insert sort algorithm is indeed a
   sorting algorithm in a standard way. That is using Inductive Proposition
   to define what is a sorting algorithm.
*)


Require Import Nat.
Require Import PeanoNat.
Require Import Lists.List.
Require Import Permutation.

Require Import FunInd.

Import ListNotations.

(** * The algorithm *)
(**
   The first version sorts list of natural number in increasing
   order.
   Generalizing with a generic order relation shouldn't be a problem.
*)
Fixpoint insert (n: nat) (l: list nat) : list nat :=
  match l with
  | []     => [n]
  | x :: xs => match leb n x with
           | true  => n :: x :: xs
           | false => x :: (insert n xs)
           end
  end.

(** We will need functional induction for the insert function. *)
Functional Scheme insert_ind := Induction for insert Sort Prop.
(** This induction principle allows to proove a proposition on the
    result of the insert function.
    To use this principle, we need to proove the proposition for
    each of the possible termination case of the function. 
*)
(**
insert_ind
     : forall (n : nat) (P : list nat -> list nat -> Prop),
       (forall l : list nat, l = [] -> P [] [n]) ->
       (forall (l : list nat) (x : nat) (xs : list nat),
        l = x :: xs -> (n <=? x) = true -> P (x :: xs) (n :: x :: xs)) ->
       (forall (l : list nat) (x : nat) (xs : list nat),
        l = x :: xs ->
        (n <=? x) = false -> P xs (insert n xs) -> P (x :: xs) (x :: insert n xs)) ->
       forall l : list nat, P l (insert n l)
*)

(** The insert_sort function is easy to define once given the insert function *)
Fixpoint insert_sort (l: list nat) : list nat :=
  match l with
  | []     => []
  | x :: xs => insert x (insert_sort xs)
  end.

(** * The Proof *)
(**
    The first thing we want to prove is that the insert function preserves sorting,
    that is, the insertion of a nat in a sorted list gives back a sorted list.

    Thus, we need to formalise what is it, for a list of nat, to be sorted
    in increasing order.
*)
Inductive Sorted: list nat -> Prop :=
| nilSorted : Sorted []
| singleSorted: forall x, Sorted [x]
| consSorted : forall xs x n, Sorted (x :: xs) -> n <= x -> Sorted (n :: x :: xs).

(** In order to have a somewhat cleaner proof, we want to be able to extract
 Sorted xs from Sorted (x :: xs)
 This could be done by the inversion Tactic, but this Lemma generates less hypothesis.
*)
Lemma Sorted_xxs_Sorted_xs: forall x xs, Sorted (x :: xs) -> Sorted xs.
Proof.
  intros x xs ant.
  inversion ant.
  - apply nilSorted.
  - assumption.
Qed.

(**
    Start with an induction on the list, then functional induction on 
    calls of insert (twice). The rest is book-keeping.
*)
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
        ** apply Sorted_xxs_Sorted_xs in ant.
           now apply IHl0 in ant.
        ** apply Nat.leb_gt in e0; now apply Nat.lt_le_incl.
      * apply consSorted.
        ** apply Sorted_xxs_Sorted_xs in ant.
           now apply IHl0 in ant.
        ** now inversion ant.
Qed.

(** The proof that the result of the sorting algorithm is a Sorted list is quite trivial
    at this point. *)
Lemma InsertSort_Sorted: forall l, Sorted (insert_sort l).
Proof.
  induction l.
  - now apply nilSorted.
  - now apply Insert_Sorted.
Qed.

(** We proceed in a similar way for the permutation aspect of the specifications
    of a sorting algorithm, proving the property firstly for the insert function,
    then for the insert_sort itself. *)

(** The first proof is done by an induction on the list and then un functional
    induction on the insert function, using some properties of Permutation *)
Lemma Insert_Permutation: forall n l, Permutation (n :: l) (insert n l).
Proof.
  intro n; induction l; trivial.
  functional induction (insert n (a :: l)); trivial.
  apply (perm_skip x) in IHl1.
  apply Permutation_trans with (l':=(x :: n :: xs)).
  + apply perm_swap.
  + assumption.
Qed.

(** The second proof is done simply by an induction on the list, using some 
    properties of Permutation and the Lemma about the insert function *)
Lemma InsertSort_Permutation: forall l, Permutation l (insert_sort l).
Proof.
  induction l; trivial.
  apply (perm_skip a) in IHl.
  apply Permutation_trans with (l':=(a :: insert_sort l)); trivial.
  apply Insert_Permutation.
Qed.

(** Now we can package all that in a single definition *)
Definition SortingAlgorithm (f: list nat -> list nat) :=
  forall l, Permutation l (f l) /\ Sorted (f l).
  
Lemma insert_sort_sorting_algorithm: SortingAlgorithm insert_sort.
Proof.
  split.
  - apply InsertSort_Permutation.
  - apply InsertSort_Sorted.
Qed.

