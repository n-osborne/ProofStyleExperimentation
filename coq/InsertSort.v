

Require Import Nat.
Require Import Lists.List.

Import ListNotations.


Fixpoint insert (n: nat) (l: list nat) : list nat :=
  match l with
  | []     => [n]
  | x :: xs => match leb n x with
           | true  => n :: x :: xs
           | false => x :: (insert n xs)
           end
  end.

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
