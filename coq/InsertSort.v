

Require Import Nat.
Require Import Lists.List.

Import ListNotations.


Fixpoint insert (n: nat) (l: list nat) : list nat :=
  match l with
  | []     => [n]
  | x :: xs => match leb n x with
           | true  => x :: (insert n xs)
           | false => n :: x :: xs
           end
  end.

Fixpoint insert_sort (l: list nat) : list nat :=
  match l with
  | []     => []
  | x :: xs => insert x (insert_sort xs)
  end.


