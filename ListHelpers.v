(** * List Helpers / Utility Functions *)

(* Imports *)
From Coq Require Import Lists.List.
Import ListNotations.

(* Helpers *)
Fixpoint update_nth {A : Type} (n : nat) (x : A) (xs : list A) : list A :=
  match n, xs with
  | 0, _ :: xs' => x :: xs'
  | S n', y :: xs' => y :: update_nth n' x xs'
  | _, [] => []
  end.
