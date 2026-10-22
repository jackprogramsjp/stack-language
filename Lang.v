From SL Require Import Maps.
From SL Require Import ListHelpers.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lia.
Import ListNotations.

Module Lang.

(* Values*)

Inductive value : Type :=
  | VNat  : nat -> value
  | VUnit : value
.

(* Types*)

Inductive ty : Type :=
  | Ty_Nat  : ty
  | Ty_Unit : ty
.

(* A location is an index into the store *)
Definition loc := nat.

(* Store = a list of values... allocation appends. *)
Definition store := list value.

Definition store_lookup (l : loc) (st : store) : value :=
  nth l st VUnit.

Definition replace (l : loc) (v : value) (st : store) : store :=
  update_nth l v st.

Lemma length_replace : forall l v st,
  length (replace l v st) = length st.
Proof.
  intros l v st.
  unfold replace.
  generalize dependent l.
  induction st as [ | h t IH]; intros l.
  - destruct l. reflexivity. reflexivity.
  - destruct l. reflexivity.
    simpl. rewrite IH. reflexivity.
Qed.

Lemma lookup_replace_eq : forall l v st,
  l < length st ->
  store_lookup l (replace l v st) = v.
Proof.
  intros l v st.
  unfold store_lookup, replace.
  generalize dependent l.
  induction st as [ | h t IH]; intros l Hlen.
  - inversion Hlen.
  - destruct l as [ | l']; simpl; auto.
    apply IH. simpl in Hlen. lia.
Qed.

Lemma lookup_replace_neq : forall l1 l2 v st,
  l1 <> l2 ->
  store_lookup l1 (replace l2 v st) = store_lookup l1 st.
Proof.
  unfold store_lookup, replace.
  induction l1 as [|l1' IH]; intros l2 v st Hneq.
  - destruct st as [|h t].
    + destruct l2; reflexivity.
    + destruct l2 as [|l2'].
      * contradiction Hneq. reflexivity.
      * reflexivity.
  - destruct st as [|h t].
    + destruct l2; reflexivity.
    + destruct l2 as [|l2'].
      * reflexivity.
      * simpl.
        apply IH.
        congruence.
        (* intro Heq.
        apply Hneq.
        rewrite Heq.
        reflexivity. *)
Qed.

(* map program variables to locations *)
Definition env := partial_map loc.

(* Terms *)

Inductive tm : Type :=
  | tm_val    : value -> tm
  | tm_var    : string -> tm
  | tm_add    : tm -> tm -> tm
  | tm_mul    : tm -> tm -> tm
  | tm_letvar : string -> tm -> tm -> tm   (* letvar x = e1 in e2 *)
  | tm_assign : string -> tm -> tm         (* x := e *)
  | tm_seq    : tm -> tm -> tm             (* e1 ; e2 *)
.

Definition tm_nat (n : nat) : tm := tm_val (VNat n).

(* Big-step semantics *)
(* Under environment rho and store st, term e evaluates to value v with final store st' *)

Inductive eval : tm -> env -> store -> value -> store -> Prop :=
  | E_Val : forall rho st v,
      eval (tm_val v) rho st v st

  | E_Var : forall rho st x l,
      rho x = Some l ->
      l < length st ->
      eval (tm_var x) rho st (store_lookup l st) st

  | E_Add : forall rho st st1 st2 e1 e2 n1 n2,
      eval e1 rho st (VNat n1) st1 ->
      eval e2 rho st1 (VNat n2) st2 ->
      eval (tm_add e1 e2) rho st (VNat (n1 + n2)) st2

  | E_Mul : forall rho st st1 st2 e1 e2 n1 n2,
      eval e1 rho st (VNat n1) st1 ->
      eval e2 rho st1 (VNat n2) st2 ->
      eval (tm_mul e1 e2) rho st (VNat (n1 * n2)) st2

  | E_LetVar : forall rho st st1 st2 x e1 e2 v1 v2,
      eval e1 rho st v1 st1 ->
      eval e2 (update rho x (length st1)) (st1 ++ [v1]) v2 st2 ->
      eval (tm_letvar x e1 e2) rho st v2 st2

  | E_Assign : forall rho st st1 x e l v,
      rho x = Some l ->
      eval e rho st v st1 ->
      l < length st1 ->
      eval (tm_assign x e) rho st VUnit (replace l v st1)

  | E_Seq : forall rho st st1 st2 e1 e2 v1 v2,
      eval e1 rho st v1 st1 ->
      eval e2 rho st1 v2 st2 ->
      eval (tm_seq e1 e2) rho st v2 st2
.

#[global] Hint Constructors eval : core.

(* Examples*)

Example eval_letvar_read :
  eval (tm_letvar "x" (tm_nat 5) (tm_var "x")) empty [] (VNat 5) [VNat 5].
Proof.
  apply E_LetVar with (v1 := VNat 5) (st1 := []).
  - apply E_Val.
  - simpl.
    apply E_Var with (l := 0).
    + rewrite update_eq. reflexivity.
    + simpl. lia.
Qed.

Example eval_letvar_assign :
  eval
    (tm_letvar "x" (tm_nat 5)
       (tm_seq (tm_assign "x" (tm_nat 7)) (tm_var "x")))
    empty [] (VNat 7) [VNat 7].
Proof.
  apply E_LetVar with (v1 := VNat 5) (st1 := []).
  - apply E_Val.
  - simpl.
    eapply E_Seq.
    + apply E_Assign with (l := 0) (v := VNat 7).
      * rewrite update_eq. reflexivity.
      * apply E_Val.
      * simpl. lia.
    + unfold replace. simpl.
      apply E_Var with (l := 0).
      * rewrite update_eq. reflexivity.
      * simpl. lia.
Qed.

End Lang.
