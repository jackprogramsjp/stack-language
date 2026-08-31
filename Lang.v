From SL Require Import Maps.
From SL Require Import Stack.
From Stdlib Require Import Strings.String.

Module Lang.

(* Types for the language *)
Inductive ty : Type :=
  | Ty_Nat  : ty
.

(* Terms for the language *)
Inductive tm : Type :=
  | tm_nat  : nat -> tm
  | tm_add  : tm -> tm -> tm
  | tm_mul  : tm -> tm -> tm
.

(* Value for operational semantics *)
Inductive value : tm -> Prop :=
  | v_nat : forall t,
      value (tm_nat t)
.

Hint Constructors value : core.

(* Define multi-step reduction *)

Definition relation (X : Type) := X -> X -> Prop.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

(*  *)

Theorem multi_R : forall (X : Type) (R : relation X) (x y : X),
  R x y -> (multi R) x y.
Proof.
  intros X R x y H.
  apply multi_step with y.
  - exact H.
  - apply multi_refl.
Qed.

Theorem multi_trans :
  forall (X : Type) (R : relation X) (x y z : X),
    multi R x y ->
    multi R y z ->
    multi R x z.
Proof.
  intros X R x y z G H.
  induction G.
  - (* multi_refl *) exact H.
  - (* multi_step *)
    apply multi_step with y.
    + exact H0.
    + apply IHG. exact H.
Qed.

(* Substitution *)
Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_nat _ =>
      t
  | tm_add t1 t2 =>
      tm_add (subst x s t1) (subst x s t2)
  | tm_mul t1 t2 =>
      tm_mul (subst x s t1) (subst x s t2)
  end.

(* Substitution as an inductive relation *)
Inductive substi (s : tm) (x : string) : tm -> tm -> Prop :=
  | s_nat : forall n,
      substi s x (tm_nat n) (tm_nat n)
  | s_add : forall t1 t1' t2 t2',
      substi s x t1 t1' ->
      substi s x t2 t2' ->
      substi s x (tm_add t1 t2) (tm_add t1' t2')
  | s_mul : forall t1 t1' t2 t2',
      substi s x t1 t1' ->
      substi s x t2 t2' ->
      substi s x (tm_mul t1 t2) (tm_mul t1' t2')
.

Hint Constructors substi : core.

(* Proof that the relation coincides with the function. *)
Theorem substi_correct : forall s x t t',
  subst x s t = t' <-> substi s x t t'.
Proof.
  intros s x t.
  induction t; intros t'; split; intros H.
  - (* tm_nat, goal: substi *)
    simpl in H.
    subst t'.
    apply s_nat.
  - (* tm_nat, goal: subst *)
    simpl.
    inversion H.
    reflexivity.
  - (* tm_add, goal: substi *)
    simpl in H.
    subst t'.
    apply s_add.
    + apply IHt1.
      reflexivity.
    + apply IHt2.
      reflexivity.
  - (* tm_add, goal: subst *)
    simpl.
    inversion H; subst; simpl.
    apply IHt1 in H2.
    apply IHt2 in H4.
    subst.
    reflexivity.
  - (* tm_mul, goal: substi *)
    simpl in H.
    subst t'.
    apply s_mul.
    + apply IHt1.
      reflexivity.
    + apply IHt2.
      reflexivity.
  - (* tm_mul, goal: subst *)
    simpl.
    inversion H; subst; simpl.
    apply IHt1 in H2.
    apply IHt2 in H4.
    subst.
    reflexivity.
Qed.

(* Define small-step semantics relation for the language *)
Inductive step : tm -> tm -> Prop :=
  | ST_Mult1 : forall t1 t1' t2,
    step t1 t1' ->
    step (tm_mul t1 t2) (tm_mul t1' t2)
  | ST_Mult2 : forall v1 t2 t2',
    value v1 ->
    step t2 t2' ->
    step (tm_mul v1 t2) (tm_mul v1 t2')
  | ST_MultNat : forall (n1 n2 : nat),
    step (tm_mul (tm_nat n1) (tm_nat n2)) (tm_nat (n1 * n2))
  | ST_Add1 : forall t1 t1' t2,
    step t1 t1' ->
    step (tm_add t1 t2) (tm_add t1' t2)
  | ST_Add2 : forall v1 t2 t2',
    value v1 ->
    step t2 t2' ->
    step (tm_add v1 t2) (tm_add v1 t2')
  | ST_AddNat : forall (n1 n2 : nat),
    step (tm_add (tm_nat n1) (tm_nat n2)) (tm_nat (n1 + n2))
.

Notation multistep := (multi step).

Hint Constructors step : core.

(* One example of natural numbers *)

(* 1 + (2 * 3) = 7 *)
Example Nat_step_example : exists t,
  multistep (tm_add (tm_nat 1) (tm_mul (tm_nat 2) (tm_nat 3))) t.
Proof.
  exists (tm_nat 7).
  eapply multi_step.
  - apply ST_Add2.
    + apply v_nat.
    + apply ST_MultNat.
  - eapply multi_step.
    + apply ST_AddNat.
    + apply multi_refl.
Qed.

End Lang.
