From SL Require Import Maps.
From SL Require Import Stack.
From Stdlib Require Import Strings.String.
From Coq Require Import Lists.List.
Import ListNotations.

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

(* Define value as a Rocq function *)
(* Eventually, it will be a Fixpoint! *)
Definition valuef (t : tm) : bool :=
  match t with
  | tm_nat _ => true
  | tm_add t1 t2 => false
  | tm_mul t1 t2 => false
  end.

(* Helper function for checking term is a value *)
Definition assert (b : bool) (a : option tm) : option tm :=
  if b then a else None.

(* Operational semantics as a Rocq function *)
Fixpoint stepf (t : tm) : option tm :=
  match t with
  | tm_nat _ => None (* because it is a number value *)

  (* arithmetic operations *)
  | tm_add t1 t2 =>
    match stepf t1, stepf t2, t1, t2 with
      | Some t1', _, _, _ => Some (tm_add t1' t2)
      | None, Some t2', tm_nat n, _ => Some (tm_add (tm_nat n) t2')
      | None, None, tm_nat n1, tm_nat n2 => Some (tm_nat (n1 + n2))
      | _, _, _, _ => None
    end
  | tm_mul t1 t2 =>
    match stepf t1, stepf t2, t1, t2 with
      | Some t1', _, _, _ => Some (tm_mul t1' t2)
      | None, Some t2', tm_nat n, _ => Some (tm_mul (tm_nat n) t2')
      | None, None, tm_nat n1, tm_nat n2 => Some (tm_nat (n1 * n2))
      | _, _, _, _ => None
    end
  end.

(* Prove that small-step evaluation and small-step relation coincides *)

Theorem small_step_fixpoint_correctness :
  forall t t',
    stepf t = Some t' <-> step t t'.
Proof.
  intros t t'.
  split.
  - (* functional -> relation *)
    generalize dependent t'.
    induction t; intros t' H.
    + (* tm_nat *)
      simpl in H.
      inversion H.
    + (* tm_add *)
      destruct (stepf t1) eqn:H1.
      
      * (* t1 takes a step *)
        simpl in H.
        rewrite H1 in H.
        inversion H.
        apply ST_Add1.
        apply IHt1.
        reflexivity.
      * (* t1 does not take a step *)
        simpl in H.
        rewrite H1 in H.
        destruct (stepf t2) eqn:H2.
        -- (* t2 takes a step *)
           destruct t1 as [n1 | t11 t12 | t11 t12].
           ++ (* t1 = tm_nat n1 *)
              inversion H.
              apply ST_Add2.
              ** apply v_nat.
              ** apply IHt2. reflexivity.
           ++ (* t1 = tm_add ... *)
              discriminate H.
           ++ (* t1 = tm_mul ... *)
              discriminate H.
        -- (* neither t1 nor t2 steps *)
           destruct t1 as [n1 | | ]; destruct t2 as [n2 | | ];
           simpl in H; try discriminate H.
           injection H as H; subst t'.
           apply ST_AddNat. 
    + (* tm_add *)
      destruct (stepf t1) eqn:H1.
      
      * (* t1 takes a step *)
        simpl in H.
        rewrite H1 in H.
        inversion H.
        apply ST_Mult1.
        apply IHt1.
        reflexivity.
      * (* t1 does not take a step *)
        simpl in H.
        rewrite H1 in H.
        destruct (stepf t2) eqn:H2.
        -- (* t2 takes a step *)
           destruct t1 as [n1 | t11 t12 | t11 t12].
           ++ (* t1 = tm_nat n1 *)
              inversion H.
              apply ST_Mult2.
              ** apply v_nat.
              ** apply IHt2. reflexivity.
           ++ (* t1 = tm_add ... *)
              discriminate H.
           ++ (* t1 = tm_mul ... *)
              discriminate H.
        -- (* neither t1 nor t2 steps *)
           destruct t1 as [n1 | | ]; destruct t2 as [n2 | | ];
           simpl in H; try discriminate H.
           injection H as H; subst t'.
           apply ST_MultNat. 
  - (* relation -> functional *)
    intro H.
    induction H; simpl; try reflexivity;
    try rewrite IHstep; try reflexivity;
    inversion H; subst; simpl; reflexivity.
Qed.

(* Compilation from Language to Stack instructions *)
Fixpoint compile (t : tm) : stackProgram :=
  match t with
  | tm_nat n => [IPush n]
  | tm_add t1 t2 => compile t1 ++ compile t2 ++ [IAdd]
  | tm_mul t1 t2 => compile t1 ++ compile t2 ++ [IMul]
  end.

(* Lemma, proving that one source step does not change the compiled behavior *)
Lemma compile_step_preservation :
  forall t t',
    step t t' ->
    forall st,
      stackEvalF (compile t) st =
      stackEvalF (compile t') st.
Proof.
  intros t t' H.
  induction H; intros st.
  - (* ST_Mult1 *)
    simpl.
    rewrite stackEvalF_app. (* Can definitely do repeat rewrite as well *)
    rewrite IHstep.
    rewrite <- stackEvalF_app.
    reflexivity.
Admitted.

(* (2 * 3) --> 6 *)
Example compile_step_example :
  stackEvalF
    (compile (tm_mul (tm_nat 2) (tm_nat 3)))
    {| stack := []; frame := [] |}
  =
  stackEvalF
    (compile (tm_nat 6))
    {| stack := []; frame := [] |}.
Proof.
  apply compile_step_preservation.
  apply ST_MultNat.
Qed.

Lemma compile_multistep_preservation :
  forall t t',
    multistep t t' ->
    forall st,
      stackEvalF (compile t) st =
      stackEvalF (compile t') st.
Proof.
  intros t t' H.
  induction H as [x | x y z Hxy Hyz IH].
Admitted.

End Lang.
