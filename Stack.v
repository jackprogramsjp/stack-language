(** * Stack-based Virtual Machine *)

(* Imports *)
From Coq Require Import Lists.List.
Import ListNotations.

(* Operand stack where it's a list of natural numbers *)
Definition operandStack := list nat.

(* Frame array which is space for long-term storage *)
Definition frameArray := list nat.

(* Imperative commands for the stack state *)
Inductive stackInstr : Type :=
  | IPush : nat -> stackInstr                       (* PUSH X:NAT *)
  | IPop : stackInstr                               (* POP *)
  | IAdd : stackInstr                               (* ADD *)
  | IMul : stackInstr                               (* MUL *)
  .

(* Stack program *)
Definition stackProgram := list stackInstr.

(* The actual virtual machine state *)
Record vmState := {
  stack : operandStack;
  frame : frameArray
}.

(* Defin notations *)
Declare Custom Entry stack.

Notation "<<{ p }>>" := p
  (p custom stack at level 99).

Notation "'PUSH' n" := ([IPush n])
  (in custom stack at level 0,
   n constr at level 0).

Notation "'POP'" := ([IPop])
  (in custom stack at level 0).

Notation "'ADD'" := ([IAdd])
  (in custom stack at level 0).

Notation "'MUL'" := ([IMul])
  (in custom stack at level 0).

Notation "x ; y" := (x ++ y)
  (in custom stack at level 80,
   right associativity).

(* Direct interpreter / evaluation big-step *)
Fixpoint stackEvalF
  (p : stackProgram)
  (st : vmState)
  : vmState :=
  match p with
  | [] => st

  | instr :: rest =>
      match instr with
      | IPush n =>
          stackEvalF rest
            {| stack := n :: st.(stack);
               frame := st.(frame) |}

      | IPop =>
          match st.(stack) with
          | [] =>
              stackEvalF rest st
          | _ :: s' =>
              stackEvalF rest
                {| stack := s';
                   frame := st.(frame) |}
          end

      | IAdd =>
          match st.(stack) with
          | x :: y :: s' =>
              stackEvalF rest
                {| stack := (x + y) :: s';
                   frame := st.(frame) |}
          | _ =>
              stackEvalF rest st
          end

      | IMul =>
          match st.(stack) with
          | x :: y :: s' =>
              stackEvalF rest
                {| stack := (x * y) :: s';
                   frame := st.(frame) |}
          | _ =>
              stackEvalF rest st
          end
      end
  end.

Reserved Notation "p '/' st '==>' st'"
  (at level 40, st at level 39).

  (* Propositions for big-step execution *)
Inductive stackExecute : stackProgram -> vmState -> vmState -> Prop :=

  | E_Done : forall s f,
      [] /
        {| stack := s;
           frame := f |}
      ==>
        {| stack := s;
           frame := f |}

  | E_Push : forall n rest s f st',
      rest /
        {| stack := n :: s;
           frame := f |}
      ==> st' ->
      (IPush n :: rest) /
        {| stack := s;
           frame := f |}
      ==> st'

  | E_Pop : forall x s rest f st',
      rest /
        {| stack := s;
           frame := f |}
      ==> st' ->
      (IPop :: rest) /
        {| stack := x :: s;
           frame := f |}
      ==> st'

  | E_Add : forall x y s rest f st',
      rest /
        {| stack := (x + y) :: s;
           frame := f |}
      ==> st' ->
      (IAdd :: rest) /
        {| stack := x :: y :: s;
           frame := f |}
      ==> st'

  | E_Mul : forall x y s rest f st',
      rest /
        {| stack := (x * y) :: s;
           frame := f |}
      ==> st' ->
      (IMul :: rest) /
        {| stack := x :: y :: s;
           frame := f |}
      ==> st'
  
  | E_PopEmpty : forall rest f st',
      rest /
        {| stack := [];
          frame := f |}
      ==> st' ->
      (IPop :: rest) /
        {| stack := [];
          frame := f |}
      ==> st'

  | E_AddEmpty : forall rest f st',
      rest /
        {| stack := [];
          frame := f |}
      ==> st' ->
      (IAdd :: rest) /
        {| stack := [];
          frame := f |}
      ==> st'

  | E_AddOne : forall x rest f st',
      rest /
        {| stack := [x];
          frame := f |}
      ==> st' ->
      (IAdd :: rest) /
        {| stack := [x];
          frame := f |}
      ==> st'

  | E_MulEmpty : forall rest f st',
      rest /
        {| stack := [];
          frame := f |}
      ==> st' ->
      (IMul :: rest) /
        {| stack := [];
          frame := f |}
      ==> st'

  | E_MulOne : forall x rest f st',
      rest /
        {| stack := [x];
          frame := f |}
      ==> st' ->
      (IMul :: rest) /
        {| stack := [x];
          frame := f |}
      ==> st'

where "p '/' st '==>' st'" := (stackExecute p st st').

Example test_big_step_1 :
  <<{ PUSH 2; PUSH 5; ADD }>> /
    {| stack := [];
       frame := [] |}
  ==>
    {| stack := [7];
       frame := [] |}.
Proof.
  apply E_Push.
  apply E_Push.
  apply E_Add.
  apply E_Done.
Qed.

Example test_big_step_2 :
  <<{
    PUSH 5;
    PUSH 10;
    PUSH 25;
    PUSH 3;
    MUL;
    ADD;
    ADD
  }>> /
    {| stack := [];
       frame := [] |}
  ==>
    {| stack := [90];
       frame := [] |}.
Proof.
  apply E_Push.
  apply E_Push.
  apply E_Push.
  apply E_Push.
  apply E_Mul.
  apply E_Add.
  apply E_Add.
  apply E_Done.
Qed.

Theorem big_step_fixpoint_correctness :
  forall p si sf,
    stackEvalF p si = sf <->
    p / si ==> sf.
Proof.
  intros p si sf.
  split.
  - (* functional -> relational *)
    generalize dependent si.
    generalize dependent sf.
    induction p as [| instr rest IH]; intros sf si H.
    + simpl in H.
      subst sf.
      destruct si as [s f].
      apply E_Done.
    + destruct instr.
      * (* IPush *)
        apply IH in H.
        destruct si.
        apply E_Push.
        simpl in H.
        apply IH.
        assumption.
      * (* IPop *)
        destruct si.
        destruct stack0; simpl in H; apply IH in H.
        1: apply E_PopEmpty.
        2: apply E_Pop.
        all: assumption.
      * (* IAdd *)
        destruct si as [s f].
        destruct s as [| n s'].
        -- apply E_AddEmpty.
           apply IH in H.
           assumption.
        -- destruct s' as [| n' s'']; simpl in H; apply IH in H.
           1: apply E_AddOne.
           2: apply E_Add.
           all: assumption.
      * (* IMul *)
        destruct si as [s f].
        destruct s as [| n s'].
        -- apply E_MulEmpty.
           apply IH in H.
           assumption.
        -- destruct s' as [| n' s'']; simpl in H; apply IH in H.
           1: apply E_MulOne.
           2: apply E_Mul.
           all: assumption.
  - (* relational -> functional *)
    intro H.
    induction H; simpl; try reflexivity; try assumption.
Qed.

(* Lemma about stack programs concatenated *)
Lemma stackEvalF_app :
  forall p1 p2 st,
    stackEvalF (p1 ++ p2) st =
    stackEvalF p2 (stackEvalF p1 st).
Proof.
  induction p1 as [| i p1 IH]; intros p2 [s f].
  - reflexivity.
  - destruct i; simpl.
    + apply IH.
    + destruct s; apply IH.
    + destruct s as [| n s'].
      * apply IH.
      * destruct s' as [| n' s'']; apply IH.
    + destruct s as [| n s'].
      * apply IH.
      * destruct s' as [| n' s'']; apply IH.
Qed.
