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
  (s : operandStack)
  : vmState :=
  match p with
  | [] =>
      {|
        stack := s;
        frame := [];
      |}

  | instr :: rest =>
      match instr with
      | IPush n =>
          stackEvalF rest (n :: s)

      | IPop =>
          match s with
          | [] => stackEvalF rest []
          | _ :: s' => stackEvalF rest s'
          end

      | IAdd =>
          match s with
          | x :: y :: s' =>
              stackEvalF rest ((x + y) :: s')
          | [] =>
              stackEvalF rest []
          | x :: [] =>
              stackEvalF rest [x]
          end

      | IMul =>
          match s with
          | x :: y :: s' =>
              stackEvalF rest ((x * y) :: s')
          | [] =>
              stackEvalF rest []
          | x :: [] =>
              stackEvalF rest [x]
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
