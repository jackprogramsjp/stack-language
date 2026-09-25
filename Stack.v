(** * Stack-based Virtual Machine *)

(* Imports *)
From Coq Require Import Lists.List.
Import ListNotations.

(* Types *)
Inductive ty :=
  | TNat
  | TBool
  | TRef : ty -> ty.

(* Heap addresses. *)
Definition addr := nat.

(* Runtime values *)
Inductive value : Type :=
  | VNat  : nat -> value
  | VBool : bool -> value
  | VRef  : addr -> value.

(* Operand stack where it's a list of natural numbers *)
Definition operandStack := list value.

(* Frame array which is space for long-term storage *)
Definition frameArray := list value.

(* Heap maps addresses to values. *)
Definition heap := list value.

(* Binary operations *)
Inductive binOp : Type :=
  | OpAdd
  | OpSub
  | OpMul
  | OpDiv.

(* Evaluator for numbers *)
Definition evalBinOp (op : binOp) (x y : nat) : nat :=
  match op with
  | OpAdd => x + y
  | OpSub => x - y
  | OpMul => x * y
  | OpDiv => Nat.div x y
  end.

(* Imperative commands for the stack state *)
Inductive stackInstr : Type :=
  | IPush : value -> stackInstr                       (* PUSH X:NAT *)
  | IPop : stackInstr                               (* POP *)
  | IBinOp : binOp -> stackInstr                    (* BINOP *)
  | IDup : stackInstr                               (* DUP *)
  | ISwap : stackInstr                              (* SWAP *)

  (* Heap operations *)
  | IAlloc : stackInstr
  | ILoad  : stackInstr
  | IStore : stackInstr.

(* Stack program *)
Definition stackProgram := list stackInstr.

(* The actual virtual machine state *)
Record vmState := {
  stack   : operandStack;
  frame   : frameArray;
  mem     : heap
}.

(* Defin notations *)
Declare Custom Entry stack.

Notation "<<{ p }>>" := p
  (p custom stack at level 99).

Notation "'PUSH' v" := ([IPush v])
  (in custom stack at level 0,
   v constr at level 0).

Notation "'POP'" := ([IPop])
  (in custom stack at level 0).

Notation "'ADD'" := ([IBinOp OpAdd])
  (in custom stack at level 0).

Notation "'SUB'" := ([IBinOp OpSub])
  (in custom stack at level 0).

Notation "'MUL'" := ([IBinOp OpMul])
  (in custom stack at level 0).

Notation "'DIV'" := ([IBinOp OpDiv])
  (in custom stack at level 0).

Notation "'DUP'" := ([IDup])
  (in custom stack at level 0).

Notation "'SWAP'" := ([ISwap])
  (in custom stack at level 0).

Notation "'ALLOC'" := ([IAlloc])
  (in custom stack at level 0).

Notation "'LOAD'" := ([ILoad])
  (in custom stack at level 0).

Notation "'STORE'" := ([IStore])
  (in custom stack at level 0).

Notation "x ; y" := (x ++ y)
  (in custom stack at level 80,
   right associativity).

(* Errors defined by VM *)
Inductive runtimeError : Type :=
  | EDivByZero
  | EInvalidAddress.

(*  *)
Inductive stuckReason : Type :=
  | STypeMismatch
  | SStackUnderflow.

(* Result of terminating execution. *)
Inductive stackExecuteResult : Type :=
  | RState : vmState -> stackExecuteResult
  | RError : runtimeError -> stackExecuteResult
  | RStuck : stuckReason -> stackExecuteResult.

(* Direct interpreter / evaluation big-step *)
Fixpoint stackEvalF
  (p : stackProgram)
  (st : vmState)
  : stackExecuteResult :=
  match p with
  | [] =>
      RState st

  | instr :: rest =>
      match instr with

      | IPush v =>
          stackEvalF rest
            {| stack := v :: st.(stack);
               frame := st.(frame);
               mem := st.(mem) |}

      | IPop =>
          match st.(stack) with
          | [] =>
              RStuck SStackUnderflow
          | _ :: s' =>
              stackEvalF rest
                {| stack := s';
                   frame := st.(frame);
                   mem := st.(mem) |}
          end

      | IBinOp op =>
          match st.(stack) with
          | VNat x :: VNat y :: s' =>
              match op with
              | OpDiv =>
                  match x with
                  | 0 =>
                      RError EDivByZero
                  | S _ =>
                      stackEvalF rest
                        {| stack := VNat (Nat.div y x) :: s';
                           frame := st.(frame);
                           mem := st.(mem) |}
                  end

              | _ =>
                  stackEvalF rest
                    {| stack := VNat (evalBinOp op y x) :: s';
                       frame := st.(frame);
                       mem := st.(mem) |}
              end

          | _ =>
              RStuck STypeMismatch
          end

      | IDup =>
          match st.(stack) with
          | [] =>
              RStuck SStackUnderflow
          | v :: s' =>
              stackEvalF rest
                {| stack := v :: v :: s';
                   frame := st.(frame);
                   mem := st.(mem) |}
          end

      | ISwap =>
          match st.(stack) with
          | x :: y :: s' =>
              stackEvalF rest
                {| stack := y :: x :: s';
                   frame := st.(frame);
                   mem := st.(mem) |}
          | _ =>
              RStuck SStackUnderflow
          end

      | IAlloc =>
          (* implement later *)
          RError EInvalidAddress

      | ILoad =>
          (* implement later *)
          RError EInvalidAddress

      | IStore =>
          (* implement later *)
          RError EInvalidAddress
      end
  end.

Reserved Notation "p '/' st '==>' st'"
  (at level 40, st at level 39).

(* Propositions for big-step execution *)
Inductive stackExecute :
  stackProgram -> vmState -> stackExecuteResult -> Prop :=

  (* Finished program*)
  | E_Done :
      forall st,
        [] / st ==> RState st

  (* PUSH *)
  | E_Push :
      forall v rest s f h r,
        rest /
          {| stack := v :: s;
             frame := f;
             mem := h |}
        ==> r ->
        (IPush v :: rest) /
          {| stack := s;
             frame := f;
             mem := h |}
        ==> r

  (* POP *)
  | E_Pop :
      forall v s rest f h r,
        rest /
          {| stack := s;
             frame := f;
             mem := h |}
        ==> r ->
        (IPop :: rest) /
          {| stack := v :: s;
             frame := f;
             mem := h |}
        ==> r

  (* DUP *)
  | E_Dup :
      forall v s rest f h r,
        rest /
          {| stack := v :: v :: s;
             frame := f;
             mem := h |}
        ==> r ->
        (IDup :: rest) /
          {| stack := v :: s;
             frame := f;
             mem := h |}
        ==> r

  (* SWAP *)
  | E_Swap :
      forall x y s rest f h r,
        rest /
          {| stack := y :: x :: s;
             frame := f;
             mem := h |}
        ==> r ->
        (ISwap :: rest) /
          {| stack := x :: y :: s;
             frame := f;
             mem := h |}
        ==> r

  (* ADD *)
  | E_Add :
      forall x y s rest f h r,
        rest /
          {| stack := VNat (y + x) :: s;
             frame := f;
             mem := h |}
        ==> r ->
        (IBinOp OpAdd :: rest) /
          {| stack := VNat x :: VNat y :: s;
             frame := f;
             mem := h |}
        ==> r

  (* SUB *)
  | E_Sub :
      forall x y s rest f h r,
        rest /
          {| stack := VNat (y - x) :: s;
             frame := f;
             mem := h |}
        ==> r ->
        (IBinOp OpSub :: rest) /
          {| stack := VNat x :: VNat y :: s;
             frame := f;
             mem := h |}
        ==> r

  (* MUL *)
  | E_Mul :
      forall x y s rest f h r,
        rest /
          {| stack := VNat (y * x) :: s;
             frame := f;
             mem := h |}
        ==> r ->
        (IBinOp OpMul :: rest) /
          {| stack := VNat x :: VNat y :: s;
             frame := f;
             mem := h |}
        ==> r

  (* DIV with a valid denominator *)
  | E_Div :
      forall x y s rest f h r,
        x <> 0 ->
        rest /
          {| stack := VNat (Nat.div y x) :: s;
             frame := f;
             mem := h |}
        ==> r ->
        (IBinOp OpDiv :: rest) /
          {| stack := VNat x :: VNat y :: s;
             frame := f;
             mem := h |}
        ==> r

  (* DIV with runtime error *)
  | E_DivZero :
      forall y s rest f h,
        (IBinOp OpDiv :: rest) /
          {| stack := VNat 0 :: VNat y :: s;
             frame := f;
             mem := h |}
        ==> RError EDivByZero

where "p '/' st '==>' r" := (stackExecute p st r).

(* CoInductive stackExecuteDiverges :
    stackProgram -> vmState -> Prop :=
  ...
. *)

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
  apply E_BinOp.
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
  apply E_BinOp.
  apply E_BinOp.
  apply E_BinOp.
  apply E_Done.
Qed.

Example test_big_step_3 :
  <<{
    PUSH 5;
    PUSH 10;
    ADD;
    PUSH 20;
    SWAP;
    DUP;
    ADD
  }>> /
    {| stack := [];
       frame := [] |}
  ==>
    {| stack := [30; 20];
       frame := [] |}.
Proof.
  apply E_Push.
  apply E_Push.
  apply E_BinOp.
  apply E_Push.
  apply E_Swap.
  apply E_Dup.
  apply E_BinOp.
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
        assumption.
      * (* IPop *)
        destruct si.
        destruct stack0; simpl in H; apply IH in H.
        1: apply E_PopEmpty.
        2: apply E_Pop.
        all: assumption.
      * (* IBinOp *)
        destruct si as [s f].
        destruct s as [| n s'].
        -- apply E_BinOpEmpty.
           apply IH in H.
           assumption.
        -- destruct s' as [| n' s'']; simpl in H; apply IH in H.
           1: apply E_BinOpOne.
           2: apply E_BinOp.
           all: assumption.
      * (* IDup *)
        destruct si.
        destruct stack0; simpl in H; apply IH in H.
        1: apply E_DupEmpty.
        2: apply E_Dup.
        all: assumption.
      * (* ISwap *)
        destruct si as [s f].
        destruct s as [| n s'].
        -- apply E_SwapEmpty.
           apply IH in H.
           assumption.
        -- destruct s' as [| n' s'']; simpl in H; apply IH in H.
           1: apply E_SwapOne.
           2: apply E_Swap.
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
    + destruct s as [| n s'].
      * apply IH.
      * destruct s' as [| n' s'']; apply IH.
Qed.
