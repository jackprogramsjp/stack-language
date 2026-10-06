(** * Stack-based Virtual Machine *)

(* Imports *)
From Coq Require Import Lists.List.
Import ListNotations.

From SL Require Import ListHelpers.

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
  | IAllocConst : nat -> stackInstr
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

(* Values inside stack syntax *)
Notation "n" := (VNat n)
  (in custom stack at level 0,
   n constr at level 0).

Notation "'true'" := (VBool true)
  (in custom stack at level 0).

Notation "'false'" := (VBool false)
  (in custom stack at level 0).

Notation "'REF' n" := (VRef n)
  (in custom stack at level 0,
   n constr at level 0).

(* Instructions *)
Notation "'PUSH' v" := ([IPush v])
  (in custom stack at level 10,
   v custom stack at level 0).

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

Notation "'ALLOC_CONST' n" := ([IAllocConst n])
  (in custom stack at level 10,
   n constr at level 0).

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

      | IAllocConst size =>
          let a := length st.(mem) in
          stackEvalF rest
            {| stack := VRef a :: st.(stack);
              frame := st.(frame);
              mem := st.(mem) ++ repeat (VNat 0) size |}

      | IAlloc =>
          match st.(stack) with
          | VNat n :: s' =>
              let a := length st.(mem) in
              stackEvalF rest
                {| stack := VRef a :: s';
                   frame := st.(frame);
                   mem := st.(mem) ++ repeat (VNat 0) n |}
          | _ :: _ =>
              RStuck STypeMismatch
          | [] =>
              RStuck SStackUnderflow
          end

      | ILoad =>
          match st.(stack) with
          | VRef a :: s' =>
              match nth_error st.(mem) a with
              | Some v =>
                  stackEvalF rest
                    {| stack := v :: s';
                      frame := st.(frame);
                      mem := st.(mem) |}
              | None => RError EInvalidAddress
              end
          | _ :: _ =>
              RStuck STypeMismatch
          | [] =>
              RStuck SStackUnderflow
          end

      | IStore =>
          match st.(stack) with
          | v :: VRef a :: s' =>
              match nth_error st.(mem) a with
              | Some _ =>
                  stackEvalF rest
                    {| stack := s';
                      frame := st.(frame);
                      mem := update_nth a v st.(mem) |}
              | None => RError EInvalidAddress
              end
          | _ :: _ :: _ =>
              RStuck STypeMismatch
          | [_] =>
              RStuck SStackUnderflow
          | [] =>
              RStuck SStackUnderflow
          end
      end
  end.

(* Propositions for big-step execution *)
Inductive stackExecute :
  stackProgram -> vmState -> stackExecuteResult -> Prop :=

  (* Finished program *)
  | E_Done :
      forall st,
        stackExecute [] st (RState st)

  (* PUSH *)
  | E_Push :
      forall v rest s f h r,
        stackExecute rest
          {| stack := v :: s;
             frame := f;
             mem := h |}
          r ->
        stackExecute (IPush v :: rest)
          {| stack := s;
             frame := f;
             mem := h |}
          r

  (* POP *)
  | E_Pop :
      forall v s rest f h r,
        stackExecute rest
          {| stack := s;
             frame := f;
             mem := h |}
          r ->
        stackExecute (IPop :: rest)
          {| stack := v :: s;
             frame := f;
             mem := h |}
          r

  (* DUP *)
  | E_Dup :
      forall v s rest f h r,
        stackExecute rest
          {| stack := v :: v :: s;
             frame := f;
             mem := h |}
          r ->
        stackExecute (IDup :: rest)
          {| stack := v :: s;
             frame := f;
             mem := h |}
          r

  (* SWAP *)
  | E_Swap :
      forall x y s rest f h r,
        stackExecute rest
          {| stack := y :: x :: s;
             frame := f;
             mem := h |}
          r ->
        stackExecute (ISwap :: rest)
          {| stack := x :: y :: s;
             frame := f;
             mem := h |}
          r

  (* ADD *)
  | E_Add :
      forall x y s rest f h r,
        stackExecute rest
          {| stack := VNat (y + x) :: s;
             frame := f;
             mem := h |}
          r ->
        stackExecute (IBinOp OpAdd :: rest)
          {| stack := VNat x :: VNat y :: s;
             frame := f;
             mem := h |}
          r

  (* SUB *)
  | E_Sub :
      forall x y s rest f h r,
        stackExecute rest
          {| stack := VNat (y - x) :: s;
             frame := f;
             mem := h |}
          r ->
        stackExecute (IBinOp OpSub :: rest)
          {| stack := VNat x :: VNat y :: s;
             frame := f;
             mem := h |}
          r

  (* MUL *)
  | E_Mul :
      forall x y s rest f h r,
        stackExecute rest
          {| stack := VNat (y * x) :: s;
             frame := f;
             mem := h |}
          r ->
        stackExecute (IBinOp OpMul :: rest)
          {| stack := VNat x :: VNat y :: s;
             frame := f;
             mem := h |}
          r

  (* DIV with a valid denominator *)
  | E_Div :
      forall x y s rest f h r,
        x <> 0 ->
        stackExecute rest
          {| stack := VNat (Nat.div y x) :: s;
             frame := f;
             mem := h |}
          r ->
        stackExecute (IBinOp OpDiv :: rest)
          {| stack := VNat x :: VNat y :: s;
             frame := f;
             mem := h |}
          r

  (* DIV with runtime error *)
  | E_DivZero :
      forall y s rest f h,
        stackExecute (IBinOp OpDiv :: rest)
          {| stack := VNat 0 :: VNat y :: s;
             frame := f;
             mem := h |}
          (RError EDivByZero)
  
  (* ALLOC_CONST *)
  | E_AllocConst :
      forall size rest s f h r,
        let a := length h in
        stackExecute rest
          {| stack := VRef a :: s;
             frame := f;
             mem := h ++ repeat (VNat 0) size |}
          r ->
        stackExecute (IAllocConst size :: rest)
          {| stack := s;
             frame := f;
             mem := h |}
          r

  (* ALLOC *)
  | E_Alloc :
      forall n rest s f h r,
        let a := length h in
        stackExecute rest
          {| stack := VRef a :: s;
             frame := f;
             mem := h ++ repeat (VNat 0) n |}
          r ->
        stackExecute (IAlloc :: rest)
          {| stack := VNat n :: s;
             frame := f;
             mem := h |}
          r

  (* LOAD *)
  | E_Load :
      forall a v rest s f h r,
        nth_error h a = Some v ->
        stackExecute rest
          {| stack := v :: s;
             frame := f;
             mem := h |}
          r ->
        stackExecute (ILoad :: rest)
          {| stack := VRef a :: s;
             frame := f;
             mem := h |}
          r

  (* LOAD with invalid heap address *)
  | E_LoadInvalidAddress :
      forall a rest s f h,
        nth_error h a = None ->
        stackExecute (ILoad :: rest)
          {| stack := VRef a :: s;
             frame := f;
             mem := h |}
          (RError EInvalidAddress)

  (* STORE *)
  | E_Store :
      forall a v old rest s f h r,
        nth_error h a = Some old ->
        stackExecute rest
          {| stack := s;
             frame := f;
             mem := update_nth a v h |}
          r ->
        stackExecute (IStore :: rest)
          {| stack := v :: VRef a :: s;
             frame := f;
             mem := h |}
          r

  (* STORE with invalid heap address *)
  | E_StoreInvalidAddress :
      forall a v rest s f h,
        nth_error h a = None ->
        stackExecute (IStore :: rest)
          {| stack := v :: VRef a :: s;
             frame := f;
             mem := h |}
          (RError EInvalidAddress)
  

    (* ALLOC type mismatch *)
  | E_AllocTypeMismatch :
      forall v rest s f h,
        (forall n, v <> VNat n) ->
        stackExecute (IAlloc :: rest)
          {| stack := v :: s;
             frame := f;
             mem := h |}
          (RStuck STypeMismatch)

  (* ALLOC stack underflow *)
  | E_AllocUnderflow :
      forall rest f h,
        stackExecute (IAlloc :: rest)
          {| stack := [];
             frame := f;
             mem := h |}
          (RStuck SStackUnderflow)

  (* LOAD type mismatch *)
  | E_LoadTypeMismatch :
      forall v rest s f h,
        (forall a, v <> VRef a) ->
        stackExecute (ILoad :: rest)
          {| stack := v :: s;
             frame := f;
             mem := h |}
          (RStuck STypeMismatch)

  (* LOAD stack underflow *)
  | E_LoadUnderflow :
      forall rest f h,
        stackExecute (ILoad :: rest)
          {| stack := [];
             frame := f;
             mem := h |}
          (RStuck SStackUnderflow)

  (* STORE type mismatch: enough operands, but second is not a reference *)
  | E_StoreTypeMismatch :
      forall v v2 rest s f h,
        (forall a, v2 <> VRef a) ->
        stackExecute (IStore :: rest)
          {| stack := v :: v2 :: s;
             frame := f;
             mem := h |}
          (RStuck STypeMismatch)

  (* STORE with only one stack value *)
  | E_StoreUnderflowOne :
      forall v rest f h,
        stackExecute (IStore :: rest)
          {| stack := [v];
             frame := f;
             mem := h |}
          (RStuck SStackUnderflow)

  (* STORE with empty stack *)
  | E_StoreUnderflowEmpty :
      forall rest f h,
        stackExecute (IStore :: rest)
          {| stack := [];
             frame := f;
             mem := h |}
          (RStuck SStackUnderflow).

(* CoInductive stackExecuteDiverges :
    stackProgram -> vmState -> Prop :=
  ...
. *)

Example test_big_step_1 :
  stackExecute <<{ PUSH 2; PUSH 5; ADD }>>
    {| stack := [];
       frame := [];
       mem   := [] |}
    (RState
      {| stack := [VNat 7];
         frame := [];
         mem   := [] |}).
Proof.
  apply E_Push.
  apply E_Push.
  apply E_Add.
  apply E_Done.
Qed.

Example test_big_step_2 :
  stackExecute <<{
    PUSH 5;
    PUSH 10;
    PUSH 25;
    PUSH 3;
    MUL;
    ADD;
    ADD
  }>>
    {| stack := [];
       frame := [];
       mem   := [] |}
    (RState
      {| stack := [VNat 90];
         frame := [];
         mem   := [] |}).
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

Example test_big_step_3 :
  stackExecute <<{
    PUSH 5;
    PUSH 10;
    ADD;
    PUSH 20;
    SWAP;
    DUP;
    ADD
  }>>
    {| stack := [];
       frame := [];
       mem   := [] |}
    (RState
      {| stack := [VNat 30; VNat 20];
         frame := [];
         mem   := [] |}).
Proof.
  apply E_Push.
  apply E_Push.
  apply E_Add.
  apply E_Push.
  apply E_Swap.
  apply E_Dup.
  apply E_Add.
  apply E_Done.
Qed.

Theorem big_step_fixpoint_correctness :
  forall p si sf,
    stackEvalF p si = sf <-> stackExecute p si sf.
Proof.
  intros p si sf.
Admitted.

(* Lemma about stack programs concatenated *)
Lemma stackEvalF_app :
  forall p1 p2 st,
    stackEvalF p1 st = RState st ->
    stackEvalF (p1 ++ p2) st =
    stackEvalF p2 st.
Proof.
  Admitted.
