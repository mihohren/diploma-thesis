Require Import Coq.Unicode.Utf8.
Require Coq.Vectors.Vector.

Record Signature := mkSignature {
                        FuncS : Type;
                        FuncArr : FuncS -> nat;
                        RelS : Type;
                        RelArr : RelS -> nat
                      }.

Arguments FuncArr [_].
Arguments RelArr [_].

Section Peano.
  Inductive PeanoFuncT := o | s | plus | mult.
  Definition PeanoFuncArr (f : PeanoFuncT) : nat :=
    match f with
    | o => 0
    | s => 1
    | plus => 2
    | mult => 2
    end.

  Inductive PeanoRelT := eq.
  Definition PeanoRelArr (f : PeanoRelT) : nat :=
    match f with
    | eq => 2
    end.

  Definition PeanoSig : Signature :=
    {|
      FuncS := PeanoFuncT;
      FuncArr := PeanoFuncArr;
      RelS := PeanoRelT;
      RelArr := PeanoRelArr
    |}.

  Coercion PeanoFuncT_FuncS (f : PeanoFuncT) : FuncS PeanoSig := f.
  Coercion PeanoRelT_RelS (R : PeanoRelT) : RelS PeanoSig := R.
End Peano.

Module V := Vector.
Definition Vec := V.t.
Print V.t.

Section term.
  Variable σ : Signature.

  Inductive term : Type :=
  | var : nat -> term
  | func : forall f : FuncS σ, Vec term (FuncArr f) -> term.
End term.

Arguments var {σ}.
Arguments func {σ}.

Arguments V.nil {A}.
Arguments V.cons {A} h {n}.

Section term_examples.
  Example peano_zero :=
    func o V.nil.

  Example peano_one :=
    func s (V.cons peano_zero V.nil).

  Example peano_plus :=
    func plus (V.cons peano_zero (V.cons peano_one V.nil)).
End term_examples.
(* As we can see, manually defining terms is a bit clunky.
   The problem is, if we define a signature to be implicit for
   [var] and [func], Coq can not deduce that [o] is of type
   [FuncS PeanoSig] - it thinks that [o] is of type [PeanoFuncT]
   (and indeed it is).

   By addiong [Coercion]s, readability has improved a bit.
 *)

Section formula.
  Variable σ : Signature.

  (* A FOL formula.  To make this a FOL_ID formula,
     we need to differentiate between normal relational symbols
     and inductive relational symbols. *)
  Inductive formula : Type :=
  | formRel : forall R : RelS σ, Vec (term σ) (RelArr R) -> formula
  | formAnd : formula -> formula -> formula
  | formOr  : formula -> formula -> formula
  | formImp : formula -> formula -> formula
  | formNeg : formula -> formula
  | formAll : (nat -> formula) -> formula.
End formula.
