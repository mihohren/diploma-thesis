Require Import Coq.Unicode.Utf8.
Require Coq.Vectors.Vector.

Record signature := mkSig {
                        FuncS : Type;
                        FuncArr : FuncS -> nat;
                        PredS : Type; (* ordinary predicate symbols *)
                        PredArr : PredS -> nat;
                        IndPredS : Type; (* inductive predicate symbols *)
                        IndPredArr : IndPredS -> nat
                      }.


Arguments FuncArr {Σ} : rename.
Arguments PredArr {Σ} : rename.
Arguments IndPredArr {Σ} : rename.

Section Peano.
  Inductive PeanoFuncT := o | s | plus | mult.
  Definition PeanoFuncArr (f : PeanoFuncT) : nat :=
    match f with
    | o => 0
    | s => 1
    | plus => 2
    | mult => 2
    end.

  Inductive PeanoPredT := eq.
  Definition PeanoPredArr (f : PeanoPredT) : nat :=
    match f with
    | eq => 2
    end.

  Definition PeanoSig : signature :=
    {|
      FuncS := PeanoFuncT;
      FuncArr := PeanoFuncArr;
      PredS := PeanoPredT;
      PredArr := PeanoPredArr;
      IndPredS := Empty_set;
      IndPredArr := fun e => match e with end
    |}.

  Coercion PeanoFuncT_FuncS (f : PeanoFuncT) : FuncS PeanoSig := f.
  Coercion PeanoPredT_PredS (R : PeanoPredT) : PredS PeanoSig := R.
End Peano.

Module V := Vector.
Definition vec := V.t.
Print V.t.

Section term.
  Variable Σ : signature.
  Definition var := nat.

  Inductive term : Type :=
  | TVar : var -> term
  | TFunc : forall f : FuncS Σ, vec term (FuncArr f) -> term.
  (* constant symbols are function symbols with arity 0 *)
End term.

Arguments TVar {Σ}.
Arguments TFunc {Σ}.

Arguments V.nil {A}.
Arguments V.cons {A} _ {n}.

Section term_examples.
  Example peano_zero :=
    TFunc o V.nil.

  Example peano_one :=
    TFunc s (V.cons peano_zero V.nil).

  Example peano_plus :=
    TFunc plus (V.cons peano_zero (V.cons peano_one V.nil)).
End term_examples.
(* As we can see, manually defining terms is a bit clunky.
   The problem is, if we define a signature to be implicit for
   [var] and [func], Coq can not deduce that [o] is of type
   [FuncS PeanoSig] - it thinks that [o] is of type [PeanoFuncT]
   (and indeed it is).

   By addiong [Coercion]s, readability has improved a bit.
 *)

Section formula.
  Variable Σ : signature.

  Inductive formula : Type :=
  | FPred : forall R : PredS Σ, vec (term Σ) (PredArr R) -> formula
  | FIndPred : forall R : IndPredS Σ, vec (term Σ) (IndPredArr R) -> formula
  | FAnd : formula -> formula -> formula
  | FOr  : formula -> formula -> formula
  | FImp : formula -> formula -> formula
  | FNeg : formula -> formula
  | FAll : (var -> formula) -> formula
  | FExist : (var -> formula) -> formula.  
End formula.
