Require Import CFOLID.Signature CFOLID.Term CFOLID.Formula CFOLID.Structure.

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

