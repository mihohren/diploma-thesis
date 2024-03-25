Require Import Coq.Unicode.Utf8.

Structure signature := {
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
