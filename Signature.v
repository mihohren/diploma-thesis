Require Import Base.

Structure signature := {
    FuncS : Type;
    FuncArr : FuncS -> nat;
    PredS : Type; (* ordinary predicate symbols *)
    PredArr : PredS -> nat;
    IndPredS : Type; (* inductive predicate symbols *)
    IndPredArr : IndPredS -> nat
  }.

Arguments FuncArr {Σ} _ : rename.
Arguments PredArr {Σ} _ : rename.
Arguments IndPredArr {Σ} _ : rename.
