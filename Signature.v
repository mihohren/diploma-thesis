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
