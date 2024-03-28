Require Import Base.

Structure signature := {
    FuncS : Type;
    fun_ar : FuncS -> nat;
    PredS : Type;
    pred_ar : PredS -> nat;
    IndPredS : Type;
    indpred_ar : IndPredS -> nat
  }.

Arguments fun_ar {Σ} f : rename.
Arguments pred_ar {Σ} P : rename.
Arguments indpred_ar {Σ} P : rename.
