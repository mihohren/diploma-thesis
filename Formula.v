Require Import Base Signature Term.

Section formula.
  Context {Σ : signature}.

  Inductive formula : Type :=
  | FPred : forall R : PredS Σ, vec (term Σ) (pred_ar R) -> formula
  | FIndPred : forall R : IndPredS Σ, vec (term Σ) (indpred_ar R) -> formula
  | FImp : formula -> formula -> formula
  | FNeg : formula -> formula
  | FAll : formula -> formula.

  Inductive FV : formula -> E.Ensemble var :=
  | FV_Pred : forall R args v,
      V.Forall (fun t => ~ Var t v) args -> FV (FPred R args) v
  | FV_IndPred : forall R args v,
      V.Forall (fun t => ~ Var t v) args -> FV (FIndPred R args) v
  | FV_Imp_l : forall F G v, FV F v -> FV (FImp F G) v
  | FV_Imp_r : forall F G v, FV G v -> FV (FImp F G) v
  | FV_Neg : forall F v, FV F v -> FV (FNeg F) v
  | FV_All : forall F v, FV F v -> FV (FAll F) (S v).
    
End formula.

Arguments formula : clear implicits.
