Require Import Base Signature Term.

Section formula.
  Variable Σ : signature.

  Inductive formula : Type :=
  | FPred : forall R : PredS Σ, vec (term Σ) (PredArr R) -> formula
  | FIndPred : forall R : IndPredS Σ, vec (term Σ) (IndPredArr R) -> formula
  | FImp : formula -> formula -> formula
  | FNeg : formula -> formula
  | FAll : (var -> formula) -> formula.

  Inductive FV : formula -> E.Ensemble var :=
  | FV_Pred :
    forall (R : PredS Σ) (args : vec (term Σ) (PredArr R)) (v : var),
      V.Exists (fun st => Var st v) args -> FV (FPred R args) v
  | FV_IndPred:
    forall (R : IndPredS Σ) (args : vec (term Σ) (IndPredArr R)) (v : var),
      V.Exists (fun st => Var st v) args -> FV (FIndPred R args) v
  | FV_Imp : forall (F G : formula) (v : var),
      FV F v \/ FV G v -> FV (FImp F G) v
  | FV_Neg : forall (F : formula) (v : var),
      FV F v -> FV (FNeg F) v
  | FV_All : forall (F : var -> formula) (v : var) (x : var),
      FV (F v) x /\ x <> v -> FV (FAll F) x.

  Notation " x '∈' 'FV(' F ')' " := (FV F x)
                                      ( no associativity, at level 150).
End formula.
