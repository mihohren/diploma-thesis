Require Import Base Signature Term.

Section formula.
  Context {Σ : signature}.

  Import VarNotations.
  
  Inductive formula (X : Vars) : Type :=
  | FPred : forall R : PredS Σ, vec (term Σ X) (pred_ar R) -> formula X
  | FIndPred : forall R : IndPredS Σ, vec (term Σ X) (indpred_ar R) -> formula X
  | FImp : formula X -> formula X -> formula X
  | FNeg : formula X -> formula X
  | FAll : formula X⁺ -> formula X.
   
End formula.

Arguments formula : clear implicits.
