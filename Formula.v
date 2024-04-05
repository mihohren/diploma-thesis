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
   
  Definition FExists X (φ : formula X⁺) : formula X := FNeg _ (FAll _ (FNeg _ φ)).

End formula.

Arguments formula : clear implicits.
Arguments FPred [Σ X] R _.
Arguments FIndPred [Σ X] R _.
Arguments FImp [Σ X] _ _.
Arguments FNeg [Σ X] _.
Arguments FAll [Σ X] _.
Arguments FExists [Σ X] _.



