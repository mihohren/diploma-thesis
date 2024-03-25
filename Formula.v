Require Import Coq.Unicode.Utf8.
Require Import CFOLID.Signature CFOLID.Term.

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
