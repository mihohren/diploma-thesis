Require Coq.Unicode.Utf8.
Require Coq.Vectors.Vector.
Require Import CFOLID.Signature.

Definition vec := Vector.t.

Section structure.
  Variable Σ : signature.

  Structure structure := {      (* struktura *)
      domain : Type;            (* nosač *)
      interpF : forall f : FuncS Σ, vec domain (FuncArr f) -> domain;
      interpP : forall P : PredS Σ, vec domain (PredArr P) -> Prop;
      interpIP : forall P : IndPredS Σ, vec domain (IndPredArr P) -> Prop;
    }.
End structure.

Arguments structure {Σ}.
Arguments domain {Σ}.
Arguments interpF {Σ}.
Arguments interpP {Σ}.
Arguments interpIP {Σ}.
Notation "| M |" := (domain M) (no associativity, at level 150).
