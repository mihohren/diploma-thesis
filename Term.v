Require Import Coq.Unicode.Utf8.
Require Import Coq.Vectors.Vector.
Require Import CFOLID.Signature.

Definition vec := Vector.t.

Section term.
  Variable Σ : signature.
  Definition var := nat.

  Inductive term : Type :=
  | TVar : var -> term
  | TFunc : forall f : FuncS Σ, vec term (FuncArr f) -> term.
  (* constant symbols are function symbols with arity 0 *)
End term.

Arguments TVar {Σ}.
Arguments TFunc {Σ}.
