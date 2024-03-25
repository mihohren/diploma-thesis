Require Import Coq.Unicode.Utf8.
Require Import Coq.Vectors.Vector.
Require Import CFOLID.Signature.

Module V := Vector.
Definition vec := V.t.

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

Arguments V.nil {A}.
Arguments V.cons {A} _ {n}.

Section term_examples.
  Example peano_zero :=
    TFunc o V.nil.

  Example peano_one :=
    TFunc s (V.cons peano_zero V.nil).

  Example peano_plus :=
    TFunc plus (V.cons peano_zero (V.cons peano_one V.nil)).
End term_examples.
(* As we can see, manually defining terms is a bit clunky.
   The problem is, if we define a signature to be implicit for
   [var] and [func], Coq can not deduce that [o] is of type
   [FuncS PeanoSig] - it thinks that [o] is of type [PeanoFuncT]
   (and indeed it is).

   By addiong [Coercion]s, readability has improved a bit.
 *)
