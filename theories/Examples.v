From Coq Require Import Vector.
Require Import Base Syntax Semantics InductiveDefinitions.
Import VectorNotations.

Inductive Func__PA :=
| PA_zero
| PA_succ
| PA_add
| PA_mult.

Definition fun_ar__PA (s : Func__PA) : nat :=
  match s with
  | PA_zero => 0
  | PA_succ => 1
  | PA_add  => 2
  | PA_mult => 2
  end.

Inductive Pred__PA := PA_eq.
Definition pred_ar__PA (s : Pred__PA) : nat :=
  match s with
  | PA_eq => 2
  end.

Inductive IndPred__PA :=
| PA_N
| PA_E
| PA_O.
Definition indpred_ar__PA (s : IndPred__PA) : nat :=
  match s with
  | PA_N => 1
  | PA_E => 1
  | PA_O => 1
  end.

Definition Σ__PA : signature
  := {|
    FuncS := Func__PA;
    fun_ar := fun_ar__PA;
    PredS := Pred__PA;
    pred_ar := pred_ar__PA;
    IndPredS := IndPred__PA;
    indpred_ar := indpred_ar__PA;
  |}.

Example PA_one (* s(o) *): term Σ__PA.
  refine (@TFunc Σ__PA PA_succ _).
  refine ([_]).
  apply TFunc with PA_zero.
  apply V.nil.
Defined.

Example PA_refl (* ∀ x, x = x *): formula Σ__PA.
  refine (FAll _).
  refine (@FPred Σ__PA PA_eq _).
  apply V.cons.
  - exact (var_term 0).
  - exact ([var_term 0]).
Defined.

Definition PA_prod_N_zero : @production Σ__PA.
  refine (@mkProd Σ__PA nil nil PA_N _).
  refine [(@TFunc Σ__PA PA_zero V.nil)].
Defined.

Print PA_prod_N_zero.

Definition PA_prod_N_succ : @production Σ__PA.
  refine (@mkProd Σ__PA nil _ PA_N _).
  - refine (cons _ nil). exists PA_N; refine [(var_term 0)].
  - refine [(@TFunc Σ__PA PA_succ ([var_term 0]))].
Defined.

Print PA_prod_N_succ.

Definition PA_prod_E_zero : @production Σ__PA.
  refine (@mkProd Σ__PA nil nil PA_E _).
  refine ( [ @TFunc Σ__PA PA_zero ([]) ] ).
Defined.

Definition PA_prod_E_succ : @production Σ__PA.
  refine (@mkProd Σ__PA nil _ PA_E _).
  - refine (cons _ nil). exists PA_O; refine ([var_term 0]).
  - refine [_].
    refine (@TFunc Σ__PA PA_succ _).
    refine [var_term 0].
Defined.

Definition PA_prod_O_succ : @production Σ__PA.
  refine (@mkProd Σ__PA nil _ PA_O _).
  - refine (cons _ nil). exists PA_E; refine ([var_term 0]).
  - refine [_].
    refine (@TFunc Σ__PA PA_succ _).
    refine ([var_term 0]).
Defined.

Inductive Φ__PA : @production Σ__PA -> Prop :=
| ID_N_zero : Φ__PA PA_prod_N_zero
| ID_N_succ : Φ__PA PA_prod_N_succ
| ID_E_zero : Φ__PA PA_prod_E_zero
| ID_E_succ : Φ__PA PA_prod_E_succ
| ID_O_succ : Φ__PA PA_prod_O_succ.

Inductive IsNat : nat -> Prop :=
| isNat : forall n, IsNat n.

Definition M__PA : @structure Σ__PA.
  refine (Build_structure nat _ _ _).
  - intros []; cbn.
    + intros. exact 0.
    + intros n. exact (S (V.hd n)).
    + intros xy. exact (V.hd xy + V.hd (V.tl xy)).
    + intros xy. exact (V.hd xy * V.hd (V.tl xy)).
  - intros []. cbn. intros args.
    exact (V.hd args = V.hd (V.tl args)).
  - intros []; cbn; intros args.
    + exact (IsNat (V.hd args)).
    + exact (Nat.Even (V.hd args)).
    + exact (Nat.Odd (V.hd args)).
Defined.

Lemma standard_model__PA : @standard_model Σ__PA Φ__PA M__PA.
Admitted.
