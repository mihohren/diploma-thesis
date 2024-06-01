From Coq Require Import Vector.
Require Import Base Syntax Semantics InductiveDefinitions LKID.
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

Inductive NAT : nat -> Prop :=
| NO : NAT 0
| NS : forall n, NAT n -> NAT (S n).

Lemma NAT_all : forall n, NAT n.
  induction n; constructor; auto.
Qed.

Inductive EVEN : nat -> Prop :=
| EO : EVEN 0
| ES : forall n, ODD n -> EVEN (S n)
with ODD : nat -> Prop :=
| OS : forall n, EVEN n -> ODD (S n).

Section Eind.
  Context (P : nat -> Prop).
  Context (HO : P O).
  Context (HS : forall n, EVEN n -> P n -> P (S (S n))).
  Definition EVEN_ind2 : forall n, EVEN n -> P n.
    fix IND 1. intros n HE. destruct n.
    - apply HO.
    - destruct n.
      + inversion HE; inversion H0.
      + apply HS.
        * inversion HE. inversion H0. assumption.
        * apply IND. inversion HE. inversion H0. assumption.
  Defined.
End Eind.

Section Oind.
  Context (P : nat -> Prop).
  Context (HO : P 1).
  Context (HS : forall n, ODD n -> P n -> P (S (S n))).
  Definition ODD_ind2 : forall n, ODD n -> P n.
    fix IND 1. intros n HODD. destruct n.
    - inversion HODD.
    - destruct n.
      + apply HO.
      + apply HS.
        * inversion HODD. inversion H0. assumption.
        * apply IND. inversion HODD. inversion H0. assumption.
  Defined.
End Oind.

Lemma pair_induction (P : nat -> Prop) :
  P 0 -> P 1 -> (forall n, P n -> P (S n) -> P (S (S n))) -> forall n, P n.
Proof.
  intros H0 H1 HS n.
  enough (P n /\ P (S n)) by tauto.
  induction n; intuition.
Qed.

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
    + exact (NAT (V.hd args)).
    + exact (EVEN (V.hd args)).
    + exact (ODD (V.hd args)).
Defined.

Import VectorNotations.

Lemma NAT_φ_Φ_ω: forall n, @φ_Φ_ω Σ__PA M__PA Φ__PA PA_N (V.cons n V.nil).
  induction n.
  - exists 1. unfold φ_Φ_n, φ_Φ, φ_P. exists PA_prod_N_zero, (conj eq_refl ID_N_zero).
    unfold φ_pr. cbn. eexists; intuition.
  - destruct IHn as [α IH]. exists (S α).
    cbn. unfold φ_Φ, φ_P. exists PA_prod_N_succ, (conj eq_refl ID_N_succ).
    unfold φ_pr. cbn. intuition. exists (fun x => match x with
                                          | 0 => n
                                          | S y => x
                                          end).
    intuition. destruct P; cbn.
    + apply inj_pair2 in H0. subst. cbn. assumption.
    + inversion H0.
    + inversion H0.
      Unshelve. intros n. exact n.
Qed.

Lemma EVEN_φ_Φ_ω : forall n, EVEN n -> @φ_Φ_ω Σ__PA M__PA Φ__PA PA_E (V.cons n V.nil).
Proof.
  intros n HE. induction HE using EVEN_ind2.
  - exists 1. unfold φ_Φ_n, φ_Φ, φ_P. exists PA_prod_E_zero, (conj eq_refl ID_E_zero).
    unfold φ_pr. cbn. eexists; intuition.
  - destruct IHHE as [a Ha]. exists (S (S a)); cbn.
    unfold φ_Φ at 1. unfold φ_P at 1.
    exists PA_prod_E_succ, (conj eq_refl ID_E_succ); cbn.
    unfold φ_pr. cbn. exists (fun x => match x with
                               | O => S n
                               | S y => x
                               end); intuition.
    destruct P; try discriminate.
    apply inj_pair2 in H0; subst; cbn.
    unfold φ_Φ, φ_P. exists PA_prod_O_succ, (conj eq_refl ID_O_succ); cbn.
    unfold φ_pr; cbn. exists (fun x => match x with
                               | O => n
                               | S y => x
                               end); intuition.
    destruct P; try discriminate.
    apply inj_pair2 in H0; subst; cbn. assumption.
    Unshelve.
    intros n; exact n.
Qed.

Lemma φ_Φ_ω_EVEN : forall n, @φ_Φ_ω Σ__PA M__PA Φ__PA PA_E (V.cons n V.nil) -> EVEN n.
Proof.
  intros n [α Hα].
  revert Hα. induction α.
  - inversion 1.
  - inversion 1. destruct H as [[Heq HΦ] H]. cbn in H.
    destruct H as (ρ & Hpreds & Hindpreds & Heval); cbn in *. destruct x; cbn in *.
    subst indcons; cbn in *. apply IHα.
    destruct α.
    + cbn. 
Admitted.

Lemma ODD_φ_Φ_ω : forall n, ODD n -> @φ_Φ_ω Σ__PA M__PA Φ__PA PA_O (V.cons n V.nil).
Proof.
  intros n HO. induction HO using ODD_ind2.
  - exists 2. unfold φ_Φ_n, φ_Φ, φ_P; cbn. exists PA_prod_O_succ, (conj eq_refl ID_O_succ); cbn.
    unfold φ_pr; cbn. exists (fun x => x); cbn; intuition.
    injection H0; intros Heq; subst.
    exists PA_prod_E_zero, (conj eq_refl ID_E_zero); cbn.
    exists (fun x => x); cbn; intuition. apply inj_pair2 in H0; subst; reflexivity.
  - destruct IHHO as [a Ha]; exists (S (S a)).
    cbn; unfold φ_Φ, φ_P at 1.
    exists PA_prod_O_succ; cbn. exists (conj eq_refl ID_O_succ).
    unfold φ_pr; cbn.
    exists (fun x => S n); cbn; intuition.
    injection H0; intros Heq; subst.
    apply inj_pair2 in H0; subst; cbn.
    exists PA_prod_E_succ, (conj eq_refl ID_E_succ); cbn.
    unfold φ_pr; cbn; exists (fun x => n); cbn; intuition.
    injection H0; intros Heq; subst.
    apply inj_pair2 in H0; subst; assumption.
Qed.   
    
Lemma standard_model__PA : @standard_model Σ__PA Φ__PA M__PA.
Proof.
  unfold standard_model. intros []; cbn; intros ts; split; intros H.
  - rewrite V.eta. remember (V.tl ts) as tail. cbn in *. pose proof (V.nil_spec tail).
    subst. rewrite H0. apply NAT_φ_Φ_ω.
  - apply NAT_all.
  - rewrite V.eta. remember (V.tl ts) as tail. cbn in *. pose proof (V.nil_spec tail).
    subst. rewrite H0. apply EVEN_φ_Φ_ω. assumption.
  - apply φ_Φ_ω_EVEN. rewrite (V.eta ts) in H. pose proof (V.nil_spec (V.tl ts)).
    rewrite H0 in H. assumption.
  - rewrite V.eta. remember (V.tl ts) as tail. cbn in *. pose proof (V.nil_spec tail).
    subst. rewrite H0. apply ODD_φ_Φ_ω. assumption.
  - admit.
Admitted.
