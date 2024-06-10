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
| PA_Nat
| PA_Even
| PA_Odd.
Definition indpred_ar__PA (s : IndPred__PA) : nat :=
  match s with
  | PA_Nat => 1
  | PA_Even => 1
  | PA_Odd => 1
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
  refine (@mkProd Σ__PA nil nil PA_Nat _).
  refine [(@TFunc Σ__PA PA_zero V.nil)].
Defined.

Print PA_prod_N_zero.

Definition PA_prod_N_succ : @production Σ__PA.
  refine (@mkProd Σ__PA nil _ PA_Nat _).
  - refine (cons _ nil). exists PA_Nat; refine [(var_term 0)].
  - refine [(@TFunc Σ__PA PA_succ ([var_term 0]))].
Defined.

Print PA_prod_N_succ.

Definition PA_prod_E_zero : @production Σ__PA.
  refine (@mkProd Σ__PA nil nil PA_Even _).
  refine ( [ @TFunc Σ__PA PA_zero ([]) ] ).
Defined.

Definition PA_prod_E_succ : @production Σ__PA.
  refine (@mkProd Σ__PA nil _ PA_Even _).
  - refine (cons _ nil). exists PA_Odd; refine ([var_term 0]).
  - refine [_].
    refine (@TFunc Σ__PA PA_succ _).
    refine [var_term 0].
Defined.

Definition PA_prod_O_succ : @production Σ__PA.
  refine (@mkProd Σ__PA nil _ PA_Odd _).
  - refine (cons _ nil). exists PA_Even; refine ([var_term 0]).
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

Lemma nat_EVEN_or_ODD : forall n : nat, EVEN n \/ ODD n.
Proof.
  induction n.
  - left; constructor.
  - destruct IHn; [right | left]; now constructor.
Qed.

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


Lemma NAT_φ_Φ_ω: forall n, @φ_Φ_ω Σ__PA M__PA Φ__PA PA_Nat ([n]).
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

Lemma EVEN_φ_Φ_ω : forall n, EVEN n -> @φ_Φ_ω Σ__PA M__PA Φ__PA PA_Even ([n]).
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


Lemma ODD_φ_Φ_ω : forall n, ODD n -> @φ_Φ_ω Σ__PA M__PA Φ__PA PA_Odd ([n]).
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

Lemma φ_Φ_n_EVEN : forall m n, @φ_Φ_n Σ__PA M__PA Φ__PA PA_Even m ([n]) -> EVEN n
  with φ_Φ_n_ODD : forall m n, @φ_Φ_n Σ__PA M__PA Φ__PA PA_Odd m ([n]) -> ODD n.
Proof.
  - induction m; intros n.
    + contradiction.
    + cbn; intros H. destruct H as [pr [[Heq HΦ] Hpr]].
    inversion HΦ; subst; try discriminate; unfold eq_rect in *.
      * destruct Hpr as [ρ [_ [_ Heval]]]; cbn in *; simpl_uip.
        inversion Heval. constructor.
      * destruct Hpr as [ρ [_ [Hindpreds Heval]]]; cbn in *; simpl_uip.
        inversion Heval.
        specialize (Hindpreds PA_Odd (V.cons (var_term 0) V.nil)); cbn in Hindpreds.
        assert (@φ_Φ_n Σ__PA M__PA Φ__PA PA_Odd m (V.cons (ρ 0) V.nil)) by intuition.
        constructor. subst. clear Heval Hindpreds.
        now apply φ_Φ_n_ODD with m.
  - induction m; intros n.
    + contradiction.
    + cbn; intros (pr & [Heq HΦ] & ρ & _ & Hindpreds & Heval).
      inversion HΦ; subst; try discriminate.
      cbn in *; unfold eq_rect in *; simpl_uip.
      inversion Heval. constructor.
      specialize (Hindpreds PA_Even (V.cons (var_term 0) V.nil)).
      assert (@φ_Φ_n Σ__PA M__PA Φ__PA PA_Even m (V.map (eval ρ) (V.cons (var_term 0) V.nil))) by auto.
      now apply φ_Φ_n_EVEN with m.
Qed.

Lemma φ_Φ_ω_EVEN : forall n, @φ_Φ_ω Σ__PA M__PA Φ__PA PA_Even ([n]) -> EVEN n.
Proof.
  intros n [α Hα]; now apply φ_Φ_n_EVEN with α.
Qed.

Lemma φ_Φ_ω_ODD : forall n, @φ_Φ_ω Σ__PA M__PA Φ__PA PA_Odd ([n]) -> ODD n.
Proof.
  intros n [α Hα]; now apply φ_Φ_n_ODD with α.
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
  - apply φ_Φ_ω_ODD. rewrite (V.eta ts) in H. pose proof (V.nil_spec (V.tl ts)).
    rewrite H0 in H. assumption.
Qed.
Print Assumptions standard_model__PA.

(* proof_irrelevance, Eqdep.Eq_rect_eq.eq_rect_eq *)
(* We could probably avoid them because all our types are finite,
   hence have decidable equality. *)

Example mut_dep_E_O : @mutually_dependent Σ__PA Φ__PA PA_Even PA_Odd.
Proof.
  split.
  - constructor. exists PA_prod_E_succ; intuition.
    + apply ID_E_succ.
    + eexists; cbn; eauto.
  - constructor. exists PA_prod_O_succ; intuition.
    + apply ID_O_succ.
    + eexists; cbn; eauto.
Qed.

Ltac simpl_destruct :=
  repeat match goal with
    | [ H : Prem _ _ |- _ ] => unfold Prem in H
    | [ H : _ /\ _ |- _ ] => destruct H
    | [ H : ex _ |- _ ] => destruct H
    | _ => unfold Prem
    end.

Ltac destruct_productions :=
  match goal with
  | [ p : production |- _] => destruct p; subst
  | [ H : Φ__PA ?p |- _ ] => inversion H; subst; try discriminate
  | _ => idtac "No production in inductive definition set found."
  end.

Require Import Relation_Operators.

Lemma Prem_Nat_Nat : @Prem Σ__PA Φ__PA PA_Nat PA_Nat.
Proof.
  exists PA_prod_N_succ; intuition.
  - apply ID_N_succ.
  - cbn. exists ([var_term 0]). now left.
Qed.

    
Lemma Prem_Nat_only_Nat : forall P, @Prem Σ__PA Φ__PA PA_Nat P -> P = PA_Nat.
Proof.
  intros [] H.
  - reflexivity.
  - simpl_destruct. induction H; subst; try discriminate; cbn in *.
    + contradiction.
    + destruct H1 as [H | H]; inversion H.
  - simpl_destruct. induction H; subst; try discriminate; cbn in *.
    + contradiction.
    + destruct H1 as [H | H]; inversion H.
Qed.

Lemma Prem_star_Nat : forall P, @Prem_star Σ__PA Φ__PA PA_Nat P -> P = PA_Nat.
Proof.
  intros P H; remember PA_Nat as x.
  induction H.
  - subst. now apply Prem_Nat_only_Nat.
  - reflexivity.
  - assert (y = x) by auto; subst; auto.
Qed.
  
Example not_mut_dep_N_E :
  ~ @mutually_dependent Σ__PA Φ__PA PA_Nat PA_Even.
Proof.
  intros [prem _].
  apply Prem_star_Nat in prem; discriminate.
Qed.

Example not_mut_dep_N_O :
  ~ @mutually_dependent Σ__PA Φ__PA PA_Nat PA_Odd.
Proof.
  intros [prem _].
  apply Prem_star_Nat in prem; discriminate.
Qed.

Lemma mut_dep_Nat_only_Nat :
  forall (P : IndPredS Σ__PA), @mutually_dependent Σ__PA Φ__PA P PA_Nat -> P = PA_Nat.
Proof.
  intros []; auto; intros [H1 H2];
  now apply Prem_star_Nat in H2.
Qed.
                              
  
Lemma approximants_of_PA_Nat : forall α n,
    @approximant_of Σ__PA M__PA Φ__PA PA_Nat α ([n])
    <-> n < α.
Proof.
  intros α n; split; intros H.
  - generalize dependent n. induction α as [| α IH]; intros n H.
    + contradiction.
    + destruct H as (pr & [Heq HΦ] & ρ & _ & Hindpreds & Heval).
      inversion HΦ; subst; try discriminate; unfold eq_rect in *; cbn in *;
        simpl_uip; inversion Heval.
      * auto with arith.
      * apply le_n_S. apply IH.
        specialize (Hindpreds PA_Nat ([var_term 0])).
        cbn in Hindpreds. apply Hindpreds. now left.
  - generalize dependent n. induction α as [| α IH].
    + inversion 1.
    + intros n Hlt. cbn. destruct n.
      * exists PA_prod_N_zero, (conj eq_refl ID_N_zero); cbn.
        exists (fun x => x); intuition.
      * exists PA_prod_N_succ, (conj eq_refl ID_N_succ); cbn.
        exists (fun x => n); intuition.
        cbn in H; inversion H; try contradiction.
        inversion H0; subst. apply inj_pair2 in H0; subst; cbn in *. apply IH.
        auto with arith.
Qed.

Import ListNotations.
Infix "⊢" := mkSeq (at level 10).


Definition Even_zero : formula Σ__PA.
  apply FIndPred with PA_Even; cbn.
  refine (V.cons _ V.nil).
  apply TFunc with PA_zero; cbn.
  exact V.nil.
Defined.

Lemma provable_Even_zero :
  @LKID Σ__PA Φ__PA ([] ⊢ [Even_zero]).
Proof.
  pose proof (@IndR Σ__PA Φ__PA ([]) ([])) as H.
  specialize (H PA_prod_E_zero); cbn in H.
  apply H with (fun t => var_term t); try contradiction.
  apply ID_E_zero.
Qed.

Definition every_nat_is_even_or_odd : formula Σ__PA :=
  FAll
    (FImp
       (@FIndPred Σ__PA PA_Nat ([var_term 0]))
       (FOr
          (@FIndPred Σ__PA PA_Even ([var_term 0]))
          (@FIndPred Σ__PA PA_Odd ([var_term 0])))).

Lemma every_nat_is_even_or_odd_Sat :
  forall (ρ : env M__PA), ρ ⊨ every_nat_is_even_or_odd.
Proof.
  intros ρ. cbn.
  intros d _ notEVEN. induction d.
  - exfalso; apply notEVEN; constructor.
  - constructor. assert (ODD d -> False).
    { intros HODD; apply notEVEN; now constructor. }
    assert (~~EVEN d) by auto.
    Require Import Classical.
    apply NNPP in H0. assumption.
Qed.

Definition z : forall (P : IndPredS Σ__PA), vec var (indpred_ar P).
  intros []; cbn; exact ([0]).
Defined.

Definition G (P : IndPredS Σ__PA) : formula Σ__PA :=
  match P with
  | PA_Nat => (FOr
          (@FIndPred Σ__PA PA_Even ([var_term 0]))
          (@FIndPred Σ__PA PA_Odd ([var_term 0])))
  | PA_Even => @FIndPred Σ__PA PA_Even ([var_term 0])
  | PA_Odd => @FIndPred Σ__PA PA_Odd ([var_term 0])
  end.


Lemma provable_every_nat_is_even_or_odd :
  @LKID Σ__PA Φ__PA ([] ⊢ [every_nat_is_even_or_odd]).
Proof.
  apply AllR; cbn.
  apply ImpR.
  apply IndL with z G.
  - intros []; cbn; repeat constructor; inversion 1.
  - intros [] H; try reflexivity.
    now assert (@mutually_dependent Σ__PA Φ__PA PA_Nat PA_Nat) by (apply mutually_dependent_refl).
  - intros pr HΦ Hmutdep Qs Gs Pi ty Fi; cbn in *.
    apply mut_dep_Nat_only_Nat in Hmutdep.
    inversion HΦ; subst; try discriminate; cbn in *.
    + apply OrR1. apply Wk with nil (cons Even_zero nil); intuition.
      apply provable_Even_zero.
    + unfold shift, funcomp in *.
      apply Wk with
        (cons (@FOr Σ__PA
            (@FIndPred Σ__PA PA_Even ([var_term 4]))
            (@FIndPred Σ__PA PA_Odd ([var_term 4]))) nil)
        (cons (@FOr Σ__PA
            (@FIndPred Σ__PA PA_Even ([(@TFunc Σ__PA PA_succ ([var_term 4]))]))
            (@FIndPred Σ__PA PA_Odd ([(@TFunc Σ__PA PA_succ ([var_term 4]))]))) nil); intuition.
      apply OrL.
      * apply OrR2.
        pose proof (@IndR Σ__PA Φ__PA
                      (cons (@FIndPred Σ__PA PA_Even ([var_term 4])) nil)
                      nil PA_prod_O_succ (fun t => var_term 4) ID_O_succ) as H.
        cbn in H; apply H; intuition.
        inversion H1; subst; apply inj_pair2 in H1; subst; cbn.
        apply AxExtended.
      * apply OrR1.
        pose proof (@IndR Σ__PA Φ__PA
                      (cons (@FIndPred Σ__PA PA_Odd ([var_term 4])) nil)
                      nil PA_prod_E_succ (fun t => var_term 4) ID_E_succ) as H.
        cbn in H. apply H; intuition.
        inversion H1; subst; apply inj_pair2 in H1; subst; cbn.
        apply AxExtended.
  - cbn; apply AxExtended.
Qed.



Definition every_succ_of_Even_is_Odd : formula Σ__PA.
  apply FAll.
  apply FImp.
  - apply FIndPred with PA_Even; cbn.
    exact ([var_term 0]).
  - apply FIndPred with PA_Odd; cbn.
    refine (V.cons _ V.nil).
    apply TFunc with PA_succ; cbn.
    exact ([var_term 0]).
Defined.

Lemma provable_every_succ_of_Even_is_Odd : forall Γ Δ,
  @LKID Σ__PA Φ__PA (Γ ⊢ (every_succ_of_Even_is_Odd :: Δ)).
Proof.
  intros Γ Δ.
  pose proof (@IndR Σ__PA Φ__PA (cons (@FIndPred Σ__PA PA_Even ([var_term 0])) (shift_formulas Γ)) (shift_formulas Δ) PA_prod_O_succ).
  specialize (H (fun t => var_term t) ID_O_succ); cbn in H.
  apply AllR; cbn. apply ImpR.
  apply H; intuition.
  inversion H1; subst.
  apply inj_pair2 in H1; subst; cbn. apply AxExtended.
Qed.

Definition Even_succ_succ_Even : formula Σ__PA.
  apply FAll; apply FImp.
  - apply FIndPred with PA_Even; cbn.
    exact ([var_term 0]).
  - apply FIndPred with PA_Even; cbn.
    refine ([_]).
    apply TFunc with PA_succ; cbn.
    refine ([_]).
    apply TFunc with PA_succ; cbn.
    exact ([var_term 0]).
Defined.

Lemma provable_Even_succ_succ_Even :
    @LKID _ Φ__PA ([] ⊢ [Even_succ_succ_Even]).
Proof.
  apply AllR. apply ImpR.
  apply Cut with (@FIndPred Σ__PA PA_Odd ([(@TFunc Σ__PA PA_succ ([var_term 0]))])).
  - pose proof (@IndR Σ__PA Φ__PA
                  ([(@FIndPred Σ__PA PA_Even ([var_term 0]))])
                  ([(@FIndPred Σ__PA PA_Even
                      ([(@TFunc Σ__PA PA_succ ([(@TFunc Σ__PA PA_succ ([var_term 0]))]))]))])
                  PA_prod_O_succ (fun x => var_term x) ID_O_succ) as H1; cbn in *.
    apply H1; intuition. inversion H0; subst; apply inj_pair2 in H0; subst; cbn in *.
    apply AxExtended.
  - pose proof (@IndR _ Φ__PA
                  ([(@FIndPred Σ__PA PA_Odd ([(@TFunc Σ__PA PA_succ ([var_term 0]))]));
                  (@FIndPred Σ__PA PA_Even ([var_term 0]))])
                  nil
                  PA_prod_E_succ (fun x => (@TFunc Σ__PA PA_succ ([var_term 0]))) ID_E_succ); cbn in *.
    apply H; intuition. inversion H1; subst; apply inj_pair2 in H1; subst; cbn.
    apply AxExtended.
Qed.

(* I believe LList can not be defined in the "negative" style. *)
CoInductive LList (A : Type) :=
| LNil : LList A
| LCons : A -> LList A -> LList A.
Arguments LNil {_}.
Arguments LCons {_} _ _.

Definition LList_destruct {A} (l : LList A) :=
  match l with
  | LNil => LNil
  | LCons h t => LCons h t
  end.

Lemma LList_destruct_id : forall {A} (l : LList A),
    LList_destruct l = l.
Proof.
  intros A [| h t]; reflexivity.
Qed.

Ltac llist_unfold t :=
  rewrite <- (LList_destruct_id t); cbn.

Inductive Finite {A} : LList A -> Prop :=
| Finite_LNil : Finite LNil
| Finite_LCons : forall a l, Finite l -> Finite (LCons a l).

CoInductive Infinite {A} : LList A -> Prop :=
| Infinite_LCons : forall a l, Infinite l -> Infinite (LCons a l).

(* well-founded proof, by induction *)
Lemma Finite_Infinite_contradiciton : forall A (l : LList A), Finite l -> Infinite l -> False.
Proof.
  intros A l Hfin. induction Hfin; inversion 1; subst; auto.
Qed.

(* non-well-founded proof, cyclic proof *)
Lemma not_Finite_is_Infinite : forall A (l : LList A), ~Finite l -> Infinite l.
Proof.
  cofix H.
  intros A l Hnotfin. destruct l as [| h t].
  - exfalso; apply Hnotfin; constructor.
  - constructor. apply H (* cyclic call *). intros Hfin. apply Hnotfin. now constructor.
Qed.

Lemma not_Infinite_is_Finite : forall A (l : LList A), ~Infinite l -> Finite l.
Proof.
  intros A l Hnotinf; destruct l; constructor.
  assert (H : ~ Infinite l).
  { intros Hinf. apply Hnotinf; now constructor. }
  destruct (classic (Finite l)) as [Hfin | Hfin]; auto.
  exfalso; now apply not_Finite_is_Infinite in Hfin.
Qed.

CoFixpoint zeros : LList nat := LCons 0 zeros.

Lemma zeros_unfold : zeros = LCons 0 zeros.
Proof.
  now (rewrite <- LList_destruct_id at 1).
Qed.

Lemma Infinite_zeros : Infinite zeros.
Proof.
  cofix H.
  rewrite zeros_unfold; constructor.
  apply H.
Qed.
Print Assumptions Infinite_zeros.

CoFixpoint from (n : nat) : LList nat := LCons n (from (S n)).

Lemma Infinite_from : forall n, Infinite (from n).
Proof.
  cofix H.
  intros n.
  now llist_unfold (from n).
Qed.
Print Infinite_from.
Print Assumptions Infinite_from. (* Closed under the global context. *)

Definition nats : LList nat := from 0.
Lemma Infinite_nats : Infinite nats.
Proof.
  apply Infinite_from.
Qed.

Ltac prove_finite :=
  repeat match goal with
    | [ |- Finite LNil ] => constructor
    | [ |- Finite ?l ] => rewrite <- (LList_destruct_id l); cbn; constructor
    end.

Definition zero_to_four := LCons 0 (LCons 1 (LCons 2 (LCons 3 (LCons 4 LNil)))).

Lemma Finite_zero_to_four : Finite zero_to_four.
Proof.
  prove_finite.
Qed.

Lemma Finite_nats : Finite nats.
Proof.
  Fail Timeout 2 prove_finite.  (* ad infinitum *)
Abort.

CoInductive COINDFinite {A} : LList A -> Prop :=
| COINDFinite_LNil : COINDFinite LNil
| COINDFinite_LCons : forall a l, COINDFinite l -> COINDFinite (LCons a l).

Lemma all_COINDFinite : forall A (l : LList A), COINDFinite l.
Proof.
  intros A; cofix H.
  intros []; constructor; apply H.
Qed.
