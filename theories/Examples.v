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
Definition pred_ar__PA (s : Pred__PA) : nat := 2.

Inductive IndPred__PA :=
| PA_Nat
| PA_Even
| PA_Odd.
Definition indpred_ar__PA (s : IndPred__PA) : nat := 1.

Definition Σ__PA : signature
  := {|
    FuncS := Func__PA;
    fun_ar := fun_ar__PA;
    PredS := Pred__PA;
    pred_ar := pred_ar__PA;
    IndPredS := IndPred__PA;
    indpred_ar := indpred_ar__PA;
  |}.

Coercion coerce_func (f : Func__PA) : FuncS Σ__PA := f.
Coercion coerce_pred (P : Pred__PA) : PredS Σ__PA := P.
Coercion coerce_indpred (P : IndPred__PA) : IndPredS Σ__PA := P.
Set Printing Coercions.

Example PA_one (* s(o) *): term Σ__PA :=
  TFunc PA_succ [TFunc PA_zero []].

Example PA_refl (* ∀ x, x = x *): formula Σ__PA.
  refine (FAll _).
  refine (FPred PA_eq _).
  refine [_; _]; exact (var_term 0).
Defined.

Definition PA_prod_N_zero : production Σ__PA.
  refine (mkProd nil nil PA_Nat _).
  refine [TFunc PA_zero []].
Defined.

Definition PA_prod_N_succ : production Σ__PA.
  refine (mkProd nil _ PA_Nat _).
  - refine (cons _ nil). exists PA_Nat; refine [var_term 0].
  - refine [TFunc PA_succ [var_term 0]].
Defined.

Definition PA_prod_E_zero : production Σ__PA.
  refine (mkProd nil nil PA_Even _).
  refine [ TFunc PA_zero []].
Defined.

Definition PA_prod_E_succ : production Σ__PA.
  refine (mkProd nil _ PA_Even _).
  - refine (cons _ nil). exists PA_Odd; refine [var_term 0].
  - refine [TFunc PA_succ [var_term 0]].
Defined.

Definition PA_prod_O_succ : production Σ__PA.
  refine (mkProd nil _ PA_Odd _).
  - refine (cons _ nil). exists PA_Even; refine [var_term 0].
  - refine [TFunc PA_succ [var_term 0]].
Defined.

Inductive Φ__PA : production Σ__PA -> Prop :=
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

Definition M__PA : structure Σ__PA.
  refine (Build_structure nat _ _ _).
  - intros f; destruct f.
    + intros. exact 0.
    + intros n. exact (S (V.hd n)).
    + intros xy. exact (V.hd xy + V.hd (V.tl xy)).
    + intros xy. exact (V.hd xy * V.hd (V.tl xy)).
  - intros P args; destruct P.
    exact (V.hd args = V.hd (V.tl args)).
  - intros P args; destruct P. 
    + exact (NAT (V.hd args)).
    + exact (EVEN (V.hd args)).
    + exact (ODD (V.hd args)).
Defined.


Lemma NAT_φ_Φ_ω: forall n, φ_Φ_ω Φ__PA M__PA PA_Nat [n].
  induction n.
  - exists 1. unfold φ_Φ_n, φ_Φ, φ_P. exists PA_prod_N_zero, (conj eq_refl ID_N_zero), id.
    repeat split; intros; contradiction.
  - destruct IHn as [α IH]. exists (S α).
    cbn. unfold φ_Φ, φ_P. exists PA_prod_N_succ, (conj eq_refl ID_N_succ), (fun x => n).
    cbn; repeat split; auto; intros; try contradiction.
    destruct H; try contradiction.
    inversion H; subst. apply inj_pair2 in H; now subst.
Qed.

Lemma EVEN_φ_Φ_ω : forall n, EVEN n -> φ_Φ_ω Φ__PA M__PA PA_Even [n].
Proof.
  intros n HE. induction HE using EVEN_ind2.
  - exists 1. unfold φ_Φ_n, φ_Φ, φ_P. exists PA_prod_E_zero, (conj eq_refl ID_E_zero), id.
    repeat split; auto; inversion 1.
  - destruct IHHE as [a Ha]. exists (S (S a)); cbn.
    unfold φ_Φ at 1. unfold φ_P at 1.
    exists PA_prod_E_succ, (conj eq_refl ID_E_succ), (fun x => S n).
    repeat split; cbn; intros; try contradiction.
    destruct H; try contradiction.
    inversion H; subst. apply inj_pair2 in H; subst.
    exists PA_prod_O_succ, (conj eq_refl ID_O_succ), (fun x => n).
    repeat split; cbn; intros; try contradiction.
    destruct H; try contradiction.
    inversion H; subst. apply inj_pair2 in H; now subst.
Qed.

Lemma ODD_φ_Φ_ω : forall n, ODD n -> φ_Φ_ω Φ__PA M__PA PA_Odd [n].
Proof.
  intros n HO. induction HO using ODD_ind2.
  - exists 2, PA_prod_O_succ, (conj eq_refl ID_O_succ), id.
    cbn; repeat split; intros; try contradiction.
    destruct H; try contradiction.
    inversion H; subst. apply inj_pair2 in H; subst.
    exists PA_prod_E_zero, (conj eq_refl ID_E_zero), id.
    cbn; repeat split; intros; contradiction.
  - destruct IHHO as [a Ha]; exists (S (S a)), PA_prod_O_succ, (conj eq_refl ID_O_succ), (fun x => S n).
    cbn; repeat split; intros; try contradiction.
    destruct H; try contradiction.
    inversion H; subst. apply inj_pair2 in H; subst.
    exists PA_prod_E_succ, (conj eq_refl ID_E_succ), (fun x => n).
    cbn; repeat split; intros; try contradiction.
    destruct H; try contradiction.
    inversion H; subst. apply inj_pair2 in H; now subst.
Qed.

Lemma φ_Φ_n_EVEN : forall m n, φ_Φ_n Φ__PA M__PA m PA_Even [n] -> EVEN n
  with φ_Φ_n_ODD : forall m n, φ_Φ_n Φ__PA M__PA m PA_Odd [n] -> ODD n.
Proof.
  - induction m; intros n.
    + contradiction.
    + cbn; intros H. destruct H as [pr [[Heq HΦ] Hpr]].
    inversion HΦ; subst; try discriminate; unfold eq_rect in *.
      * destruct Hpr as [ρ [_ [_ Heval]]]; cbn in *.
        unfold coerce_indpred in *; simpl_uip. inversion Heval. constructor.
      * destruct Hpr as [ρ [_ [Hindpreds Heval]]]; cbn in *.
        unfold coerce_indpred in *; simpl_uip.
        inversion Heval.
        specialize (Hindpreds PA_Odd [var_term 0]); cbn in Hindpreds.
        assert (φ_Φ_n Φ__PA M__PA m PA_Odd [ρ 0]) by auto.
        constructor. subst. clear Heval Hindpreds.
        now apply φ_Φ_n_ODD with m.
  - induction m; intros n.
    + contradiction.
    + cbn; intros (pr & [Heq HΦ] & ρ & _ & Hindpreds & Heval).
      inversion HΦ; subst; try discriminate.
      cbn in *; unfold eq_rect in *; unfold coerce_indpred in *; simpl_uip.
      inversion Heval. constructor.
      specialize (Hindpreds PA_Even [var_term 0]).
      assert (φ_Φ_n Φ__PA M__PA m PA_Even (V.map (eval ρ) [var_term 0])) by auto.
      now apply φ_Φ_n_EVEN with m.
Qed.

Lemma φ_Φ_ω_EVEN : forall n, φ_Φ_ω Φ__PA M__PA PA_Even [n] -> EVEN n.
Proof.
  intros n [α Hα]; now apply φ_Φ_n_EVEN with α.
Qed.

Lemma φ_Φ_ω_ODD : forall n, φ_Φ_ω Φ__PA M__PA PA_Odd [n] -> ODD n.
Proof.
  intros n [α Hα]; now apply φ_Φ_n_ODD with α.
Qed.

Lemma standard_model__PA : standard_model Φ__PA M__PA.
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

Example mut_dep_E_O : mutually_dependent Φ__PA PA_Even PA_Odd.
Proof.
  split.
  - constructor. exists PA_prod_E_succ; repeat split.
    + apply ID_E_succ.
    + exists [var_term 0]; now left.
  - constructor. exists PA_prod_O_succ; repeat split.
    + apply ID_O_succ.
    + exists [var_term 0]; now left.
Qed.

Ltac simpl_destruct :=
  repeat match goal with
    | [ H : Prem _ _ _ |- _ ] => unfold Prem in H
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

Lemma Prem_Nat_Nat : Prem Φ__PA PA_Nat PA_Nat.
Proof.
  exists PA_prod_N_succ; repeat split.
  - apply ID_N_succ.
  - exists ([var_term 0]). now left.
Qed.
    
Lemma Prem_Nat_only_Nat : forall P, Prem Φ__PA PA_Nat P -> P = PA_Nat.
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

Lemma Prem_star_Nat : forall P, Prem_star Φ__PA PA_Nat P -> P = PA_Nat.
Proof.
  intros P H; remember PA_Nat as x.
  induction H.
  - subst. now apply Prem_Nat_only_Nat.
  - reflexivity.
  - assert (y = x) by auto; subst; auto.
Qed.
  
Example not_mut_dep_N_E :
  ~ mutually_dependent Φ__PA PA_Nat PA_Even.
Proof.
  intros [prem _].
  apply Prem_star_Nat in prem; discriminate.
Qed.

Example not_mut_dep_N_O :
  ~ mutually_dependent Φ__PA PA_Nat PA_Odd.
Proof.
  intros [prem _].
  apply Prem_star_Nat in prem; discriminate.
Qed.

Lemma mut_dep_Nat_only_Nat :
  forall (P : IndPredS Σ__PA), mutually_dependent Φ__PA P PA_Nat -> P = PA_Nat.
Proof.
  intros []; auto; intros [H1 H2];
  now apply Prem_star_Nat in H2.
Qed.                              
  
Lemma approximants_of_PA_Nat : forall α n,
    φ_Φ_n Φ__PA M__PA α PA_Nat [n] <-> n < α.
Proof.
  intros α n; split; intros H.
  - generalize dependent n. induction α as [| α IH]; intros n H.
    + contradiction.
    + destruct H as (pr & [Heq HΦ] & ρ & _ & Hindpreds & Heval).
      inversion HΦ; subst; try discriminate; unfold eq_rect in *; cbn in *;
        unfold coerce_indpred in *; simpl_uip; inversion Heval.
      * auto with arith.
      * apply le_n_S. apply IH.
        specialize (Hindpreds PA_Nat [var_term 0]).
        cbn in Hindpreds. apply Hindpreds. now left.
  - generalize dependent n. induction α as [| α IH].
    + inversion 1.
    + intros n Hlt. cbn. destruct n.
      * exists PA_prod_N_zero, (conj eq_refl ID_N_zero), id.
        repeat split; intros; contradiction.
      * exists PA_prod_N_succ, (conj eq_refl ID_N_succ), (fun x => n).
        cbn; repeat split; intros; try contradiction.
        destruct H; try contradiction.
        inversion H; subst. apply inj_pair2 in H; subst.
        apply IH. auto with arith.
Qed.

Import ListNotations.
Infix "⊢" := mkSeq (at level 10).

Definition Even_zero : formula Σ__PA :=
  FIndPred PA_Even [TFunc PA_zero []].

Definition LKID__PA := LKID Φ__PA. 

Lemma provable_Even_zero :
  provable LKID__PA Even_zero.
Proof.
  pose proof (IndR Φ__PA ([]) ([])) as H.
  specialize (H PA_prod_E_zero); cbn in H.
  apply H with (fun t => var_term t); try contradiction.
  apply ID_E_zero.
Qed.

Definition every_nat_is_even_or_odd : formula Σ__PA :=
  FAll
    (FImp
       (FIndPred PA_Nat [var_term 0])
       (FOr
          (FIndPred PA_Even [var_term 0])
          (FIndPred PA_Odd  [var_term 0]))).

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
  intros []; cbn; exact [0].
Defined.

Definition G (P : IndPredS Σ__PA) : formula Σ__PA :=
  match P with
  | PA_Nat => (FOr
          (FIndPred PA_Even ([var_term 0]))
          (FIndPred PA_Odd ([var_term 0])))
  | PA_Even => FIndPred PA_Even ([var_term 0])
  | PA_Odd => FIndPred PA_Odd ([var_term 0])
  end.


Lemma provable_every_nat_is_even_or_odd :
  provable LKID__PA every_nat_is_even_or_odd.
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
        (cons (FOr
            (FIndPred PA_Even [var_term 4])
            (FIndPred PA_Odd [var_term 4])) nil)
        (cons (FOr 
            (FIndPred PA_Even [TFunc PA_succ [var_term 4]])
            (FIndPred PA_Odd [TFunc PA_succ [var_term 4]])) nil); intuition.
      apply OrL.
      * apply OrR2.
        pose proof (@IndR Σ__PA Φ__PA
                      (cons (FIndPred PA_Even [var_term 4]) nil)
                      nil PA_prod_O_succ (fun t => var_term 4) ID_O_succ) as H.
        cbn in H; apply H; intuition.
        inversion H1; subst; apply inj_pair2 in H1; subst; cbn.
        apply AxExtended.
      * apply OrR1.
        pose proof (@IndR Σ__PA Φ__PA
                      (cons (FIndPred PA_Odd [var_term 4]) nil)
                      nil PA_prod_E_succ (fun t => var_term 4) ID_E_succ) as H.
        cbn in H. apply H; intuition.
        inversion H1; subst; apply inj_pair2 in H1; subst; cbn.
        apply AxExtended.
  - cbn; apply AxExtended.
Qed.



Definition every_succ_of_Even_is_Odd : formula Σ__PA :=
  FAll
    (FImp
       (FIndPred PA_Even [var_term 0])
       (FIndPred PA_Odd [TFunc PA_succ [var_term 0]])).

Lemma provable_every_succ_of_Even_is_Odd :
  provable LKID__PA every_succ_of_Even_is_Odd.
Proof.
  pose proof (@IndR Σ__PA Φ__PA
                (cons (FIndPred PA_Even [var_term 0]) nil)
                nil
                PA_prod_O_succ).
  specialize (H (fun t => var_term t) ID_O_succ); cbn in H.
  apply AllR; cbn. apply ImpR.
  apply H; intuition.
  inversion H1; subst.
  apply inj_pair2 in H1; subst; cbn. apply AxExtended.
Qed.

Definition Even_succ_succ_Even : formula Σ__PA :=
  let x := var_term 0 in
  FAll
    (FImp
       (FIndPred PA_Even [x])
       (FIndPred PA_Even [TFunc PA_succ
                            [TFunc PA_succ
                               [x]]])).

Lemma provable_Even_succ_succ_Even :
    provable LKID__PA Even_succ_succ_Even.
Proof.
  apply AllR. apply ImpR.
  apply Cut with (FIndPred PA_Odd [TFunc PA_succ [var_term 0]]).
  - pose proof (@IndR Σ__PA Φ__PA
                  [FIndPred PA_Even [var_term 0]]
                  [FIndPred PA_Even
                      [TFunc PA_succ [TFunc PA_succ [var_term 0]]]]
                  PA_prod_O_succ (fun x => var_term x) ID_O_succ) as H1; cbn in *.
    apply H1; intuition. inversion H0; subst; apply inj_pair2 in H0; subst; cbn in *.
    apply AxExtended.
  - pose proof (@IndR _ Φ__PA
                  [FIndPred PA_Odd [TFunc PA_succ [var_term 0]];
                  FIndPred PA_Even [var_term 0]]
                  nil
                  PA_prod_E_succ (fun x => TFunc PA_succ [var_term 0]) ID_E_succ); cbn in *.
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

CoFixpoint from (n : nat) : LList nat := LCons n (from (S n)).

Lemma Infinite_from : forall n, Infinite (from n).
Proof.
  cofix H.
  intros n.
  now llist_unfold (from n).
Qed.

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

CoInductive COINDFinite {A} : LList A -> Prop :=
| COINDFinite_LNil : COINDFinite LNil
| COINDFinite_LCons : forall a l, COINDFinite l -> COINDFinite (LCons a l).

Lemma all_COINDFinite : forall A (l : LList A), COINDFinite l.
Proof.
  intros A; cofix H.
  intros []; constructor; apply H.
Qed.
