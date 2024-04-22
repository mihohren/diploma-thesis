Require Import Base Syntax Semantics.
Require Import Arith.

Section inductive_definition_set.
  Context {Σ : signature}.
  
  Record production := mkProd {
      preds : list ({ P : PredS Σ & vec (term Σ) (pred_ar P) });
      indpreds : list ({ P : IndPredS Σ & vec (term Σ) (indpred_ar P) });
      indcons : IndPredS Σ;
      indargs : vec (term Σ) (indpred_ar indcons);
    }.

  Definition IndDefSet := production -> Prop .
End inductive_definition_set.

Section definition_set_operator.
  Context {Σ : signature}.
  Context {M : structure Σ}.
  Context {Φ : @IndDefSet Σ}.
  Let D := domain M.             
  (*
    D^k ≡ vec D k
    Pow(D^k) ≡ vec D k -> Prop
    Pow(D^1) × ... × Pow(D^k) ≡ ∀ P, vec D (indpred_ar P) -> Prop
   *)

  (* Definition Φ_P (* Φ_i *) (P : IndPredS Σ): production -> Prop := *)
  (*   fun pr => Φ pr /\ indcons pr = P. *)
  
  Definition φ_pr (* φ_{i, r} *)
    (pr : production)
    (args : forall P : IndPredS Σ, vec D (indpred_ar P) -> Prop)
    (ds : vec D (indpred_ar (indcons pr)))
    : Prop :=
        exists (ρ : env M),
        (forall Q us, List.In (existT _ Q us) (preds pr) ->
                 interpP Q (V.map (eval ρ) us))
        /\
          ( forall P ts, List.In (existT _ P ts) (indpreds pr) ->
                    args P (V.map (eval ρ) ts))
        /\
          ds = V.map (eval ρ) (indargs pr).

  Definition φ_P (* φ_i *)
    (P : IndPredS Σ)
    (args : forall P : IndPredS Σ, vec D (indpred_ar P) -> Prop)
    : vec D (indpred_ar P) -> Prop.
    refine (fun ds => _).
    refine (@ex production (fun pr => _)).
    refine (@ex (P = indcons pr /\ Φ pr) (fun H => _)).
    destruct H as [Heq HΦ].
    rewrite Heq in ds.
    exact (φ_pr pr args ds).
  Defined.
  
  Definition φ_Φ (args : forall P : IndPredS Σ, vec D (indpred_ar P) -> Prop)
    : forall P : IndPredS Σ, vec D (indpred_ar P) -> Prop :=
    fun P => φ_P P args.

  Proposition φ_Φ_monotone : forall (x y : forall P, vec D (indpred_ar P) -> Prop),
      (forall P v, x P v -> y P v) ->
      (forall P v, φ_Φ x P v -> φ_Φ y P v).
  Proof.
    intros x y Hle P v Hφ.
    unfold φ_Φ, φ_P in *.
    destruct Hφ as (pr & (Heq & HΦ) & Hφ_P_pr).
    destruct Hφ_P_pr as (ρ & Hpreds & Hindpreds & Hcons).
    exists pr, (conj Heq HΦ).
    unfold φ_pr in *.
    exists ρ; repeat split.
    - apply Hpreds.
    - intros PP ts HIn. apply Hle. apply Hindpreds; auto.
    - apply Hcons.
  Qed.
End definition_set_operator.

Section approximants.
  Context {Σ : signature} {M : structure Σ}.
  Context {Φ : @IndDefSet Σ}.
  Let D := domain M.

  Fixpoint φ_Φ_n P (α : nat) (v : vec D (indpred_ar P)) : Prop :=
    match α with
    | 0 => False
    | S α => @φ_Φ Σ M Φ (fun P => φ_Φ_n P α) P v
    end.

  Corollary (* 2.2.10 *) cor : forall α P v,
      φ_Φ_n P (S α) v <-> @φ_Φ Σ M Φ (fun P => φ_Φ_n P α) P v.
  Proof.
    intros α P v. cbn; split; auto.
  Qed.
    
  Definition approximant_of (P : IndPredS Σ)
    : nat -> vec D (indpred_ar P) -> Prop :=
    φ_Φ_n P.

  Lemma zeroth_approximant_empty :
    forall P v, ~approximant_of P 0 v.
  Proof.
    intros P v Happrox; inversion Happrox.
  Qed.

  Proposition (* 2.2.9 *) approximant_succ : forall α P v, approximant_of P α v -> approximant_of P (S α) v.
  Proof.
    unfold approximant_of; induction α; intros P v H.
    - inversion H.
    - apply φ_Φ_monotone with (fun P => φ_Φ_n P α).
      + intros Q u H'. cbn. apply IHα. apply H'.
      + apply H.
  Qed.
  
  Lemma approximant_monotone : forall α β, α < β -> forall P v, approximant_of P α v -> approximant_of P β v.
  Proof.
    unfold approximant_of. intros α β Hle P v Hφ.
    induction Hle.
    - now apply approximant_succ.
    - now apply approximant_succ.
  Qed.  
      
  Lemma approximant_characterization : forall α P v,
      φ_Φ_n P α v <-> exists β, β < α /\ @φ_Φ Σ M Φ (fun P => φ_Φ_n P β) P v.
  Proof.
    intros α P v; split; intros H.
    - induction α.
      + inversion H.
      + exists α; split; [apply le_n | apply H].
    - destruct H as [β [Hle Hφ]]; induction Hle.
      + apply Hφ.
      + now apply approximant_succ.
  Qed.

  Lemma lema_iza_cor_2_2_10 :   (* nije prava lema, napisana je kao komentar *)
    forall α, (forall P v, φ_Φ_n P (S α) v <-> φ_Φ_n P α v) <->
           (forall P v, @φ_Φ Σ M Φ (fun P => φ_Φ_n P α) P v -> φ_Φ_n P α v).
  Proof.
    intros α; split; intros H.
    - intros P v H1. apply H. apply H1.
    - intros P v; split.
      + intros H1. apply H. apply H1.
      + intros H1. cbn. now apply approximant_succ.
  Qed.
  
  Definition φ_Φ_ω P v := exists α, φ_Φ_n P α v.

  Lemma φ_Φ_ω_characterization : forall P v, φ_Φ_ω P v <-> exists α, @φ_Φ Σ M Φ (fun P => φ_Φ_n P α) P v.
  Proof.
    intros P v; split; intros [α Hφ].
    - destruct α.
      + inversion Hφ.
      + exists α. apply Hφ.
    - exists (S α). apply Hφ.
  Qed.
  
  Notation "{ X , Y }" := (existT _ X Y) (only printing).
  Notation "Q '^M'" := (interpP Q) (at level 10, only printing).
  Notation "vs @ f" := (V.map f vs) (at level 10, only printing).
  Notation "'|' Q '|'" := (pred_ar Q) (only printing).
  Notation "'|' R '|'" := (indpred_ar R) (only printing).

  Require Import List Lia Arith.
  Import ListNotations.

  Section experiment.
    Variable T : Type.
    Variable P : T -> nat -> Prop.
    Hypothesis P_succ : forall t n, P t n -> P t (S n).

    Lemma P_monotone : forall t n m, n < m -> P t n -> P t m.
    Proof.
      intros t n m Hle. induction Hle.
      - apply P_succ.
      - intros H. apply P_succ. auto.
    Qed.

    Variable ls : list T.
    Hypothesis In_ls_P : forall t, In t ls -> exists n, P t n.

    Lemma supremum : exists α, forall t, In t ls -> P t α.
    Proof.
      induction ls.
      - exists 0. cbn; intros; subst; contradiction.
      - assert (In_a : In a (a :: l)) by now left.
        destruct (In_ls_P a In_a) as [α HPα].
        assert (In_tail_P : forall t, In t l -> exists n, P t n).
        { intros t Hin. apply In_ls_P. now right. }
        pose proof (IHl In_tail_P) as [β HPβ].
        set (γ := Nat.max α β).
        exists (S γ). intros t Hin.
        inversion Hin.
        + subst. apply P_monotone with α; [lia | assumption].
        + clear Hin. apply P_monotone with β; [lia | auto].
    Qed.
  End experiment.

  Require Import Program.
  
  Section lemma_2_2_11.
    Lemma ω_prefixed : forall P v, @φ_Φ Σ M Φ φ_Φ_ω P v -> φ_Φ_ω P v.
    Proof.
      intros P y H.
      (* apply φ_Φ_ω_characterization; eexists. *)
      (* eapply φ_Φ_monotone. *)
      (* 2: { apply H. } *)
      (* intros Q u. intros [α HQ]. apply HQ. *)
      unfold φ_Φ, φ_P, φ_pr in H;
      destruct H as (pr & [Heq Hpr] & (ρ & H1 & H2 & H3)).
      unfold eq_rect in H3; subst P; subst y.
      assert (Hsup : exists α, forall P ts, In (existT _ P ts) (indpreds pr) -> φ_Φ_n P α (V.map (eval ρ) ts)).
      {
        induction (indpreds pr).
        - exists 0. intros. contradiction.
        - destruct a. pose proof (H2 x t).
          assert (In (existT _ x t) ((existT _ x t) :: l)) by now left.
          apply H in H0. destruct H0 as [α Hα].
          assert (IH_help : forall P ts, In (existT _ P ts) l -> φ_Φ_ω P (V.map (eval ρ) ts)).
          { intros P ts Hin. apply H2. now right. }
          apply IHl in IH_help.
          destruct IH_help as [β Hβ].
          exists (S (max α β)).
          intros P ts Hin.
          inversion Hin.
          + apply approximant_monotone with α.
            * auto with arith.
            * apply EqdepFacts.eq_sigT_fst in H0 as HHH.
              subst x. unfold approximant_of.
              apply inj_pair2 in H0 as HH. subst t. assumption.
          + apply approximant_monotone with β.
            * auto with arith.
            * clear Hin. now apply Hβ.                                
      }
      destruct Hsup as [κ Hsup].
      exists (S (S κ)).
      apply approximant_succ.
      cbn. unfold φ_Φ.
      unfold φ_P.
      exists pr, (conj eq_refl Hpr).
      unfold φ_pr. exists ρ; split; auto.
    Qed.

    Print Assumptions ω_prefixed. (* Axioms: proof irrelevance *)

    Lemma ω_least : forall args, (forall P v, @φ_Φ Σ M Φ args P v -> args P v) ->
                            forall P v, φ_Φ_ω P v -> args P v.
    Proof.
      intros args (* prefixed point *) Hprefixed P v Hω.
      destruct Hω as [α Hφ].
      enough (H : forall m, @φ_Φ Σ M Φ (fun P => φ_Φ_n P m) P v ->
                       @φ_Φ Σ M Φ args P v).
      - apply Hprefixed. apply H with α.
        apply approximant_succ. apply Hφ.
      - intros m. apply φ_Φ_monotone. induction m; intros Q u HQ.
        + inversion HQ.
        + apply Hprefixed. eapply φ_Φ_monotone.
          2:{ apply HQ. }
          intros. cbn in *. fold φ_Φ_n in H. apply IHm. apply H.
    Qed.    
  End lemma_2_2_11.
End approximants.

Definition standard_model
  (Σ : signature) (Φ: @IndDefSet Σ)
  : structure Σ -> Prop :=
  fun M =>
    forall (P : IndPredS Σ) ts, interpIP P ts <-> exists α, @φ_Φ_n Σ M Φ P α ts.

