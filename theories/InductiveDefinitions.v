Require Import Base Syntax Semantics.

Section inductive_definition_set.
  Context (Σ : signature).
  
  Record production :=
    mkProd {
        preds : list { P : PredS Σ & vec (term Σ) (pred_ar P) };
        indpreds : list { P : IndPredS Σ & vec (term Σ) (indpred_ar P) };
        indcons : IndPredS Σ;
        indargs : vec (term Σ) (indpred_ar indcons);
      }.
  
  Definition IndDefSet := production -> Prop.
End inductive_definition_set.

Arguments mkProd {Σ}.
Arguments preds {Σ}.
Arguments indpreds {Σ}.
Arguments indcons {Σ}.
Arguments indargs {Σ}.

Section definition_set_operator.
  Context {Σ : signature}.
  Context (Φ : IndDefSet Σ).
  Context (M : structure Σ).

  (* interpretation of inductive predicates *)
  Definition InterpInd := forall P : IndPredS Σ, vec M (indpred_ar P) -> Prop.

  Definition subset (U V : InterpInd) := forall P v, U P v -> V P v.
  Notation "U ⊑ V" := (subset U V) (at level 11).
  
  Definition monotone (F : InterpInd -> InterpInd) := forall U V : InterpInd, U ⊑ V -> F U ⊑ F V.
  
  Definition φ_pr
    (pr : production Σ)
    (args : InterpInd)
    (ds : vec M (indpred_ar (indcons pr)))
    : Prop :=
        exists (ρ : env M),
        (forall Q us, List.In (Q; us) (preds pr) ->
                 interpP Q (V.map (eval ρ) us)) /\
          (forall P ts, List.In (P; ts) (indpreds pr) ->
                    args P (V.map (eval ρ) ts)) /\
          ds = V.map (eval ρ) (indargs pr).

  Definition φ_P
    (P : IndPredS Σ)
    (args : InterpInd)
    : vec M (indpred_ar P) -> Prop.
    refine (fun ds => _).
    refine (@ex (production Σ) (fun pr => _)).
    refine (@ex (P = indcons pr /\ Φ pr) (fun '(conj Heq HΦ) => _)).
    rewrite Heq in ds.
    exact (φ_pr pr args ds).
  Defined.
  
  Definition φ_Φ (args : InterpInd) : InterpInd :=
    fun P => φ_P P args.
  
  Proposition φ_Φ_monotone : monotone φ_Φ.
  Proof.
    intros f g Hle P v Hφ.
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

  Fixpoint φ_Φ_n (α : nat) : InterpInd :=
    match α with
    | 0 => fun _ _ => False
    | S α => φ_Φ (φ_Φ_n α)
    end.

  Lemma φ_Φ_n_succ : forall α : nat, φ_Φ_n α ⊑ φ_Φ_n (S α).
  Proof.
    induction α as [| α IH].
    - inversion 1.
    - apply φ_Φ_monotone, IH.
  Qed.
      
  Lemma φ_Φ_n_monotone : forall α β : nat, α <= β -> φ_Φ_n α ⊑ φ_Φ_n β.
  Proof.
    intros α β Hle; induction Hle as [| β _ IH].
    - red; auto.
    - pose proof (φ_Φ_n_succ β); red; auto.
  Qed.
      
  Definition approximant_of (P : IndPredS Σ)
    : nat -> vec M (indpred_ar P) -> Prop :=
    fun α => φ_Φ_n α P.

  Proposition approximant_succ : forall α P v,
      approximant_of P α v -> approximant_of P (S α) v.
  Proof.
    now apply φ_Φ_n_succ.
  Qed.
  
  Lemma approximant_monotone : forall α β, α <= β -> forall P v,
        approximant_of P α v -> approximant_of P β v.
  Proof.
    now apply φ_Φ_n_monotone.
  Qed.  
      
  Lemma approximation_characterization : forall α P v,
      φ_Φ_n α P v <-> exists β, β < α /\ φ_Φ (φ_Φ_n β) P v.
  Proof.
    intros α P v; split; intros H.
    - induction α.
      + inversion H.
      + exists α; split; [apply le_n | apply H].
    - destruct H as [β [Hle Hφ]]; induction Hle.
      + apply Hφ.
      + now apply φ_Φ_n_succ.
  Qed.

  Definition φ_Φ_ω : InterpInd := fun P v => exists α, φ_Φ_n α P v.
  
  Definition prefixed (U : InterpInd) := φ_Φ U ⊑ U.
  Definition least (P : InterpInd -> Prop) (U : InterpInd) := P U /\ (forall V, P V -> U ⊑ V).
  
  Lemma φ_Φ_ω_least_prefixed : least prefixed φ_Φ_ω.
  Proof.
    split.
    - intros P v H.
      unfold φ_Φ, φ_P, φ_pr in H;
        destruct H as (pr & [Heq Hpr] & (ρ & H1 & H2 & H3)).
      unfold eq_rect in H3; subst P; subst v.
      assert (Hsup : exists α, forall P ts, In (P; ts) (indpreds pr) -> φ_Φ_n α P (V.map (eval ρ) ts)).
      {
        induction (indpreds pr).
        + exists 0. intros. contradiction.
        + destruct a. pose proof (H2 x t).
          assert (In (x; t) ((x; t) :: l)) by now left.
          apply H in H0. destruct H0 as [α Hα].
          assert (IH_help : forall P ts, In (P; ts) l -> φ_Φ_ω P (V.map (eval ρ) ts)).
          { intros P ts Hin. apply H2. now right. }
          apply IHl in IH_help.
          destruct IH_help as [β Hβ].
          exists (S (max α β)).
          intros P ts Hin.
          inversion Hin.
          * apply approximant_monotone with α.
            -- auto with arith.
            -- apply EqdepFacts.eq_sigT_fst in H0 as HHH.
               subst x. unfold approximant_of.
               apply inj_pair2 in H0 as HH. subst t. assumption.
          * apply approximant_monotone with β.
            -- auto with arith.
            -- clear Hin. now apply Hβ.                                
      }
      destruct Hsup as [κ Hsup].
      exists (S κ).
      cbn. unfold φ_Φ.
      unfold φ_P.
      exists pr, (conj eq_refl Hpr).
      unfold φ_pr. exists ρ; split; auto.
    - intros args Hprefixed P v Hω.
      destruct Hω as [α Hφ].
      enough (H: forall β, φ_Φ (φ_Φ_n β) P v -> φ_Φ args P v).
      + now apply Hprefixed, (H α), φ_Φ_n_succ.
      + intros β; apply φ_Φ_monotone. induction β as [| β IH].
        * inversion 1.
        * cbn; unfold prefixed in Hprefixed.
          apply φ_Φ_monotone in IH. red; auto.
  Qed.
End definition_set_operator.

Section standard_model.
  Context {Σ : signature}.
  
  Definition standard_model (Φ: IndDefSet Σ) (M : structure Σ) : Prop :=
    forall (P : IndPredS Σ) ts, interpIP P ts <-> φ_Φ_ω Φ M P ts.
End standard_model.
