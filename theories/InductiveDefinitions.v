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

  Lemma lema_iza_cor_2_2_10 :
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

  Section lemma_2_2_11.
    Lemma ω_prefixed : forall P v, @φ_Φ Σ M Φ φ_Φ_ω P v -> φ_Φ_ω P v.
    Proof.
      intros P v H. unfold φ_Φ_ω in *.
      unfold φ_Φ, φ_P in H.
      destruct H as (pr & [Heq Hpr] & (ρ & H1 & H2 & H3)).
      subst P; unfold eq_rect in H3; subst v.
      (* k := max od svih razina koje postoje zbog H2 *)
      (*      a jer je lista indpreds pr konacna, takav broj postoji *)
      (* onda postoji k + 2 *)
      set (k := 1).
    Admitted.

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

