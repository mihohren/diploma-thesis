Require Export Utf8.
Require Export Arith Bool Lia List Program.
Require Export Relations RelationClasses.
Require Export Sorting.Permutation.
Require Export Logic.Classical.
Require Export unscoped.

Export SigTNotations.
Export ListNotations.
Export Vector.VectorNotations.

Require Vectors.Vector.
Module V := Vector.
Notation vec := (V.t).
Arguments V.nil {A}.
Arguments V.cons {A} _ {n} _.
Arguments V.In {A} a {n} v.


Lemma vec_In_nil_false : forall A (a : A), V.In a V.nil -> False.
Proof.
  inversion 1.
Qed.

Lemma vec_Exists_exists : forall A (P : A -> Prop) n (v : vec A n),
    V.Exists P v <-> exists t, V.In t v /\ P t.
Proof.
  intros A P n v; split.
  - intros Hex; induction Hex.
    + exists x. split; auto; left.
    + destruct IHHex as [y [Hiny HPy]]. exists y. split; [right | ]; auto.
  - intros (x & Hinx & HPx). induction Hinx.
    + apply V.Exists_cons_hd; assumption.
    + apply V.Exists_cons_tl; assumption.
Qed.

Lemma vec_In_of_list : forall A (a : A) (l : list A), In a l <-> V.In a (V.of_list l).
Proof.
  intros A a l; induction l as [| h t IH].
  - split; inversion 1.
  - cbn. rewrite V.In_cons_iff; split; intros [H | H]; tauto.
Qed.

Lemma vec_in_map : forall A B (f : A -> B) {n} (a : A) (v : vec A n),
    V.In a v -> V.In (f a) (V.map f v).
Proof.
  intros A B f n a v Hin.
  rewrite V.to_list_In in *.
  rewrite V.to_list_map.
  now apply in_map.
Qed.

Inductive ForallT {A : Type} (P : A -> Type) : forall {n : nat}, vec A n -> Type :=
| ForallT_nil : ForallT P V.nil
| ForallT_cons : forall (a : A) {n} (v : vec A n), P a -> ForallT P v -> ForallT P (V.cons a v).  

Definition vec_id {A : Type} {f : A -> A} (Hid : forall x, f x = x) :
  forall {n} (v : vec A n), V.map f v = v.
  intros n v. induction v.
  - reflexivity.
  - simpl. rewrite IHv. rewrite Hid. reflexivity.
Defined.

Definition vec_ext {A B} {f g : A -> B} :
  (forall x, f x = g x) -> forall {n} (v : vec A n),  V.map f v = V.map g v.
  intros Heq n; induction v.
  - reflexivity.
  - cbn. f_equal.
    + apply Heq.
    + apply IHv.
Defined.

Definition vec_comp {A B C} {f: A -> B} {g: B -> C} {h} :
  (forall x, (funcomp g f) x = h x) ->
  forall {n} (v : vec A n), V.map g (V.map f v) = V.map h v.
Proof.
  intros Heq n; induction v.
  - reflexivity.
  - cbn. rewrite <- Heq. f_equal. apply IHv.
Defined.

Lemma vec_in_dec : forall [A], (forall x y : A, {x = y} + {x <> y}) ->
                          forall (a : A) {n} (v : vec A n),
                            {V.In a v} + {~V.In a v}.
Proof.
  intros A Adec a n v.
  destruct (in_dec Adec a (V.to_list v)) as [H | H];
    rewrite <- V.to_list_In in H; auto.
Qed.

Inductive VecNoDup {A : Type} : forall {n : nat}, vec A n -> Prop :=
| VecNoDup_nil : VecNoDup (V.nil)
| VecNoDup_cons : forall (a : A) {n : nat} (v : vec A n),
    ~Vector.In a v -> VecNoDup v ->VecNoDup (V.cons a v).

Lemma VecNoDup_iff_ListNoDup :
  forall (A : Type) (n : nat) (v : vec A n),
    VecNoDup v <-> NoDup (V.to_list v).
Proof.
  intros A n v; split; intros H.
  - induction H.
    + constructor.
    + rewrite V.to_list_cons; constructor.
      * now rewrite <- V.to_list_In.
      * assumption.
  - induction v.
    + constructor.
    + rewrite V.to_list_cons in H; inversion H; subst.
      constructor; auto. now rewrite V.to_list_In.
Qed.

Lemma ListNoDup_iff_VecNoDup :
  forall (A : Type) (l : list A),
    NoDup l <-> VecNoDup (V.of_list l).
Proof.
  intros A l; split; intros H.
  - induction H; cbn; constructor; auto; now rewrite vec_In_of_list in H.
  - induction l; cbn; constructor.
    + cbn in H. inversion H; subst. apply Eqdep_dec.inj_pair2_eq_dec in H2; auto using Nat.eq_dec; subst.
      now rewrite vec_In_of_list.
    + apply IHl. inversion H; subst. apply Eqdep_dec.inj_pair2_eq_dec in H2; auto using Nat.eq_dec; subst.
      assumption.
Qed.

Definition max_fold (l : list nat) := fold_right Nat.max 0 l.
                                          
Definition vec_max_fold {n} (v : vec nat n) := V.fold_right Nat.max v 0.

Lemma vec_max_fold_ge : forall {n} (vs : vec nat n) v,
    V.In v vs -> v <= vec_max_fold vs.
Proof.
  intros n; induction vs as [| h m t IH]; intros v Hin; cbn.
  - inversion Hin.
  - apply V.In_cons_iff in Hin as [Hhd | Htl].
    + subst h. apply Nat.le_max_l.
    + specialize IH with v. apply IH in Htl.
      fold (vec_max_fold t). lia.
Qed.

Lemma max_fold_ge : forall (xs : list nat) x,
    In x xs -> x <= max_fold xs.
Proof.
  induction xs as [| h t IH]; intros x; inversion 1; cbn.
  - subst; auto with arith.
  - specialize (IH x H0). unfold max_fold in IH. lia.
Qed.
    
Lemma lt_any_lt_maxfold :
  forall {A : Type} (f : A -> nat) {n} (ys : vec A n) x y,
    V.In y ys -> x < f y -> x < vec_max_fold (V.map f ys).
Proof.
  intros A f n; induction ys as [| ysh len yst IH];
    intros x y Hin Hlt.
  - inversion Hin.
  - cbn. fold (vec_max_fold (V.map f yst)).
    apply V.In_cons_iff in Hin as [Hhd | Htl].
    + subst; lia.
    + specialize IH with x y.
      pose proof (IH Htl Hlt); lia.
Qed.

Lemma NoDup_injective_map : forall {A B} (l : list A) (f : A -> B),
    (forall x y, In x l -> In y l -> f x = f y -> x = y) -> NoDup l -> NoDup (map f l).
Proof.
  intros A B l f Hinj Hnodup. induction l as [| h t IHt].
  - constructor.
  - rewrite map_cons. constructor.
    + intros Hin. inversion Hnodup; subst. apply H1.
      apply in_map_iff in Hin as [b [Heq Hin]].
      assert (Heq1 : b = h).
      { apply Hinj; [right | left | ]; auto. }
      now subst.
    + inversion Hnodup; subst; apply IHt; auto.
      intros x y Hinx Hiny Heq. apply Hinj; auto; now right.
Qed.

Fixpoint finitely_generated_fun {A} (f : nat -> A) {n} (x : vec nat n) (y : vec A n) : nat -> A :=
  match x in vec _ n return vec A n -> nat -> A with
  | V.cons xh xt =>
      fun y m =>
        if m =? xh
        then V.hd y
        else finitely_generated_fun f xt (V.tl y) m
  | V.nil => fun _ => f
  end y.          

Notation "A ⊆ B" := (incl A B) (no associativity, at level 10).
