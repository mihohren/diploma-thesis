Require Import Relations RelationClasses.
Require Export Utf8.
Require Export Arith Bool Lia Program.
Require Export unscoped.
Require Export ListSet.

Export SigTNotations.

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

Fixpoint vec_iota (n : nat) : vec nat n :=
  match n with
  | 0 => V.nil
  | S n' => V.cons n' (vec_iota n')
  end.

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

Section monotone_operator.
  Context {A : Type}.
  Context (le : relation A).
  Context (le_order : order A le).
  Local Notation "x <= y" := (le x y).

  Definition monotone (f : A -> A) :=
    forall x y, x <= y -> f x <= f y.

  Definition prefixed_point (f : A -> A) (x : A) :=
    x <= f x.
End monotone_operator.

Notation "A ⊆ B" := (incl A B) (no associativity, at level 10).

