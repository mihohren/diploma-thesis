Require Export Utf8.
Require Export Arith Bool.
Require Export unscoped.

Require Vectors.Vector.
Module V := Vector.
Notation vec := (V.t).
Arguments V.nil {A}.
Arguments V.cons {A} _ {n} _.
Arguments V.In {A} a {n} v.

Require Sets.Ensembles.
Module E := Ensembles.
Arguments E.In {U} A x.

Lemma vec_Exists_exists : forall A (P : A -> Prop) n (v : vec A n),
    V.Exists P v <-> ex (fun t => V.In t v /\ P t).
Proof.
  intros A P n v; split.
  - intros Hex; induction Hex.
    + exists x. split; auto; left.
    + destruct IHHex as [y [Hiny HPy]]. exists y. split; [right | ]; auto.
  - intros (x & Hinx & HPx). induction Hinx.
    + apply V.Exists_cons_hd; assumption.
    + apply V.Exists_cons_tl; assumption.
Qed.

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
