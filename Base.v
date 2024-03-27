Require Export Utf8.
Require Export Arith Bool.

Require Vectors.Vector.
Module V := Vector.
Notation vec := (V.t).
Arguments V.nil {A}.
Arguments V.cons {A} _ {n} _.
Arguments V.In {A} a {n} v.

Require Sets.Ensembles.
Module E := Ensembles.
Arguments E.In {U} A x.

Lemma Exists_exists : forall A (P : A -> Prop) n (v : V.t A n),
    V.Exists P v <-> (exists a : A, V.In a v /\ P a).
Proof.
  intros A P n v; split.
  - intros Hex; induction Hex.
    + exists x. split; auto; left.
    + destruct IHHex as [y [Hiny HPy]]. exists y. split; [right | ]; auto.
  - intros (x & Hinx & HPx). induction Hinx.
    + apply V.Exists_cons_hd; assumption.
    + apply V.Exists_cons_tl; assumption.
Qed.
