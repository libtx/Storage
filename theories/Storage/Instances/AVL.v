From Coq Require Import
  FMapAVL
  OrderedType.

Require Import Classes.

Module Type Make (E : OrderedType).
  Include FMapAVL.Make E.

  Parameter dec_eq_is_eq : forall a b, E.eq a b <-> a = b.

  Lemma fmap_new_empty {ValT : Type} k : find k (@empty ValT) = None.
  Proof.
    remember (find k (empty ValT)) as maybe_v.
    destruct maybe_v as [v|].
    - exfalso.
      specialize (@empty_1 ValT k v) as H.
      symmetry in Heqmaybe_v. now apply find_2 in Heqmaybe_v.
    - reflexivity.
  Qed.

  Lemma fmap_keep {ValT : Type} s k (v : ValT) : find k (add k v s) = Some v.
  Proof.
    specialize (@add_1 ValT s k k v (E.eq_refl k)) as H.
    now apply find_1.
  Qed.

  Lemma fmap_distinct {ValT : Type} s k1 k2 (v2 : ValT) :
    k1 <> k2 ->
    find k1 s = find k1 (add k2 v2 s).
  Proof.
    intros Hk.
    assert (Hk' : ~E.eq k2 k1). {
      intros Habsurd.
      apply not_eq_sym in Hk.
      now apply dec_eq_is_eq in Habsurd.
    }
    apply Raw.Proofs.find_find.
    intros v. split.
    - intros H.
      apply find_1.
      apply find_2 in H.
      now apply add_2.
    - intros H.
      apply find_1.
      apply find_2 in H.
      eapply add_3; eauto.
  Qed.

  Lemma fmap_delete_keep {ValT : Type} s k:
      @find ValT k (remove k s) = None.
  Proof.
    specialize (@remove_1 ValT s k k (E.eq_refl k)) as H.
    remember (remove (elt:=ValT) k s) as s'.
    unfold find, remove, In in H.
    destruct s' as [s' bst'].
    apply Raw.Proofs.not_find_iff.
    - assumption.
    - now rewrite Raw.Proofs.In_alt in H.
  Qed.

  Lemma fmap_delete_distinct {ValT : Type} (s : t ValT) k1 k2 :
    k1 <> k2 ->
    find k1 s = find k1 (remove k2 s).
  Proof.
    intros Hk.
    assert (Hk' : ~E.eq k2 k1). {
      intros Habsurd.
      apply not_eq_sym in Hk.
      now apply dec_eq_is_eq in Habsurd.
    }
    apply Raw.Proofs.find_find.
    intros v1. split.
    - intros H.
      apply find_1.
      apply find_2 in H.
      now apply remove_2.
    - intros H.
      apply find_1.
      apply find_2 in H.
      eapply remove_3; eauto.
  Qed.

  Global Instance fmapStorage {Val : Type} : @Storage E.t Val (t Val) :=
    {|
      new := @empty Val;
      get := @find Val;
      put := @add Val;
      delete := @remove Val;
      new_empty := @fmap_new_empty Val;
      keep := @fmap_keep Val;
      distinct := @fmap_distinct Val;
      delete_keep := @fmap_delete_keep Val;
      delete_distinct := @fmap_delete_distinct Val;
    |}.
End Make.
