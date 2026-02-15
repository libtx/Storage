From Coq Require Import
  FMapAVL
  OrderedType.

Require Import Classes.

Module Type Make (E : OrderedType).
  Module M := FMapAVL.Make E.

  Definition t := M.t.

  Parameter dec_eq_is_eq : forall a b, E.eq a b <-> a = b.

  Section defn.
    Context {ValT : Type}.

    Lemma fmap_new_empty k : M.find k (@M.empty ValT) = None.
    Proof.
      remember (M.find k (M.empty ValT)) as maybe_v.
      destruct maybe_v as [v|].
      - exfalso.
        specialize (@M.empty_1 ValT k v) as H.
        symmetry in Heqmaybe_v. now apply M.find_2 in Heqmaybe_v.
      - reflexivity.
    Qed.

    Lemma fmap_keep s k (v : ValT) : M.find k (M.add k v s) = Some v.
    Proof.
      specialize (@M.add_1 ValT s k k v (E.eq_refl k)) as H.
      now apply M.find_1.
    Qed.

    Lemma fmap_distinct s k1 k2 (v2 : ValT) :
      k1 <> k2 ->
      M.find k1 s = M.find k1 (M.add k2 v2 s).
    Proof.
      intros Hk.
      assert (Hk' : ~E.eq k2 k1). {
        intros Habsurd.
        apply not_eq_sym in Hk.
        now apply dec_eq_is_eq in Habsurd.
      }
      apply M.Raw.Proofs.find_find.
      intros v. split.
      - intros H.
        apply M.find_1.
        apply M.find_2 in H.
        now apply M.add_2.
      - intros H.
        apply M.find_1.
        apply M.find_2 in H.
        eapply M.add_3; eauto.
    Qed.

    Lemma fmap_delete_keep s k:
        @M.find ValT k (M.remove k s) = None.
    Proof.
      specialize (@M.remove_1 ValT s k k (E.eq_refl k)) as H.
      remember (M.remove k s) as s'.
      unfold M.find, M.remove, M.In in H.
      destruct s' as [s' bst'].
      apply M.Raw.Proofs.not_find_iff.
      - assumption.
      - now rewrite M.Raw.Proofs.In_alt in H.
    Qed.

    Lemma fmap_delete_distinct (s : t ValT) k1 k2 :
      k1 <> k2 ->
      M.find k1 s = M.find k1 (M.remove k2 s).
    Proof.
      intros Hk.
      assert (Hk' : ~E.eq k2 k1). {
        intros Habsurd.
        apply not_eq_sym in Hk.
        now apply dec_eq_is_eq in Habsurd.
      }
      apply M.Raw.Proofs.find_find.
      intros v1. split.
      - intros H.
        apply M.find_1.
        apply M.find_2 in H.
        now apply M.remove_2.
      - intros H.
        apply M.find_1.
        apply M.find_2 in H.
        eapply M.remove_3; eauto.
    Qed.

    Global Instance fmapStorage : @Storage E.t ValT (t ValT) :=
      {|
        new := @M.empty ValT;
        get := @M.find ValT;
        put := @M.add ValT;
        delete := @M.remove ValT;
        new_empty := fmap_new_empty;
        keep := fmap_keep;
        distinct := fmap_distinct;
        delete_keep := fmap_delete_keep;
        delete_distinct := fmap_delete_distinct;
      |}.
  End defn.
End Make.

Print Module Make.
