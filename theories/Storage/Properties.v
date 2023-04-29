From Coq Require Import
  List
  Classes.EquivDec.

Import ListNotations.

From Hammer Require Import
  Tactics.

From LibTx Require Import
  Storage.Classes
  Storage.Tactics.

Section basic.
  Context {K V : Type} `{HKeq_dec : EqDec K eq} {T} `{HT_Storage : @Storage K V T}.

  Lemma s_eq_self : forall (s : T), s =s= s.
  Proof.
    sauto.
  Qed.

  Hint Resolve s_eq_self : storage.

  Lemma put_eq_eq : forall (s1 s2 : T) k v,
      s1 =s= s2 ->
      put k v s1 =s= put k v s2.
  Proof with auto with storage.
    intros s1 s2 k v Heq.
    unfold_s_eq as k_.
    unfold_s_eq in Heq.
    storage_key_case_analysis k_...
  Qed.

  Lemma put_same : forall (s : T) k v,
      get k s = Some v ->
      s =s= put k v s.
  Proof with auto with storage.
    intros s k v Hkv.
    unfold_s_eq as k_.
    storage_key_case_analysis k_...
  Qed.

  Lemma put_distict_comm : forall (s : T) k1 k2 v1 v2,
      k1 <> k2 ->
      put k2 v2 (put k1 v1 s) =s= put k1 v1 (put k2 v2 s).
  Proof with auto with storage.
    intros s k1 k2 v1 v2 H12.
    unfold_s_eq as k_.
    repeat storage_key_case_analysis k_...
  Qed.
End basic.

Section s_eq.
  Context {t1 t2} `{Storage t1} `{Storage t2}.

  Lemma s_eq_refl a :
    a =s= a.
  Proof.
    sauto.
  Qed.

  Lemma s_eq_trans a b c :
    a =s= b -> b =s= c -> a =s= c.
  Proof.
    sauto.
  Qed.

  Lemma s_eq_symm a b :
    a =s= b -> b =s= a.
  Proof.
    sauto.
  Qed.
End s_eq.

#[export] Hint Resolve s_eq_refl : storage.

Section keys_snapshot.
  Context `{HT_Storage : KeysSnapshot}.

  Theorem keys_snapshot_empty : forall (s : t) k,
      ~In k (keys_snapshot s) -> get k s = None.
  Proof.
    intros s k Hin.
    specialize (keys_snapshot_some s k) as [Hs Hs_rev].
    destruct (get k s).
    - exfalso. apply Hin. apply Hs_rev. exists v. reflexivity.
    - reflexivity.
  Qed.

  Theorem keys_snapshot_some_inv : forall (s : t) k v,
      Some v = get k s -> In k (keys_snapshot s).
  Proof.
    intros.
    apply keys_snapshot_some. exists v. easy.
  Qed.
End keys_snapshot.

Section wlog_props.
  Context `{Storage} `{HKeq_dec : EqDec K eq}.

  Lemma wlog_get_cons l1 l2 a s1 s2 :
    get (wlog_elem_key a) (wlog_apply (a :: l1) s1) = get (wlog_elem_key a) (wlog_apply (a :: l2) s2).
  Proof.
    destruct a as [k v|k];
      now storage_simpl.
  Qed.

  Lemma wlog_apply_same : forall (l : Wlog) (s1 s2 : t),
      s1 =s= s2 ->
      wlog_apply l s1 =s= wlog_apply l s2.
  Proof with auto with storage.
    intros l s1 s2 Hs12.
    induction l as [|[k v|k] l IH].
    - sauto.
    - unfold_s_eq as k_. unfold_s_eq in IH. specialize (IH k_).
      simpl. storage_key_case_analysis k_...
    - unfold_s_eq as k_. unfold_s_eq in IH. specialize (IH k_).
      simpl. storage_key_case_analysis k_...
  Qed.

  Lemma wlog_app (l1 l2 : Wlog) s :
    wlog_apply (l1 ++ l2) s = wlog_apply l1 (wlog_apply l2 s).
  Proof.
    unfold wlog_apply.
    apply fold_right_app.
  Qed.

  Lemma wlog_split (l1 l2 : Wlog) (s s'' : t) :
      wlog_apply (l1 ++ l2) s =s= s'' ->
      exists s',
        (wlog_apply l2 s) =s= s' /\ (wlog_apply l1 s') =s= s''.
  Proof.
    intros H12.
    rewrite wlog_app in H12.
    set (s' := fold_right wlog_elem_apply s l2).
    exists s'. sauto.
  Qed.

  Definition wlog_equiv (l1 l2 : Wlog) :=
    forall s, wlog_apply l1 s =s= wlog_apply l2 s.

  Lemma wlog_equiv_cons a l1 l2 :
    wlog_equiv l1 l2 ->
    wlog_equiv (a :: l1) (a :: l2).
  Proof.
    intros H12 s.
    specialize (H12 s).
    destruct a as [k v|k]; simpl;
      unfold_s_eq as k_; unfold_s_eq in H12; specialize (H12 k_);
      storage_key_case_analysis k_;
      sauto.
  Qed.

  Lemma wlog_equiv_head_shadow (l : Wlog) (e1 e2 : Wlog_elem) :
      wlog_elem_key e1 = wlog_elem_key e2 ->
      wlog_equiv (e1 :: e2 :: l) (e1 :: l).
  Proof with auto with storage.
    intros Hk s.
    unfold_s_eq as k_.
    destruct e1 as [k1 v1|k1]; destruct e2 as [k2 v2|k2];
      unfold wlog_elem_key in Hk;
      subst k2;
      storage_simpl;
      storage_key_case_analysis k_...
  Qed.

  Lemma wlog_equiv_head_comm (l : Wlog) (e1 e2 : Wlog_elem) :
      wlog_elem_key e1 <> wlog_elem_key e2 ->
      wlog_equiv (e2 :: e1 :: l) (e1 :: e2 :: l).
  Proof with auto with storage.
    intros Hk s.
    unfold_s_eq as k_.
    destruct e1 as [k1 v1|k1]; destruct e2 as [k2 v2|k2];
      unfold wlog_elem_key in Hk;
      rev_wlog_induction l as k v l' IH;
      storage_simpl;
      repeat storage_key_case_analysis k_...
  Qed.

  Lemma wlog_equiv_trans (l1 l2 l3 : Wlog) :
      wlog_equiv l1 l2 ->
      wlog_equiv l2 l3 ->
      wlog_equiv l1 l3.
  Proof.
    intros H12 H23 s.
    specialize (H12 s).
    specialize (H23 s).
    eapply s_eq_trans; eauto.
  Qed.

  Lemma wlog_equiv_refl l :
    wlog_equiv l l.
  Proof.
    intros s.
    apply s_eq_refl.
  Qed.

  Lemma wlog_equiv_symm l1 l2 :
    wlog_equiv l1 l2 -> wlog_equiv l2 l1.
  Proof.
    intros H12 s. specialize (H12 s).
    now apply s_eq_symm.
  Qed.

  Global Instance Wlog_refl : Reflexive wlog_equiv := wlog_equiv_refl.

  Global Instance Wlog_symm : Symmetric wlog_equiv := wlog_equiv_symm.

  Global Instance Wlog_trans : Transitive wlog_equiv := wlog_equiv_trans.

  Global Instance Wlog_equiv : Equivalence wlog_equiv := {}.

  Lemma wlog_equiv_append (l1 l2 : @Wlog K V) a :
      wlog_equiv l1 l2 ->
      wlog_equiv (l1 ++ [a]) (l2 ++ [a]).
  Proof.
    intros H12 s.
    set (s' := wlog_elem_apply a s).
    specialize (H12 s').
    unfold wlog_apply. repeat rewrite fold_right_app.
    replace (fold_right wlog_elem_apply s [a]) with s' by reflexivity.
    assumption.
  Qed.
End wlog_props.

Section dirty_bootstrap.
  Context `{KeysSnapshot} `{HKeq_dec : EqDec K eq}.

  Inductive LossyWlog : @Wlog K V -> @Wlog K V -> Prop :=
  | lwl_skip : forall a l l',
      LossyWlog l l' ->
      LossyWlog (a :: l) l'
  | lwl_keep : forall a l l',
      LossyWlog l l' ->
      LossyWlog (a :: l) (a :: l').

  Lemma wlog_cons_get_different k e s :
      wlog_elem_key e <> k ->
      get k (wlog_elem_apply e s) = get k s.
  Proof.
    intros Hk.
    destruct e as [k1 v1|k1];
      simpl in Hk;
      storage_simpl;
      auto.
  Qed.

  Lemma wlog_append_get_different k e l s :
      wlog_elem_key e <> k ->
      get k (wlog_apply l (wlog_elem_apply e s)) = get k (wlog_apply l s).
  Proof.
    intros Hk.
    unfold wlog_apply. repeat rewrite fold_right_app.
    induction l as [|[k1 v1|k1] l IH];
      destruct e as [k__e v__e|k__e];
      simpl in Hk;
      storage_simpl;
      auto;
      storage_key_case_analysis k;
      auto.
  Qed.

  Theorem dirty_bootstrap : forall l l',
      LossyWlog l l' ->
      wlog_equiv (l ++ l') l.
  Proof.
    intros l.
    induction l; intros l' Hl'.
    - sauto.
    - inversion_clear Hl'.
      + rewrite <-app_comm_cons.
        apply wlog_equiv_cons. sauto.
      + specialize (IHl l'0). apply IHl in H1.
        intros s. specialize (H1 s).
        unfold_s_eq as k_.
        simpl. rewrite wlog_app in *.
        set (s' := wlog_apply l s) in *.
        destruct (equiv_dec (wlog_elem_key a) k_) as [Hkk|Hkk].
        * unfold equiv in Hkk. subst.
          apply wlog_get_cons.
        * apply equiv_dec_to_neq in Hkk.
          repeat rewrite wlog_cons_get_different by assumption.
          simpl.
          rewrite wlog_append_get_different by assumption.
          unfold_s_eq in H1. specialize (H1 k_).
          apply H1.
  Qed.
End dirty_bootstrap.
