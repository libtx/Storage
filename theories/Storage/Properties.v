From Coq Require Import
  List
  Classes.EquivDec.

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

  Lemma wlog_apply_same : forall (l : Wlog) (s1 s2 : t),
      s1 =s= s2 ->
      wlog_apply l s1 =s= wlog_apply l s2.
  Proof with auto with storage.
    intros l s1 s2 Hs12.
    rev_wlog_induction l as k v l_ IH;
      storage_simpl;
      unfold_s_eq as k_;
      unfold_s_eq in IH;
      specialize (IH k_);
      storage_simpl;
      storage_key_case_analysis k_...
  Qed.

  Lemma wlog_apply_cons_s_eq l1 l2 e s :
    wlog_apply l1 s =s= wlog_apply l2 s ->
    wlog_apply (e :: l1) s =s= wlog_apply (e :: l2) s.
  Admitted.

  Lemma wlog_head_shadow : forall (l : Wlog) (e1 e2 : Wlog_elem) (s : t),
      wlog_elem_key e1 = wlog_elem_key e2 ->
      wlog_apply (e2 :: e1 :: l) s =s= wlog_apply (e1 :: l) s.
  Proof with auto with storage.
    intros l e1 e2 s Hk.
    unfold_s_eq as k_.
    destruct e1 as [k1 v1|k1]; destruct e2 as [k2 v2|k2];
      unfold wlog_elem_key in Hk;
      subst k1;
      rev_wlog_induction l as k v l' IH;
      storage_simpl;
      storage_key_case_analysis k_...
  Qed.

  Lemma wlog_head_comm : forall (l : Wlog) (e1 e2 : Wlog_elem) (s : t),
      wlog_elem_key e1 <> wlog_elem_key e2 ->
      wlog_apply (e2 :: e1 :: l) s =s= wlog_apply (e1 :: e2 :: l) s.
  Proof with auto with storage.
    intros l e1 e2 s Hk.
    unfold_s_eq as k_.
    destruct e1 as [k1 v1|k1]; destruct e2 as [k2 v2|k2];
      unfold wlog_elem_key in Hk;
      rev_wlog_induction l as k v l' IH;
      storage_simpl;
      repeat storage_key_case_analysis k_...
  Qed.

  Lemma wlog_split : forall (l1 l2 : Wlog) (s s'' : t),
      wlog_apply (l1 ++ l2) s =s= s'' ->
      exists s',
        (wlog_apply l1 s) =s= s' /\ (wlog_apply l2 s') =s= s''.
  Proof.
    intros l1 l2.
    induction l1; intros; sauto.
  Qed.

  Lemma wlog_shadow : forall (l : Wlog) (e : Wlog_elem) (s : t),
      wlog_has_key (wlog_elem_key e) l ->
      wlog_apply (e :: l) s =s= wlog_apply l s.
  Proof.
    intros *. intros Hk.
    induction l as [|e' l IH].
    - exfalso. inversion Hk.
    - destruct (equiv_dec (wlog_elem_key e) (wlog_elem_key e')) as [Heq|Hneq].
      + unfold equiv in Heq.
        now apply wlog_head_shadow.
      + apply equiv_dec_to_neq in Hneq.
        specialize (wlog_head_comm l e e' s Hneq) as Hcomm.
        apply s_eq_trans with (b := wlog_apply (e' :: e :: l) s).
        * now apply s_eq_symm.
        * apply wlog_apply_cons_s_eq, IH.
          destruct e as [k1 v1|k1]; destruct e' as [k2 v2|k2];
            destruct Hk; sauto.
  Qed.

  Lemma wlog_shadow_list : forall (l l' : Wlog) (s : t),
      Forall (fun e => wlog_has_key (wlog_elem_key e) l) l' ->
      wlog_apply (l' ++ l) s =s= wlog_apply l s.
  Proof with auto with storage.
    intros *. intros Hk.
    induction l' as [|e l' IH].
    + simpl. apply s_eq_refl.
    + inversion_clear Hk.
      apply wlog_shadow with (s := s) in H0.
      replace ((e :: l') ++ l) with (e :: (l' ++ l))...
      apply IH in H1.
      apply s_eq_trans with (b := wlog_apply (e :: l) s)...
      apply wlog_apply_cons_s_eq.
      apply s_eq_trans with (b := wlog_apply l s)...
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

  Lemma loss_wlog_has_key l l' :
    LossyWlog l l' ->
    Forall (fun e => wlog_has_key (wlog_elem_key e) l) l'.
  Admitted.

  Theorem dirty_bootstrap : forall (l l' : @Wlog K V) (s : t),
      LossyWlog l l' ->
      wlog_apply l s =s= wlog_apply (l' ++ l) s.
  Proof.
    intros l l' s Hll'.
    eapply loss_wlog_has_key, wlog_shadow_list, s_eq_symm in Hll'.
    eauto.
  Qed.
End dirty_bootstrap.
