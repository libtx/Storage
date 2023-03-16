From Coq Require Import
  List
  Classes.EquivDec.

From LibTx Require Import
  Storage.Classes.

#[export] Hint Constructors s_eq : storage.

Ltac unfold_s_eq k :=
  match goal with
    |- ?a =s= ?b =>
      constructor;
      intros k
  end.

Ltac unfold_s_eq_in k :=
  destruct k as [k].

Tactic Notation "unfold_s_eq" "in" ident(k) :=
  unfold_s_eq_in k.

Tactic Notation "unfold_s_eq" "as" ident(k) :=
  unfold_s_eq k.

Ltac rev_wlog_induction l k v t IH :=
  rewrite <-(rev_involutive l) in *;
  induction (rev l) as [|[k v|k] t IH]; try easy.

Tactic Notation "rev_wlog_induction" hyp(l) "as" ident(k) ident(v) ident(t) ident(IH) :=
  rev_wlog_induction l k v t IH.

Ltac storage_simpl_same_key e :=
  lazymatch e with
  | get ?k (put ?k _ _) => rewrite keep
  | get ?k (delete ?k _) => rewrite delete_keep
  end.

Lemma neq_symm {T} (k1 k2 : T) :
  k1 <> k2 ->
  k2 <> k1.
Proof.
  intros H.
  cbv in *. intros H1.
  symmetry in H1.
  apply H, H1.
Qed.

Ltac storage_simpl_different_key H k1 k2 e :=
  lazymatch e with
  | get k1 (put k2 _ _) => rewrite <-distinct by (apply H)
  | get k2 (put k1 _ _) => rewrite <-distinct by (apply neq_symm, H)
  | get k1 (delete k2 _) => rewrite <-delete_distinct by (apply H)
  | get k2 (delete k1 _) => rewrite <-delete_distinct by (apply neq_symm, H)
  end.

Ltac storage_simpl_wlog_apply e :=
  match e with
  | get ?k (wlog_apply ?l ?s) =>
      unfold wlog_apply;
      progress repeat rewrite fold_left_app;
      simpl
  end.

Ltac storage_simpl :=
  simpl; unfold equiv, complement in *;
  repeat
    match goal with
    | [H : ?k1 <> ?k2 |- ?e1 = ?e2] =>
        storage_simpl_different_key H k1 k2 e1 + storage_simpl_different_key H k1 k2 e2
    | |- ?e1 = ?e2 =>
        storage_simpl_same_key e1 + storage_simpl_same_key e2
    | |- ?e1 = ?e2 =>
        storage_simpl_wlog_apply e1 + storage_simpl_wlog_apply e2
    end.

Section tests.
  Import ListNotations.

  Goal forall `{Storage} k v s, get k (put k v s) = Some v.
    intros.
    now storage_simpl.
  Qed.

  Goal forall `{Storage} k v s, Some v = get k (put k v s).
    intros.
    now storage_simpl.
  Qed.

  Goal forall `{Storage} k s, get k (delete k s) = None.
    intros.
    now storage_simpl.
  Qed.

  Goal forall `{Storage} k s, None = get k (delete k s).
    intros.
    now storage_simpl.
  Qed.

  Goal forall `{Storage} k1 k2 s v,
      k1 <> k2 ->
      get k1 (put k2 v s) = get k1 s.
    intros.
    now storage_simpl.
  Qed.

  Goal forall `{Storage} k1 k2 s v,
      k1 <> k2 ->
      get k1 s = get k1 (put k2 v s).
    intros.
    now storage_simpl.
  Qed.

  Goal forall `{Storage} k1 k2 s v,
      k2 <> k1 ->
      get k1 s = get k1 (put k2 v s).
    intros.
    now storage_simpl.
  Qed.

  Goal forall `{Storage} k1 k2 s,
      k1 <> k2 ->
      get k1 s = get k1 (delete k2 s).
    intros.
    now storage_simpl.
  Qed.

  Goal forall `{Storage} k1 k2 v s,
      k1 <> k2 ->
      get k1 (put k2 v s) = get k1 (delete k2 s).
    intros.
    now storage_simpl.
  Qed.

  Goal forall `{Storage} k1 k2 k3 v1 v2 s,
      k1 <> k2 ->
      k1 <> k3 ->
      get k1 (put k2 v1 s) = get k1 (delete k2 (put k3 v2 s)).
    intros.
    now storage_simpl.
  Qed.

  Goal forall `{Storage} k1 k2 v s,
      k1 <> k2 ->
      get k1 (put k1 v s) = get k1 (delete k2 (put k1 v s)).
    intros.
    now storage_simpl.
  Qed.
End tests.

Lemma equiv_dec_to_neq : forall {T} (a b : T) `{Equivalence T eq}, a =/= b -> a <> b.
Proof.
  intros T a b Heq H.
  cbv in H.
  easy.
Qed.

Ltac storage_key_case_analysis_ k1 k2 :=
      let Heq := fresh "Heq" in
      let Hneq := fresh "Hneq" in
      destruct (equiv_dec k1 k2) as [Heq|Hneq];
      [ destruct Heq
      | apply equiv_dec_to_neq in Hneq
      ];
      storage_simpl.

Ltac storage_key_case_analysis k :=
  lazymatch goal with
  | |- context G [get k (put ?k2 _ _)] => storage_key_case_analysis_ k k2
  | |- context G [get k (delete ?k2 _)] => storage_key_case_analysis_ k k2
  end.

Section test.
  Goal forall `{Storage} `{EqDec K eq} k1 k2 v s,
      get k1 (put k2 v s) = get k1 (put k2 v s).
    intros.
    storage_key_case_analysis k1.
    - reflexivity.
    - reflexivity.
  Qed.

  Goal forall `{Storage} `{EqDec K eq} k1 k2 v s,
      Some v = get k1 (put k2 v s).
    intros.
    storage_key_case_analysis k1.
    - reflexivity.
    - give_up.
  Abort.
End test.

#[export] Hint Unfold equiv : storage.
#[export] Hint Unfold complement : storage.
