From Coq Require Import
  List
  Classes.EquivDec.

Import ListNotations.

From LibTx Require Import
  Storage.Classes.

Section defns.
Context {K V : Type} `{HKeq_dec : EqDec K eq}.

Definition t := list (K * V).

Let eq_dec (a b : K) : {a = b} + {a <> b}.
Proof.
  apply (HKeq_dec a b).
Defined.

Fixpoint list_delete (k : K) s : t :=
  match s with
  | [] => []
  | (k', v) :: t =>
      if eq_dec k k'
      then list_delete k t
      else (k', v) :: list_delete k t
  end.

Definition list_put (k : K) (v : V) s : t :=
  (k, v) :: (list_delete k s).

Fixpoint list_get (k : K) (s : t) : option V :=
  match s with
  | [] => None
  | (k', v) :: t =>
      if eq_dec k' k
      then Some v
      else list_get k t
  end.

Fixpoint list_keys (s : t) : list K :=
  match s with
  | [] => []
  | (k, _) :: t => k :: list_keys t
  end.

Let list_new_empty : forall k,
    list_get k [] = None.
Proof.
  easy.
Qed.

Let list_keep : forall (s : t) (k : K) (v : V),
    list_get k (list_put k v s) = Some v.
Proof.
  intros.
  simpl. destruct (eq_dec k k); easy.
Qed.

Let list_delete_keep : forall (s : t) k,
    list_get k (list_delete k s) = None.
Proof with try easy.
  intros.
  induction s as [|[k1 v] t IH]...
  simpl.
  destruct (eq_dec k k1)...
  simpl.
  rewrite IH.
  destruct (eq_dec k1 k) as [H|H]; try symmetry in H...
Qed.

Let list_delete_distinct : forall (s : t) (k1 k2 : K),
    k1 <> k2 ->
    list_get k1 s = list_get k1 (list_delete k2 s).
Proof with auto.
  intros.
  induction s...
  destruct a as [k v].
  destruct (eq_dec k k1) as [|Hneq_k_k1]; subst.
  - simpl in *...
    destruct (eq_dec k2 k1) as [Heq12|Hneq12].
    + subst. now contradiction H.
    + simpl.
      destruct (eq_dec k1 k1)...
  - simpl...
    destruct (eq_dec k k1); destruct (eq_dec k2 k); firstorder.
    simpl.
    destruct (eq_dec k k1); firstorder.
Qed.

Let list_distinct : forall (s : t) (k1 k2 : K) (v2 : V),
    k1 <> k2 ->
    list_get k1 s = list_get k1 (list_put k2 v2 s).
Proof.
  intros. simpl.
  destruct (eq_dec k2 k1) as [He|He].
  - symmetry in He. easy.
  - rewrite <-list_delete_distinct; easy.
Qed.

Let list_keys_some : forall (s : t) k,
    In k (list_keys s) <-> exists v, list_get k s = Some v.
Proof with auto.
  intros.
  split; intros H.
  { induction s; firstorder.
    destruct a as [k' v].
    destruct (eq_dec k k'); subst.
    - exists v. simpl...
      destruct (eq_dec k' k')...
      firstorder.
    - destruct IHs.
      + simpl in H. destruct H as [H|H]...
        symmetry in H.
        now contradiction n.
      + exists x.
        simpl.
        destruct (eq_dec k' k)...
        symmetry in e. firstorder.
  }
  { destruct H.
    induction s.
    - unfold list_get. simpl in *. inversion H.
    - destruct a as [k' v].
      simpl in *.
      destruct (eq_dec k' k); auto.
  }
Qed.

Global Instance listStorage : @Storage K V t :=
  {| new := [];
    put := list_put;
    get := list_get;
    delete := list_delete;
    new_empty := list_new_empty;
    keep := list_keep;
    distinct := list_distinct;
    delete_keep := list_delete_keep;
    delete_distinct := list_delete_distinct;
  |}.

Global Instance listKeysSnapshot : @KeysSnapshot K V t listStorage :=
  {| keys_snapshot := list_keys;
    keys_snapshot_some := list_keys_some
  |}.

End defns.
