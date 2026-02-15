From Coq Require Import
  List
  Classes.EquivDec
  Classes.SetoidClass.

Section defns.
  Context {K V : Type}.

  (** Basic key-value storage type (without ability to iterate over
  keys) *)
  Class Storage t : Type :=
    { new : t;
      put : K -> V -> t -> t;
      get : K -> t -> option V;
      delete : K -> t -> t;

      (* Axioms: *)
      new_empty : forall k, get k new = None;
      keep : forall s k v, get k (put k v s) = Some v;
      distinct : forall s k1 k2 v2,
          k1 <> k2 ->
          get k1 s = get k1 (put k2 v2 s);
      delete_keep : forall s k,
          get k (delete k s) = None;
      delete_distinct : forall s k1 k2,
          k1 <> k2 ->
          get k1 s = get k1 (delete k2 s);
    }.

  (** A storage type that allows to take a snapshot of the keys and
  iterate over it. *)
  Class KeysSnapshot t `{Storage t} : Type :=
    {
      keys_snapshot : t -> list K;

      (* Axioms: *)
      keys_snapshot_some : forall s k,
          In k (keys_snapshot s) <-> exists v, get k s = Some v;
    }.
End defns.

Section Operations.
  Context {K V T} `{KeysSnapshot K V T}.

  Definition getT (k : K) (s : T) (Hin : In k (keys_snapshot s)) : V.
    remember (get k s) as v.
    destruct v.
    - destruct Heqv. apply v.
    - exfalso.
      apply keys_snapshot_some in Hin.
      rewrite <- Heqv in Hin.
      destruct Hin as [v Hin].
      discriminate.
  Defined.
End Operations.

Section EquivalenceOfDistinctStorages.
  Context {K V} {T1 T2} `{@Storage K V T1, Storage K V T2}.

  Inductive s_eq (s1 : T1) (s2 : T2) :=
  | s_eq_ : (forall k, get k s1 = get k s2) -> s_eq s1 s2.
End EquivalenceOfDistinctStorages.

Notation "s1 =s= s2" := (s_eq s1 s2) (at level 50).
#[export] Hint Constructors s_eq : storage.

Section Setoid.
  Context `{Hstorage : Storage}.

  Global Instance s_eq_refl : Reflexive s_eq.
  Proof.
    intros x. constructor. intros k.
    reflexivity.
  Qed.

  Global Instance s_eq_symmetry : Symmetric s_eq.
  Proof.
    intros x y H. constructor. intros k.
    destruct H as [H].
    now rewrite H.
  Qed.

  Global Instance s_eq_transitive : Transitive s_eq.
  Proof.
    intros x y z Hxy Hyz. constructor. intros k.
    destruct Hxy as [Hxy]. destruct Hyz as [Hyz].
    now rewrite Hxy, Hyz.
  Qed.

  Global Instance s_eq_equiv : Equivalence s_eq :=
    {|
      Equivalence_Reflexive := s_eq_refl;
      Equivalence_Symmetric := s_eq_symmetry;
      Equivalence_Transitive := s_eq_transitive;
    |}.

  Global Instance s_eq_setoid : Setoid t :=
    {|
      equiv := s_eq;
      setoid_equiv := s_eq_equiv;
    |}.
End Setoid.

Add Parametric Morphism {K V} t `{H : @Storage K V t} `{Hkdec : EqDec K eq} : (@put K V t H) with
    signature (@eq K) ==> (@eq V) ==> (@s_eq K V t t H H) ==> (@s_eq K V t t H H) as put_mor.
Proof.
  intros k v s1 s2 Hs.
  destruct Hs as [Hs].
  constructor. intros k_.
  destruct (equiv_dec k k_) as [Heq | Hneq].
  - rewrite Heq. now repeat rewrite keep.
  - repeat rewrite <- distinct; auto.
Qed.

Add Parametric Morphism {K V} t `{H : @Storage K V t} `{Hkdec : EqDec K eq} : (@delete K V t H) with
    signature (@eq K) ==> (@s_eq K V t t H H) ==> (@s_eq K V t t H H) as delete_mor.
Proof.
  intros k s1 s2 Hs.
  destruct Hs as [Hs].
  constructor. intros k_.
  destruct (equiv_dec k k_) as [Heq | Hneq].
  - rewrite Heq. now repeat rewrite delete_keep.
  - repeat rewrite <- delete_distinct; auto.
Qed.

Section WriteLog.
  Context {K V : Type} `{HKeq_dec : EqDec K eq} {T} `{HT_Storage : @Storage K V T}.

  Inductive Wlog_elem :=
  | wl_write : K -> V -> Wlog_elem
  | wl_delete : K -> Wlog_elem.

  Definition wlog_elem_key (e : Wlog_elem) :=
    match e with
    | wl_write k _ => k
    | wl_delete k => k
    end.

  Definition wlog_elem_apply (e : Wlog_elem) (s : T) : T :=
    match e with
    | wl_write k v => put k v s
    | wl_delete k => delete k s
    end.

  Definition Wlog := list Wlog_elem.

  Definition wlog_apply (l : Wlog) (s : T) :=
    fold_right wlog_elem_apply s l.

  Definition wlog_has_key (k : K) (l : Wlog) : Prop :=
    In k (map (fun x => match x with
                     | wl_write k _ => k
                     | wl_delete k => k
                     end) l).
End WriteLog.
