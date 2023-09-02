From Coq Require Import
     List
     Classes.EquivDec.

Import ListNotations.
Require Import Classes.

Section defns.
  Context {Level : Set} `{HLeqdec : EqDec Level eq}.


  Inductive Topic :=
  | t_end : Level -> Topic
  | t_cons : Level -> Topic -> Topic.

  Inductive FilterLevel :=
  | fl_const : Level -> FilterLevel
  | fl_plus.

  Inductive Filter :=
  | filt_hash
  | filt_end : FilterLevel -> Filter
  | filt_cons : FilterLevel -> Filter -> Filter.

  Definition match_level (f : FilterLevel) (l : Level) :=
    match f with
    | fl_plus    => true
    | fl_const f =>
        match equiv_dec f l with
        | left _  => true
        | right _ => false
        end
    end.

  Fixpoint matches (f : Filter) (t : Topic) : bool :=
    match f                 , t with
    | filt_hash             , _           => true
    | filt_end f            , t_end l     => match_level f l
    | filt_cons f filt_hash , t_end l     => match_level f l
    | filt_cons f next      , t_cons l tl =>
        match match_level f l with
        | true                            => matches next tl
        | false                           => false
        end
    | _                     , _           => false
    end.
End defns.

Notation "'t[' a ']'" := (t_end a)(only parsing).
Notation "'t[' a ; .. ; b ; c ']'" := (t_cons a .. (t_cons b (t_end c)) ..)(only parsing).

Declare Custom Entry filter.
Notation "+" := (fl_plus) (in custom filter at level 40).
Notation "x" := (fl_const x) (in custom filter at level 40, x constr).

Notation "'f[' x ']'" := (filt_end x) (x custom filter, only parsing).
Notation "'f#[' a ; .. ; b ]" := (filt_cons a .. (filt_cons b filt_hash) ..) (a custom filter, b custom filter, only parsing).
Notation "'f[' a ; .. ; b ; c ]" := (filt_cons a .. (filt_cons b (filt_end c)) ..) (a custom filter, b custom filter, c custom filter, only parsing).

Section tests.
  Goal matches filt_hash t[1;2;3] = true.
    reflexivity.
  Qed.

  Goal matches f[1] t[1] = true.
    reflexivity.
  Qed.

  Goal matches f#[1] t[1] = true.
    reflexivity.
  Qed.

  Goal matches f[1;1 ] t[1] = false.
    reflexivity.
  Qed.

  Goal matches f[1;1] t[1; 1] = true.
    reflexivity.
  Qed.

  Goal matches f[+;+] t[1; 2] = true.
    reflexivity.
  Qed.

  Goal matches f[+;+] t[1] = false.
    reflexivity.
  Qed.

  Goal matches f[+;+] t[1; 2; 3] = false.
    reflexivity.
  Qed.

  Goal matches f[1;+] t[1; 2] = true.
    reflexivity.
  Qed.

  Goal matches f#[1;2] t[1; 2] = true.
    reflexivity.
  Qed.

  Goal matches f#[1;2] t[1; 2; 3; 4] = true.
    reflexivity.
  Qed.
End tests.

Section MQTTSemantics.
  Context {Level Value : Type} `{HLeqdec : EqDec Level eq}.

  Definition Sub
