Require Import Ascii.
Require Import Relation_Definitions.

From mathcomp Require Import ssreflect seq ssrnat.
Set Bullet Behavior "Strict Subproofs".

From ExtLib Require Import Structures.Monad.
Import MonadNotation.
Open Scope monad_scope.

Definition string := seq ascii.

Record Output (A : Type) := MkOutput { output : A * string }.

Arguments MkOutput {_}.
Arguments output {_}.

Instance OutputMonad : Monad Output :=
  {| ret  := fun (t : Type) X => MkOutput (X, [::]);
     bind := fun (t t' : Type) m f =>
               let (a, s) := output m in
               let (b, s') := output (f a) in
               MkOutput (b, s ++ s')
  |}.

Definition out (c : ascii) : Output unit :=
  MkOutput (tt, [:: c]).

Definition collect (m : Output unit) : string :=
  snd (output m).

Lemma collect_length_prop : forall (m1 m2 : Output unit),
    size (collect (m1 ;; m2)) = size (collect (m2 ;; m1)).
Proof.
  move=>m1 m2 /=. case (output m1). case (output m2).
  intros. rewrite /collect /= !size_cat addnC //.
Qed.

Record Output' (A : Type) := MkOutput' { output' : string -> A * string }.

Arguments MkOutput' {_}.
Arguments output' {_}.

Instance OutputMonad' : Monad Output' :=
  {| ret  := fun (t : Type) X => MkOutput' (fun s => (X, s));
     bind := fun (t t' : Type) m f =>
               MkOutput' (fun s =>
                            let (a, s') := output' m s in
                            output' (f a) s')
  |}.

Section FailedAttempt.
  Definition out' (c : ascii) : Output' unit :=
    MkOutput' (fun s => (tt, c :: s)).

  Definition collect' (m : Output' unit) : string :=
    let s := output' m [::] in
    rev (snd s).

  Lemma collect_length'_prop : forall (m1 m2 : Output' unit),
      size (collect' (m1 ;; m2)) = size (collect' (m2 ;; m1)).
  Proof.
    move=>m1 m2 /=. rewrite /collect' /= !size_rev.
    case (output' m1 [::]). case (output' m2 [::]). intros.
  Abort.
End FailedAttempt.

Reset FailedAttempt.

Set Implicit Arguments.

Section Reflection.
  
  Variable A : Type.
  
  Definition reflect (m : Output A) : Output' A :=
    let (a, s) := output m in
    MkOutput' (fun s' => (a, rev s ++ s')).

  Definition reify (m : Output' A) : Output A :=
    let (a, s) := output' m [::] in
    MkOutput (a, rev s).

  Lemma reify_reflect : forall m,
      reify (reflect m) = m.
  Proof.
    move=>m. rewrite /reflect /reify.
    case m. case. simpl. intros. f_equal.
    by rewrite cats0 revK //.
  Qed.
End Reflection.

Section NewAttempt.
  Definition out' (c : ascii) : Output' unit :=
    reflect (out c).

  Definition collect' (m : Output' unit) : string :=
    collect (reify m).

  Lemma collect_length'_prop : forall (m1 m2 : Output' unit),
      size (collect' (m1 ;; m2)) = size (collect' (m2 ;; m1)).
  Proof.
    move=>m1 m2. rewrite /collect' /reify.
    case m1. case m2. simpl.
  Abort.
End NewAttempt.

Unset Implicit Arguments.

Class purification (A : Type) :=
  { pure : Type }.

Global Polymorphic Instance unit_purification : purification (unit) :=
  { pure := unit }.

Global Instance string_purification : purification string :=
  { pure := string }.

Notation "| A |" := (@pure A _) (at level 98).

Section Purification.
  Polymorphic Variables A B : Type.
  Polymorphic Context `{ purification A }.
  Polymorphic Context `{ purification B }.

  Global Polymorphic Instance tuple_purification : purification (A * B) :=
    { pure := |A| * |B| }.

  Global Polymorphic Instance fun_purification : purification (A -> B) :=
    { pure := |A| -> |B| }.

  Global Polymorphic Instance output_purification :
    purification (Output A) :=
    { pure := Output (|A|) }.

  Global Polymorphic Instance output'_purification :
    purification (Output' A) :=
    { pure := Output (|A|) }.
End Purification.

Definition prel (A : Type) `{purification A} := |A| -> A -> Prop.

Class denotation_rel (A : Type) `{purification A} :=
  { relates : prel A }.

Notation "A ~ B" := (relates A B) (at level 99).

Global Polymorphic Inductive unit_rel : prel unit :=
| unit_relates : unit_rel tt tt.

Global Instance unit_denotation_rel : denotation_rel unit :=
  { relates := unit_rel }.

Inductive string_rel : relation string :=
| string_relates : forall (s : string), string_rel s s.

Global Instance string_denotation_rel : denotation_rel string :=
  { relates := string_rel }.

Section Relation.
  Polymorphic Variables A B : Type.
  Polymorphic Context `{ denotation_rel A }.
  Polymorphic Context `{ denotation_rel B }.

  Polymorphic Inductive tuple_rel : prel (A * B) :=
  | tuple_relates : forall a a' b b',
      a ~ a' -> b ~ b' -> tuple_rel (a, b) (a', b').

  Global Polymorphic Instance tuple_denotation_rel : denotation_rel (A * B) :=
    { relates := tuple_rel }.

  Polymorphic Inductive fun_rel : prel (A -> B) :=
  | fun_relates : forall f f',
      (forall a a', a ~ a' -> (f a) ~ (f' a')) -> fun_rel f f'.

  Global Polymorphic Instance fun_denotation_rel : denotation_rel (A -> B) :=
    { relates := fun_rel }.
End Relation.

Section OutputRelation.
  Variable A : Type.
  Context `{ denotation_rel A }.
  
  Inductive output_rel : prel (Output A) :=
  | output_relates : forall m m',
      @relates (A * string) _ _ (output m) (output m') -> output_rel m m'.

  Global Instance output_denotation_rel : denotation_rel (Output A) :=
    { relates := output_rel }.

  Inductive output'_rel : prel (Output' A) :=
  | output'_relates : forall m m',
      @relates (string -> A * string) _ _ (output' (reflect m)) (output' m') ->
      output'_rel m m'.

  Global Instance output'_denotation_rel : denotation_rel (Output' A) :=
    { relates := output'_rel }.
End OutputRelation.

Section RelationLemmata.
  Variables A B : Type.
  Context `{ denotation_rel A }.
  Context `{ denotation_rel B }.
  
  Lemma rel_ret : forall (a : |A|) (a' : A),
      a ~ a' -> (ret a) ~ (ret a').
  Proof.
    intros. constructor. rewrite /reflect /output' /=.
    constructor. intros. constructor; auto.
  Qed.

  Lemma rel_bind : forall m (m' : Output' A) f (f': A -> Output' B),
      m ~ m' ->
      f ~ f' ->
      @relates (Output' B) _ _ (m >>= f) (m' >>= f').
  Proof.
    intros. constructor. rewrite /reflect /output' /=.
    constructor. intros. simpl.
    destruct m. destruct m'. simpl.
    destruct output0. destruct (output'0 a') eqn:Houtput'0.
    destruct (f p) eqn:Hf. simpl. destruct output0. simpl.
    destruct (f' a0) eqn:Hf'. simpl. destruct (output'1 s0) eqn:Houtput'1.
    inversion H3; subst. move: H6.
    rewrite /reflect /output' /=. move=>Hfun.
    inversion Hfun. specialize (H6 a a' H5).
    rewrite Houtput'0 in H6. inversion H6; subst.
    inversion H4. specialize (H7 p a0 H12).
    move: H7. rewrite Hf Hf' /=. move=>Hout.
    inversion Hout. rewrite /reflect /output' /= in H7.
    inversion H7. specialize (H13 (rev s ++ a) s0 H14).
    rewrite Houtput'1 in H13. inversion H13. constructor; auto.
    rewrite rev_cat -catA //. 
  Qed.
End RelationLemmata.

Definition empty : string := nil.
Definition empty' : |string| := empty.

Lemma empty_rel : empty ~ empty'.
Proof. constructor. Qed.


Lemma reify_rel : forall m (m' : Output' unit),
    @relates (Output' unit) _ _ m m' ->
    @relates (Output unit) _ _ m (reify m').
Proof.
  intros. inversion H; subst. inversion H0; subst.
  rewrite -[m]reify_reflect.
  specialize (H1 empty empty empty_rel).
  constructor. move: H1. rewrite /output' /=.
  destruct m. destruct output0. simpl.
  destruct m'. destruct (output'0 empty) eqn:Hout.
  rewrite /reify. simpl. rewrite Hout /=.
  intros. inversion H1; constructor; auto.
  inversion H7; subst. rewrite rev_cat revK. constructor.
Qed.

Lemma relates_eq : forall m m',
    @relates (Output unit) _ _ m m' ->
    m = m'.
Proof.
  intros. inversion H; subst.
  inversion H0; subst. inversion H4; subst. inversion H3; subst.
  destruct m. destruct m'. simpl in H1. simpl in H2. subst.
  reflexivity.
Qed.

Lemma reify_eq :  forall m (m' : Output' unit),
    @relates (Output' unit) _ _ m m' ->
    m = (reify m').
Proof.
  intros. apply relates_eq. by apply reify_rel.
Qed.

Lemma collect_length'_prop : forall (m1' m2' : Output' unit) (m1 m2 : Output unit),
    @relates (Output' unit) _ _ m1 m1' ->
    @relates (Output' unit) _ _ m2 m2' ->
    size (collect' (m1' ;; m2')) = size (collect' (m2' ;; m1')).
Proof.
  intros.
  have: (m1 >>= (fun _ => m2)) ~ (m1' >>= (fun _ => m2')).
  { apply (rel_bind unit unit) with (m:=m1)(m':=m1')(f:=fun _ => m2)(f':=fun _ => m2').
    assumption. constructor; auto. }
  have: (m2 >>= (fun _ => m1)) ~ (m2' >>= (fun _ => m1')).
  { apply (rel_bind unit unit) with (m:=m2)(m':=m2')(f:=fun _ => m1)(f':=fun _ => m1').
    assumption. constructor; auto. }
  rewrite /collect'.
  do 2 move /reify_eq <-. apply collect_length_prop.
Qed.
