Require Import ZArith.
From mathcomp Require Import ssrbool ssreflect.

Set Implicit Arguments.

Inductive Typ :=
| Int
| Bool.

Definition const (a : Typ) : Type :=
  match a with
  | Int => nat
  | Bool => bool
  end.

Record ref (a : Typ) : Type :=
  { addr : nat; init : const a }.
  
Definition dec_eq_typ (a b : Typ) : decidable (a = b).
Proof. rewrite /decidable. repeat decide equality. Defined.
