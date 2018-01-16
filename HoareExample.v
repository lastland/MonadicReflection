From mathcomp Require Import ssreflect ssrnat seq.
From MonadicEffect Require Import Hoare.

Require Import Program.

Inductive Tree (a : Set) :=
| Leaf : a -> Tree a
| Node : Tree a -> Tree a -> Tree a.

Arguments Leaf {a}.
Arguments Node {a}.

Fixpoint size {a : Set} (t : Tree a) : nat :=
  match t with
  | Leaf x => 1
  | Node l r => size l + size r
  end.

Fixpoint seq (x n : nat) : list nat :=
  match n with
  | O => nil
  | S k => x :: seq (S x) k
  end.

Lemma seq_split : forall y x z,
    seq x (y + z) = seq x y ++ seq (x + y) z.
Proof.
  elim=> [| y IHy] x z /=.
  - by rewrite addn0 add0n.
  - by rewrite (IHy x.+1 z) -addSnnS.
Qed.

Fixpoint flatten {a : Set} (t : Tree a) : list a :=
  match t with
  | Leaf x => x :: nil
  | Node l r => flatten l ++ flatten r
  end.

Program Fixpoint relabel {a : Set} (t : Tree a) :
  HoareState nat
             (@top nat)
             (Tree nat) 
             (fun i t f => f = i + size t /\ flatten t = seq i (size t)) :=
  match t with
  | Leaf x =>
    n <- get ;;
    put (n + 1) ;;
    ret (Leaf n)
  | Node l r =>
    l' <- relabel l ;;
    r' <- relabel r ;;
    ret (Node l' r')
  end.
Next Obligation.
  case (relabel a l >>= _) => /=.
  case=> x' n [t1] [n2] [[H0 H1] H2].
  case: H2 => t2 [n3] [[H3 H4] [H5 H6]].  
  rewrite H6. split => /=.
  - rewrite -H5 H3 H0 addnA //.
  - rewrite H1 H4 seq_split H0 //.
Defined.
