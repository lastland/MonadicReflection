From mathcomp Require Import ssreflect ssrnat seq.

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
