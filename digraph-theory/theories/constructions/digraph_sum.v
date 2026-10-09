(** * Digraph.digraph_sum — the disjoint union (sum) of two finite digraphs

    [digraph_sum D1 D2] has the vertices of [D1 + D2]: the arcs of [D1] between left vertices, the arcs of [D2]
    between right vertices, and no arc between the two sides, in either direction.  Every arc of a summand is kept
    as it is, loops and asymmetric arcs included: no loopless or oriented condition is imposed, and either summand
    may be empty.  The carrier is the sum type with its canonical [Finite] structure; the arc relation is declared
    as a canonical [HasArc] instance on the alias, as for [lexprod] (constructions/product.v).  The simple-graph
    disjoint union is upstream GraphTheory's [sjoin]; this is its directed counterpart, not a join (which would add
    cross arcs, as [heroes.djoin] does).
    API: the arc relation, the two injections, the two cross directions and the number of vertices.
    Registry: meta/library_primitives/disjoint-union.json (A28). *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section DigraphSum.
Variables D1 D2 : diGraphType.

Definition digraph_sum : Type := (D1 + D2)%type.
HB.instance Definition _ := Finite.on digraph_sum.

(** Arcs inside each summand, none across. *)
Definition digraph_sum_rel (x y : D1 + D2) : bool :=
  match x, y with
  | inl a, inl b => a --> b
  | inr a, inr b => a --> b
  | _, _ => false
  end.

HB.instance Definition _ := HasArc.Build digraph_sum digraph_sum_rel.

Lemma digraph_sum_arcE (x y : digraph_sum) : (x --> y) = digraph_sum_rel x y.
Proof. by []. Qed.

Lemma digraph_sum_arc_inl (a b : D1) : ((inl a : digraph_sum) --> inl b) = (a --> b).
Proof. by []. Qed.

Lemma digraph_sum_arc_inr (a b : D2) : ((inr a : digraph_sum) --> inr b) = (a --> b).
Proof. by []. Qed.

Lemma digraph_sum_arc_inl_inr (a : D1) (b : D2) : ((inl a : digraph_sum) --> inr b) = false.
Proof. by []. Qed.

Lemma digraph_sum_arc_inr_inl (a : D2) (b : D1) : ((inr a : digraph_sum) --> inl b) = false.
Proof. by []. Qed.

Lemma card_digraph_sum : #|{: digraph_sum}| = #|D1| + #|D2|.
Proof. by rewrite card_sum. Qed.

End DigraphSum.
