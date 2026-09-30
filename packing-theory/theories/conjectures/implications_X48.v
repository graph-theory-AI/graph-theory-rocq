(** * Packing.conjectures.implications_X48 -- wave X48 corpus-relation edges

    e066: the Bensmail-Harutyunyan-Le-Thomasse row (arxiv:1507.08208#00, X47.v) implies the
    Klimosova-Thomasse row (arxiv:1907.11600#00, X48.v).  The two rows have literally the same
    shape -- the same tree-decomposition-into-copies conclusion under the same three hypotheses
    -- and differ only in the parameter feeding the required edge-connectivity: the maximum
    degree [Delta T] for X47, the number of leaves [x48_leaf_count T] for X48.

    The proof is the corpus argument:
    - both [x47_edge_connected] and [x47_min_degree_at_least] are ANTITONE in their numeric
      argument (they are lower bounds on cut sizes / degrees), so replacing X47's witness [f]
      by its nondecreasing majorant [f' m = \max_(d < m.+1) f d] only strengthens X47's
      hypotheses, i.e. X47's conclusion still applies;
    - [Delta T <= x48_leaf_count T] for every forest [T] (Packing.foundations.tree_leaves,
      [forest_Delta_leq_leaves]), whence [f (Delta T) <= f' (x48_leaf_count T)];
    - [f #|E(T)| <= f' #|E(T)|] gives the minimum-degree hypothesis, and the divisibility
      hypothesis is literally the same.

    So [f'] witnesses X48.  Note that the target is the weaker row, consistently with the
    history: the Delta-version was disproved (arXiv:1803.03704) and the leaf-version is its
    proposed repair.

    The file is axiom-free: no Axiom/Parameter/Admitted. *)

From GTBase Require Import base.
From Packing.foundations Require Import tree_leaves.
From Packing.conjectures Require Import X47 X48.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The nondecreasing majorant of [f] at [m]: [\max_{d <= m} f d]. *)
Definition majorant (f : nat -> nat) (m : nat) : nat := \max_(d < m.+1) f d.

Lemma leq_majorant (f : nat -> nat) (k m : nat) : k <= m -> f k <= majorant f m.
Proof.
move=> km; have kk : k < m.+1 by rewrite ltnS.
by rewrite /majorant; apply: (leq_bigmax (Ordinal kk)).
Qed.

(** Antitonicity of the two numeric hypotheses of X47/X48. *)
Lemma x47_edge_connected_leq (G : sgraph) (k k' : nat) :
  k <= k' -> @x47_edge_connected G k' -> @x47_edge_connected G k.
Proof. by move=> kk' H S S0 ST; apply: leq_trans (H S S0 ST). Qed.

Lemma x47_min_degree_at_least_leq (G : sgraph) (k k' : nat) :
  k <= k' -> @x47_min_degree_at_least G k' -> @x47_min_degree_at_least G k.
Proof. by move=> kk' H v; apply: leq_trans (H v). Qed.

(*@EDGE from=tree_decomposition_delta_edge_connected_statement to=tree_decomposition_leaf_edge_connected_statement kind=implies status=verified proof=tree_decomposition_delta_edge_connected_implies_tree_decomposition_leaf_edge_connected cite="gc:e066" note="Same statement shape; only the parameter of the edge-connectivity hypothesis differs (Delta T vs. number of leaves of T). Replace X47's witness f by its nondecreasing majorant f'(m) = max_{d<=m} f d: both x47_edge_connected and x47_min_degree_at_least are antitone in their numeric argument, and Delta T <= (number of leaves of T) for every forest T (Packing.foundations.tree_leaves.forest_Delta_leq_leaves: a max-degree vertex v sends every neighbour into a branch of T - v containing a leaf, and in a forest an irredundant path leaving v meets exactly one neighbour of v). Hence f' witnesses X48." *)
Theorem tree_decomposition_delta_edge_connected_implies_tree_decomposition_leaf_edge_connected :
  tree_decomposition_delta_edge_connected_statement ->
  tree_decomposition_leaf_edge_connected_statement.
Proof.
case=> f Hf; exists (majorant f) => T G Ttree TE Hconn Hdeg Hdvd.
apply: (Hf T G Ttree TE); last exact: Hdvd.
- apply: x47_edge_connected_leq Hconn; apply: leq_majorant.
  by rewrite /x48_leaf_count; case: Ttree => Tf _; exact: forest_Delta_leq_leaves.
- by apply: x47_min_degree_at_least_leq Hdeg; apply: leq_majorant.
Qed.
