(** * GTBase.complete_multipartite_graphs -- complete multipartite graphs with equal parts, on the product carrier

    [complete_multipartite_graph k m] has the vertices ['I_k * 'I_m]: the first coordinate names one of [k] parts and
    the second one of the [m] vertices of that part.  Two vertices are adjacent iff they lie in different parts,
    [x.1 != y.1].  This is K_{m*k} (k parts of size m), also written K_k(m).  Every [k] and [m] is allowed: [k = 0] or
    [m = 0] gives the empty graph, [k = 1] gives [m] isolated vertices and [m = 1] the complete graph on [k] vertices.
    The upstream complete graph ['K_k] (on ['I_k]) and complete bipartite graph ['K_n,m] (on ['I_n + 'I_m]) live on
    other carriers: [complete_multipartite_graph k 1] is isomorphic to ['K_k], never convertible.  The arbitrary-size
    partition predicate of Extremal XE1 and the oriented predicate of Digraph X221 are different notions.
    API: the adjacency view and k*m vertices, same and different parts, zero parameters, one part, singleton parts.
    Registry: meta/library_primitives/complete-multipartite.json (A27). *)
From mathcomp Require Import all_boot.
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section CompleteMultipartite.
Variables k m : nat.

(** Vertices in different parts are adjacent. *)
Definition complete_multipartite_rel : rel ('I_k * 'I_m) := fun x y => x.1 != y.1.

Lemma complete_multipartite_sym : symmetric complete_multipartite_rel.
Proof. by move=> x y; rewrite /complete_multipartite_rel eq_sym. Qed.

Lemma complete_multipartite_irrefl : irreflexive complete_multipartite_rel.
Proof. by move=> x; rewrite /complete_multipartite_rel eqxx. Qed.

Definition complete_multipartite_graph : sgraph := SGraph complete_multipartite_sym complete_multipartite_irrefl.

Lemma complete_multipartite_edgeE (x y : 'I_k * 'I_m) : @edge_rel complete_multipartite_graph x y = (x.1 != y.1).
Proof. by []. Qed.

Lemma card_complete_multipartite_graph : #|complete_multipartite_graph| = k * m.
Proof. by rewrite card_prod !card_ord. Qed.

(** Two vertices of one part are never adjacent; vertices of different parts always are. *)
Lemma complete_multipartite_same_part (i : 'I_k) (a b : 'I_m) :
  ~~ @edge_rel complete_multipartite_graph (i, a) (i, b).
Proof. by rewrite complete_multipartite_edgeE eqxx. Qed.

Lemma complete_multipartite_diff_part (i j : 'I_k) (a b : 'I_m) :
  i != j -> @edge_rel complete_multipartite_graph (i, a) (j, b).
Proof. by rewrite complete_multipartite_edgeE. Qed.

End CompleteMultipartite.

(** ** Degenerate parameters: no part or empty parts, one part, singleton parts *)

Lemma card_complete_multipartite_graph0n (m : nat) : #|complete_multipartite_graph 0 m| = 0.
Proof. by rewrite card_complete_multipartite_graph. Qed.

Lemma card_complete_multipartite_graphn0 (k : nat) : #|complete_multipartite_graph k 0| = 0.
Proof. by rewrite card_complete_multipartite_graph muln0. Qed.

Lemma complete_multipartite_graph1n_edgeless (m : nat) (x y : complete_multipartite_graph 1 m) : ~~ (x -- y).
Proof. by rewrite complete_multipartite_edgeE (ord1 x.1) (ord1 y.1) eqxx. Qed.

Lemma complete_multipartite_graphn1_edgeE (k : nat) (x y : complete_multipartite_graph k 1) : (x -- y) = (x != y).
Proof.
by case: x y => [i a] [j b]; rewrite (ord1 a) (ord1 b) complete_multipartite_edgeE /= xpair_eqE eqxx andbT.
Qed.

(** Singleton parts: the complete graph, up to the isomorphism of ['I_k * 'I_1] with ['I_k]. *)
Lemma complete_multipartite_graphn1_diso (k : nat) : complete_multipartite_graph k 1 ≃ 'K_k.
Proof.
rewrite -[X in 'K_X](muln1 k) -card_complete_multipartite_graph.
by apply: diso_Kn => x y; rewrite complete_multipartite_graphn1_edgeE.
Qed.
