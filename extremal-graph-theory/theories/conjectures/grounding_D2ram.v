(** * Extremal.conjectures.grounding_D2ram — grounding lemmas for milestone D2ram.

    SIMPLE, Qed-closed sanity results validating the genuinely new primitives introduced
    in [D2ram.v].  For each new definition we record a SATISFIABLE witness and/or at least
    one textbook identity.  These are statement-validation lemmas, NOT the (open)
    conjectures themselves — every conjecture row stays statement-only in [D2ram.v].

    Most importantly, [common_graph_complete1] discharges the non-vacuity concern flagged
    in review: the corrected [common_graph] predicate is genuinely satisfiable (the
    one-vertex / edgeless graph is common), so the Row 3 statement is not trivially true
    by an empty hypothesis.

    Primitives reused verbatim from GTBase.base / coq-graph-theory (χ, ω, α, compl,
    [_ ⇀ _] = isubgraph, [E(_)] = sg_edge_set) are not re-grounded here. *)

From mathcomp Require Import all_boot all_fingroup.
From GTBase Require Import base.
From GraphTheory Require Import minor.
From Extremal.conjectures Require Import D2ram.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Shared edge count

    [edge_count] reuses [E(_)]; on the edgeless one-vertex graph it is 0. *)
Lemma edge_count_complete1 : edge_count (complete 1) = 0.
Proof. by rewrite /edge_count card_edge_Kn. Qed.

(** ** Row 1 — multicolour Erdős–Hajnal pattern vocabulary *)

(** [uses_all_colours] is satisfiable: with a single colour ['I_1], the constant pattern
    on ['K_2] (two distinct vertices) uses every colour. *)
Lemma uses_all_colours_const :
  uses_all_colours (fun _ _ : 'I_2 => ord0 : 'I_1).
Proof.
move=> c; exists ord0, (@Ordinal 2 1 isT); split.
- by [].
- by rewrite [c]ord1.
Qed.

(** [contains_pattern] is reflexive: every pattern places itself (identity injection). *)
Lemma contains_pattern_refl (k m : nat) (chi : 'I_k -> 'I_k -> 'I_m) :
  contains_pattern chi chi.
Proof. by exists id; split=> // i j _. Qed.

(** [palette_on] on the empty vertex set is the empty palette. *)
Lemma palette_on_set0 (n m : nat) (col : 'I_n -> 'I_n -> 'I_m) :
  palette_on col set0 = set0.
Proof.
apply/setP=> c; rewrite !inE.
apply/negbTE; rewrite negb_exists; apply/forallP=> x.
rewrite negb_exists; apply/forallP=> y.
by rewrite in_set0.
Qed.

(** ** Row 2 — perfect graphs / complete bipartite subgraphs *)

(** [perfect_graph] is satisfiable: complete graphs are perfect (every induced subgraph
    is a clique, so χ = |·| = ω there). *)
Lemma perfect_graph_complete (n : nat) : perfect_graph (complete n).
Proof. exact: GTBase.perfect_graphs.is_perfect_graph_complete. Qed.

(** Textbook identity: a perfect graph satisfies χ = ω on the whole vertex set
    (the [A = setT] instance, i.e. the surface "weak perfect" equality). *)
Lemma perfect_graph_whole (G : sgraph) :
  perfect_graph G -> χ([set: G]) = ω([set: G]).
Proof. exact: GTBase.perfect_graphs.is_perfect_graph_whole. Qed.

(** [complete_bipartite_sub] is satisfiable: the empty parts give a (vacuous) biclique. *)
Lemma complete_bipartite_sub0 (G : sgraph) :
  @complete_bipartite_sub G set0 set0.
Proof.
split; first by rewrite -setI_eq0 set0I eqxx.
by move=> a b; rewrite in_set0.
Qed.

(** Textbook identity: a complete bipartite subgraph is symmetric in its two parts. *)
Lemma complete_bipartite_sub_sym (G : sgraph) (A B : {set G}) :
  complete_bipartite_sub A B -> complete_bipartite_sub B A.
Proof.
move=> [dAB adj]; split; first by rewrite disjoint_sym.
by move=> a b aB bA; rewrite sgP; apply: adj.
Qed.

(** ** Row 3 — monochromatic copies / common graphs *)

(** [mono_copies] never exceeds the number of all vertex maps [n ^ |V(H)|]. *)
Lemma mono_copies_max (H : sgraph) (n : nat) (col : rel 'I_n) :
  (mono_copies H col <= n ^ #|H|)%N.
Proof.
rewrite /mono_copies.
apply: leq_trans (max_card _) _.
by rewrite card_ffun card_ord.
Qed.

(** On the edgeless one-vertex graph, every vertex map is (vacuously) monochromatic, so
    [mono_copies] counts all [n] maps. *)
Lemma mono_copies_complete1 (n : nat) (col : rel 'I_n) :
  mono_copies (complete 1) col = n.
Proof.
rewrite /mono_copies.
transitivity #|[set: {ffun complete 1 -> 'I_n}]|; last first.
  by rewrite cardsT card_ffun card_ord card_ord expn1.
apply: eq_card => f; rewrite in_setT inE.
apply/existsP; exists true; apply/forallP=> x; apply/forallP=> y; apply/implyP.
by have -> : (x -- y) = false by rewrite [x]ord1 [y]ord1 sgP.
Qed.

(** KEY non-vacuity witness: the corrected [common_graph] predicate is SATISFIABLE — the
    one-vertex (edgeless) graph is common, so the Row 3 statement is not vacuous. *)
Lemma common_graph_complete1 : common_graph (complete 1).
Proof.
exists 0 => n col _ _.
rewrite mono_copies_complete1 edge_count_complete1 expn0 muln1 card_ord expn1.
exact: leqnn.
Qed.

(** ** Row 4 — undirected Cayley graphs *)

(** With the empty connection set the Cayley graph is edgeless. *)
Lemma cayley_adj_set0 (gT : finGroupType) (x y : gT) :
  @cayley_adj gT set0 x y = false.
Proof. by rewrite /cayley_adj !in_set0 orbF andbF. Qed.

(** With the full connection set the Cayley graph is the complete graph on [gT]. *)
Lemma cayley_adj_setT (gT : finGroupType) (x y : gT) :
  @cayley_adj gT setT x y = (x != y).
Proof. by rewrite /cayley_adj !in_setT orbT andbT. Qed.

(** ** Row 5 — induced copies *)

(** [has_induced_copy] is reflexive: every graph contains an induced copy of itself. *)
Lemma has_induced_copy_refl (G : sgraph) : has_induced_copy G G.
Proof. by constructor; apply: (@ISubgraph G G id (@inj_id _)) => x y. Qed.

(** [has_induced_copy] has TEETH: ['K_2] has NO induced copy in ['K_1], so the
    Erdős–Hajnal hypothesis [~ has_induced_copy H G] is genuinely satisfiable (the
    H-induced-free class is nonempty — not vacuously true).  An induced embedding
    ['K_2 ⇀ 'K_1] would inject the two distinct vertices of ['K_2] into the single
    vertex of ['K_1], contradicting [isubgraph_inj]. *)
Lemma not_has_induced_copy_K2_K1 : ~ has_induced_copy 'K_2 'K_1.
Proof.
case=> emb.
have E : emb ord0 = emb (@Ordinal 2 1 isT).
  by rewrite [emb ord0]ord1 [emb (@Ordinal 2 1 isT)]ord1.
have contra := isubgraph_inj emb ord0 (@Ordinal 2 1 isT) E.
by move/eqP: contra; rewrite -val_eqE.
Qed.
