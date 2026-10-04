(** * Cycle.foundations.eulerian — Eulerian multigraphs: connected with every degree even

    The shared ("textbook") Eulerian predicate of cycle theory, factored out of
    [Cycle.conjectures.U6] (library migration B17) as a focused adapter over the
    public connectivity layer [Cycle.foundations.connectivity]:

      [eulerian G] := [mconnected G /\ forall v : G, ~~ odd (mdeg v)]

    on an [mgraph] read as an UNDIRECTED multigraph (carrier convention of
    [connectivity]).  [mdeg] counts ARC ENDS, so a loop contributes 2 and never
    breaks evenness; [mconnected] quantifies over ALL vertices through base's
    undirected [uwalk], so the reference orientation of an arc is immaterial.
    Consequences, recorded below as groundings:
      - the EMPTY multigraph and an ISOLATED vertex are eulerian (vacuous or
        zero-degree evenness, trivial connectivity);
      - one loop, two loops, and two vertices joined by two parallel arcs
        pointing the same way are eulerian;
      - a single edge is not (its ends have degree 1); two isolated vertices
        are not, and a loop component plus an isolated vertex is not (all
        degrees even, but disconnected).
    No nonempty, loopless, simple, minimum-degree or tour premise is part of
    the contract: U6's rows add their own guards ([0 < #|G|], [0 < #|edge G|],
    [simple_mgraph], [4 <= mdeg v], [edge_connected G 6], a supplied
    [is_eulerian_tour] or a transition system) at the statement.  In
    particular NO tour equivalence is stated here: [U6.is_eulerian_tour w] is a
    DIRECTED closed walk from an existential vertex, so the empty multigraph is
    eulerian without any tour, and an even connected multigraph may have no
    eulerian reference orientation; that limitation stays documented in U6's
    row.  The directed degree balance of digraphs
    ([Digraph.foundations.degree_balance]) is a different notion.

    IMPORT ORDER: [mgraph] before [base] (see [connectivity]). *)

From GraphTheory Require Import mgraph.
From GTBase Require Import base.
From Cycle.foundations Require Import connectivity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section EulerianContract.
Variable G : mgraph.

(** Every vertex has even multigraph degree (arc ends: a loop counts two). *)
Definition even_degrees : Prop := forall v : G, ~~ odd (mdeg v).

(** The Boolean form of [even_degrees] over the finite carrier. *)
Definition even_degreesb : bool := [forall v : G, ~~ odd (mdeg v)].

Lemma even_degreesP : reflect even_degrees even_degreesb.
Proof. exact: forallP. Qed.

(** The contract: connected over all vertices, and every degree even. *)
Definition eulerian : Prop := mconnected G /\ forall v : G, ~~ odd (mdeg v).

Lemma eulerianI : mconnected G -> even_degrees -> eulerian.
Proof. by []. Qed.

Lemma eulerian_mconnected : eulerian -> mconnected G.
Proof. by case. Qed.

Lemma eulerian_even_degrees : eulerian -> even_degrees.
Proof. by case. Qed.

Lemma eulerian_even (v : G) : eulerian -> ~~ odd (mdeg v).
Proof. by case=> _ /(_ v). Qed.

Lemma eulerian_even_degreesb : eulerian -> even_degreesb.
Proof. by case=> _ /even_degreesP. Qed.

(** The connectivity conjunct stays a [Prop] (base's [uwalk] existence); only
    the degree conjunct has a Boolean form. *)
Lemma eulerianE : eulerian <-> mconnected G /\ even_degreesb.
Proof. by split=> -[c /even_degreesP e]; split. Qed.

End EulerianContract.

(** ** Groundings on concrete carriers (coq-graph-theory's constructors) *)

Section Groundings.

(** The empty multigraph: no vertex, no edge; eulerian vacuously. *)
Definition empty_mgraph : mgraph := void_graph unit unit.

Lemma eulerian_empty : eulerian empty_mgraph.
Proof. by split=> -[]. Qed.

(** One isolated vertex: connected, of degree 0. *)
Definition isolated_vertex : mgraph := unit_graph tt.

Lemma edgeT_isolated_vertex : [set: edge isolated_vertex] = set0.
Proof. by apply/setP; case. Qed.

Lemma mdeg_isolated_vertex (v : isolated_vertex) : mdeg v = 0.
Proof. by rewrite /mdeg edgeT_isolated_vertex subdeg0. Qed.

Lemma mconnected_isolated_vertex : mconnected isolated_vertex.
Proof. by move=> x y; exists [::]; case: x; case: y. Qed.

Lemma eulerian_isolated_vertex : eulerian isolated_vertex.
Proof.
by split; [exact: mconnected_isolated_vertex | move=> v; rewrite mdeg_isolated_vertex].
Qed.

(** One vertex carrying one loop: degree 2, since a loop contributes both ends. *)
Definition one_loop : mgraph := mgraph.add_edge isolated_vertex tt tt tt.

Lemma edge_one_loop (e : edge one_loop) : e = None.
Proof. by case: e => [[]|]. Qed.

Lemma edgeT_one_loop : [set: edge one_loop] = [set (None : edge one_loop)].
Proof. by apply/setP => e; rewrite !inE [e]edge_one_loop eqxx. Qed.

Lemma mdeg_one_loop (v : one_loop) : mdeg v = 2.
Proof. by rewrite /mdeg edgeT_one_loop; apply: subdeg_loop; case: v. Qed.

Lemma mconnected_one_loop : mconnected one_loop.
Proof. by move=> [] []; exists [::]. Qed.

Lemma eulerian_one_loop : eulerian one_loop.
Proof. by split; [exact: mconnected_one_loop | move=> v; rewrite mdeg_one_loop]. Qed.

(** One vertex carrying two loops: degree 4. *)
Definition two_loops : mgraph := mgraph.add_edge one_loop tt tt tt.

Lemma card_edge_two_loops : #|edge two_loops| = 2.
Proof. by rewrite /two_loops /one_loop /isolated_vertex !card_option card_void. Qed.

Lemma ends_at_two_loops (b : bool) (v : two_loops) :
  ends_at [set: edge two_loops] b v = [set: edge two_loops].
Proof. by apply/setP => e; rewrite !inE; case: v; case: b; case: e => [[[]|]|]. Qed.

Lemma mdeg_two_loops (v : two_loops) : mdeg v = 4.
Proof. by rewrite /mdeg /subdeg !ends_at_two_loops cardsT card_edge_two_loops. Qed.

Lemma mconnected_two_loops : mconnected two_loops.
Proof. by move=> [] []; exists [::]. Qed.

Lemma eulerian_two_loops : eulerian two_loops.
Proof. by split; [exact: mconnected_two_loops | move=> v; rewrite mdeg_two_loops]. Qed.

(** Two vertices; one arc between them; then a second PARALLEL arc pointing
    the same way (both references [inl tt -> inr tt]). *)
Definition two_vertices : mgraph := two_graph tt tt.
Definition one_edge : mgraph := mgraph.add_edge two_vertices (inl tt) (inr tt) tt.
Definition parallel_pair : mgraph := mgraph.add_edge one_edge (inl tt) (inr tt) tt.

Lemma card_edge_one_edge : #|edge one_edge| = 1.
Proof. by rewrite /one_edge /two_vertices card_option card_sum !card_void. Qed.

Lemma card_edge_parallel_pair : #|edge parallel_pair| = 2.
Proof. by rewrite /parallel_pair /one_edge /two_vertices !card_option card_sum !card_void. Qed.

Lemma src_one_edge (e : edge one_edge) : source e = inl tt.
Proof. by case: e => [[[]|[]]|]. Qed.

Lemma tgt_one_edge (e : edge one_edge) : target e = inr tt.
Proof. by case: e => [[[]|[]]|]. Qed.

Lemma src_parallel_pair (e : edge parallel_pair) : source e = inl tt.
Proof. by case: e => [[[[]|[]]|]|]. Qed.

Lemma tgt_parallel_pair (e : edge parallel_pair) : target e = inr tt.
Proof. by case: e => [[[[]|[]]|]|]. Qed.

Lemma ends_at_parallel_pair_inl_src :
  ends_at [set: edge parallel_pair] false (inl tt) = [set: edge parallel_pair].
Proof. by apply/setP => e; rewrite !inE src_parallel_pair eqxx. Qed.

Lemma ends_at_parallel_pair_inl_tgt :
  ends_at [set: edge parallel_pair] true (inl tt) = set0.
Proof. by apply/setP => e; rewrite !inE tgt_parallel_pair. Qed.

Lemma ends_at_parallel_pair_inr_src :
  ends_at [set: edge parallel_pair] false (inr tt) = set0.
Proof. by apply/setP => e; rewrite !inE src_parallel_pair. Qed.

Lemma ends_at_parallel_pair_inr_tgt :
  ends_at [set: edge parallel_pair] true (inr tt) = [set: edge parallel_pair].
Proof. by apply/setP => e; rewrite !inE tgt_parallel_pair eqxx. Qed.

(** Both vertices have degree 2 although every arc leaves [inl tt]. *)
Lemma mdeg_parallel_pair (v : parallel_pair) : mdeg v = 2.
Proof.
case: v => -[]; rewrite /mdeg /subdeg.
- by rewrite ends_at_parallel_pair_inl_src ends_at_parallel_pair_inl_tgt cardsT
    card_edge_parallel_pair cards0.
- by rewrite ends_at_parallel_pair_inr_src ends_at_parallel_pair_inr_tgt cardsT
    card_edge_parallel_pair cards0.
Qed.

Lemma mconnected_parallel_pair : mconnected parallel_pair.
Proof.
by move=> x y; case: x => -[]; case: y => -[];
  [exists [::] | exists [:: None] | exists [:: None] | exists [::]].
Qed.

Lemma eulerian_parallel_pair : eulerian parallel_pair.
Proof.
by split; [exact: mconnected_parallel_pair | move=> v; rewrite mdeg_parallel_pair].
Qed.

(** TEETH: a single edge is not eulerian, its ends having degree 1. *)
Lemma ends_at_one_edge_inl_src :
  ends_at [set: edge one_edge] false (inl tt) = [set: edge one_edge].
Proof. by apply/setP => e; rewrite !inE src_one_edge eqxx. Qed.

Lemma ends_at_one_edge_inl_tgt : ends_at [set: edge one_edge] true (inl tt) = set0.
Proof. by apply/setP => e; rewrite !inE tgt_one_edge. Qed.

Lemma mdeg_one_edge_inl : mdeg (inl tt : one_edge) = 1.
Proof.
by rewrite /mdeg /subdeg ends_at_one_edge_inl_src ends_at_one_edge_inl_tgt cardsT
  card_edge_one_edge cards0.
Qed.

Lemma not_eulerian_one_edge : ~ eulerian one_edge.
Proof. by move=> [_ /(_ (inl tt))]; rewrite mdeg_one_edge_inl. Qed.

(** TEETH: two isolated vertices have even (zero) degrees but are not connected. *)
Lemma edgeT_two_vertices : [set: edge two_vertices] = set0.
Proof. by apply/setP => -[[]|[]]. Qed.

Lemma mdeg_two_vertices (v : two_vertices) : mdeg v = 0.
Proof. by rewrite /mdeg edgeT_two_vertices subdeg0. Qed.

Lemma even_degrees_two_vertices : even_degrees two_vertices.
Proof. by move=> v; rewrite mdeg_two_vertices. Qed.

Lemma not_mconnected_two_vertices : ~ mconnected two_vertices.
Proof. by move=> /(_ (inl tt) (inr tt)) [[|[[]|[]] w]]. Qed.

Lemma not_eulerian_two_vertices : ~ eulerian two_vertices.
Proof. by move=> /eulerian_mconnected; exact: not_mconnected_two_vertices. Qed.

(** TEETH: adding an isolated vertex to the loop component keeps every degree
    even (2 and 0) but destroys connectivity. *)
Definition loop_and_vertex : mgraph := mgraph.add_vertex one_loop tt.

Lemma uwalk_loop_and_vertex (w : seq (edge loop_and_vertex)) :
  ~~ uwalk (inl tt : loop_and_vertex) (inr tt) w.
Proof.
elim: w => [|e w IH] //=.
by case: e => [[[]|]|[]] /=; rewrite (negbTE IH) ?andbF.
Qed.

Lemma not_mconnected_loop_and_vertex : ~ mconnected loop_and_vertex.
Proof.
by move=> /(_ (inl tt) (inr tt)) [w]; apply/negP; exact: uwalk_loop_and_vertex.
Qed.

Lemma ends_at_loop_and_vertex_inl (b : bool) :
  ends_at [set: edge loop_and_vertex] b (inl tt) = [set (inl None : edge loop_and_vertex)].
Proof. by apply/setP => e; rewrite !inE; case: e => [[[]|]|[]]; case: b. Qed.

Lemma ends_at_loop_and_vertex_inr (b : bool) :
  ends_at [set: edge loop_and_vertex] b (inr tt) = set0.
Proof. by apply/setP => e; rewrite !inE; case: e => [[[]|]|[]]; case: b. Qed.

Lemma mdeg_loop_and_vertex_inl : mdeg (inl tt : loop_and_vertex) = 2.
Proof. by rewrite /mdeg /subdeg !ends_at_loop_and_vertex_inl cards1. Qed.

Lemma mdeg_loop_and_vertex_inr : mdeg (inr tt : loop_and_vertex) = 0.
Proof. by rewrite /mdeg /subdeg !ends_at_loop_and_vertex_inr cards0. Qed.

Lemma even_degrees_loop_and_vertex : even_degrees loop_and_vertex.
Proof.
by move=> v; case: v => -[]; [rewrite mdeg_loop_and_vertex_inl | rewrite mdeg_loop_and_vertex_inr].
Qed.

Lemma not_eulerian_loop_and_vertex : ~ eulerian loop_and_vertex.
Proof. by move=> /eulerian_mconnected; exact: not_mconnected_loop_and_vertex. Qed.

End Groundings.
