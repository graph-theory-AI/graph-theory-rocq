(** * Cycle.conjectures.grounding_U6 — grounding lemmas for milestone U6

    Qed-closed, axiom-free sanity results for the new primitives introduced in
    [Cycle.conjectures.U6].  For each primitive we provide:
      - a SATISFIABLE witness (the predicate is inhabited / non-contradictory);
      - at least one textbook IDENTITY it must satisfy.

    Witness models used:
      - [Gd]: the digon (2 vertices, 2 oppositely-oriented parallel edges) — a
        genuine nonempty circuit / 2-factor / eulerian multigraph; grounds the
        structural primitives ([is_circuit], [two_factor], [cdc], ...).
      - [U]: a single vertex, no edges — grounds the connectivity /
        empty-decomposition primitives.
      - [void_graph]: no vertices — grounds the spanning/2-factor primitives
        vacuously.
      - [Gloop]: one vertex with one LOOP — grounds the degree convention
        (a loop has degree 2, so it is an [even_subgraph] and an [is_circuit]).

    NOTE on walks: the connectivity primitives of
    [Cycle.foundations.connectivity] ([mconnected], [subgraph_connected],
    [is_circuit], [is_bridge] via [ueseparates], ...) all go through base's
    UNDIRECTED [uwalk], which traverses each arc in either direction, so the
    reference orientation of an edge is immaterial; coq-graph-theory's DIRECTED
    [walk] survives only in [U6.is_eulerian_tour].  [is_path] / [two_connected]
    still have no cheap concrete nonempty witness, and for those we record
    structural identities / teeth.  [cubic] is grounded by a two-vertex graph
    with three parallel non-loop edges. *)

From GraphTheory Require Import mgraph.
From GTBase Require Import base.
From Cycle.conjectures Require Import U6.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The digon witness graph [Gd] *)

Definition G0 : mgraph := two_graph tt tt.
Definition G1 : mgraph := mgraph.add_edge G0 (inl tt) (inr tt) tt.
Definition Gd : mgraph := mgraph.add_edge G1 (inr tt) (inl tt) tt.
Definition G2p : mgraph := mgraph.add_edge G1 (inl tt) (inr tt) tt.
Definition G3p : mgraph := mgraph.add_edge G2p (inl tt) (inr tt) tt.

(** Trivial witness graphs: one vertex (no edges) and the empty graph. *)
Definition U : mgraph := unit_graph tt.
Definition V : mgraph := void_graph unit unit.

Lemma card_edge_Gd : #|edge Gd| = 2.
Proof. by rewrite /Gd /G1 /G0 !card_option card_sum !card_void. Qed.

Lemma card_edge_G3p : #|edge G3p| = 3.
Proof. by rewrite /G3p /G2p /G1 /G0 !card_option card_sum !card_void. Qed.

Lemma inc_all (v : Gd) (e : edge Gd) : incident v e.
Proof.
rewrite /incident; apply/existsP.
by case: v => -[]; case: e => [[[[]|[]]|]|];
  [exists false|exists true|exists true|exists false].
Qed.

Lemma inc_all_G3p (v : G3p) (e : edge G3p) : incident v e.
Proof.
rewrite /incident; apply/existsP.
by case: v => -[]; case: e => [[[[[]|[]]|]|]|];
  [exists false|exists false|exists false|exists true|exists true|exists true].
Qed.

Lemma edges_at_Gd (v : Gd) : edges_at v = [set: edge Gd].
Proof. by apply/setP => e; rewrite !inE inc_all. Qed.

Lemma edges_at_G3p (v : G3p) : edges_at v = [set: edge G3p].
Proof. by apply/setP => e; rewrite !inE inc_all_G3p. Qed.

(** [Gd] and [G3p] are LOOPLESS, so their [subdeg]/[mdeg] (which count arc ENDS,
    giving a loop degree 2) agree with the incidence count. *)
Lemma loopless_Gd : loopless Gd.
Proof. by case=> [[[[]|[]]|]|]. Qed.

Lemma loopless_G3p : loopless G3p.
Proof. by case=> [[[[[]|[]]|]|]|]. Qed.

Lemma subdeg_Gd (H : {set edge Gd}) (v : Gd) : subdeg H v = #|H|.
Proof. by rewrite (subdeg_loopless _ _ loopless_Gd) edges_at_Gd setTI. Qed.

Lemma mdeg_Gd (v : Gd) : mdeg v = 2.
Proof. by rewrite /mdeg subdeg_Gd cardsT card_edge_Gd. Qed.

Lemma mdeg_G3p (v : G3p) : mdeg v = 3.
Proof.
by rewrite (mdeg_loopless _ loopless_G3p) edges_at_G3p cardsT card_edge_G3p.
Qed.

(** ** [subdeg] / [mdeg] : identities *)

Lemma subdeg_set0 (G : mgraph) (v : G) : subdeg (@set0 (edge G)) v = 0.
Proof. exact: subdeg0. Qed.

Lemma subdeg_setT (G : mgraph) (v : G) : subdeg [set: edge G] v = mdeg v.
Proof. by []. Qed.

Lemma subdeg_le_mdeg (G : mgraph) (H : {set edge G}) (v : G) :
  (subdeg H v <= mdeg v)%N.
Proof. exact: subdeg_mdeg. Qed.

(** ** [subgraph_kregular] : witness + identity *)

Lemma subgraph_kregular_set0 (G : mgraph) (k : nat) :
  subgraph_kregular (@set0 (edge G)) k.
Proof. by move=> v; left; rewrite subdeg_set0. Qed.

Lemma two_factor_kregular (G : mgraph) (F : {set edge G}) :
  two_factor F -> subgraph_kregular F 2.
Proof. by move=> H v; right; rewrite H. Qed.

Lemma subgraph_kregular_Gd : subgraph_kregular (G:=Gd) [set: edge Gd] 2.
Proof. by move=> v; right; rewrite subdeg_Gd cardsT card_edge_Gd. Qed.

(** ** [two_factor] : witness (void) + identity, and the digon 2-factor *)

Lemma two_factor_void : two_factor (@set0 (edge (V))).
Proof. by case. Qed.

Lemma two_factor_Gd : two_factor (G:=Gd) [set: edge Gd].
Proof. by move=> v; rewrite subdeg_Gd cardsT card_edge_Gd. Qed.

(** ** [even_subgraph] : witness + identity *)

Lemma even_subgraph_set0 (G : mgraph) : even_subgraph (@set0 (edge G)).
Proof. by move=> v; rewrite subdeg_set0. Qed.

Lemma two_factor_even (G : mgraph) (F : {set edge G}) :
  two_factor F -> even_subgraph F.
Proof. by move=> H v; rewrite H. Qed.

Lemma even_subgraph_Gd : even_subgraph (G:=Gd) [set: edge Gd].
Proof. by move=> v; rewrite subdeg_Gd cardsT card_edge_Gd. Qed.

(** ** [walk_in] : witness + identity (reflexive empty walk) *)

Lemma walk_in_nil (G : mgraph) (H : {set edge G}) (x : G) : walk_in H x x [::].
Proof. by rewrite /walk_in /= eqxx. Qed.

(** ** [mconnected] : witness *)

Lemma mconnected_unit : mconnected (U).
Proof. by move=> x y; exists [::]; case: x; case: y. Qed.

(** ** [connected_del_edges] / [connected_del_verts] : witnesses *)

Lemma connected_del_edges_unit :
  connected_del_edges (G:=U) set0.
Proof. by move=> x y; exists [::]; split; [case: x; case: y|]. Qed.

Lemma connected_del_verts_unit :
  connected_del_verts (G:=U) set0.
Proof. by move=> x y _ _; exists [::]; split; [case: x; case: y|]. Qed.

(** ** [two_connected] : identity + teeth *)

Lemma two_connected_card (G : mgraph) : two_connected G -> (3 <= #|G|)%N.
Proof. by case. Qed.

Lemma not_two_connected_unit : ~ two_connected U.
Proof. by move=> /two_connected_card; rewrite card_unit. Qed.

(** ** [edge_connected] : witness (vacuous at k=0) + identity *)

Lemma edge_connected0 (G : mgraph) : edge_connected G 0.
Proof. by move=> E; rewrite ltn0. Qed.

(** ** [H_inc] / [subgraph_connected] : identity + witness *)

Lemma H_inc_set0 (G : mgraph) (x : G) : H_inc (@set0 (edge G)) x = false.
Proof. by apply: negbTE; apply/existsPn => e; rewrite in_set0. Qed.

Lemma subgraph_connected_set0 (G : mgraph) :
  subgraph_connected (@set0 (edge G)).
Proof. by move=> x y; rewrite H_inc_set0. Qed.

Lemma subgraph_connected_Gd : subgraph_connected (G:=Gd) [set: edge Gd].
Proof.
move=> x y _ _; case: x => -[]; case: y => -[].
- by exists [::].
- by exists [:: Some None]; rewrite /walk_in /= !inE.
- by exists [:: None]; rewrite /walk_in /= !inE.
- by exists [::].
Qed.

(** ** [is_circuit] : witness (digon) + identity *)

Lemma is_circuit_neq0 (G : mgraph) (C : {set edge G}) :
  is_circuit C -> C != set0.
Proof. by case. Qed.

Lemma is_circuit_Gd : is_circuit (G:=Gd) [set: edge Gd].
Proof.
split.
- by rewrite -card_gt0 cardsT card_edge_Gd.
- exact: subgraph_kregular_Gd.
- exact: subgraph_connected_Gd.
Qed.

(** ** [acyclic] : witness + identity *)

Lemma acyclic_set0 (G : mgraph) : acyclic (@set0 (edge G)).
Proof.
move=> C; rewrite subset0 => /eqP ->.
by case=> Hne _ _; move: Hne; rewrite eqxx.
Qed.

(** ** [is_path] : identity (no cheap nonempty witness, directed walks) *)

Lemma is_path_neq0 (G : mgraph) (P : {set edge G}) : is_path P -> P != set0.
Proof. by case. Qed.

(** ** [is_matching] : witness + identity *)

Lemma is_matching_set0 (G : mgraph) : is_matching (@set0 (edge G)).
Proof. by move=> v; rewrite subdeg_set0. Qed.

(** ** [spanning_connected] / [spanning_tree] : witness *)

Lemma spanning_tree_unit : spanning_tree (G:=U) set0.
Proof.
split.
- by move=> x y; exists [::]; split; [case: x; case: y|].
- exact: acyclic_set0.
Qed.

(** ** [is_bridge] / [bridgeless] : witness *)

Lemma bridgeless_unit : bridgeless (U).
Proof. by case. Qed.

(** ** [cubic] : witness + identities *)

Lemma cubic_loopless (G : mgraph) : cubic G -> loopless G.
Proof. by case. Qed.

Lemma cubic_mdeg (G : mgraph) : cubic G -> forall v : G, mdeg v = 3.
Proof. by case. Qed.

(** Witness: two vertices joined by three parallel non-loop edges are cubic
    ([loopless_G3p] is proved with the other degree lemmas above). *)
Lemma cubic_G3p : cubic G3p.
Proof. by split; [exact: loopless_G3p | exact: mdeg_G3p]. Qed.

(** ** [simple_mgraph] : witness *)

Lemma edges_at_unit (v : U) : edges_at v = set0.
Proof. by apply/setP => -[]. Qed.

Lemma simple_mgraph_unit : simple_mgraph (U).
Proof.
split; first by case.
have e0 : forall u v : U, edges u v = set0 by move=> u v; apply/setP => -[].
by move=> x y; rewrite !e0 cards0.
Qed.

(** ** [eulerian] : witness + identity *)

Lemma edgeT_unit : [set: edge U] = set0.
Proof. by apply/setP => -[]. Qed.

Lemma mdeg_unit (v : U) : mdeg v = 0.
Proof. by rewrite /mdeg edgeT_unit subdeg0. Qed.

Lemma eulerian_unit : eulerian (U).
Proof. by split; [exact: mconnected_unit | move=> v; rewrite mdeg_unit]. Qed.

Lemma eulerian_mconnected (G : mgraph) : eulerian G -> mconnected G.
Proof. by case. Qed.

Lemma eulerian_Gd : eulerian Gd.
Proof.
split.
- by move=> x y; case: x => -[]; case: y => -[];
    [exists [::]|exists [:: Some None]|exists [:: None]|exists [::]].
- by move=> v; rewrite mdeg_Gd.
Qed.

(** ** [is_eulerian_tour] : witness *)

Lemma eulerian_tour_unit : is_eulerian_tour (G:=U) [::].
Proof. by split; [exists tt | case]. Qed.

(** ** [edge_partitionT] / [edge_partition_of] : witnesses + identities *)

Lemma edge_partitionT_Gd : edge_partitionT (G:=Gd) [:: [set: edge Gd]].
Proof. by move=> e; rewrite /= in_setT. Qed.

Lemma edge_partition_of_Gd :
  edge_partition_of (G:=Gd) [set: edge Gd] [:: [set: edge Gd]].
Proof. by move=> e; rewrite /= !in_setT. Qed.

Lemma edge_partition_of_unit :
  edge_partition_of (G:=U) set0 [::].
Proof. by case. Qed.

(** ** [cycle_decomposition_of] / [cycle_decomposition] / [path_decomposition] *)

Lemma cycle_decomposition_Gd : cycle_decomposition (G:=Gd) [:: [set: edge Gd]].
Proof.
split; last exact: edge_partitionT_Gd.
by move=> C; rewrite inE => /eqP ->; exact: is_circuit_Gd.
Qed.

Lemma cycle_decomposition_unit : cycle_decomposition (G:=U) [::].
Proof. by split; [move=> C | case]. Qed.

Lemma cycle_decomposition_of_Gd :
  cycle_decomposition_of (G:=Gd) [set: edge Gd] [:: [set: edge Gd]].
Proof.
split; last exact: edge_partition_of_Gd.
by move=> C; rewrite inE => /eqP ->; exact: is_circuit_Gd.
Qed.

Lemma path_decomposition_unit : path_decomposition (G:=U) [::].
Proof. by split; [move=> C | case]. Qed.

(** ** [cdc] : witness (digon double cover) + identity *)

Lemma cdc_Gd : cdc (G:=Gd) [:: [set: edge Gd]; [set: edge Gd]].
Proof.
split.
- by move=> C; rewrite !inE => /orP[] /eqP ->; exact: is_circuit_Gd.
- by move=> e; rewrite /= !in_setT.
Qed.

Lemma cdc_unit : cdc (G:=U) [::].
Proof. by split; [move=> C | case]. Qed.

(** ** A LOOP has degree 2: the one-vertex loop graph [Gloop]

    The degree layer of [Cycle.foundations.connectivity] counts ARC ENDS, so a
    loop contributes 2 -- the textbook convention, and the one that makes a
    single loop a circuit of length 1 and an element of the cycle space.  These
    lemmas pin that down.  (Before the degree repair of 2026-09-23, [mdeg] and
    [subdeg] counted INCIDENT EDGES, so a loop had degree 1: the single-loop
    edge set was neither an [even_subgraph] nor an [is_circuit], which made
    [cycle_double_cover_statement] and
    [X212.orientable_five_cycle_double_cover_statement] axiom-free refutable on
    this very graph -- see meta/probe_hints/cycle_double_cover_statement.v and
    meta/probe_hints/orientable_five_cycle_double_cover_statement.v, both of
    which must now FAIL to compile.) *)

Definition Gloop : mgraph := mgraph.add_edge U tt tt tt.

Lemma card_edge_Gloop : #|edge Gloop| = 1.
Proof. by rewrite /Gloop /U card_option card_void. Qed.

Lemma edge_Gloop_eq (e : edge Gloop) : e = None.
Proof. by case: e => [[]|]. Qed.

Lemma src_Gloop (e : edge Gloop) : source e = tt.
Proof. by case: (source e). Qed.

Lemma tgt_Gloop (e : edge Gloop) : target e = tt.
Proof. by case: (target e). Qed.

Lemma edgeT_Gloop : [set: edge Gloop] = [set (None : edge Gloop)].
Proof. by apply/setP => e; rewrite !inE [e]edge_Gloop_eq eqxx. Qed.

(** THE POINT: the vertex carrying one loop has degree 2, not 1. *)
Lemma subdeg_Gloop (v : Gloop) : subdeg [set: edge Gloop] v = 2.
Proof.
rewrite edgeT_Gloop; apply: subdeg_loop;
  by [rewrite src_Gloop; case: v | rewrite tgt_Gloop; case: v].
Qed.

Lemma mdeg_Gloop (v : Gloop) : mdeg v = 2.
Proof. exact: subdeg_Gloop. Qed.

(** ... hence the single loop IS an even subgraph, a 2-regular subgraph and a
    circuit, as the classical conventions require. *)
Lemma even_subgraph_Gloop : even_subgraph (G := Gloop) [set: edge Gloop].
Proof. by move=> v; rewrite subdeg_Gloop. Qed.

Lemma subgraph_kregular_Gloop :
  subgraph_kregular (G := Gloop) [set: edge Gloop] 2.
Proof. by move=> v; right; exact: subdeg_Gloop. Qed.

Lemma subgraph_connected_Gloop :
  subgraph_connected (G := Gloop) [set: edge Gloop].
Proof. by move=> x y _ _; exists [::]; rewrite /walk_in /=; case: x; case: y. Qed.

Lemma is_circuit_Gloop : is_circuit (G := Gloop) [set: edge Gloop].
Proof.
split.
- by rewrite -card_gt0 cardsT card_edge_Gloop.
- exact: subgraph_kregular_Gloop.
- exact: subgraph_connected_Gloop.
Qed.

Lemma two_factor_Gloop : two_factor (G := Gloop) [set: edge Gloop].
Proof. by move=> v; exact: subdeg_Gloop. Qed.

(** ... and a loop is never a cut edge, so the loop graph is 2-edge-connected
    and DOES carry a cycle double cover -- the conclusion the old degree layer
    made unsatisfiable. *)
Lemma mconnected_Gloop : mconnected Gloop.
Proof. by move=> [] []; exists [::]. Qed.

Lemma bridgeless_Gloop : bridgeless Gloop.
Proof. by move=> e; apply: loop_not_bridge; rewrite src_Gloop tgt_Gloop. Qed.

Lemma two_edge_connected_Gloop : two_edge_connected Gloop.
Proof. by split; [exact: mconnected_Gloop | exact: bridgeless_Gloop]. Qed.

Lemma cdc_Gloop : cdc (G := Gloop) [:: [set: edge Gloop]; [set: edge Gloop]].
Proof.
split.
- by move=> C; rewrite !inE => /orP[] /eqP ->; exact: is_circuit_Gloop.
- by move=> e; rewrite /= !in_setT.
Qed.

(** TEETH on the other side: a loop cannot sit in a matching (its end count is
    2), which is also the textbook convention. *)
Lemma not_matching_Gloop : ~ is_matching (G := Gloop) [set: edge Gloop].
Proof. by move=> /(_ tt); rewrite subdeg_Gloop. Qed.

(** ** The FOURTH victim of the old loop convention: one vertex, TWO loops

    [decomposing_eulerian_graphs_statement] is guarded by [edge_connected G 6]
    and [eulerian G] only -- no looplessness -- so the one-vertex two-loop
    multigraph [G2loop] is in its hypothesis class.  While a LOOP had degree 1,
    neither single loop was an [is_circuit], so the only cycle decomposition was
    [:: [set lp1; lp2] ], whose trace at the vertex IS the transition
    [ [set lp1; lp2] ]: the row was refutable there.  With the repaired degree
    (a loop contributes 2) each loop is a circuit of length 1 and
    [:: [set lp1]; [set lp2] ] is a COMPATIBLE decomposition.  The lemmas below
    pin the whole instance down, hypotheses and conclusion. *)

Definition G2loop : mgraph := mgraph.add_edge Gloop tt tt tt.

Definition lp1 : edge G2loop := Some None.
Definition lp2 : edge G2loop := None.

Lemma card_edge_G2loop : #|edge G2loop| = 2.
Proof. by rewrite /G2loop /Gloop /U !card_option card_void. Qed.

Lemma src_G2loop (e : edge G2loop) : source e = tt.
Proof. by case: (source e). Qed.

Lemma tgt_G2loop (e : edge G2loop) : target e = tt.
Proof. by case: (target e). Qed.

Lemma edgeT_G2loop : [set: edge G2loop] = [set lp1; lp2].
Proof. by apply/setP => e; rewrite !inE /lp1 /lp2; case: e => [[[]|]|]. Qed.

Lemma ends_at_G2loop (b : bool) (v : G2loop) :
  ends_at [set: edge G2loop] b v = [set: edge G2loop].
Proof.
apply/setP => e; rewrite !inE.
by case: v; case: b; [rewrite tgt_G2loop | rewrite src_G2loop].
Qed.

(** THE POINT: the vertex carrying two loops has degree 4, not 2. *)
Lemma mdeg_G2loop (v : G2loop) : mdeg v = 4.
Proof. by rewrite /mdeg /subdeg !ends_at_G2loop cardsT card_edge_G2loop. Qed.

Lemma mconnected_G2loop : mconnected G2loop.
Proof. by move=> [] []; exists [::]. Qed.

Lemma eulerian_G2loop : eulerian G2loop.
Proof. by split; [exact: mconnected_G2loop | move=> v; rewrite mdeg_G2loop]. Qed.

(** One vertex: deleting ANY edge set leaves it connected. *)
Lemma edge_connected_G2loop (k : nat) : edge_connected G2loop k.
Proof. by move=> E _ [] []; exists [::]. Qed.

Lemma edges_at_G2loop (v : G2loop) : edges_at v = [set: edge G2loop].
Proof.
by apply/setP => e; rewrite !inE incidentE src_G2loop; case: v; rewrite eqxx.
Qed.

(** The 2-transition system pairing the two loops. *)
Definition Ptwo (v : G2loop) : {set {set edge G2loop}} := [set [set lp1; lp2]].

Lemma lp12_neq : lp1 != lp2.
Proof. by []. Qed.

Lemma transition2_G2loop : transition2_system Ptwo.
Proof.
split.
- move=> v; rewrite edges_at_G2loop edgeT_G2loop /Ptwo; apply/and3P; split.
  + by rewrite /cover big_set1 eqxx.
  + exact: trivIset1.
  + by rewrite inE eq_sym; apply/negP => /eqP/setP/(_ lp1); rewrite !inE eqxx.
- by move=> v T; rewrite /Ptwo inE => /eqP ->; rewrite cards2 lp12_neq.
Qed.

(** Each loop IS a circuit of length 1 (this is what the repair bought). *)
Lemma is_circuit_loop_G2loop (e : edge G2loop) : is_circuit [set e].
Proof.
split.
- by apply/set0Pn; exists e; rewrite inE.
- by move=> v; right; apply: subdeg_loop;
     [rewrite src_G2loop | rewrite tgt_G2loop]; case: v.
- by move=> x y _ _; exists [::]; rewrite /walk_in /=; case: x; case: y.
Qed.

Lemma cycle_decomposition_G2loop :
  cycle_decomposition (G := G2loop) [:: [set lp1]; [set lp2]].
Proof.
split.
- by move=> C; rewrite !inE => /orP[] /eqP ->; exact: is_circuit_loop_G2loop.
- by move=> e; rewrite /= !inE /lp1 /lp2; case: e => [[[]|]|].
Qed.

(** ... and splitting the two loops apart is COMPATIBLE with [Ptwo]: each
    circuit's trace at the vertex is a singleton, never the two-element
    transition. *)
Lemma compatible_decomposition_G2loop :
  compatible_decomposition Ptwo [:: [set lp1]; [set lp2]].
Proof.
have hcard (e : edge G2loop) : [set e] != [set lp1; lp2].
  apply/negP => /eqP /(congr1 (fun S : {set edge G2loop} => #|S|)).
  by rewrite cards1 cards2 lp12_neq.
split; first exact: cycle_decomposition_G2loop.
by move=> C; rewrite !inE => /orP[] /eqP -> v;
   rewrite edges_at_G2loop setTI /Ptwo inE; apply: hcard.
Qed.

Lemma card_G2loop : #|G2loop| = 1.
Proof. by rewrite card_unit. Qed.

(** The full INSTANCE of [U6.decomposing_eulerian_graphs_statement] on the
    two-loop carrier: all five hypotheses, and the conclusion exhibited. *)
Lemma u6_decomposing_eulerian_G2loop :
  [/\ (0 < #|G2loop|)%N, (0 < #|edge G2loop|)%N, edge_connected G2loop 6,
      eulerian G2loop & transition2_system Ptwo]
  /\ exists D : seq {set edge G2loop}, compatible_decomposition Ptwo D.
Proof.
split; last first.
  by exists [:: [set lp1]; [set lp2]]; exact: compatible_decomposition_G2loop.
split.
- by rewrite card_G2loop.
- by rewrite card_edge_G2loop.
- exact: edge_connected_G2loop.
- exact: eulerian_G2loop.
- exact: transition2_G2loop.
Qed.

(** ** [faithful_cover] : witness + identity (cdc is a faithful cover for [p=2]) *)

Lemma faithful_cover_Gd : faithful_cover (G:=Gd) (fun _ => 1) [:: [set: edge Gd]].
Proof.
split.
- by move=> C; rewrite inE => /eqP ->; exact: is_circuit_Gd.
- by move=> e; rewrite /= in_setT.
Qed.

Lemma cdc_faithful (G : mgraph) (L : seq {set edge G}) :
  cdc L -> faithful_cover (fun _ => 2) L.
Proof. by case=> ? H; split=> // e; exact: H. Qed.

(** ** [cut] : identities *)

Lemma cut_set0 (G : mgraph) : cut (@set0 G) = set0.
Proof. by apply/setP => e; rewrite !inE. Qed.

Lemma cut_setT (G : mgraph) : cut [set: G] = set0.
Proof. by apply/setP => e; rewrite !inE. Qed.

(** ** [admissible] : witness (the zero weighting) *)

Lemma admissible0 (G : mgraph) : admissible (G:=G) (fun _ => 0).
Proof.
move=> S e _; split; first by rewrite muln0.
by rewrite big1.
Qed.

(** ** [transition2_system] : witness (the digon's unique transition) *)

Lemma transition2_Gd :
  transition2_system (G:=Gd) (fun _ => [set [set: edge Gd]]).
Proof.
split.
- move=> v; rewrite edges_at_Gd; apply/and3P; split.
  + by rewrite /cover big_set1 eqxx.
  + exact: trivIset1.
  + by rewrite inE eq_sym -card_gt0 cardsT card_edge_Gd.
- by move=> v T; rewrite inE => /eqP ->; rewrite cardsT card_edge_Gd.
Qed.

(** ** [compatible_decomposition] : witness (vacuous, single vertex) *)

Lemma compatible_decomposition_unit :
  compatible_decomposition (G:=U) (fun _ => set0) [::].
Proof. by split; [exact: cycle_decomposition_unit | move=> C]. Qed.

(** ** [cyc_pairs] / [two_consecutive] : identities *)

Lemma cyc_pairs_nil (G : mgraph) : cyc_pairs (G:=G) [::] = [::].
Proof. by []. Qed.

Lemma two_consecutive_set0 (G : mgraph) (w : seq (edge G)) :
  two_consecutive w set0 = false.
Proof. by apply: negbTE; apply/hasPn => p _; rewrite in_set0. Qed.

(** ** [oddness_le] : witness (void graph, oddness 0) *)

Lemma oddness_le_void : oddness_le (V) 0.
Proof.
exists set0, [::]; split.
- by case.
- by split; [move=> C | case].
- by [].
Qed.

(** ** Axiom audit for the degree-convention witnesses ******************** *)

Print Assumptions subdeg_Gloop.
Print Assumptions mdeg_Gloop.
Print Assumptions even_subgraph_Gloop.
Print Assumptions is_circuit_Gloop.
Print Assumptions two_factor_Gloop.
Print Assumptions bridgeless_Gloop.
Print Assumptions two_edge_connected_Gloop.
Print Assumptions cdc_Gloop.
Print Assumptions not_matching_Gloop.
Print Assumptions mdeg_G2loop.
Print Assumptions is_circuit_loop_G2loop.
Print Assumptions transition2_G2loop.
Print Assumptions compatible_decomposition_G2loop.
Print Assumptions u6_decomposing_eulerian_G2loop.
