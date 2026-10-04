(** A25 simple line graphs (chromatic): X43's line graph on the edges of a simple graph -- the vertex subtype, the
    relation, its two constructor proofs, the graph and the strong edge colouring of its square -- with the complete
    row, frozen at the A24 baseline 897a7d3, and the complete pre-M1+A1 row at 061154c.  Baseline, hashes and exact
    substitutions are recorded in meta/migration_reports/simple_line_graphs.spec.json.
    - [X43Legacy] (897a7d3): the carrier [{e : {set G} | e \in x43_edge_set G}], the relation
      [(val e != val f) && (val e :&: val f != set0)], the two constructor proofs with their scripts, the graph, the
      strong edge colouring (chi of the square of the line graph at most k) and the row (cubic, no induced diamond,
      no induced claw).
    - [X43Original] (061154c): the same chain on M1's frozen raw comprehension [exists_edge_set], and the row over
      A1's frozen raw [x43_induced_free]; M1's and A1's certificate modules are aliased, not imported.
    The frozen carrier and relation are convertible to GTBase.simple_line_graphs's; the frozen graph differs from
    [simple_line_graph] only in its opaque proof fields, so the two are related by pointwise adjacency and the
    identity isomorphism, and the chromatic numbers of their squares by [chi_graph_power_diso].  The raw carrier is
    another subtype of the same set (M1's [x43_edge_set_compat]): [val] maps the two subtypes onto each other and
    gives the isomorphism. *)
From GraphTheory Require Import bij.
From GTBase Require Import base simple_line_graphs.
From Chromatic.conjectures Require Import X43.
From Chromatic.migration Require simple_edges induced_free.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** M1's and A1's certificate modules, aliased without Import (A1's module names coincide with this file's). *)
Module M1 := Chromatic.migration.simple_edges.
Module A1 := Chromatic.migration.induced_free.

Module X43Legacy.

Definition x43_line_vertex (G : sgraph) : Type :=
  {e : {set G} | e \in x43_edge_set G}.

Definition x43_line_rel (G : sgraph) : rel (X43Legacy.x43_line_vertex G) :=
  fun e f => (val e != val f) && (val e :&: val f != set0).

Lemma x43_line_rel_sym (G : sgraph) : symmetric (@X43Legacy.x43_line_rel G).
Proof. by move=> e f; rewrite /X43Legacy.x43_line_rel eq_sym setIC. Qed.

Lemma x43_line_rel_irrefl (G : sgraph) : irreflexive (@X43Legacy.x43_line_rel G).
Proof. by move=> e; rewrite /X43Legacy.x43_line_rel eqxx. Qed.

Definition x43_line_graph (G : sgraph) : sgraph :=
  SGraph (@X43Legacy.x43_line_rel_sym G) (@X43Legacy.x43_line_rel_irrefl G).

Definition x43_strong_edge_colourable (G : sgraph) (k : nat) : Prop :=
  χ([set: graph_power (X43Legacy.x43_line_graph G) 2]) <= k.

Definition diamond_free_claw_free_cubic_strong_six_edge_colourable_statement : Prop :=
  forall G : sgraph,
    regular G 3 ->
    x43_induced_free G x43_diamond ->
    x43_induced_free G x43_claw ->
    X43Legacy.x43_strong_edge_colourable G 6.

End X43Legacy.

Module X43Original.

Definition x43_line_vertex (G : sgraph) : Type :=
  {e : {set G} | e \in M1.Legacy.exists_edge_set G}.

Definition x43_line_rel (G : sgraph) : rel (X43Original.x43_line_vertex G) :=
  fun e f => (val e != val f) && (val e :&: val f != set0).

Lemma x43_line_rel_sym (G : sgraph) : symmetric (@X43Original.x43_line_rel G).
Proof. by move=> e f; rewrite /X43Original.x43_line_rel eq_sym setIC. Qed.

Lemma x43_line_rel_irrefl (G : sgraph) : irreflexive (@X43Original.x43_line_rel G).
Proof. by move=> e; rewrite /X43Original.x43_line_rel eqxx. Qed.

Definition x43_line_graph (G : sgraph) : sgraph :=
  SGraph (@X43Original.x43_line_rel_sym G) (@X43Original.x43_line_rel_irrefl G).

Definition x43_strong_edge_colourable (G : sgraph) (k : nat) : Prop :=
  χ([set: graph_power (X43Original.x43_line_graph G) 2]) <= k.

Definition diamond_free_claw_free_cubic_strong_six_edge_colourable_statement : Prop :=
  forall G : sgraph,
    regular G 3 ->
    A1.Legacy.x43_induced_free G x43_diamond ->
    A1.Legacy.x43_induced_free G x43_claw ->
    X43Original.x43_strong_edge_colourable G 6.

End X43Original.

(** The current chain: the carrier and the relation are the public ones by conversion; the constructor proofs and the
    graphs are related by the identity isomorphism, never by an equation between proof fields. *)
Lemma x43_line_vertex_compat (G : sgraph) :
  X43Legacy.x43_line_vertex G = Chromatic.conjectures.X43.x43_line_vertex G.
Proof.
by [].
Qed.

Lemma x43_line_rel_compat (G : sgraph) (e f : X43Legacy.x43_line_vertex G) :
  @X43Legacy.x43_line_rel G e f = @Chromatic.conjectures.X43.x43_line_rel G e f.
Proof.
by [].
Qed.

Lemma x43_line_rel_proofs_compat (G : sgraph) :
  SGraph (@X43Legacy.x43_line_rel_sym G) (@X43Legacy.x43_line_rel_irrefl G) ≃
  SGraph (@Chromatic.conjectures.X43.x43_line_rel_sym G) (@Chromatic.conjectures.X43.x43_line_rel_irrefl G).
Proof. by apply: eq_diso => e f. Qed.

Lemma x43_line_graph_compat (G : sgraph) :
  @edge_rel (X43Legacy.x43_line_graph G) =2 @edge_rel (Chromatic.conjectures.X43.x43_line_graph G).
Proof.
by [].
Qed.

Lemma x43_line_graph_diso (G : sgraph) : X43Legacy.x43_line_graph G ≃ Chromatic.conjectures.X43.x43_line_graph G.
Proof. by rewrite /X43Legacy.x43_line_graph /Chromatic.conjectures.X43.x43_line_graph /simple_line_graph; apply: eq_diso => e f. Qed.

(** The squares of isomorphic graphs have the same chromatic number. *)
Lemma x43_strong_edge_colourable_compat (G : sgraph) (k : nat) :
  X43Legacy.x43_strong_edge_colourable G k <-> Chromatic.conjectures.X43.x43_strong_edge_colourable G k.
Proof.
by rewrite /X43Legacy.x43_strong_edge_colourable /Chromatic.conjectures.X43.x43_strong_edge_colourable
  (chi_graph_power_diso 2 (x43_line_graph_diso G)).
Qed.

Lemma diamond_free_claw_free_cubic_strong_six_edge_colourable_statement_compat :
  X43Legacy.diamond_free_claw_free_cubic_strong_six_edge_colourable_statement <->
  Chromatic.conjectures.X43.diamond_free_claw_free_cubic_strong_six_edge_colourable_statement.
Proof. by split=> st G reg diamond claw; apply/x43_strong_edge_colourable_compat; apply: st. Qed.

(** The pre-M1 carrier: the raw comprehension and [E(G)] are the same set (M1), so [val] maps the two subtypes onto
    each other, and the line relations, which only read [val], agree. *)
Section RawCarrier.
Variable G : sgraph.

Lemma raw_edge_in (e : {set G}) : e \in M1.Legacy.exists_edge_set G -> e \in E(G).
Proof. by rewrite M1.x43_edge_set_compat /x43_edge_set. Qed.

Lemma raw_edge_out (e : {set G}) : e \in E(G) -> e \in M1.Legacy.exists_edge_set G.
Proof. by rewrite M1.x43_edge_set_compat /x43_edge_set. Qed.

Definition x43_raw_line_map (a : X43Original.x43_line_graph G) : Chromatic.conjectures.X43.x43_line_graph G :=
  Sub (val a) (raw_edge_in (valP a)).

Definition x43_raw_line_unmap (a : Chromatic.conjectures.X43.x43_line_graph G) : X43Original.x43_line_graph G :=
  Sub (val a) (raw_edge_out (valP a)).

Lemma x43_raw_line_mapK : cancel x43_raw_line_map x43_raw_line_unmap.
Proof. by move=> a; apply: val_inj. Qed.

Lemma x43_raw_line_unmapK : cancel x43_raw_line_unmap x43_raw_line_map.
Proof. by move=> a; apply: val_inj. Qed.

Lemma x43_raw_line_map_mono : {mono x43_raw_line_map : a b / a -- b}.
Proof. by []. Qed.

End RawCarrier.

Lemma x43_line_graph_original_diso (G : sgraph) : X43Original.x43_line_graph G ≃ Chromatic.conjectures.X43.x43_line_graph G.
Proof. exact: Diso' (@x43_raw_line_mapK G) (@x43_raw_line_unmapK G) (@x43_raw_line_map_mono G). Qed.

Lemma x43_line_vertex_original_compat (G : sgraph) :
  X43Original.x43_line_vertex G = Chromatic.conjectures.X43.x43_line_vertex G.
Proof.
by rewrite /X43Original.x43_line_vertex M1.x43_edge_set_compat.
Qed.

Lemma x43_line_rel_original_compat (G : sgraph) (e f : X43Original.x43_line_vertex G) :
  @X43Original.x43_line_rel G e f = @Chromatic.conjectures.X43.x43_line_rel G (x43_raw_line_map e) (x43_raw_line_map f).
Proof.
by [].
Qed.

Lemma x43_line_rel_proofs_original_compat (G : sgraph) :
  SGraph (@X43Original.x43_line_rel_sym G) (@X43Original.x43_line_rel_irrefl G) ≃
  SGraph (@Chromatic.conjectures.X43.x43_line_rel_sym G) (@Chromatic.conjectures.X43.x43_line_rel_irrefl G).
Proof.
apply: diso_comp (x43_line_graph_original_diso G) _.
by rewrite /Chromatic.conjectures.X43.x43_line_graph /simple_line_graph; apply: eq_diso => e f.
Qed.

Lemma x43_strong_edge_colourable_original_compat (G : sgraph) (k : nat) :
  X43Original.x43_strong_edge_colourable G k <-> Chromatic.conjectures.X43.x43_strong_edge_colourable G k.
Proof.
by rewrite /X43Original.x43_strong_edge_colourable /Chromatic.conjectures.X43.x43_strong_edge_colourable
  (chi_graph_power_diso 2 (x43_line_graph_original_diso G)).
Qed.

(** The complete pre-M1+A1 row: the raw guards are A1's, the square's chromatic number moves along the raw-carrier
    isomorphism. *)
Lemma diamond_free_claw_free_cubic_strong_six_edge_colourable_statement_original_compat :
  X43Original.diamond_free_claw_free_cubic_strong_six_edge_colourable_statement <->
  Chromatic.conjectures.X43.diamond_free_claw_free_cubic_strong_six_edge_colourable_statement.
Proof.
split=> st G reg diamond claw; apply/x43_strong_edge_colourable_original_compat; apply: st reg _ _;
  by apply/A1.x43_induced_free_compat.
Qed.
