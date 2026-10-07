(** A25 simple line graphs (minor): containment's verbatim copy of U11's Section [SLine] -- relation, two constructor
    proofs and graph -- frozen at the A24 baseline 897a7d3 with X220's two complete rows over it.  Baseline, hashes and
    exact substitutions are recorded in meta/migration_reports/simple_line_graphs.spec.json.
    - [Legacy], [ProofsLegacy], [GraphLegacy]: the Section in dependency order, each in a verbatim copy of its
      scaffolding [Variable G : sgraph]; references to earlier frozen names are module-qualified.
    - [X220Legacy]: the bounded-degree wall or line-wall row ([forall d, exists f, forall k G], the full induced
      disjunction) and the four-family logarithmic-treewidth row ([forall t, exists c, forall G], the clique and
      biclique exclusions, both quantified subdivision exclusions, [c * (trunc_log 2 #|G|).+1]).
    - [X220Original] (A25 + C19 composition): the same complete four-family row over BOTH frozen raw chains, C19's
      subdivision support [MS.Legacy.is_subdivision_of] (raw row baseline bb0bf3c; the provider is aliased, not
      imported, and not recreated) and this file's frozen line graph.  A25's [X220Legacy] row (live subdivision
      support) and C19's own X220Legacy row (live line graph) stay unchanged as partial snapshots.
    The frozen relation is convertible to GTBase.simple_line_graphs's; the frozen graph differs from
    [simple_line_graph] only in its opaque proof fields, so the two are related by the identity isomorphism, which
    moves induced copies both ways. *)
From GTBase Require Import base graph_classes simple_line_graphs.
From GraphTheory Require Import minor.
From Minor.foundations Require Import containment width_params.
From Minor.conjectures Require Import X27 X42 X220.
From Minor.migration Require model_support.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module MS := Minor.migration.model_support.

Module Legacy.

Section SLine.
Variable G : sgraph.
Definition sline_rel : rel {e : {set G} | e \in E(G)} :=
  fun e1 e2 => (val e1 != val e2) && (val e1 :&: val e2 != set0).
End SLine.

End Legacy.

Module ProofsLegacy.

Section SLine.
Variable G : sgraph.
Lemma sline_sym : symmetric (@Legacy.sline_rel G).
Proof. by move=> e1 e2; rewrite /Legacy.sline_rel eq_sym setIC. Qed.
Lemma sline_irrefl : irreflexive (@Legacy.sline_rel G).
Proof. by move=> e; rewrite /Legacy.sline_rel eqxx. Qed.
End SLine.

End ProofsLegacy.

Module GraphLegacy.

Section SLine.
Variable G : sgraph.
Definition sline_graph : sgraph := SGraph (@ProofsLegacy.sline_sym G) (@ProofsLegacy.sline_irrefl G).
End SLine.

End GraphLegacy.

Module X220Legacy.

Definition bounded_degree_induced_wall_or_line_wall_statement : Prop :=
  forall d : nat, exists f : nat -> nat,
    forall (k : nat) (G : sgraph),
      Delta G <= d -> tw_ge G (f k) ->
      has_induced_copy G (x220_wall k) \/
      has_induced_copy G (GraphLegacy.sline_graph (x220_wall k)).

Definition four_family_free_logarithmic_treewidth_statement : Prop :=
  forall t : nat, exists c : nat,
    forall G : sgraph,
      ~ has_induced_copy G 'K_t ->
      ~ has_induced_copy G (KB t t) ->
      (forall W : sgraph, is_subdivision_of W (x220_wall t) -> ~ has_induced_copy G W) ->
      (forall W : sgraph, is_subdivision_of W (x220_wall t) ->
         ~ has_induced_copy G (GraphLegacy.sline_graph W)) ->
      tw_le G (c * (trunc_log 2 #|G|).+1).

End X220Legacy.

Module X220Original.

Definition four_family_free_logarithmic_treewidth_statement : Prop :=
  forall t : nat, exists c : nat,
    forall G : sgraph,
      ~ has_induced_copy G 'K_t ->
      ~ has_induced_copy G (KB t t) ->
      (forall W : sgraph, MS.Legacy.is_subdivision_of W (x220_wall t) -> ~ has_induced_copy G W) ->
      (forall W : sgraph, MS.Legacy.is_subdivision_of W (x220_wall t) ->
         ~ has_induced_copy G (GraphLegacy.sline_graph W)) ->
      tw_le G (c * (trunc_log 2 #|G|).+1).

End X220Original.

(** The Section: the relation is the public one by conversion; the constructor proofs and the graphs are related by
    the identity isomorphism, never by an equation between proof fields. *)
Lemma sline_rel_compat (G : sgraph) (e f : {e : {set G} | e \in E(G)}) :
  @Legacy.sline_rel G e f = @Minor.foundations.containment.sline_rel G e f.
Proof.
by [].
Qed.

Lemma sline_proofs_compat (G : sgraph) :
  SGraph (@ProofsLegacy.sline_sym G) (@ProofsLegacy.sline_irrefl G) ≃ SGraph (@Minor.foundations.containment.sline_sym G) (@Minor.foundations.containment.sline_irrefl G).
Proof. by apply: eq_diso => e f. Qed.

Lemma sline_graph_compat (G : sgraph) :
  @edge_rel (GraphLegacy.sline_graph G) =2 @edge_rel (Minor.foundations.containment.sline_graph G).
Proof.
by [].
Qed.

Lemma sline_graph_diso (G : sgraph) : GraphLegacy.sline_graph G ≃ Minor.foundations.containment.sline_graph G.
Proof. by rewrite /GraphLegacy.sline_graph /Minor.foundations.containment.sline_graph /simple_line_graph; apply: eq_diso => e f. Qed.

(** An induced copy of one line graph is an induced copy of the other. *)
Lemma has_induced_copy_sline_compat (G W : sgraph) :
  has_induced_copy G (GraphLegacy.sline_graph W) <-> has_induced_copy G (Minor.foundations.containment.sline_graph W).
Proof.
split=> -[i]; constructor.
- exact: isubgraph_comp (iso_isubgraph (diso_sym (sline_graph_diso W))) i.
- exact: isubgraph_comp (iso_isubgraph (sline_graph_diso W)) i.
Qed.

Lemma bounded_degree_induced_wall_or_line_wall_statement_compat :
  X220Legacy.bounded_degree_induced_wall_or_line_wall_statement <->
  Minor.conjectures.X220.bounded_degree_induced_wall_or_line_wall_statement.
Proof.
split=> st d; have [f Hf] := st d; exists f => k G dG twG;
  by case: (Hf k G dG twG) => [h|/has_induced_copy_sline_compat h]; [left|right].
Qed.

Lemma four_family_free_logarithmic_treewidth_statement_compat :
  X220Legacy.four_family_free_logarithmic_treewidth_statement <->
  Minor.conjectures.X220.four_family_free_logarithmic_treewidth_statement.
Proof.
split=> st t; have [c Hc] := st t; exists c => G nK nKB nW nLW; apply: Hc nK nKB nW _ => W sW;
  by move/has_induced_copy_sline_compat; exact: nLW sW.
Qed.

(** A25 + C19: the complete Original.  C19's frozen subdivision chain converts to the live one (its certificates are
    [iff_refl]), so the Original is the A25 row up to conversion and A25's line-graph transport certifies it. *)
Lemma four_family_free_logarithmic_treewidth_statement_original_compat :
  X220Original.four_family_free_logarithmic_treewidth_statement <->
  Minor.conjectures.X220.four_family_free_logarithmic_treewidth_statement.
Proof. exact: four_family_free_logarithmic_treewidth_statement_compat. Qed.
