(** * Chromatic.conjectures.implications_X219 -- dependency-graph EDGES for wave X219.

    Machine-checked implication edges into / out of the X219 statements.  Every
    SCHEDULED edge is a RELATIVE theorem: a [Qed]-closed [Theorem A -> B] proved
    WITHOUT resolving either endpoint.  Axiom-free: no [Axiom] / [Parameter] /
    [Admitted] / [Conjecture].  Candidate edges record the exact obstruction.

    The [cite="gc:eNNN"] fields point at [meta/corpus_relations.json]; rebuild it
    with [meta/build_corpus_relations.py] after this wave's manifest
    regeneration so the new formal names reach the relation endpoints. *)

From GTBase Require Import base.
From Chromatic.foundations Require Import chi_bounding choice_number edge_colourings.
From Chromatic.conjectures Require Import U4 X32 X219 grounding_X219.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The 7/8 bound ==> the 5/6 bound ***********************************)

(*@EDGE from=triangle_free_planar_large_induced_two_degenerate_statement to=triangle_free_planar_five_sixths_two_degenerate_statement kind=implies status=verified proved=true proof=triangle_free_planar_large_induced_two_degenerate_implies_triangle_free_planar_five_sixths_two_degenerate cite="gc:e082" note="Corpus relation e082 (confirmed): identical hypothesis class (triangle-free planar) and identical conclusion type (an induced 2-degenerate subgraph on a prescribed fraction of the vertices), with a monotone parameter, 7/8 >= 5/6. The same vertex set S witnesses both bounds; the whole content is the cross-multiplied arithmetic 8|S| >= 7n implies 6|S| >= 5n." *)
Theorem triangle_free_planar_large_induced_two_degenerate_implies_triangle_free_planar_five_sixths_two_degenerate :
  triangle_free_planar_large_induced_two_degenerate_statement ->
  triangle_free_planar_five_sixths_two_degenerate_statement.
Proof.
move=> H G pl tf; have [S [Hcard Hdeg]] := H G pl tf.
by exists S; split => //; apply: x219_seven_eighths_implies_five_sixths.
Qed.

(** ** Candidate edges ****************************************************)

(*@EDGE from=toroidal_five_choosability_critical_iff_six_critical_statement to=toroidal_five_choosable_iff_five_colourable_statement kind=equiv status=candidate proved=false cite="gc:e027" note="Corpus relation e027 (confirmed equivalence; the paper itself states that Conjecture 2 and Conjecture 3 are equivalent). PARTIAL PROGRESS (2026-09-24): the free half is now a Qed-closed theorem in this file, [toroidal_five_choosable_iff_implies_critical_forward] -- Conjecture 3 yields the implication 'critical for 5-choosability ==> 6-critical' for every toroidal connected graph, because the non-choosability of G transfers through Conjecture 3 AT G ITSELF and the one-deletion half is free (chi <= ch always: Chromatic.foundations.chi_bounding.chi_le_choosable). Exactly ONE shape of ingredient is still missing, and it is needed for BOTH remaining halves: Conjecture 3 has to be applied to PROPER SUBGRAPHS of G, and NEITHER of its two hypotheses is known to survive a deletion. (a) [surface_embeddable 1] is not known to be subgraph-monotone -- GTBase base/theories/surface.v has no restriction lemma for rotation systems. The two missing lemmas are [surface_embeddable g G -> surface_embeddable g (del_edges [set u; v])] (same carrier, one edge removed) and [surface_embeddable g G -> forall v, surface_embeddable g (induced ([set: G] :\ v))]. Restricting the rotation permutation to the surviving darts (erot' d := erot^k d for the least k >= 1 with erot^k d surviving) is routine; the cost sits in the FACE COUNT, where one must prove that deleting one edge changes [#|porbits (surface_erot * surface_edge_perm)|] by exactly 0 or 1 and in the direction that keeps 2 + E - V - F from increasing (bridge: F unchanged, E drops, genus drops; non-bridge: the two incident faces merge, F and E both drop, genus unchanged). That is a genuine permutation-combinatorics development, estimated at 300+ lines, and was out of budget in this pass. (b) [connected [set: G]] is NOT inherited by one-deletions at all, so the subgraph application ALSO needs either 'a graph critical for a subgraph-monotone property has no cut vertex and no bridge' or '5-choosability of a graph follows from 5-choosability of each of its connected components' (plus toroidality of each component). (c) The direction Conjecture 2 ==> Conjecture 3 needs in addition CRITICAL-SUBGRAPH EXTRACTION ('a graph failing a subgraph-monotone property contains a subgraph that is critical for it', by minimal-counterexample induction over #|V| + #|E|) together with monotonicity of chi along that subgraph relation; the extraction first needs a UNIFORM subgraph relation, because [induced] and [del_edges] have different carriers (different vertex types), so the wrapper's two elementary deletions cannot be iterated as stated. None of (a)-(c) is about either conjecture, so the edge stays candidate." *)
Theorem toroidal_five_choosable_iff_implies_critical_forward :
  toroidal_five_choosable_iff_five_colourable_statement ->
  forall G : sgraph,
    surface_embeddable 1 G -> connected [set: G] ->
    x219_subgraph_critical_for (fun H : sgraph => choosable H 5) G ->
    x219_subgraph_critical_for (fun H : sgraph => χ([set: H]) <= 5) G.
Proof.
move=> B G emb con [nch hv he]; have [_ back] := B G emb con; split.
- by move=> chi5; apply: nch; exact: back chi5.
- by move=> v; apply: chi_le_choosable; exact: hv v.
by move=> u v uv; apply: chi_le_choosable; exact: he u v uv.
Qed.

(*@EDGE from=toroidal_five_choosable_iff_five_colourable_statement to=toroidal_edge_width_four_five_choosable_statement kind=implies status=candidate proved=false cite="gc:e123" note="Corpus relation e123 (confirmed; the paper introduces Conjecture 4 as a step towards Conjecture 3). BLOCKED TARGET: [toroidal_edge_width_four_five_choosable_statement] is this wave's blocked placeholder, in which edge-width at least four is replaced by GIRTH at least four because GTBase.surface has no contractibility predicate; proving the edge against the placeholder would certify a statement that is not the conjecture. Mathematically the step also needs that no 6-critical toroidal graph embeds with edge-width at least four, a case analysis over the four known 6-critical toroidal graphs, which is a theorem rather than a consequence of the source." *)

(* cross-package edge asymmetric_bipartite_list_colouring_statement -> list_chromatic_number_and_maximum_degree_of_bipartit_statement: annotation and proof now live in atlas/theories/conjectures/implications_A1.v or A2.v (wave A1, 2026-09-24) *)

(*@EDGE from=edge_list_coloring_statement to=list_chromatic_index_even_clique_statement kind=implies status=verified proved=true proof=edge_list_coloring_implies_list_chromatic_index_even_clique cite="gc:e039" note="Corpus relation e039 (confirmed): the List Colouring Conjecture restricted to cliques of even order is exactly the open half of this row. Proof, for n = N + 1 even (N odd): (1) K_n as a loopless multigraph is foundations/edge_colourings.kn_mgraph (one edge per strictly increasing pair, kn_loopless); (2) its line graph HAS a choice number ch (foundations/choice_number.choice_number_ex -- palette canonicalisation makes choosability a boolean, so ex_minn applies), and U4's statement gives ch = chi(L(K_n)); (3) chi(L(K_n)) <= N by the round-robin 1-factorisation (edge_colourings.kn_chi_line: colour {i,j} by (i+j) mod N and {i,N} by 2i mod N; 2 is invertible modulo odd N); hence the line graph is N-choosable (choosable_leqW); (4) a list colouring of the line graph's vertices is a symmetric proper list edge colouring of K_n from any symmetric list assignment (edge_colourings.kn_edge_choosable_of), which is x219_edge_choosable 'K_n (n-1). The edge resolves neither endpoint: the only colouring fact used, chi'(K_n) = n-1 for even n, is classical." *)
Theorem edge_list_coloring_implies_list_chromatic_index_even_clique :
  edge_list_coloring_statement -> list_chromatic_index_even_clique_statement.
Proof.
move=> ELC n pos evn; case: n pos evn => [|[|m]] pos evn //.
have oN : odd m.+1 by move: evn; rewrite /= negbK.
pose e0 : kn_edge m.+2 := exist _ (ord0, ord_max) (ltn0Sn m).
have gpos : 0 < #|line_graph (kn_mgraph m.+2)| by apply/card_gt0P; exists e0.
have [ch icn] := choice_number_ex gpos.
have chE := ELC (kn_mgraph m.+2) ch (@kn_loopless m.+2) icn.
have chle : ch <= m.+1 by rewrite chE; exact: kn_chi_line oN.
have chn : choosable (line_graph (kn_mgraph m.+2)) m.+1.
  by apply: choosable_leqW chle _; case: icn.
move=> C L Lsym Lcard.
exact: (kn_edge_choosable_of (isT : 1 < m.+2) chn Lsym Lcard).
Qed.

(* cross-package edge planar_fractional_vertex_arboricity_two_statement -> large_induced_forest_in_a_planar_graph_statement: annotation and proof now live in atlas/theories/conjectures/implications_A1.v or A2.v (wave A1, 2026-09-24) *)

Print Assumptions triangle_free_planar_large_induced_two_degenerate_implies_triangle_free_planar_five_sixths_two_degenerate.
Print Assumptions toroidal_five_choosable_iff_implies_critical_forward.
Print Assumptions edge_list_coloring_implies_list_chromatic_index_even_clique.
