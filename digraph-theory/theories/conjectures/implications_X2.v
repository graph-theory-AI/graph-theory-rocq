(** * Digraph.conjectures.implications_X2 — wave X2 implication edges

    Implication edges of meta/corpus_relations.json whose TARGET row belongs to
    milestone X2.

      - e020 : arxiv:2305.15585#00 ==> arxiv:2305.15585#01
               (the degeneracy version of "chromatic number is not
               tournament-local" implies the cycle version).
               VERIFIED: instantiate the source at d = 2 and turn "some
               nonempty set of the out-neighbourhood graph has minimum degree
               at least 2 inside itself" into a cycle
               ([foundations/cycles.v: min_deg2_has_cycle]).

      - e074 : opg:subdivision_of_a_transitive_tournament_in_digraphs_with_large_outdegree
               ==> arxiv:1610.00876#01 (every oriented tree is
               delta-plus-maderian).
               VERIFIED (wave E4, after the nonemptiness guard repair): an
               oriented tree is acyclic, hence a subdigraph of the transitive
               tournament on its vertices along a topological order, and a
               subdivision of [TT k] contains a subdivision of each of its
               subdigraphs.
      - e173 : the same source ==> arxiv:1610.00876#00  (Mader out-degree ==>
               Mader semidegree).
               Recorded as a candidate: the hypothesis-class half is Qed-closed
               here ([subdivision_TT_gives_delta0_bound]), but the LEAST clause
               of [least_mader_delta_zero] is not constructively available -
               see the annotation.

    Before the wave-E4 guard repair BOTH edges were blocked for a different
    reason: all three statements were refutable on the EMPTY digraph, which
    satisfies every pointwise minimum-degree hypothesis vacuously while
    containing no subdivision of a nonempty digraph. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude interop_graph_theory digraph oriented tournament.
From Digraph Require Import dipath cycles subdivision.
From Digraph.conjectures Require Import chi_bounded X2 P9.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Degeneracy at least two, in the [sg_degeneracy_at_least] form of X2.v,
    yields a genuine cycle: this is the "degeneracy <= 1 iff forest" half that
    the corpus argument for e020 appeals to. *)
Lemma sg_degeneracy2_has_cycle (G : sgraph) :
  sg_degeneracy_at_least G 2 -> sg_has_cycle G.
Proof. by move=> [S [hS hdeg]]; exact: min_deg2_has_cycle hS hdeg. Qed.

(*@EDGE from=tournament_outneighborhood_degeneracy_statement to=tournament_outneighborhood_cycle_statement kind=implies status=verified proof=tournament_outneighborhood_degeneracy_implies_tournament_outneighborhood_cycle cite="gc:e020" note="Parameter instantiation at d = 2 plus one graph-theory lemma: a nonempty vertex set in which every vertex has at least two neighbours inside the set contains a cycle on at least three vertices (foundations/cycles.v: min_deg2_has_cycle, proved by taking a longest duplicate-free walk inside the set). The bound C of the source at d = 2 is reused verbatim, and the two statements quantify over the same tournament/graph pair and the same out-neighbourhood subgraph." *)

Theorem tournament_outneighborhood_degeneracy_implies_tournament_outneighborhood_cycle :
  tournament_outneighborhood_degeneracy_statement ->
  tournament_outneighborhood_cycle_statement.
Proof.
move=> H; have [C hC] := H 2; exists C => T E Esym Eirr hchi.
have [v hv] := hC T E Esym Eirr hchi.
by exists v; exact: sg_degeneracy2_has_cycle hv.
Qed.

(*@EDGE from=subdivision_of_a_transitive_tournament_in_digraphs_w_statement to=mader_delta0_transitive_tournament_statement kind=implies status=candidate proved=false cite="gc:e173" note="BLOCKED after the wave-E4 nonemptiness guard repair, and now on CONSTRUCTIVITY rather than on faithfulness. The hypothesis-class half of the corpus argument is Qed-closed here as subdivision_TT_gives_delta0_bound: delta^0(D) >= f k gives delta^+(D) >= f k, so the source bound f k IS a mader_delta_zero_bound for TT k (the P9 spelling of a subdivision is transported to the X2 one by subdivides_contains_subdivision). What does NOT follow is the LEAST clause of least_mader_delta_zero: mader_delta_zero_bound (TT k) c quantifies over ALL digraphs, is not a Boolean predicate, so ex_minn is unavailable; and the least-element principle for an upward-closed Prop-valued predicate on nat is equivalent to excluded middle (with P n := (1 <= n) or A, a least element of P decides A), which this package forbids (no boolp / classical lemma). This is the same obstruction as the one recorded for corpus e053 in minor-theory/theories/conjectures/implications_X27.v. Missing ingredient: either the row body asserts only that SOME bound exists (mader_delta_zero_bound, the mathematical content of the corpus sentence, the least one then existing by classical well-ordering), or a decidability lemma for mader_delta_zero_bound." *)


(** ** Wave E4: the two Mader rows, after the nonemptiness GUARD REPAIR

    The source row (P9.v) speaks of [P9.subdivides D H]; the two X2 targets speak
    of [X2.contains_subdivision H D].  The two encodings agree, and the first
    lemma below is the bridge; then a subdivision of a digraph is a subdivision of
    each of its subdigraphs, and every oriented tree on [k] vertices is a
    subdigraph of [TT k]. *)

(** *** The two subdivision encodings agree *)

(** The interior of a replacement path, as a SET ([X2]) and as the SEQUENCE
    [behead (belast _ _)] ([P9]). *)
Lemma mem_x2_internal (H D : diGraphType) (b : H -> D) (u v : H) (s : seq D)
    (z : D) :
  last (b u) s = b v -> z \in x2_path_internal b u v s ->
  z \in behead (belast (b u) s).
Proof.
rewrite /x2_path_internal /x2_path_vertices !inE => hlast /andP[hn hz].
move: hn; rewrite negb_or => /andP[h1 h2].
by apply: mem_behead_belast => //; rewrite hlast.
Qed.

(** [P9.subdivides D H] implies [X2.contains_subdivision H D] for a LOOPLESS [H]
    (the branch map, the replacement paths and the disjointness clauses are the
    same data; only the interiors are spelled differently, and the nonemptiness of
    each replacement path follows from the injectivity of the branch map). *)
Lemma subdivides_contains_subdivision (H D : diGraphType) :
  (forall u : H, ~~ (u --> u)) -> subdivides D H -> contains_subdivision H D.
Proof.
move=> Hirr [b [p [binj hpath hbranch hdisj]]].
exists b; split=> //; exists p; split.
- move=> u v huv; have [hp hlast] := hpath u v huv.
  have huvn : u != v by apply/negP => /eqP e; move: huv; rewrite e (negbTE (Hirr v)).
  have hbn : b u != b v by apply: contra huvn => /eqP /binj ->.
  have hsz : (0 < size (p u v))%N.
    case: (p u v) hlast => [/= e|a s _] //.
    by move: hbn; rewrite e eqxx.
  split=> //; apply/preliminaries.disjointP => z hz.
  rewrite inE => /existsP[x /eqP hx].
  by move: (hbranch u v huv x); rewrite hx (mem_x2_internal hlast hz).
- move=> u v x y huv hxy hne; apply/preliminaries.disjointP => z hz1 hz2.
  have [_ hl1] := hpath u v huv; have [_ hl2] := hpath x y hxy.
  move/negP: (hdisj u v x y huv hxy hne) => hno; apply: hno.
  apply/hasP; exists z; first exact: mem_x2_internal hl1 hz1.
  exact: mem_x2_internal hl2 hz2.
Qed.

(** *** Subdivisions are monotone under subdigraphs *)

(** A subdivision of [G] contains a subdivision of every subdigraph [F] of [G]:
    keep the branch vertices and the replacement paths of the arcs of [F]. *)
Lemma contains_subdivision_sub (F G D : diGraphType) :
  subdigraph_embed F G -> contains_subdivision G D -> contains_subdivision F D.
Proof.
move=> [e [einj earc]] [branch [binj [paths [hpath hdisj]]]].
exists (branch \o e); split; first exact: inj_comp binj einj.
exists (fun u v : F => paths (e u) (e v)); split.
- move=> u v huv; have [h1 h2 h3 h4] := hpath _ _ (earc _ _ huv).
  move/preliminaries.disjointP: h4 => h4'.
  split=> //; apply/preliminaries.disjointP => z hz hz2; apply: (h4' z hz).
  move: hz2; rewrite !inE => /existsP[x /eqP hx].
  by apply/existsP; exists (e x); apply/eqP; exact: hx.
- move=> u v x y huv hxy hne.
  apply: (hdisj (e u) (e v) (e x) (e y) (earc _ _ huv) (earc _ _ hxy)).
  apply/orP; case/orP: hne => h.
  + by left; apply/negP => /eqP /einj eq; move: h; rewrite eq eqxx.
  + by right; apply/negP => /eqP /einj eq; move: h; rewrite eq eqxx.
Qed.

(** *** Every oriented tree on [k] vertices sits inside [TT k] *)

Lemma oriented_tree_arc_irr (F : orientedDigraph) :
  chi_bounded.oriented_dg F -> forall u : F, ~~ (u --> u).
Proof. by move=> hor u; apply/negP => h; move: (hor _ _ h); rewrite h. Qed.

Lemma oriented_tree_in_TT (F : orientedDigraph) :
  X2.oriented_tree F -> subdigraph_embed F (TT #|F| : diGraphType).
Proof.
move=> [hcard hor hforest _].
have hirr := oriented_tree_arc_irr hor.
have harc : forall u v : F, u --> v ->
    (u : chi_bounded.underlying F) -- (v : chi_bounded.underlying F).
  move=> u v huv; have hne : u != v.
    by apply/negP => /eqP e; move: huv; rewrite e (negbTE (hirr v)).
  by rewrite /edge_rel/= /chi_bounded.urel hne huv.
have hnb := @forest_no_backarc F (chi_bounded.underlying F) id (@inj_id _) harc hforest hor.
have [g [ginj gmono]] := acyclic_topo_embed hnb.
exists g; split=> // u v huv; rewrite arcTTE; exact: gmono.
Qed.

(*@EDGE from=subdivision_of_a_transitive_tournament_in_digraphs_w_statement to=oriented_trees_delta_plus_maderian_statement kind=implies status=verified proof=subdivision_of_a_transitive_tournament_in_digraphs_w_implies_oriented_trees_delta_plus_maderian cite="gc:e074" note="The corpus argument, verbatim, on the repaired bodies: an oriented tree F is acyclic (a directed walk returning to its tail would give a digon or a cycle of the underlying forest, foundations/subdivision.v: forest_no_backarc), so it has a topological order, i.e. an injective numbering strictly increasing along arcs (acyclic_topo_embed, ranked by the number of ancestors with enum_rank breaking ties); that numbering is a subdigraph embedding F -> TT #|F| (oriented_tree_in_TT). The source applied at k = #|F| to a non-empty host of minimum out-degree at least f k yields a subdivision of TT k in the P9 spelling, transported to the X2 spelling by subdivides_contains_subdivision, and restricted to the subdigraph F by contains_subdivision_sub. The nonemptiness guard 0 < #|D| repaired in wave E4 on BOTH bodies is what makes this an implication with content (before the repair both bodies were refutable on the empty digraph)." *)

Theorem subdivision_of_a_transitive_tournament_in_digraphs_w_implies_oriented_trees_delta_plus_maderian :
  subdivision_of_a_transitive_tournament_in_digraphs_w_statement ->
  oriented_trees_delta_plus_maderian_statement.
Proof.
move=> [f hf] F hF; exists (f #|F|) => D hD hdeg.
apply: (contains_subdivision_sub (oriented_tree_in_TT hF)).
apply: subdivides_contains_subdivision; first by move=> u; rewrite arcTTE ltnn.
exact: hf hD hdeg.
Qed.

(** *** e173: the existence half, and why the LEAST clause does not follow *)

(** The whole content of corpus edge e173 that is available constructively:
    minimum semidegree at least [m] implies minimum out-degree at least [m], so
    the source's bound [f k] IS a [mader_delta_zero_bound] for [TT k]. *)
Lemma subdivision_TT_gives_delta0_bound :
  subdivision_of_a_transitive_tournament_in_digraphs_w_statement ->
  forall k : nat, exists m : nat, mader_delta_zero_bound (TT k) m.
Proof.
move=> [f hf] k; exists (f k) => D hD hsemi.
apply: subdivides_contains_subdivision; first by move=> u; rewrite arcTTE ltnn.
by apply: hf => // v; case: (hsemi v).
Qed.

(** ** Print Assumptions audit *)

Print Assumptions sg_degeneracy2_has_cycle.
Print Assumptions tournament_outneighborhood_degeneracy_implies_tournament_outneighborhood_cycle.
Print Assumptions subdivides_contains_subdivision.
Print Assumptions contains_subdivision_sub.
Print Assumptions oriented_tree_in_TT.
Print Assumptions subdivision_of_a_transitive_tournament_in_digraphs_w_implies_oriented_trees_delta_plus_maderian.
Print Assumptions subdivision_TT_gives_delta0_bound.
