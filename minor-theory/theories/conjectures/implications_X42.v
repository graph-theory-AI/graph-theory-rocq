(** * Minor.conjectures.implications_X42 — corpus-relation edges landing in X42

    Edges of [meta/corpus_relations.json] whose TARGET is the X42 row
    [even_hole_k4_diamond_free_bounded_treewidth_statement].  Axiom-free: only
    [Qed]-closed results live here; a candidate edge that does not close is
    documented, never stated.

    ** The bridge F1 between the two treewidth encodings.

    X220 / X228 measure treewidth with [tw_le] (a [sdecomp] over a [forest]
    index, [width D <= k.+1]); X27 / X42 measure it with
    [x27_treewidth_at_most] (an arbitrary [sgraph] index that [is_tree], plus the
    three tree-decomposition clauses spelled out by hand).  The two are
    EQUIVALENT ([tw_le_iff_x27]).  The easy direction turns a tree index into a
    [forest] record; the other direction needs the index forest to be made
    connected, which is [Minor.foundations.width_params.tw_le_tree].  In both
    directions the only real friction is that [sbag_conn] states its
    connectedness with the PREDICATE [[pred t | x \in B t]] while
    [x27_tree_decomposition] states it with the SET [[set t | x \in bag t]];
    [restrict_bag] + [eq_connect] mediate.

    ** e050 (PROVED).  [even_hole_diamond_free_bounded_tree_alpha_statement] ⟹
    [even_hole_k4_diamond_free_bounded_treewidth_statement]: an (even hole, K_4,
    diamond)-free graph is in particular (even hole, diamond)-free, so the source
    gives a tree decomposition whose bags have independence number at most [k];
    K_4-freeness forbids a clique of size 4 inside a bag; finite Ramsey
    ([Minor.foundations.ramsey_small.ramsey_bound] at [s = 4], [a = k]) then
    bounds every bag, hence the width, and F1 delivers the X27-shaped
    conclusion. *)

From GTBase Require Import base.
From GraphTheory Require Import preliminaries.
From Minor.foundations Require Import containment width_params ramsey_small hole_containments.
From Minor.conjectures Require Import X27 X42 X220.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The bridge F1 : [tw_le] ⟺ [x27_treewidth_at_most] *******************)

(** The two spellings of "the index nodes whose bag contains [v]". *)
Lemma restrict_bag (G T : sgraph) (D : T -> {set G}) (v : G) :
  restrict [pred t : T | v \in D t] (@sedge T)
    =2 restrict [set t : T | v \in D t] (@sedge T).
Proof. by move=> a b; rewrite /restrict_mem /= !inE. Qed.

Lemma tw_le_x27 (G : sgraph) (k : nat) : tw_le G k -> x27_treewidth_at_most G k.
Proof.
case/tw_le_tree => T [D [dec w conn]].
exists (sgraph_of_forest T), D; split; first by split; [exact: forest_is_forest|exact: conn].
split.
- split=> [v|].
  + by have [t vt] := sbag_cover dec v; apply/existsP; exists t.
  + split=> [x y xy|v t1 t2 h1 h2].
    * by have [t /andP[xt yt]] := sbag_edge dec xy; apply/existsP; exists t; rewrite xt yt.
    * rewrite inE in h1; rewrite inE in h2.
      rewrite -(eq_connect (@restrict_bag G T D v)).
      exact: (sbag_conn dec h1 h2).
- by move=> t; apply: leq_trans w; rewrite /width; exact: leq_bigmax.
Qed.

Lemma x27_tw_le (G : sgraph) (k : nat) : x27_treewidth_at_most G k -> tw_le G k.
Proof.
case=> T [bag [[tf tc] [[cov [edg cn]] bnd]]].
exists (@Forest T tf), bag; split; last first.
  by rewrite /width; apply/bigmax_leqP => t _; exact: bnd.
split.
- by move=> x; have /existsP[t ht] := cov x; exists t.
- by move=> x y xy; have /existsP[t ht] := edg x y xy; exists t.
- move=> x t1 t2 h1 h2; rewrite (eq_connect (@restrict_bag G T bag x)).
  by apply: (cn x); rewrite inE.
Qed.

Lemma tw_le_iff_x27 (G : sgraph) (k : nat) :
  tw_le G k <-> x27_treewidth_at_most G k.
Proof. by split; [exact: tw_le_x27|exact: x27_tw_le]. Qed.

(** ** Dictionary between the two "induced-H-free" spellings ***************)

(** [x42_induced_free] (no vertex set induces a copy of [H]) implies the
    negation of [has_induced_copy] (no injective edge-reflecting map [H -> G]):
    the image of such a map is a vertex set that induces a copy of [H]
    ([isubgraph_induced]). *)
Lemma induced_free_no_copy (G H : sgraph) :
  x42_induced_free G H -> ~ has_induced_copy G H.
Proof.
move=> hf [i]; apply: (hf [set x in codom i]); split.
exact: diso_sym (isubgraph_induced i).
Qed.

(** A clique on exactly four vertices induces a copy of ['K_4]. *)
Lemma clique4_K4 (G : sgraph) (S : {set G}) :
  clique S -> #|S| = 4 -> inhabited (induced S ≃ 'K_4).
Proof.
move=> cS c4; split.
have e : #|induced S| = 4 by rewrite card_induced.
rewrite -e; apply: diso_Kn => x y xy.
by apply: (cS _ _ (valP x) (valP y)); rewrite val_eqE.
Qed.

(** ** e050 (PROVED) *******************************************************)

Theorem even_hole_diamond_free_bounded_tree_alpha_implies_even_hole_k4_diamond_free_bounded_treewidth :
  even_hole_diamond_free_bounded_tree_alpha_statement ->
  even_hole_k4_diamond_free_bounded_treewidth_statement.
Proof.
case=> k src.
have [N HN] := ramsey_bound 4 k.
exists N => G eh k4 dia.
have [T [D [dec ab]]] := src G eh (induced_free_no_copy dia).
have cl4 : forall (t : T) (S : {set G}), S \subset D t -> clique S -> #|S| != 4.
  move=> t S _ cS; apply/negP => /eqP c4.
  exact: (k4 S (clique4_K4 cS c4)).
apply: tw_le_x27; exists T, D; split; first exact: dec.
rewrite /width; apply/bigmax_leqP => t _.
by apply: leq_trans (HN G (D t) (ab t) (cl4 t)) (leqnSn N).
Qed.

(*@EDGE from=even_hole_diamond_free_bounded_tree_alpha_statement to=even_hole_k4_diamond_free_bounded_treewidth_statement kind=implies status=verified proved=true proof=even_hole_diamond_free_bounded_tree_alpha_implies_even_hole_k4_diamond_free_bounded_treewidth cite="gc:e050" note="Hypothesis-class containment plus Ramsey: (even hole, K_4, diamond)-free graphs are (even hole, diamond)-free, so the source bounds the independence number of every bag of some tree decomposition by k; no induced K_4 forbids a clique of size 4 inside a bag, so finite Ramsey (foundations/ramsey_small.v, ramsey_bound at s=4, a=k) bounds every bag by N(4,k), hence the width; the bridge F1 (tw_le_x27, built on foundations/width_params.v tw_le_tree) converts the forest-indexed sdecomp into the tree-indexed x27_treewidth_at_most. Constant c := N(4,k)." *)

(** ** e051 — the four even-hole containments, and the one hypothesis left ***

    [theta_prism_even_wheel_free_bounded_treewidth_statement] ⟹
    [even_hole_k4_diamond_free_bounded_treewidth_statement] (gc:e051).

    Re-derivation.  Instantiate the source at [t = 4] (the source's [exists c] is then
    available with no choice principle, since [t] is FIXED — contrast e053).  Five of
    the six hypotheses the source needs on an (even hole, K_4, diamond)-free [G] are
    now discharged below, and the conclusion is converted by the bridge F1
    ([tw_le_x27]):

    - [~ has_induced_copy G (cycle_graph 4)] : [even_hole_free_no_C4] — a [C_4] IS an
      even hole ([Minor.foundations.hole_containments.C4_even_hole]);
    - [~ has_induced_copy G x42_diamond] : [induced_free_no_copy];
    - [forall H, x220_theta H -> ~ has_induced_copy G H] : [even_hole_free_no_theta] —
      a theta, i.e. a graph that IS a subdivision of ['K_2,3], contains an even hole
      ([subdiv_KB23_even_hole]): of the three internally disjoint paths joining the two
      branch vertices two have the same parity, and since the encoded theta is EXACT
      ([subdiv_rep] forces every edge of [H] to be an edge of a subdivision path) their
      union is an INDUCED cycle;
    - [forall H, x220_prism H -> ~ has_induced_copy G H] : [even_hole_free_no_prism] —
      the same parity argument on the three matching paths of a prism
      ([prism_even_hole]);
    - [x220_clique_free G 4] : [K4_free_clique_free] — a clique with at least four
      vertices has a four-element subset ([sub_card_exact]), which is again a clique
      ([clique_sub]) and induces a copy of ['K_4] ([clique4_K4]).

    What is LEFT is exactly one containment, [x220_even_wheel_free G]: a hole [c] of an
    even-hole-free graph has ODD length, so if a vertex [v] outside [c] had an EVEN
    number [k >= 4] of neighbours on [c], the [k] arcs of [c] cut out by those
    neighbours would have lengths summing to the odd [#|c|], hence one arc would have
    EVEN length, and that arc together with [v] is an even hole.  Formalising it needs
    the arc decomposition of a cyclic sequence by a set of its vertices, which is a
    genuinely new piece of machinery (nothing in [MathComp]'s [path.v] / [arc.v] gives
    the arc lengths of a hole as a partition of its size).  [e051_modulo_even_wheel]
    below states the edge modulo exactly that one containment, so the gap is pinned. *)

(** *** The three even-hole containments *)

Lemma even_hole_free_no_C4 (G : sgraph) :
  x27_even_hole_free G -> ~ has_induced_copy G (cycle_graph 4).
Proof. by move=> eh [i]; case: (C4_even_hole i) => c [hc pc]; exact: (eh c hc pc). Qed.

Lemma even_hole_free_no_theta (G H : sgraph) :
  x27_even_hole_free G -> x220_theta H -> ~ has_induced_copy G H.
Proof.
move=> eh th [i]; case: (subdiv_KB23_even_hole th) => c [hc pc].
apply: (eh [seq i x | x <- c]); first exact: isubgraph_hole.
by rewrite size_map.
Qed.

Lemma even_hole_free_no_prism (G H : sgraph) :
  x27_even_hole_free G -> x220_prism H -> ~ has_induced_copy G H.
Proof.
move=> eh pr [i]; case: (prism_even_hole pr) => c [hc pc].
apply: (eh [seq i x | x <- c]); first exact: isubgraph_hole.
by rewrite size_map.
Qed.

(** *** No induced ['K_4] bounds the clique number by 4 *)

Lemma K4_free_clique_free (G : sgraph) :
  x42_induced_free G 'K_4 -> x220_clique_free G 4.
Proof.
move=> k4 S cS; rewrite ltnNge; apply/negP => h4.
have [B sub cardB] := sub_card_exact h4.
exact: (k4 B (clique4_K4 (clique_sub cS sub) cardB)).
Qed.

(** *** The edge, modulo the one missing containment *)

Theorem e051_modulo_even_wheel :
  (forall G : sgraph,
     x27_even_hole_free G -> x42_induced_free G x42_diamond ->
     x220_even_wheel_free G) ->
  theta_prism_even_wheel_free_bounded_treewidth_statement ->
  even_hole_k4_diamond_free_bounded_treewidth_statement.
Proof.
move=> wheel src; case: (src 4) => c Hc.
exists c => G eh k4 dia; apply: tw_le_x27; apply: Hc.
- exact: even_hole_free_no_C4.
- exact: induced_free_no_copy dia.
- by move=> H th; exact: even_hole_free_no_theta eh th.
- by move=> H pr; exact: even_hole_free_no_prism eh pr.
- exact: wheel G eh dia.
- exact: K4_free_clique_free k4.
Qed.

(*@EDGE from=theta_prism_even_wheel_free_bounded_treewidth_statement to=even_hole_k4_diamond_free_bounded_treewidth_statement kind=implies status=candidate proved=false cite="gc:e051" note="Corpus argument: each of C_4, theta, prism and even wheel contains an even hole, so (even hole, K_4, diamond)-free graphs lie in the class C*_4 and the t = 4 instance of the source bounds their treewidth. FIVE of the six source hypotheses are now PROVED here plus in foundations/hole_containments.v: ~has_induced_copy G (cycle_graph 4) (even_hole_free_no_C4, from four_cycle_hole), ~has_induced_copy G x42_diamond (induced_free_no_copy), theta-freeness (even_hole_free_no_theta, from subdiv_KB23_even_hole: two of the three internally disjoint K_2,3-subdivision paths have equal parity and, subdiv_rep being EXACT, their union is an induced even cycle), prism-freeness (even_hole_free_no_prism, same parity argument on the three matching paths), x220_clique_free G 4 (K4_free_clique_free, via sub_card_exact + clique4_K4); and the treewidth-encoding gap is CLOSED (bridge F1, tw_le_x27). BLOCKED on exactly one containment: even_wheel_has_even_hole, i.e. x220_even_wheel_free G for an even-hole-free diamond-free G. The mathematics is settled (the hole is odd, so k even forces an arc of even length, and that arc plus the wheel centre is an even hole) but it needs the ARC DECOMPOSITION of a cyclic sequence by a subset of its vertices, machinery that neither MathComp path.v/arc.v nor this development provides. Theorem e051_modulo_even_wheel in this file states the edge modulo that single hypothesis, so the gap is exactly pinned." *)

Print Assumptions tw_le_x27.
Print Assumptions even_hole_free_no_C4.
Print Assumptions even_hole_free_no_theta.
Print Assumptions even_hole_free_no_prism.
Print Assumptions K4_free_clique_free.
Print Assumptions e051_modulo_even_wheel.
Print Assumptions x27_tw_le.
Print Assumptions even_hole_diamond_free_bounded_tree_alpha_implies_even_hole_k4_diamond_free_bounded_treewidth.
