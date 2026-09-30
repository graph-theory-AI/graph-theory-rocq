(** * Chromatic.conjectures.implications_X218 -- dependency-graph EDGES for wave X218.

    Machine-checked implication edges out of / into the X218 statements.  Every
    SCHEDULED edge is a RELATIVE theorem: a [Qed]-closed [Theorem A -> B] proved
    WITHOUT resolving either endpoint.  Axiom-free: no [Axiom] / [Parameter] /
    [Admitted] / [Conjecture].  Candidate edges record the exact obstruction.

    The [cite="gc:eNNN"] fields point at [meta/corpus_relations.json]; rebuild it
    with [meta/build_corpus_relations.py] after this wave's manifest
    regeneration so the new formal names reach the relation endpoints. *)

From GTBase Require Import base.
From Chromatic.foundations Require Import chi_bounding poly_forms forest_paths.
From Chromatic.conjectures Require Import U8 X3 X65 X218.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Arithmetic and embedding helpers **********************************)

Lemma x218_leq_expn_base (m n e : nat) : m <= n -> m ^ e <= n ^ e.
Proof. by move=> le; elim: e => [|e IH] //; rewrite !expnS leq_mul. Qed.

(** A clique on [d*t] vertices contains the complete [d]-partite graph with all
    parts of size [t] as a SUBGRAPH: any injection of its [d*t] vertices into
    the clique preserves edges, since every two distinct clique vertices are
    adjacent. *)
Lemma x218_clique_has_multipartite (G : sgraph) (d t : nat) :
  d * t <= ω([set: G]) -> has_subgraph G (x218_complete_multipartite d t).
Proof.
case: omegaP => K KM le.
have cl := maxclique_clique KM.
have cardle : #|{: 'I_d * 'I_t}| <= #|K| by rewrite card_prod !card_ord; exact: le.
pose f (x : 'I_d * 'I_t) : G := @enum_val G (mem K) (widen_ord cardle (enum_rank x)).
have finj : injective f.
  move=> x y /enum_val_inj /(f_equal (@nat_of_ord _)) /= exy.
  by apply: enum_rank_inj; apply: val_inj.
exists f => // x y.
rewrite /edge_rel /= /x218_multipartite_rel => ne.
have xy : x != y by apply: contraNneq ne => ->; rewrite eqxx.
by apply: cl; rewrite ?enum_valP //; apply: contraNneq xy => /finj.
Qed.

(** All parts of size ONE: [K_d(1)] is [K_d], and any two DISTINCT vertices of
    it are adjacent, since their second coordinates agree in ['I_1] and hence
    their parts must differ. *)
Lemma x218_multipartite1_edge (d : nat) (a b : x218_complete_multipartite d 1) :
  a != b -> a -- b.
Proof.
move=> ab; rewrite /edge_rel /= /x218_multipartite_rel.
apply: contraNneq ab => e1.
by rewrite -pair_eqE /= e1 (ord1 a.2) (ord1 b.2) !eqxx.
Qed.

(** Converse of [x218_clique_has_multipartite] at [t = 1]: a SUBGRAPH copy of
    [K_d(1)] in [G] is a clique of [G] on [d] vertices, so it forces
    [d <= omega(G)]. *)
Lemma x218_multipartite1_omega (G : sgraph) (d : nat) :
  has_subgraph G (x218_complete_multipartite d 1) -> d <= ω([set: G]).
Proof.
case=> f finj fhom.
have card_im : #|f @: [set: x218_complete_multipartite d 1]| = d.
  by rewrite card_imset // cardsT card_prod !card_ord muln1.
rewrite -card_im; apply: clique_bound; rewrite inE subsetT /=.
apply/cliqueP => u v /imsetP[a _ ->] /imsetP[b _ ->] ne.
have ab : a != b by apply: contraNneq ne => ->.
by apply: fhom; [exact: x218_multipartite1_edge | exact: ne].
Qed.

(** ** Polynomial Gyarfas-Sumner ==> Gyarfas-Sumner ***********************)

(*@EDGE from=polynomial_gyarfas_sumner_tree_statement to=graphs_with_a_forbidden_induced_tree_are_chi_bounded_statement kind=implies status=verified proved=true proof=polynomial_gyarfas_sumner_tree_implies_graphs_with_a_forbidden_induced_tree_are_chi_bounded cite="gc:e175" note="Corpus relation e175 (confirmed): a polynomial chi-bounding function is in particular a chi-bounding function. Under the X218 encoding the bounding function of U8 is literally the polynomial t |-> c * t ^ d produced by poly_chi_bounded." *)
Theorem polynomial_gyarfas_sumner_tree_implies_graphs_with_a_forbidden_induced_tree_are_chi_bounded :
  polynomial_gyarfas_sumner_tree_statement ->
  graphs_with_a_forbidden_induced_tree_are_chi_bounded_statement.
Proof. by move=> H T Tt; have [c [d Hcd]] := H T Tt; exists (fun s => c * s ^ d). Qed.

(** ** Every forest is good ==> every forest is multibounding *************)

(*@EDGE from=every_forest_is_good_statement to=every_forest_is_multibounding_statement kind=implies status=verified proved=true proof=every_forest_is_good_implies_every_forest_is_multibounding cite="gc:e171" note="Corpus relation e171 (confirmed, and stated in the target's own context): if G is H-free with no K_d(t) subgraph then omega(G) < d*t, because a clique on d*t vertices contains K_d(t) as a spanning subgraph; so chi(G) <= c * omega(G)^e <= c * d^e * t^e, a polynomial in t for each fixed d." *)
Theorem every_forest_is_good_implies_every_forest_is_multibounding :
  every_forest_is_good_statement -> every_forest_is_multibounding_statement.
Proof.
move=> H F Ff; have [c [e Hce]] := H F Ff.
exists (fun d : nat => c * d ^ e), (fun _ : nat => e) => d dpos t G tpos nind nsub /=.
apply: leq_trans (Hce G nind) _.
have wle : ω([set: G]) <= d * t.
  rewrite leqNgt; apply/negP => lt.
  by apply: nsub; apply: x218_clique_has_multipartite; apply: ltnW.
rewrite -mulnA -expnMn leq_mul2l; apply/orP; right.
exact: x218_leq_expn_base.
Qed.

(** ** Every forest is multibounding ==> Gyarfas-Sumner *******************)

(*@EDGE from=every_forest_is_multibounding_statement to=graphs_with_a_forbidden_induced_tree_are_chi_bounded_statement kind=implies status=verified proved=true proof=every_forest_is_multibounding_implies_graphs_with_a_forbidden_induced_tree_are_chi_bounded cite="gc:e035" note="Corpus relation e035 (confirmed): every tree is a forest, so it is multibounding; take t = 1, where K_d(1) = K_d, and apply multiboundedness at d = omega(G)+1. A subgraph copy of K_d(1) is a clique on d vertices (x218_multipartite1_omega), so an omega(G)+1 copy is impossible, and the multibounding bound reads chi(G) <= c(omega(G)+1) * 1 ^ e(omega(G)+1) = c(omega(G)+1); the chi-bounding function of U8 is s |-> c s.+1. This edge is what the 2026-09-24 RE-ENCODING of x218_multibounding buys: with the earlier 'forall d, exists c e' body the function s |-> c s.+1 could not be built without countable choice." *)
Theorem every_forest_is_multibounding_implies_graphs_with_a_forbidden_induced_tree_are_chi_bounded :
  every_forest_is_multibounding_statement ->
  graphs_with_a_forbidden_induced_tree_are_chi_bounded_statement.
Proof.
move=> M T Tt; have [Tf _] := Tt; have [c [e Hce]] := M T Tf.
exists (fun s : nat => c s.+1) => G nind.
have bound := Hce (ω([set: G])).+1 (ltn0Sn _) 1 G (leqnn 1) nind.
rewrite exp1n muln1 in bound.
apply: bound => Hsub.
by move: (x218_multipartite1_omega Hsub); rewrite ltnn.
Qed.

(** ** The X65 coefficient-list form and the X218 normal form agree ******)

(*@EDGE from=forest_free_polynomial_chi_bound_statement to=every_forest_is_good_statement kind=equiv status=verified proved=true proof=forest_free_polynomial_chi_bound_equiv_every_forest_is_good cite="audit: meta/X211-X229_faithfulness_audit.md:2063 (corpus same_conjecture e007/e008)" note="The two rows are the SAME mathematical statement, stated for two different papers (arxiv:2202.05557#00 in X65.v, arxiv:2202.10412#00 in X218.v): 'every forest H is good', i.e. the class of H-free graphs is polynomially chi-bounded. They differ only in the encoding of 'polynomially chi-bounded': X65 uses an arbitrary coefficient list evaluated by Horner (x3_polynomially_chi_bounded), X218 the normal form c * omega ^ d (poly_chi_bounded). Over the naturals the two encodings are equivalent (foundations/poly_forms.v): list ==> normal form is the Horner domination F4 (chi_bounding.horner_nat_dom) at omega >= 1 plus the omega = 0 corner (a graph with clique number 0 has no vertex, hence chromatic number 0); normal form ==> list takes the coefficient list of d zeros followed by c. Hence the equivalence, with the SAME forest hypothesis on both sides." *)
Theorem forest_free_polynomial_chi_bound_equiv_every_forest_is_good :
  forest_free_polynomial_chi_bound_statement <-> every_forest_is_good_statement.
Proof.
split=> X H Hf.
  by apply: x3_poly_chi_boundedW; exact: X H Hf.
by apply: poly_chi_bounded_x3W; exact: X H Hf.
Qed.

(** ** X65's forest bound ==> the polynomial Gyarfas-Sumner row ***********)

(*@EDGE from=forest_free_polynomial_chi_bound_statement to=polynomial_gyarfas_sumner_tree_statement kind=implies status=verified proved=true proof=forest_free_polynomial_chi_bound_implies_polynomial_gyarfas_sumner_tree cite="gc:e033" note="Corpus relation e033 (confirmed): every tree is a forest, so the X65 forest statement specialises to trees. The encoding gap between the coefficient-list polynomial of X65 and the c * omega^d normal form of X218 is closed by the F4 Horner domination lemma of foundations/poly_forms.v (x3_poly_chi_boundedW), which is exactly the missing ingredient recorded by the earlier candidate annotation." *)
Theorem forest_free_polynomial_chi_bound_implies_polynomial_gyarfas_sumner_tree :
  forest_free_polynomial_chi_bound_statement ->
  polynomial_gyarfas_sumner_tree_statement.
Proof.
move=> X T [Tf _].
by apply: (forest_free_polynomial_chi_bound_equiv_every_forest_is_good.1 X).
Qed.

(** ** X65's forest bound ==> every forest is multibounding **************)

(*@EDGE from=forest_free_polynomial_chi_bound_statement to=every_forest_is_multibounding_statement kind=implies status=verified proved=true proof=forest_free_polynomial_chi_bound_implies_every_forest_is_multibounding cite="gc:e034" note="Corpus relation e034 (confirmed, and stated in the target's context). The coefficient-list polynomial of X65 is first put in the c * t^d normal form (F4, foundations/poly_forms.v), turning the source into every_forest_is_good_statement; then the omega(G) < d*t step of every_forest_is_good_implies_every_forest_is_multibounding applies verbatim." *)
Theorem forest_free_polynomial_chi_bound_implies_every_forest_is_multibounding :
  forest_free_polynomial_chi_bound_statement ->
  every_forest_is_multibounding_statement.
Proof.
move=> X; apply: every_forest_is_good_implies_every_forest_is_multibounding.
exact: (forest_free_polynomial_chi_bound_equiv_every_forest_is_good.1 X).
Qed.

(** ** Polynomial Gyarfas-Sumner ==> the path-induced rooted-tree row *****)

(*@EDGE from=polynomial_gyarfas_sumner_tree_statement to=path_induced_rooted_tree_polynomial_chi_bound_statement kind=implies status=verified proved=true proof=polynomial_gyarfas_sumner_tree_implies_path_induced_rooted_tree_polynomial_chi_bound cite="gc:e041" note="Corpus relation e041 (confirmed): a graph containing T as an INDUCED subgraph contains a path-induced copy of (T,r), because every path of a tree is induced in it; hence the path-induced-copy-free class is contained in the T-free class and the polynomial bound transfers by poly_chi_bounded_sub. The bridge recorded as missing by the earlier candidate annotation -- two non-consecutive vertices of a path of a FOREST are non-adjacent -- is now foundations/forest_paths.v (forest_run_nonadj), proved from GraphTheory's forestT_unique: a chord would give two distinct irredundant paths between its ends." *)
Theorem polynomial_gyarfas_sumner_tree_implies_path_induced_rooted_tree_polynomial_chi_bound :
  polynomial_gyarfas_sumner_tree_statement ->
  path_induced_rooted_tree_polynomial_chi_bound_statement.
Proof.
move=> PGS T r Tt; have [Tf _] := Tt.
apply: (poly_chi_bounded_sub _ (PGS T Tt)) => G nocopy hind.
apply: nocopy; case: hind => S [iso].
pose phi (u : T) : G := val (bij.bij_fwd iso u).
have phiE u v : (phi u -- phi v) = (u -- v).
  by rewrite /phi -induced_edge edge_diso.
exists phi; split.
- by move=> u v /val_inj /(@bij.bij_injective _ _ iso).
- by move=> u v; rewrite phiE.
move=> p pth uq i j hj hij.
rewrite size_map in hj.
have hi : i < size (r :: p).
  by rewrite /= ltnS; apply: leq_trans (leq_trans (leqnSn i) (ltnW hij)) hj.
have hjj : j < size (r :: p) by exact: hj.
rewrite (nth_map r) // (nth_map r) // phiE.
exact: (@forest_run_nonadj T Tf p r r i j pth uq hj hij).
Qed.

(** ** Candidate edges ****************************************************)





(* cross-package edge every_forest_is_good_statement -> conj2_1605_statement: annotation and proof now live in atlas/theories/conjectures/implications_A1.v or A2.v (wave A1, 2026-09-24) *)

(*@EDGE from=odd_minor_free_defective_clustered_treedepth_statement to=clustered_chromatic_minor_class_treedepth_bound_statement kind=implies status=candidate proved=false cite="gc:e168" note="Corpus relation e168 (confirmed, after the reviewers corrected both extracted statements). BLOCKED SOURCE ENDPOINT: [odd_minor_free_defective_clustered_treedepth_statement] is the wave's blocked placeholder (the odd-minor normalisation and the connected tree-depth convention td-bar are not verified against arXiv:2308.15721), and X194's target uses ordinary tree-depth with the bound 2k-2 rather than the connected tree-depth with k-1. Until the placeholder is re-authored against the paper the edge must not be scheduled: proving it would only validate the guess." *)

Print Assumptions polynomial_gyarfas_sumner_tree_implies_graphs_with_a_forbidden_induced_tree_are_chi_bounded.
Print Assumptions every_forest_is_good_implies_every_forest_is_multibounding.
Print Assumptions every_forest_is_multibounding_implies_graphs_with_a_forbidden_induced_tree_are_chi_bounded.

Print Assumptions forest_free_polynomial_chi_bound_equiv_every_forest_is_good.
Print Assumptions forest_free_polynomial_chi_bound_implies_polynomial_gyarfas_sumner_tree.
Print Assumptions forest_free_polynomial_chi_bound_implies_every_forest_is_multibounding.

Print Assumptions polynomial_gyarfas_sumner_tree_implies_path_induced_rooted_tree_polynomial_chi_bound.
