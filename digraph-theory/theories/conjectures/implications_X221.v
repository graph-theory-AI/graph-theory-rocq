(** * Digraph.conjectures.implications_X221 — wave X221 implication edges

    The three confirmed [implies] relations of meta/corpus_relations.json whose
    BOTH endpoints now own a Rocq statement:

      - e105 : arxiv:2306.04710#02 ==> arxiv:2202.13306#00
               (hero status of Delta(1,2,2) in {K_1 + P⃗_2}-free digraphs implies
               the same in oriented complete multipartite graphs).
               VERIFIED here by the Qed theorem
               [delta122_hero_k1_plus_dipath2_free_implies_delta122_hero_oriented_complete_multipartite]: an oriented complete
               multipartite digraph has no induced copy of an arc plus an
               isolated vertex, so its class is contained in the source class
               and the single dicolouring bound transfers.
      - e106 : arxiv:2410.23566#03 ==> arxiv:2410.23566#05
               ([conj_9] of conjectures/unvd.v implies
               [kextension_linear_unavoidability_statement]).
               CANDIDATE: the literature argument deletes the k added vertices
               one at a time and applies unvd(E) <= C * unvd(E - v) at each
               step, which over the RELATIONAL [unvd] of conjectures/unvd.v
               needs, for every intermediate digraph, the EXISTENCE of a pinned
               unavoidability value (and its monotone behaviour under vertex
               deletion inside the k-extension). Neither is available from the
               two statements alone, so the edge is recorded, not proved.
      - e158 : arxiv:2403.02298#00 ==> arxiv:2403.02298#01
               (the acyclic-number Theta conjecture implies the dichromatic
               Theta conjecture).
               CANDIDATE: the source's argument goes through the inequality
               t-vec(n) >= n / a-vec(n) and the paper's already-proved upper
               bound t-vec(n) <= (sqrt 2 + o(1)) sqrt(n / log n). Both are
               external inputs (the first is the standard
               chi-vec >= |V| / alpha-vec bound, the second a theorem of the
               paper); neither is formalized, so the edge is recorded, not
               proved. Asserting it with the missing halves as hypotheses would
               smuggle in the conclusion.

    No X216 implication file exists: the only corpus relation touching
    bm:bm-070 is e233 to opg:caccetta_haggkvist_conjecture, whose verdict is
    [related_only] ("neither implies the other"), so no edge is scheduled. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup all_algebra.
From Digraph Require Import prelude interop_graph_theory digraph oriented tournament.
From Digraph Require Import dipath order strong classic_core dichromatic omegabar.
From Digraph Require Import heroes heroes_dichotomy unvd twinwidth twinwidth_ordered.
From GTBase Require Import asymptotics.
From Digraph Require Import X221.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The class bridge for e105

    In an oriented complete multipartite digraph, non-adjacency is transitive,
    so no vertex can be non-adjacent to both ends of an arc: there is no
    induced copy of an arc together with an isolated vertex. *)
Lemma x221_ocm_no_arrow (D : diGraphType) :
  x221_oriented_complete_multipartite D -> no_induced_arrowK2_K1 D.
Proof.
move=> [_ tr] [a [b [c [_ [_ [_ [ab [_ [nacx [ncax [nbcx ncbx]]]]]]]]]]].
have h1 : x221_nonadj a c by rewrite /x221_nonadj nacx ncax.
have h2 : x221_nonadj c b by rewrite /x221_nonadj ncbx nbcx.
by have := tr _ _ _ h1 h2; rewrite /x221_nonadj ab.
Qed.

(*@EDGE from=delta122_hero_k1_plus_dipath2_free_statement to=delta122_hero_oriented_complete_multipartite_statement kind=implies status=verified proof=delta122_hero_k1_plus_dipath2_free_implies_delta122_hero_oriented_complete_multipartite cite="gc:e105" note="Class containment: an oriented complete multipartite digraph has transitive non-adjacency, hence no induced arc-plus-isolated-vertex (K_1 + P_2-directed); so the guarded class of the source is a superclass of the target's and the single dicolouring bound transfers verbatim." *)

Theorem delta122_hero_k1_plus_dipath2_free_implies_delta122_hero_oriented_complete_multipartite :
  delta122_hero_k1_plus_dipath2_free_statement ->
  delta122_hero_oriented_complete_multipartite_statement.
Proof.
move=> [B hB]; exists B => D [ocm df]; apply: hB; split.
- by case: ocm.
- exact: x221_ocm_no_arrow ocm.
- exact: df.
Qed.

(** ** The converse class bridge (the reverse of e105)

    Within ORIENTED digraphs the two class descriptions coincide: if
    non-adjacency were not transitive there would be vertices [u], [v], [w] with
    [u], [v] non-adjacent, [v], [w] non-adjacent and [u], [w] adjacent, which is
    an induced arc plus a vertex non-adjacent to both its ends.  (The degenerate
    equalities are discharged by the adjacency of [u] and [w].) *)
Lemma x221_no_arrow_ocm (D : diGraphType) :
  oriented_dg D -> no_induced_arrowK2_K1 D ->
  x221_oriented_complete_multipartite D.
Proof.
move=> Dor naf.
have arc_neq : forall x y : D, x --> y -> x != y.
  move=> x y xy; apply/eqP => e; rewrite -e in xy.
  by apply: (negP (Dor _ _ xy)).
have key : forall a b c : D, a --> b ->
    ~~ (a --> c) -> ~~ (c --> a) -> ~~ (b --> c) -> ~~ (c --> b) -> False.
  move=> a b c ab nac nca nbc ncb; apply: naf; exists a, b, c.
  have hab : a != b := arc_neq _ _ ab.
  have hac : a != c.
    by apply/eqP => e; rewrite -e in ncb; apply: (negP ncb).
  have hbc : b != c.
    by apply/eqP => e; rewrite -e in nac; apply: (negP nac).
  exact: (conj hab (conj hac (conj hbc (conj ab
            (conj (Dor _ _ ab) (conj nac (conj nca (conj nbc ncb)))))))).
split; first exact: Dor.
move=> u v w; rewrite /x221_nonadj => /andP[nuv nvu] /andP[nvw nwv].
apply/andP; split; apply/negP => harc.
- exact: (key u w v harc nuv nvu nwv nvw).
- exact: (key w u v harc nwv nvw nuv nvu).
Qed.

(*@EDGE from=delta122_hero_oriented_complete_multipartite_statement to=delta122_hero_k1_plus_dipath2_free_statement kind=implies status=verified proof=delta122_hero_oriented_complete_multipartite_implies_delta122_hero_k1_plus_dipath2_free cite="audit: meta/X211-X229_faithfulness_audit.md:178 (corpus e105 is the other direction)" note="Converse class bridge: within oriented digraphs 'no induced arc-plus-isolated-vertex' IMPLIES that non-adjacency is transitive (a non-transitivity witness u,v,w is exactly such an induced pattern), so the two guarded classes are equal and the single dicolouring bound transfers back. Together with the e105 direction the two Props are equivalent; the corpus nevertheless lists the source row disproved and the target row open." *)

Theorem delta122_hero_oriented_complete_multipartite_implies_delta122_hero_k1_plus_dipath2_free :
  delta122_hero_oriented_complete_multipartite_statement ->
  delta122_hero_k1_plus_dipath2_free_statement.
Proof.
move=> [B hB]; exists B => D [Dor naf df]; apply: hB; split=> //.
exact: x221_no_arrow_ocm.
Qed.

(*@EDGE from=conj_9 to=kextension_linear_unavoidability_statement kind=implies status=candidate proved=false cite="gc:e106" note="Literature argument (the target's own context says it 'would follow from Conjecture 9'): delete the k added vertices one at a time and apply unvd(E) <= C * unvd(E-v) at each step, giving unvd(E) <= C^k * unvd(D) <= C^k * c * |V(E)|. Over the RELATIONAL unvd of conjectures/unvd.v this needs, for each intermediate digraph, that an unavoidability value EXISTS and that deleting a vertex of the k-set keeps the digraph acyclic and lands in the chain; neither is derivable from the two Props alone, so the edge is not Qed-closed here." *)

(*@EDGE from=oriented_triangle_free_acyclic_number_theta_statement to=oriented_triangle_free_dichromatic_theta_statement kind=implies status=candidate proved=false cite="gc:e158" note="Source argument: t-vec(n) >= n / a-vec(n) turns the a-vec upper bound into the missing t-vec lower bound, and the matching t-vec upper bound (sqrt 2 + o(1)) sqrt(n/log n) is already proved in arXiv:2403.02298. Both inputs are external to the two statements (the first is the chi-vec >= |V|/alpha-vec bound, the second a theorem of the paper); adding them as hypotheses would smuggle in the conclusion, so the edge stays a candidate." *)

(** ** Print Assumptions audit *)

Print Assumptions x221_ocm_no_arrow.
Print Assumptions delta122_hero_k1_plus_dipath2_free_implies_delta122_hero_oriented_complete_multipartite.
Print Assumptions x221_no_arrow_ocm.
Print Assumptions delta122_hero_oriented_complete_multipartite_implies_delta122_hero_k1_plus_dipath2_free.
