(** * Chromatic.conjectures.implications_X213 -- dependency-graph EDGES for wave X213.

    Machine-checked implication edges between the X213 statements and the
    statements already committed in this package.  Every SCHEDULED edge is a
    RELATIVE theorem: a [Qed]-closed [Theorem A -> B] proved WITHOUT resolving
    either endpoint.  The file is axiom-free: no [Axiom] / [Parameter] /
    [Admitted] / [Conjecture].  Candidate edges carry the obstruction that stops
    them from closing, in the annotation's [note].

    The [cite="gc:eNNN"] fields point at the upstream corpus relations of
    [meta/corpus_relations.json] (rebuild it with [meta/build_corpus_relations.py]
    after this wave's manifest regeneration, so that the new formal names reach
    the relation endpoints). *)

From GTBase Require Import base.
From Chromatic.conjectures Require Import U1 U8 X213.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** A triangle-free graph has clique number at most two *****************)

Lemma x213_triangle_free_omega (G : sgraph) :
  triangle_free G -> ω([set: G]) <= 2.
Proof.
move=> tf; case: omegaP => K KM.
rewrite leqNgt; apply/negP => /card_gt2P [x [y [z [[xK yK zK] [xy yz zx]]]]].
have cl := maxclique_clique KM.
by apply: (tf x y z); apply: cl.
Qed.

(** ** Gyarfas-Sumner ==> the triangle-free induced-tree bound *************)

(*@EDGE from=graphs_with_a_forbidden_induced_tree_are_chi_bounded_statement to=triangle_free_induced_tree_chi_bounded_statement kind=implies status=verified proved=true proof=graphs_with_a_forbidden_induced_tree_are_chi_bounded_implies_triangle_free_induced_tree_chi_bounded cite="gc:e229" note="Corpus relation e229 (confirmed): Gyarfas-Sumner implies Bondy-Murty A.50. Under the U8 encoding the derivation is elementary: a triangle-free graph has clique number at most two, so the chi-bounding function f of the T-free class is only ever evaluated at 0, 1 or 2, and the sum of those three values is a uniform bound, which is what the A.50 statement asks for." *)
Theorem graphs_with_a_forbidden_induced_tree_are_chi_bounded_implies_triangle_free_induced_tree_chi_bounded :
  graphs_with_a_forbidden_induced_tree_are_chi_bounded_statement ->
  triangle_free_induced_tree_chi_bounded_statement.
Proof.
move=> GS T Ttree; have [f Hf] := GS T Ttree.
exists (f 0 + f 1 + f 2) => G tf nind.
apply: leq_trans (Hf G nind) _.
have w2 : ω([set: G]) <= 2 by exact: x213_triangle_free_omega.
move: w2; case: (ω([set: G])) => [|[|[|k]]] //= _.
- by rewrite -addnA leq_addr.
- by apply: leq_trans (leq_addl _ _) (leq_addr _ _).
- by rewrite leq_addl.
Qed.

(** ** Erdos-Lovasz Tihany ==> the double-critical graph conjecture ********
    The edge is VERIFIED and lives in [implications_U1.v], whose wave owns the
    target row [double_critical_graph_statement]; see the annotation there. *)


Print Assumptions graphs_with_a_forbidden_induced_tree_are_chi_bounded_implies_triangle_free_induced_tree_chi_bounded.
