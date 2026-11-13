(** * Packing.conjectures.implications_X5 -- a Rocq-only EDGE between X5 and U9 (Tuza's conjecture).

    X5 (erdos:167, [triangle_packing_transversal_statement]) and U9's row
    opg:triangle_packing_vs_triangle_edge_transversal
    ([triangle_packing_vs_triangle_edge_transversal_statement]) both state Tuza's conjecture: a graph with no
    k + 1 pairwise edge-disjoint triangles has 2k edges meeting every triangle.  X5's Notes call it U9's
    Erdos-numbered twin; the encodings differ only in the packing (a repetition-free list in X5, a set in U9) and
    in the transversal (genuine edges in X5, any two-element vertex sets in U9).  The theorem below records that
    the two are equivalent (Rocq-only: no corpus relation).
    X5 => U9: a repetition-free list has as many members as the set of its members ([card_uniqP]), so U9's packing
    bound gives X5's, and X5's transversal serves as U9's.  U9 => X5: [enum P] turns a set packing into a
    repetition-free list ([enum_uniq], [cardE]), so X5's bound gives U9's; then [S :&: E(G)] is a set of edges of
    size at most #|S| that still meets every triangle, since a pair inside a clique is an edge
    ([raw_pairs_cliqueE]).
    Axiom-free: only [Qed]-closed results, and no helper of its own. *)

From GTBase Require Export base.
From GTBase Require Import triangles.
From Packing.conjectures Require Import X5 U9.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Tuza's conjecture: the list encoding (X5) <=> the set encoding (U9) *)

(*@EDGE from=triangle_packing_transversal_statement to=triangle_packing_vs_triangle_edge_transversal_statement kind=equiv status=verified proof=triangle_packing_transversal_equiv_triangle_packing_vs_triangle_edge_transversal note="Rocq-only edge (no corpus relation), routed by Lancelot's (729), (730): the two encodings of Tuza's conjecture in packing-theory, erdos:167 (X5: a repetition-free list of pairwise edge-disjoint triangles, a transversal of genuine edges) and opg:triangle_packing_vs_triangle_edge_transversal (U9: a set packing, a transversal of any two-element vertex sets); X5's Notes call them twins. Forward: the set of a repetition-free list's members has its size (card_uniqP), and X5's transversal serves U9. Backward: enum P is a repetition-free list of P's members, and S :&: E(G) is a transversal of genuine edges, since a pair inside a clique is an edge (raw_pairs_cliqueE). Both rows are open." *)
Theorem triangle_packing_transversal_equiv_triangle_packing_vs_triangle_edge_transversal :
  triangle_packing_transversal_statement <->
  triangle_packing_vs_triangle_edge_transversal_statement.
Proof.
split=> [x5 k G hP | u9 G k hk].
- have [|F [[_ hF] cF]] := x5 G k.
    move=> ts [uts [tts dts]].
    have -> : size ts = #|[set T in ts]| by rewrite cardsE; apply/esym/card_uniqP.
    apply: hP => [T|T1 T2]; rewrite ?inE => *; [exact: tts | exact: dts].
  exists F; split=> // T tT.
  by have [e [eF eT]] := hF T tT; exists e.
- have [|S [cS hS]] := u9 k G.
    move=> P tP dP; rewrite cardE; apply: hk; split; first exact: enum_uniq.
    by split=> [T|T U]; rewrite !mem_enum => *; [exact: tP | exact: dP].
  exists (S :&: E(G)); split; last by apply: leq_trans cS; apply: subset_leq_card; exact: subsetIl.
  split=> [|T [cT T3]]; first exact: subsetIr.
  have [e eT eS] := hS T (conj cT T3); exists e; split=> //.
  have eT' : e \in raw_pairs T := eT.
  move: eT'; rewrite (raw_pairs_cliqueE cT) !inE eS.
  by case/andP=> ->.
Qed.
