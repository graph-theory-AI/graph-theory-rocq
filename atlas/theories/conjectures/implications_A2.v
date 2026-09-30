(** * Atlas.conjectures.implications_A2 -- cross-package edges with a [Digraph] endpoint

    Same role as [implications_A1.v] for the relations whose one endpoint
    lives in [digraph-theory].  That package's prelude imports
    [mathcomp-classical] ([boolp]); the statements themselves are axiom-free
    but NO [boolp] / [classical_sets] lemma may be used in a proof here
    (every theorem must print "Closed under the global context"). *)

From GTBase Require Import base.
From Chromatic.conjectures Require Import U8 X218.
From Cycle.conjectures Require Import X9.
From Digraph.conjectures Require Import chi_bounded classic_core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Recorded dispositions (wave A2; re-read in wave A1, 2026-09-24: no edge provable within budget) *)

(*@EDGE from=conj2_1605_statement to=graphs_with_a_forbidden_induced_tree_are_chi_bounded_statement kind=equiv status=candidate proved=false cite="gc:e010" note="BLOCKED (re-read 2026-09-24): conj2_1605 is encoded on ORIENTED graphs (ind_free H G for an oriented H, chi/omega of the underlying graph), while the corpus argument reads the paper's Conjecture 2 as a statement on undirected H. (=>) conj2 -> Gyarfas-Sumner is elementary (orient a T-free graph by enum_rank; it then has no induced copy of any orientation H of T, so the if half of conj2 applies; needs only the sgraph -> diGraphType orientation bridge of interop_graph_theory.v), but (<=) fails to follow: the if half of conj2 for an oriented forest H does not follow from Gyarfas-Sumner (an oriented G avoiding H may contain U(H) induced with another orientation; this oriented version is open and stronger), and the only-if half (underlying H with a cycle => not chi-bounded) needs Erdos' high-girth high-chromatic graphs, not in the repo. Possible encoding issue in digraph-theory chi_bounded.v to be checked against arXiv:1605.07411 Conjecture 2." *)
(*@EDGE from=every_forest_is_good_statement to=conj2_1605_statement kind=implies status=candidate proved=false cite="gc:e170" note="BLOCKED (re-read 2026-09-24): the target is a biconditional on ORIENTED graphs. Its if half (oriented H with forest underlying graph => oriented-H-free class chi-bounded) does not follow from polynomial chi-boundedness of U(H)-free undirected graphs, because an oriented G avoiding H may contain U(H) induced with another orientation; its only-if half needs Erdos' high-girth high-chromatic graphs (not in the repo)." *)
(*@EDGE from=proper_edge_coloured_short_cycle_statement to=caccetta_haggkvist_statement kind=implies status=candidate proved=false cite="gc:e099" note="BLOCKED by budget (re-read 2026-09-24; the reduction is elementary and in-paper, so the edge is provable in principle): a loopless digraph with a digon has a 2-dicycle and ceil(n/r) >= 2 since r <= outdeg <= n-1; otherwise colour each edge of the underlying sgraph by enum_rank of its tail (col : {set G} -> I_n, x9_colour_classes_large from outdeg >= r), and the missing lemma is: a ucycle of the underlying graph whose incident edges get distinct tail colours is consistently oriented (each vertex is the tail of exactly one of its two cycle edges), hence it or its reversal is a dicycle of classic_core (core/dipath.v) of the same size, with ceil_div n r = (n + r - 1) %/ r. Estimated well above the 40k-token A2 budget (seq/ucycle orientation bookkeeping)." *)
