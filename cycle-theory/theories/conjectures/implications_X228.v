(** * Cycle.conjectures.implications_X228 — wave X228 dependency-graph EDGES

    The corpus relation e174 of [meta/corpus_relations.json] (confirmed, high
    confidence) says that Conjecture 6.1 of arXiv:2511.02892 — the 1/2-flow-pair
    conjecture, [X228.half_flow_pair_statement] — IMPLIES Tutte's 5-flow
    conjecture, [D1.five_flow_statement].  The source's own context gives the
    argument: from a pair (phi_2, phi_4) the combination (5*phi_2 + phi_4)/2 is a
    circular 5-flow, and the flow number of a graph is the ceiling of its
    circular flow number (Goddyn–Tarsi–Zhang), so the graph then has a
    nowhere-zero integer 5-flow.

    As in [implications_D1.v], the edge is proved WITHOUT resolving either
    endpoint and WITHOUT any axiom: the classical circular-to-integer step is
    carried as an EXPLICIT hypothesis ([external_circular_5_flow_statement],
    a [Prop], never [Axiom], never [Admitted]), while the genuine content of the
    reduction — that [5*phi_2 + phi_4] is a Kirchhoff circulation all of whose
    values lie between 2 and 8 in absolute value, i.e. that half of it is a
    nowhere-zero circular 5-flow — is proved here.

    The scaling by two is folded into the external: rather than dividing by two
    in [rat], the external is stated on the INTEGER circulation [chi] with
    [2 <= |chi e| <= 8], which is exactly "[chi/2] is a nowhere-zero circular
    5-flow" ([D1.has_nz_rflow G 5]) written without denominators. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import mgraph sgraph treewidth.
From GTBase Require Import base.
From Cycle.foundations Require Import connectivity.
From Cycle.conjectures Require Import D1 X228.
(* [all_algebra] LAST: [X228.v] re-exports [GTBase.base], which re-exports
   [all_boot]; importing it afterwards would give back [all_boot]'s [%:R] and
   break the [int] ring numerals (cf. the import note of [D1.v]). *)
From mathcomp Require Import all_algebra all_fingroup.

Import GRing.Theory Num.Theory.
(* [Order.TTheory] through the fully qualified path, to disambiguate the two
   in-scope [Order] modules (same idiom as [grounding_D1.v]); it supplies
   [le_trans]. *)
Import mathcomp.order.order.Order.TTheory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope ring_scope.

(** ================================================================= *)
(** ** External circular-to-integer flow duality (cited, NOT [Admitted]) *)

(** External theorem: L. A. Goddyn, M. Tarsi and C.-Q. Zhang, "On (k,d)-colorings
    and fractional nowhere-zero flows", Journal of Graph Theory 28 (1998)
    155-161 (the flow number of a graph is the ceiling of its circular flow
    number).
    Claim: a graph carrying a circular 5-flow — a real-valued Kirchhoff flow
    whose value has absolute value in [1,4] on every edge — has a nowhere-zero
    integer 5-flow. The Prop below states exactly the instance used here, in the
    denominator-free form obtained by scaling by two: if an integer edge
    weighting [chi] of a multigraph is Kirchhoff-conservative at every vertex
    and satisfies [2 <= |chi e| <= 8] on every edge — equivalently, [chi/2] is a
    nowhere-zero circular 5-flow — then the multigraph has a nowhere-zero
    integer 5-flow.
    Not formalized here: it is carried as an explicit hypothesis of the
    conditional edge below (never an [Axiom], never [Admitted]), which is why
    that edge is [status=conditional external=...] rather than [verified]. *)
Definition external_circular_5_flow_statement : Prop :=
  forall (G : mgraph) (chi : edge G -> int),
    iconservative chi ->
    (forall e : edge G, 2%:R <= `|chi e| /\ `|chi e| <= 8%:R) ->
    has_nz_kflow G 5.

(** ================================================================= *)
(** ** The combination [5*phi_2 + phi_4] *)

Section Combination.
Variable (G : mgraph).
Implicit Types phi : edge G -> int.

Definition x228_combine phi2 phi4 (e : edge G) : int := 5%:R * phi2 e + phi4 e.

(** Kirchhoff conservation is preserved by integer linear combinations. *)
Lemma x228_combine_conservative phi2 phi4 :
  iconservative phi2 -> iconservative phi4 -> iconservative (x228_combine phi2 phi4).
Proof.
move=> c2 c4 v; rewrite /x228_combine !big_split /= -!mulr_sumr.
by rewrite c2 c4.
Qed.

End Combination.

(** A nonzero integer has absolute value at least one. *)
Lemma x228_int_ge1 (x : int) : x != 0 -> 1 <= `|x|.
Proof. by rewrite -normr_gt0; case: `|x| => // -[]. Qed.

(** The heart of the reduction: on every edge the combination
    [5*phi_2 + phi_4] has absolute value between 2 and 8.  Where [phi_2]
    vanishes this is the pair condition [2 <= |phi_4|] together with
    [|phi_4| <= 3]; where it does not, [|5*phi_2| = 5] and the triangle
    inequality gives [5 - 3 <= |chi| <= 5 + 3]. *)
Lemma x228_combine_bounds (a b : int) :
  `|a| <= 1 -> `|b| <= 3%:R -> (a = 0 -> 2%:R <= `|b|) ->
  2%:R <= `|5%:R * a + b| /\ `|5%:R * a + b| <= 8%:R.
Proof.
move=> b2 b4 cmp.
have e83 : (8%:R : int) = 5%:R + 3%:R by rewrite -natrD.
have e53 : (5%:R : int) = 2%:R + 3%:R by rewrite -natrD.
case: (eqVneq a 0) => [a0|ne].
- rewrite a0 mulr0 add0r; split; first exact: cmp.
  by apply: le_trans b4 _; rewrite ler_nat.
- have a1 : `|a| = 1 by apply/eqP; rewrite eq_le b2 x228_int_ge1.
  have n5 : `|5%:R * a| = 5%:R :> int by rewrite normrM normr_nat a1 mulr1.
  split; last first.
  + apply: le_trans (ler_normD _ _) _.
    rewrite n5 e83 lerD2l; exact: b4.
  + have h := ler_normD (5%:R * a + b) (- b).
    rewrite addrK normrN n5 in h.
    rewrite -(lerD2r `|b|); apply: le_trans h.
    rewrite e53 lerD2l; exact: b4.
Qed.

(** ================================================================= *)
(** ** The scheduled edge *)

(*@EDGE from=half_flow_pair_statement to=five_flow_statement kind=implies status=conditional external="external_circular_5_flow_statement" proof=half_flow_pair_implies_five_flow cite="gc:e174; Workshop on Cycles and Colourings 2025, arXiv:2511.02892 Conjecture 6.1 and its context; Goddyn-Tarsi-Zhang, On (k,d)-colorings and fractional nowhere-zero flows, J. Graph Theory 28 (1998) 155-161 (flow number = ceiling of circular flow number)" note="From a 1/2-flow-pair (phi2,phi4) the integer circulation chi = 5*phi2 + phi4 satisfies 2 <= |chi| <= 8 on every edge, i.e. chi/2 is a nowhere-zero circular 5-flow; the circular-to-integer step is the cited external hypothesis external_circular_5_flow_statement" *)
Theorem half_flow_pair_implies_five_flow :
  external_circular_5_flow_statement ->
  half_flow_pair_statement -> five_flow_statement.
Proof.
move=> Hext Hpair G Hedge Hbr.
have [phi2 [phi4 [[c2 b2] [c4 b4] cmp]]] := Hpair G Hedge Hbr.
apply: (Hext G (x228_combine phi2 phi4)).
  exact: x228_combine_conservative.
move=> e; rewrite /x228_combine.
by apply: x228_combine_bounds; [exact: b2 | exact: b4 | exact: cmp].
Qed.

(** ** Axiom audit ********************************************************* *)

Print Assumptions x228_combine_conservative.
Print Assumptions x228_int_ge1.
Print Assumptions x228_combine_bounds.
Print Assumptions half_flow_pair_implies_five_flow.
