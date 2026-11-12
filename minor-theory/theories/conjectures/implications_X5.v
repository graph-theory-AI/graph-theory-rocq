(** * Minor.conjectures.implications_X5 — corpus-relation edges landing in X5

    Edges of [meta/corpus_relations.json] whose TARGET is an X5 row.  Axiom-free:
    only [Qed]-closed results live here.

    One Rocq-only edge (no corpus relation) follows e045: Dvorak and Yepremyan's
    Conjecture 1 (arxiv:1907.12999#00) is equivalent to the clique minor conjecture
    for bounded independence number
    (studies:std_clique_minor_conjecture_for_bounded_independence).

    e045.  [min_degree_six_max_degree_eight_k6_minor_statement] ⟹
    [six_regular_has_k6_minor_statement].  Pure hypothesis-class containment: a
    6-regular graph has every degree equal to 6, hence minimum degree at least 6
    and maximum degree [Delta G = 6 <= 8], so it lies in the hypothesis class of
    the source row, whose conclusion is verbatim the target's. *)

From GTBase Require Import base.
From GraphTheory Require Import minor.
From Minor.conjectures Require Import X5.
From Minor.foundations Require Import minor_dec.
From mathcomp Require Import zify.
From Stdlib Require Import Lia.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** e045 *****************************************************************)

(** A [d]-regular nonempty graph has maximum degree exactly [d]. *)
Lemma Delta_regular (G : sgraph) (d : nat) :
  0 < #|G| -> regular G d -> Delta G = d.
Proof.
move=> G0 reg; have [x0 Hx0] := eq_bigmax (fun x : G => #|N(x)|) G0.
by rewrite /Delta Hx0 reg.
Qed.

Theorem min_degree_six_max_degree_eight_k6_minor_implies_six_regular_has_k6_minor :
  min_degree_six_max_degree_eight_k6_minor_statement ->
  six_regular_has_k6_minor_statement.
Proof.
move=> src G G0 reg; apply: src => // [v|].
- by rewrite reg.
- by rewrite (Delta_regular G0 reg).
Qed.

(*@EDGE from=min_degree_six_max_degree_eight_k6_minor_statement to=six_regular_has_k6_minor_statement kind=implies status=verified proved=true proof=min_degree_six_max_degree_eight_k6_minor_implies_six_regular_has_k6_minor cite="gc:e045" note="Hypothesis-class containment: a nonempty 6-regular graph has every degree equal to 6, hence minimum degree at least 6 and Delta G = 6 <= 8 (Delta_regular, proved here from eq_bigmax), so the source row applies verbatim and its conclusion is the target's." *)

Print Assumptions Delta_regular.
Print Assumptions min_degree_six_max_degree_eight_k6_minor_implies_six_regular_has_k6_minor.

(** ** Rocq-only: Conjecture 1 (arxiv:1907.12999#00) <=> bounded independence ****)

(** Over every t and every r, both rows say that every graph on n vertices has a
    clique minor on ceil(n / alpha(G)) vertices.
    (=>) Let m = ceil_div n r, so m * r <= n + r - 1.  For m = 0 and m = 1 the K_0
    and K_1 minors suffice (n >= 1 when m = 1).  For m = t + 2, [minor] is
    decidable ([minorNN], Minor.foundations.minor_dec): without a K_(t+2) minor,
    Conjecture 1 at t + 1 gives n <= (t + 1) * alpha(G) <= (t + 1) * r < n.
    (<=) If alpha(G) = 0, G has no vertex and n = 0.  Otherwise the statement at
    r = alpha(G) gives a K_(ceil_div n alpha(G)) minor; if t * alpha(G) < n then
    t + 1 <= ceil_div n alpha(G), and [minor_K_le] gives a K_(t+1) minor. *)

(*@EDGE from=hadwiger_independence_minor_statement to=bounded_independence_clique_minor_statement kind=equiv status=verified proof=hadwiger_independence_minor_equiv_bounded_independence_clique_minor note="Rocq-only edge (no corpus relation), routed after edge-x271 (Lancelot's (697), (698)): Dvorak and Yepremyan's Conjecture 1 (arxiv:1907.12999#00; no K_(t+1) minor gives n <= t * alpha(G)) and the clique minor conjecture for bounded independence number (studies:std_clique_minor_conjecture_for_bounded_independence; alpha(G) <= r gives a K_(ceil(n / r)) minor) both say, over every t and r, that every graph has a clique minor on ceil(n / alpha(G)) vertices. Forward: with m = ceil_div n r, the K_0 and K_1 minors for m <= 1, and for m >= 2 minor's decidability (minorNN) with Conjecture 1 at m - 1. Backward: alpha(G) = 0 empties G; otherwise the statement at r = alpha(G) and minor_K_le." *)
Theorem hadwiger_independence_minor_equiv_bounded_independence_clique_minor :
  hadwiger_independence_minor_statement <-> bounded_independence_clique_minor_statement.
Proof.
have void (x : 'K_0) : False by case: x => m; rewrite ltn0.
have K0 (G : sgraph) : minor G 'K_0
  by exists (fun _ : G => None); split=> [y|y|x y]; case: (void y).
split.
- move=> hi r n G r0 cardG alr.
  rewrite /ceil_div; case: ((n + r - 1) %/ r) (leq_divM (n + r - 1) r) => [|[|t]] le.
  + exact: K0.
  + by apply: minor_K1; rewrite cardG; lia.
  + apply: minorNN => nm.
    have := hi t.+1 n G (ltn0Sn t) cardG nm.
    have := leq_mul (leqnn t.+1) alr.
    lia.
- move=> bi t n G t0 cardG nm.
  have [a0|apos] := posnP α(G).
  + move: a0 => /eqP; rewrite -alphaT alpha_eq0 => /eqP G0.
    by rewrite -cardG -cardsT G0 cards0.
  + rewrite leqNgt; apply/negP => lt.
    apply: nm; apply: minor_K_le (bi _ n G apos cardG (leqnn _)).
    rewrite /ceil_div leq_divRL //; lia.
Qed.

Print Assumptions hadwiger_independence_minor_equiv_bounded_independence_clique_minor.
