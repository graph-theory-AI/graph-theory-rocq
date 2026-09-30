(** * Extremal.foundations.degree_bounds -- maximum degree vs closed neighbourhoods

    Wave V (2026-09-24).  One reusable step, extracted from the inline proof of
    the gc:e076 edge in [Extremal.conjectures.implications_X223]: an upper bound
    on every CLOSED neighbourhood of [G] is an upper bound on [Delta G], because
    [Delta G = |N(x)|] for some [x] and [N(x)] is a proper subset of [N[x]].

    Two corpus rows spell eps-boundedness differently -- X223 with the closed
    neighbourhood ([d * |N[v]| < p * |V(G)|] for every [v]) and X58 with the
    maximum degree ([d * Delta(G) < p * |V(G)|]) -- and the edge between them
    needs exactly this implication.  The lemma mentions only library / GTBase
    vocabulary ([Delta], [N(_)], [N[_]]), so it belongs in [foundations/]; the
    named bridge between the two conjecture-file predicates lives in
    [implications_X223.v], which may import the conjecture files.

    Axiom-free: no Axiom/Parameter/Admitted. *)

From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** If every closed neighbourhood of a non-empty [G] satisfies
    [d * |N[v]| < p * |V(G)|], then so does the maximum degree. *)
Lemma Delta_lt_of_cln_lt (G : sgraph) (p d : nat) :
  0 < #|G| ->
  (forall v : G, d * #|N[v]| < p * #|G|) ->
  d * Delta G < p * #|G|.
Proof.
move=> G0 H.
have [x0 Hx0] := eq_bigmax (fun x : G => #|N(x)|) G0.
rewrite /Delta Hx0.
apply: leq_ltn_trans (H x0).
rewrite leq_mul2l; apply/orP; right; apply: ltnW.
exact: proper_card (opn_proper_cln x0).
Qed.

Print Assumptions Delta_lt_of_cln_lt.
