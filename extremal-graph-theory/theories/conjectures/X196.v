(** * Extremal.conjectures.X196 -- v2 Ramsey-nice infinitely often row
      (re-authored 2026-09-23 with the recovered "k-nice" definition, wave X223 pass) *)

From GTBase Require Export base.
From Extremal.conjectures Require Import X195.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Corpus row: arxiv:1708.07369#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1708.07369__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1708.07369__01.json
    English statement: (Aharoni, Alon, Amir, Haxell, Hefetz, Jiang, Kronenberg, Naor 2017,
      arXiv:1708.07369 Conjecture 1.5)
      Let F be a non-empty finite family of graphs, indexed by 'I_r, containing at least one
      forest.  Then for every bound k0 there is some k >= k0 for which F is k-nice, that is,
      F is k-nice for infinitely many k.
    Definitions: [x195_contains_forest Fam] and [x195_k_nice k Fam] - imported from X195.v
      (the recovered k-colour notion: every graph whose chromatic number equals the k-colour
      Ramsey number R_k(F) arrows F in k colours).
    Notes: RE-AUTHORED on 2026-09-23 together with its sibling arxiv:1708.07369#00, whose
      2026-07-16 encoding the 2026-07-17 audit found unfaithful (a k-independent predicate).
      With the recovered, genuinely k-dependent [x195_k_nice] the quantifier "for infinitely
      many k" carries content again; it is rendered in the standard finite form
      "for every k0 there is k >= k0". *)
Definition ramsey_nice_forest_family_infinite_statement : Prop :=
  forall (r : nat) (Fam : 'I_r -> sgraph),
    0 < r ->
    x195_contains_forest Fam ->
    forall k0 : nat,
      exists k : nat, k0 <= k /\ x195_k_nice k Fam.
