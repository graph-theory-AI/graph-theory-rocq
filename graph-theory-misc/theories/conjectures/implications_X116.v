(** * GTMisc.conjectures.implications_X116 -- a Rocq-only EDGE into X116 (the coarse Menger conjecture).

    X39 (studies:std_coarse_menger_conjecture_georgakopoulos_papasogl,
    [coarse_menger_ball_separator_statement]) states the coarse Menger conjecture with the separator radius c * d,
    c depending only on k.  X116 (studies:std_coarse_menger_conjecture,
    [coarse_menger_paths_bounded_separator_statement]) allows any radius l depending on both k and d.  The rows'
    Notes name that difference.  The theorem below records the Rocq-only implication (no corpus relation): X39's
    radius is one choice of X116's l.  Given c for k, take l = c * d + 1.  The paths case is the same proposition
    (both helpers are transparent aliases of [has_k_distant_set_paths]); a set Z with |Z| < k has |Z| <= k - 1;
    and a separating (c * d)-ball meets every simple S-T path ([GTBase.set_separators.seq_separatorP]), so its
    widening to radius c * d + 1 does ([GTBase.balls.set_ball_mono]).
    X116 is disproved at the pin (Nguyen, Scott and Seymour, arXiv:2401.06685v2, Theorem 1.3; CORPUS_FEEDBACK
    item 80), so the edge refutes X39 too, which the corpus still records open.  The edge is whitelisted in
    meta/edge_status_exceptions.json and the status contradiction is CORPUS_FEEDBACK item 100, to report upstream.
    Axiom-free: only [Qed]-closed results, and no helper of its own. *)

From GTBase Require Import base balls set_separators.
From GTMisc.conjectures Require Import X39 X116.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Coarse Menger with radius c * d (X39) ==> coarse Menger with any radius (X116) *)

(*@EDGE from=coarse_menger_ball_separator_statement to=coarse_menger_paths_bounded_separator_statement kind=implies status=verified proof=coarse_menger_ball_separator_implies_coarse_menger_paths_bounded_separator note="Rocq-only edge (no corpus relation), routed after edge-x271b (Lancelot's (718), (719)): the coarse Menger conjecture with separator radius c * d, c depending only on k (X39, studies:std_coarse_menger_conjecture_georgakopoulos_papasogl), implies it with any radius l(k, d) (X116, studies:std_coarse_menger_conjecture). Given c for k, l = c * d + 1: the paths case is the same proposition, |Z| < k gives |Z| <= k - 1, and a separating (c * d)-ball meets every simple S-T path (seq_separatorP), so its widening does (set_ball_mono). X116 is disproved at the pin (arXiv:2401.06685v2, Theorem 1.3; CORPUS_FEEDBACK item 80), so X39 is refuted too while the corpus records it open: whitelisted in meta/edge_status_exceptions.json, CORPUS_FEEDBACK item 100." *)
Theorem coarse_menger_ball_separator_implies_coarse_menger_paths_bounded_separator :
  coarse_menger_ball_separator_statement -> coarse_menger_paths_bounded_separator_statement.
Proof.
move=> cm k d k1 d1; have [c hc] := cm k.
exists (c * d).+1; split=> // G S T.
case: (hc d G S T) => [p|[Z [Zk sep]]]; [by left | right].
exists Z; split; first by rewrite subn1 -ltnS (ltn_predK k1).
move=> p Sp.
have nd := proj2 (seq_separatorP S T _) sep p Sp.
move/negP: nd; rewrite -setI_eq0 => /set0Pn [v]; rewrite inE => /andP [vp vZ].
exists v; split => //; exact: (subsetP (set_ball_mono Z (leqnSn (c * d))) v vZ).
Qed.
