(** * Extremal.conjectures.X58 -- v2 epsilon-bounded pure pair row *)

From GTBase Require Export base.
From GTBase Require Import set_pairs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X58 vocabulary ************************************************)

Definition x58_anticomplete (G : sgraph) (A B : {set G}) : Prop :=
  anticomplete A B.

Definition x58_induced_free (G H : sgraph) : Prop :=
  induced_free G H.

Definition x58_epsilon_bounded
    (G : sgraph) (eps_num eps_den : nat) : Prop :=
  eps_den * Delta G < eps_num * #|G|.

(** Corpus row: arxiv:1810.00058#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1810.00058__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1810.00058__00.json
    English statement: (Chudnovsky, Fox, Scott, Seymour, Spirkl 2018, arXiv:1810.00058 Conjecture 1.4)
      For every graph H there is a positive rational eps = eps_num/eps_den <= 1 such that every
      graph G on more than one vertex with no induced copy of H whose maximum degree satisfies
      eps_den * Delta(G) < eps_num * |V(G)| has two anticomplete vertex sets A and B with
      |A| >= eps * |V(G)|^eps and |B| >= eps * |V(G)|.
    Definitions: [x58_anticomplete G A B] - A and B are disjoint with no edge between them (X58.v);
      [x58_induced_free G H] - no vertex set of G induces a copy of H (X58.v);
      [x58_epsilon_bounded G eps_num eps_den] - the maximum degree is below eps * |V(G)|
      (X58.v); [Delta] - maximum degree (GTBase).
    Notes: DISCREPANCY: the source asks for an anticomplete (eps|G|, eps|G|)-pair, i.e. BOTH sides
      of linear size. The Rocq body bounds B linearly but bounds A only by the cross-multiplied
      power inequality eps_num^eps_den * |G|^eps_num <= eps_den^eps_den * |A|^eps_den, which
      reads |A| >= eps * |G|^eps - a sublinear bound whenever eps < 1. The statement is
      therefore weaker than the source on the A side (ledger). The corpus records the row as
      PARTIAL. *)
Definition epsilon_bounded_h_free_anticomplete_pair_statement : Prop :=
  forall H : sgraph,
    exists eps_num eps_den : nat,
      0 < eps_num /\ eps_num <= eps_den /\
      forall G : sgraph,
        1 < #|G| ->
        x58_induced_free G H ->
        x58_epsilon_bounded G eps_num eps_den ->
        exists A B : {set G},
          x58_anticomplete A B /\
          eps_num ^ eps_den * #|G| ^ eps_num <= eps_den ^ eps_den * #|A| ^ eps_den /\
          eps_num * #|G| <= eps_den * #|B|.

(* Correction (2026-10-26, Marc's decision), kept outside the frozen doc block above: the
   DISCREPANCY note is withdrawn. arXiv:1810.00058 Conjecture 1.4 asks for an anticomplete
   (eps|G|^eps, eps|G|)-pair in every H-free eps-bounded graph, which is this body; eps-bounded is
   spelled here as Delta(G) < eps|G|, equivalent to the paper's |N[v]| < eps|G| up to eps; the
   corpus statement_text lost the exponent in PDF extraction. Both sides linear holds exactly for
   forests H (Pure pairs I, arXiv:1809.00919, Theorem 1.4 and the remark after it). PARTIAL is the
   upstream review's status, not an encoding defect. See meta/STATEMENT_IMPROVEMENTS.md and
   meta/CORPUS_FEEDBACK.md item 13. *)
