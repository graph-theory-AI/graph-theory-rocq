(** * Extremal.conjectures.X207 -- v2 polynomial Rodl dependence row *)

From GTBase Require Export base.
From GraphTheory Require Import minor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X207 vocabulary ***********************************************)

Definition x207_H_free (H G : sgraph) : Prop := ~ minor G H.

Definition x207_density_at_least (G : sgraph) (a b : nat) : Prop :=
  a * #|G| * #|G| <= b * (2 * fg_edge_count G).

Definition x207_rodl_delta_works (H : sgraph) (d delta_num delta_den : nat) : Prop :=
  0 < delta_num /\ delta_num <= delta_den /\
  forall G : sgraph,
    x207_H_free H G ->
    exists S : {set G},
      #|S| * delta_den >= delta_num * #|G| /\
      (x207_density_at_least (induced S) d 1 \/
       x207_density_at_least (induced S) (1 - d) 1).

Definition x207_polynomial_rodl_delta (H : sgraph) : Prop :=
  exists C e : nat,
    forall d : nat,
      0 < d ->
      exists delta_num delta_den : nat,
        x207_rodl_delta_works H d delta_num delta_den /\
        delta_den <= C * d ^ e + C.

(** Corpus row: arxiv:1803.03588#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1803.03588__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1803.03588__00.json
    English statement: (Chudnovsky, Fox, Scott, Seymour, Spirkl 2018, arXiv:1803.03588, polynomial dependence of delta on d in Rodl's theorem)
      For every graph H there are constants C and e such that for every d > 0 there is a
      rational delta = delta_num/delta_den <= 1 with delta_den <= C * d^e + C and: every graph
      G with no H minor has a vertex set S with delta_den * |S| >= delta_num * |V(G)| whose
      induced subgraph has edge density at least d or at least 1 - d.
    Definitions: [x207_H_free H G] - G has no H minor, the negation of coq-graph-theory's [minor]
      (X207.v); [x207_density_at_least G a b] - a * |V(G)|^2 <= b * 2|E(G)|, i.e. the edge
      density is at least a/b (X207.v); [x207_rodl_delta_works H d dnum dden] - the
      linear-size-subset property above (X207.v); [x207_polynomial_rodl_delta H] - the
      polynomial bound on the denominator (X207.v); [fg_edge_count] - GTBase.
    Notes: this row is recorded as BLOCKED. The 2026-07-17 faithfulness audit
      (meta/BLOCKED_RETARGETING_AUDIT.md) found the body TRIVIALLY TRUE and broken on three
      independent fronts: (i) Rodl's theorem asks for an induced subgraph that is eps-SPARSE
      (density at most eps) or eps-DENSE (density at least 1-eps), but both disjuncts here are
      LOWER bounds; (ii) the second disjunct uses the nat subtraction 1 - d, which is 0 for
      every d >= 1, so it reduces to 0 <= 2|E| and holds for every S; (iii) the parameter d is
      a natural standing for a density in (0,1), which no natural other than 0 can be. Also
      [x207_H_free] uses MINOR-freeness where the source means INDUCED-subgraph-freeness. WRONG
      OBJECT and vacuous (ledger). *)
Definition polynomial_rodl_dependence_statement : Prop :=
  forall H : sgraph, x207_polynomial_rodl_delta H.
