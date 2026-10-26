(** * Extremal.conjectures.X235 -- wave X235: the list Ramsey row arxiv:2103.15175#00 (2026-10-26)

    A one-row wave under the prospective contract of meta/faithfulness_policy.json.  The row's
    statement is the registered, PROVED statement of meta/formal_resolutions.json (2103.15175__00,
    direction prove; theorem Extremal.applications.list_ramsey_graph.list_ramsey_chromatic_resolution),
    moved here with its vocabulary so that the corpus row can cite it: the four definitions below and
    [list_ramsey_chromatic_resolution_statement] keep their names and texts (from
    applications/list_ramsey_nat.v and applications/list_ramsey_graph.v, which now import this file).
    Shared vocabulary: the library chromatic number and [fg_mk_sgraph] (GTBase.finite_graph).  The
    grounding certificates are in grounding_X235.v. *)

From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local vocabulary (moved from the applications files) ***************** *)

(** Valid k-lists: every edge xy of K_n gets the same set of colours in both orientations, as a
    duplicate-free list of k natural numbers (arXiv:2103.15175 l.128, L : E(K_n) -> (N choose k)). *)
Definition lr_nat_valid_lists (V : finType) (k : nat)
    (L : V -> V -> seq nat) : Prop :=
  (forall x y c, (c \in L x y) = (c \in L y x)) /\
  forall x y, x != y -> uniq (L x y) /\ size (L x y) = k.

(** An L-colouring: a symmetric colouring of the edges choosing from the lists (l.128). *)
Definition lr_nat_admissible (V : finType) (L : V -> V -> seq nat)
    (phi : V -> V -> nat) : Prop :=
  (forall x y, phi x y = phi y x) /\
  forall x y, x != y -> phi x y \in L x y.

(** The colour class of colour c: the graph on the vertices of K_n whose edges have colour c. *)
Definition lr_color_graph (V : finType) (C : eqType) (phi : V -> V -> C) (c : C) : sgraph :=
  fg_mk_sgraph (fun x y => phi x y == c).

(** Some valid k-lists on K_n force, in every L-colouring, a colour class of chromatic number
    greater than s (l.298: a monochromatic copy of a graph of chromatic number greater than s). *)
Definition lr_nat_graph_forces (s k n : nat) : Prop :=
  exists L : 'I_n -> 'I_n -> seq nat,
    lr_nat_valid_lists k L /\
    forall phi, lr_nat_admissible L phi ->
      exists c, s < χ([set: lr_color_graph phi c]).

(** ** X235 statement ********************************************************* *)

(** Corpus row: arxiv:2103.15175#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2103.15175__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2103.15175__00.json
    English statement: (arXiv:2103.15175, Fox, He, Luo and Xu, "Multicolor list Ramsey numbers grow
      exponentially", the conjecture after Theorem thm:families)
      For s >= 2, if H_s is the family of graphs with chromatic number greater than s, then
      R_l(H_s, k) = s^k + 1: s^k + 1 is the least n such that some assignment L of k-sets of colours
      to the edges of K_n makes every L-colouring of K_n contain a monochromatic copy of a graph of
      chromatic number greater than s.
    Definitions: [lr_nat_valid_lists k L] - L gives each edge of K_n the same duplicate-free list of
      k natural colours in both orientations; [lr_nat_admissible L phi] - phi is a symmetric
      colouring of the edges choosing from the lists; [lr_color_graph phi c] - the graph on the
      vertices of K_n of the edges of colour c (GTBase [fg_mk_sgraph]); [lr_nat_graph_forces s k n]
      - some valid k-lists on K_n force, in every admissible colouring, a colour class whose
      (library) chromatic number exceeds s (this file).
    Notes: the source is the e-print main.tex of 2103.15175v2 (sha256 568a68a1...): L-colourings and
      the list Ramsey number l.128, R_l of a family l.298, Theorem thm:families (1/e s^k <= R_l(H_s, k)
      <= s^k + 1 for s >= 2) l.300-305, the conjecture "the upper bound in Theorem ... is the truth"
      l.307.  A colour class contains a copy of some graph of chromatic number greater than s iff its
      own chromatic number exceeds s (chi is monotone under subgraphs, and the class is a copy of
      itself), so the class itself is measured.  R_l(H_s, k) = s^k + 1 is encoded as: s^k + 1
      forces, and every forcing order is at least s^k + 1.  The guards 2 <= s and 0 < k mirror the
      source (s >= 2 is stated; k >= 1 is implicit in binom(N, k)).  Either guard alone can be
      dropped (informally: s = 0 or s = 1 with k >= 1, and k = 0 with s >= 1, still satisfy the
      conclusion); both together fail at s = k = 0, where 0 ^ 0 = 1 gives (s ^ k).+1 = 2 while n = 1
      already forces with the empty lists (grounding_X235.v, not_trivially_true; Arthur's correction,
      his (124)).  The statement is PROVED in Extremal.applications.list_ramsey_graph
      (list_ramsey_chromatic_resolution, registered as 2103.15175__00); its name and text are those
      of the registered statement, moved here so that the row can cite it.  The pinned review says
      open; the corpus proves the row. *)
Definition list_ramsey_chromatic_resolution_statement : Prop :=
  forall s k : nat, 2 <= s -> 0 < k ->
    lr_nat_graph_forces s k (s ^ k).+1 /\
    forall n, lr_nat_graph_forces s k n -> (s ^ k).+1 <= n.
