(** * Chromatic.conjectures.X170 -- v2 oriented-P4 chi-boundedness row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X170 vocabulary ***********************************************)

Definition x170_oriented_P4_code := 'I_8.

Definition x170_nonexceptional (P : {set x170_oriented_P4_code}) : Prop :=
  P != set0 /\ P != [set inord 7] /\ P != [set ord0].

Record x170_oriented_graph := X170OrientedGraph {
  x170_underlying :> sgraph;
  x170_arc : x170_underlying -> x170_underlying -> bool;
  x170_arc_edge : forall u v : x170_underlying, x170_arc u v -> u -- v;
  x170_arc_orients :
    forall u v : x170_underlying, u -- v -> x170_arc u v = ~~ x170_arc v u
}.

Definition x170_p4_edge (i j : 'I_4) : bool :=
  ((val i).+1 == val j) || ((val j).+1 == val i).

Definition x170_code_forward (P : x170_oriented_P4_code) (i : 'I_3) : bool :=
  odd (val P %/ (2 ^ val i)).

Definition x170_induced_oriented_P4
    (O : x170_oriented_graph) (P : x170_oriented_P4_code) : Prop :=
  exists v : 'I_4 -> O,
    injective v /\
    (forall i j : 'I_4, (v i -- v j) = x170_p4_edge i j) /\
    (forall i : 'I_3,
      x170_arc (v (inord (val i))) (v (inord (val i).+1)) =
        x170_code_forward P i).

Definition x170_forb_oriented_P4_family
    (P : {set x170_oriented_P4_code}) (O : x170_oriented_graph) : Prop :=
  forall Q : x170_oriented_P4_code,
    Q \in P -> ~ x170_induced_oriented_P4 O Q.

Definition x170_chi_bounded (C : x170_oriented_graph -> Prop) : Prop :=
  exists f : nat -> nat,
    forall O : x170_oriented_graph,
      C O -> χ([set: x170_underlying O]) <= f (ω([set: x170_underlying O])).

(** ** X170 statements *****************************************************)

(** Corpus row: arxiv:1605.07411#02
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1605.07411__02/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1605.07411__02.json
    English statement: (Aboulker, Bang-Jensen, Bousquet, Charbit, Havet, Maffray and Zamora 2016, Conjecture 5, arXiv:1605.07411)
      For every nonempty set P of orientations of the path on four vertices, other than the two
      exceptional singletons, the class of oriented graphs containing no induced oriented P4 whose
      orientation code lies in P is chi-bounded: some function f bounds chi of the underlying graph
      by f of its clique number.
    Definitions: [x170_oriented_P4_code] - the eight orientation codes of P4 as ['I_8], each bit
      of the code giving the direction of one of the three edges (this file); [x170_nonexceptional
      P] - P is nonempty and is neither of two designated singletons (this file);
      [x170_oriented_graph] - a record bundling a simple graph with an arc relation orienting each
      edge exactly one way (this file); [x170_induced_oriented_P4 O Q] - four distinct vertices
      inducing a P4 with orientation code Q (this file); [x170_forb_oriented_P4_family P] - none of
      the codes in P occurs (this file); [x170_chi_bounded] - chi-boundedness for classes of
      oriented graphs (this file).
    Notes: KNOWN UNFAITHFUL ENCODING, corpus leg blocked. The faithfulness audit of 2026-07-17,
      meta/BLOCKED_RETARGETING_AUDIT.md and the row's verification_note, found the exceptional set
      mis-encoded: the source excludes exactly the two non-chi-bounded singletons, the directed P4
      and the antidirected P4, whereas [x170_nonexceptional] excludes the codes [set inord 7] and
      [set ord0], which under this bit encoding are not those two orientations. The statement is
      therefore FALSE rather than a weaker proxy. Corpus status: the conjecture itself was resolved,
      by Corollary 35 of the source paper together with Cook, Masarik, Pilipczuk, Reinald and Souza
      2023. The body is left untouched here, WP4 changes comments only. *)
Definition oriented_P4_forb_chi_bounded_statement : Prop :=
  forall P : {set x170_oriented_P4_code},
    x170_nonexceptional P ->
    x170_chi_bounded (x170_forb_oriented_P4_family P).
