(** * Chromatic.conjectures.X162 -- v2 WSK triangular-lattice Kempe row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X162 vocabulary ***********************************************)

Definition x162_tri_rel (m n : nat) : rel ('I_m * 'I_n) :=
  fun p q =>
    [|| ((val p.1).+1 %% m == val q.1) && (p.2 == q.2),
        (p.1 == q.1) && ((val p.2).+1 %% n == val q.2)
      | ((val p.1).+1 %% m == val q.1) &&
        ((val p.2 + n.-1) %% n == val q.2)].

Definition x162_periodic_triangular_lattice (m n : nat) : sgraph :=
  @fg_mk_sgraph ('I_m * 'I_n)%type (@x162_tri_rel m n).

Definition x162_proper_colouring (G : sgraph) (q : nat) (col : G -> 'I_q) : Prop :=
  forall x y : G, x -- y -> col x != col y.

Definition x162_uses_only_two_colours
    (G : sgraph) (q : nat) (col : G -> 'I_q) (a b : 'I_q) (S : {set G}) : Prop :=
  forall v : G, v \in S -> (col v == a) || (col v == b).

Definition x162_swap_colour (q : nat) (a b c : 'I_q) : 'I_q :=
  if c == a then b else if c == b then a else c.

Definition x162_kempe_step (G : sgraph) (q : nat) (col col' : G -> 'I_q) : Prop :=
  exists (a b : 'I_q) (S : {set G}),
    [/\ a != b,
        connected S,
        x162_uses_only_two_colours col a b S &
        forall v : G,
          col' v = if v \in S then x162_swap_colour a b (col v) else col v].

Inductive x162_kempe_reachable
    (G : sgraph) (q : nat) : (G -> 'I_q) -> (G -> 'I_q) -> Prop :=
| x162_kempe_refl col : @x162_kempe_reachable G q col col
| x162_kempe_trans col1 col2 col3 :
    @x162_kempe_step G q col1 col2 ->
    @x162_kempe_reachable G q col2 col3 ->
    @x162_kempe_reachable G q col1 col3.

Definition x162_kempe_class_for_q (G : sgraph) (q : nat) : Prop :=
  forall col1 col2 : G -> 'I_q,
    x162_proper_colouring col1 ->
    x162_proper_colouring col2 ->
    @x162_kempe_reachable G q col1 col2.

(** ** X162 statements *****************************************************)

(** Corpus row: arxiv:1510.06964#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1510.06964__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1510.06964__00.json
    English statement: (Bonamy, Bousquet, Feghali and Johnson 2016, open case q = 5 of the WSK algorithm, arXiv:1510.06964)
      For all m, n > 0, any two proper 5-colourings of the periodic triangular lattice on m by n
      vertices are connected by a finite sequence of Kempe steps, each step swapping two colours on
      a connected vertex set using only those two colours; that is, the 5-colourings of the
      triangular lattice with periodic boundary conditions form a single Kempe class, which is the
      validity of the Wang-Swendsen-Kotecky algorithm for q = 5.
    Definitions: [x162_periodic_triangular_lattice m n] - the graph on ['I_m * 'I_n] with the
      three triangular-lattice adjacencies taken modulo m and n, i.e. periodic boundary conditions
      (this file); [x162_kempe_step col col'] - there are two distinct colours and a connected
      vertex set carrying only those two colours such that col' swaps them on that set and agrees
      with col elsewhere (this file); [x162_kempe_reachable] - the reflexive-transitive closure of
      Kempe steps (this file); [x162_kempe_class_for_q G q] - any two proper q-colourings are Kempe-
      reachable (this file); [x162_proper_colouring] (this file).
    Notes: KNOWN UNFAITHFUL ENCODING, corpus leg blocked. The faithfulness audit of 2026-07-17,
      meta/BLOCKED_RETARGETING_AUDIT.md and the row's verification_note, found the statement
      TRIVIALLY TRUE for every finite graph and every q, so that the lattice, the periodic boundary
      conditions and q = 5 are decorative. The defect is in [x162_kempe_step]: it asks only that S
      be connected and two-coloured, not that S be a whole Kempe component of the two colour
      classes, and the resulting colouring is not required to be proper, so arbitrary recolourings
      are reachable. The body is left untouched here, WP4 changes comments only. *)
Definition wsk_triangular_lattice_q5_kempe_class_statement : Prop :=
  forall m n : nat,
    0 < m -> 0 < n ->
    x162_kempe_class_for_q (x162_periodic_triangular_lattice m n) 5.
