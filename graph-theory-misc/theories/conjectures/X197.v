(** * GTMisc.conjectures.X197 -- v2 planar cops capture time row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X197 vocabulary ***********************************************)

Definition x197_cop_position (G : sgraph) (cops : nat) := 'I_cops -> G.

Definition x197_captured (G : sgraph) (cops : nat)
    (C : x197_cop_position G cops) (r : G) : bool :=
  [exists i : 'I_cops, C i == r].

Definition x197_cop_move (G : sgraph) (cops : nat)
    (C C' : x197_cop_position G cops) : Prop :=
  forall i : 'I_cops, (C i == C' i) || (C i -- C' i).

Definition x197_robber_move (G : sgraph) (r r' : G) : Prop :=
  (r == r') || (r -- r').

Fixpoint x197_cops_win_in (G : sgraph) (cops t : nat)
    (C : x197_cop_position G cops) (r : G) {struct t} : Prop :=
  x197_captured C r \/
  if t is t'.+1 then
    exists C' : x197_cop_position G cops,
      x197_cop_move C C' /\
      forall r' : G, x197_robber_move r r' -> x197_cops_win_in t' C' r'
  else False.

Definition x197_capture_time (G : sgraph) (cops : nat) (t : nat) : Prop :=
  exists C0 : x197_cop_position G cops,
    (forall r0 : G, x197_cops_win_in t C0 r0) /\
    forall t' : nat, t' < t -> exists r0 : G, ~ x197_cops_win_in t' C0 r0.

(** ** X197 statements *****************************************************)

(** Corpus row: arxiv:1709.09050#02
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1709.09050__02/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1709.09050__02.json
    English statement: (Bonato and Mohar 2017, "Topological directions in Cops and Robbers",
      question on the tightness of the linear capture-time bound)
      For every n0 there are a planar finite simple graph G with at least n0 vertices and a
      number t > |V(G)| such that some starting position of three cops catches every robber
      within t rounds and, for every t' < t, that same starting position fails to catch some
      robber within t' rounds.
    Definitions: [x197_cop_position G cops] - a placement of the cops, a map from cop indices
      to vertices (this file); [x197_captured C r] - some cop occupies the robber's vertex
      (this file); [x197_cop_move] / [x197_robber_move] - each cop, resp. the robber, stays put
      or moves to an adjacent vertex (this file); [x197_cops_win_in t C r] - from position C
      against a robber at r, the cops capture within t rounds, the robber moving adversarially
      (this file); [x197_capture_time G cops t] - some starting position wins in t rounds and
      in no fewer (this file); [wagner_planar] - combinatorial Wagner planarity (GTBase).
    Notes: KNOWN UNFAITHFUL, row leg is blocked (faithfulness audit 2026-07-17,
      meta/BLOCKED_RETARGETING_AUDIT.md).  The minimality clause of [x197_capture_time] is
      relative to the FIXED starting position C0 that the existential just chose, whereas the
      capture time capt_3(G) is the minimum over all starting positions of the number of rounds
      needed against the worst robber.  A deliberately bad starting position therefore
      witnesses a large t, so the statement is strictly weaker than "there is a planar graph
      with capt_3(G) > |V(G)|" and does not express the tightness question.  Recorded in
      meta/STATEMENT_IMPROVEMENTS.md. *)
Definition planar_cops_capture_time_linear_tight_statement : Prop :=
  forall n0 : nat,
    exists (G : sgraph) (t : nat),
      [/\ n0 <= #|G|, wagner_planar G, #|G| < t & x197_capture_time G 3 t].
