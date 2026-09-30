(** * Topological.conjectures.X202 -- v2 genus cop-number asymptotic row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X202 vocabulary ***********************************************)

Definition x202_cop_position (G : sgraph) (cops : nat) := 'I_cops -> G.

Definition x202_captured (G : sgraph) (cops : nat)
    (C : x202_cop_position G cops) (r : G) : bool :=
  [exists i : 'I_cops, C i == r].

Definition x202_cop_move (G : sgraph) (cops : nat)
    (C C' : x202_cop_position G cops) : Prop :=
  forall i : 'I_cops, (C i == C' i) || (C i -- C' i).

Definition x202_robber_move (G : sgraph) (r r' : G) : Prop :=
  (r == r') || (r -- r').

Fixpoint x202_cops_win_in (G : sgraph) (cops t : nat)
    (C : x202_cop_position G cops) (r : G) {struct t} : Prop :=
  x202_captured C r \/
  if t is t'.+1 then
    exists C' : x202_cop_position G cops,
      x202_cop_move C C' /\
      forall r' : G, x202_robber_move r r' -> x202_cops_win_in t' C' r'
  else False.

Definition x202_cop_number_at_most (G : sgraph) (cops : nat) : Prop :=
  exists (t : nat) (C0 : x202_cop_position G cops),
    forall r0 : G, x202_cops_win_in t C0 r0.

Definition x202_genus_cop_number_at_most (g cops : nat) : Prop :=
  forall G : sgraph, surface_embeddable g G -> x202_cop_number_at_most G cops.

Definition x202_cop_number_genus_window (g eps_num eps_den : nat) : Prop :=
  exists cops : nat,
    x202_genus_cop_number_at_most g cops /\
    eps_den * cops * cops <= (eps_den + eps_num) * g.+1.

(** ** X202 statements *****************************************************)

(** Corpus row: arxiv:1710.11281#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1710.11281__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1710.11281__00.json
    English statement: (Mohar 2017, arXiv:1710.11281, "Conjecture 8")
      Corpus claim: c(g) = g^(1/2 + o(1)) and ec(g) = g^(1/2 + o(1)), i.e. for every eps > 0
      there is g0 such that for all g >= g0 both the orientable cop number c(g) and the
      non-orientable cop number ec(g) lie strictly between g^(1/2 - eps) and g^(1/2 + eps).
      Back-translation of the Rocq body: for every rational eps = eps_num/eps_den with
      0 < eps_num <= eps_den there is a g0 such that for every g >= g0 some number of cops
      suffices to catch the robber on EVERY graph embeddable with Euler genus at most g and
      satisfies eps_den * cops^2 <= (eps_den + eps_num) * (g + 1).
    Definitions: [x202_cop_position], [x202_captured], [x202_cop_move], [x202_robber_move],
      [x202_cops_win_in] - the standard finite cops-and-robbers game: cops occupy vertices,
      each move keeps or slides each cop along an edge, the robber likewise, and the cops win
      within t rounds against every robber reply (this file); [x202_cop_number_at_most G cops]
      - some initial cop placement wins within some finite number of rounds from every robber
      start (this file); [x202_genus_cop_number_at_most g cops] - that holds for every graph
      embeddable with Euler genus at most g (this file); [x202_cop_number_genus_window] - the
      existential window above (this file); [surface_embeddable g G] - G admits a rotation
      system of Euler genus at most g (base/theories/surface.v).
    Notes: BLOCKED - recorded by the 2026-07-17 faithfulness audit
      (meta/BLOCKED_RETARGETING_AUDIT.md).  The two-sided asymptotic is rendered as a
      ONE-SIDED inequality: [x202_cop_number_genus_window] only asserts the existence of a
      cop count that suffices and is small, so the g^(1/2 - eps) LOWER bound is dropped
      entirely.  What remains is moreover not the conjectured upper bound but a stronger one:
      letting eps tend to 0 the body yields limsup c(g)^2/(g+1) <= 1, i.e.
      c(g) <= sqrt(g+1) * (1 + o(1)), whereas the conjecture only claims g^(1/2 + o(1)).  The
      non-orientable half ec(g) is not encoded at all: [surface_embeddable] is the ORIENTABLE
      rotation-system Euler genus of base/theories/surface.v, and the signed layer
      (topological-graph-theory/theories/foundations/signed_embedding.v) is not used.
      Finally the game is played on each graph separately with an arbitrary finite horizon,
      which is the usual finite cop-number notion.
      V counts every vertex including isolated ones (base fix 2026-09-23): the old count saw
      only the vertices carrying a dart, so the Euler count overstated the genus of every
      graph with an isolated vertex and this hypothesis admitted fewer graphs than intended. *)
Definition genus_cop_number_sqrt_asymptotic_statement : Prop :=
  forall eps_num eps_den : nat,
    0 < eps_num ->
    eps_num <= eps_den ->
    exists g0 : nat,
      forall g : nat,
        g0 <= g ->
        x202_cop_number_genus_window g eps_num eps_den.
