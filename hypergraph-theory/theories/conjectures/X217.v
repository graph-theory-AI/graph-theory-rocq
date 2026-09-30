(** * Hypergraph.conjectures.X217 -- cops and robbers on hypergraphs rows (wave X217, 2026-09-23) *)

From GTBase Require Export base.
From Hypergraph.foundations Require Export hypergraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The cops-and-robbers vocabulary this wave needs lives in
    [Hypergraph.foundations.hypergraph] ([hg_move], [hg_win], [hg_cop_win],
    [hg_is_cop_number], [hg_uniform], [hg_connected]); it is shared with the
    X225 wave and replaces the per-file copies of "k-uniform" that the
    improvement ledger records.  No local X217 vocabulary is needed. *)

(** ** X217 statements ***************************************************** *)

(** Corpus row: arxiv:2307.15512#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/2307.15512__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/2307.15512__00.json
    English statement: (Erde, Kang, Lehner, Mohar and Schmid 2023, "Catching a robber on a
      random k-uniform hypergraph", Conjecture 1.4)
      There is a positive constant C with the following property.  Let H be a finite
      hypergraph, all of whose hyperedges have exactly k vertices, with k at most the number
      n of vertices of H, and assume H is connected, i.e. any two vertices are joined by a
      chain of vertices in which consecutive ones share a hyperedge.  Let c be the cop number
      of H, that is, the least number of cops that have a winning strategy in the
      cops-and-robbers game on H, where in each round every cop either stays put or walks to
      a vertex sharing a hyperedge with his own, the robber is caught as soon as a cop occupies
      his vertex, and afterwards the robber moves the same way.  Then c squared times k is at
      most C squared times n; equivalently, c is at most C times the square root of n/k.
    Definitions: [hg_uniform E k] - every hyperedge has exactly k vertices
      (hypergraph-theory/theories/foundations/hypergraph.v); [hg_connected E] - any two
      vertices are joined by the reflexive-transitive closure of [hg_link], which holds of two
      vertices lying in a common hyperedge (same file); [hg_move E] - a single move of a
      player: stay put or step to a vertex of a common hyperedge (same file);
      [hg_win E m C r] - the cops placed at [C] catch a robber at [r] within [m] rounds, the
      cops moving first (same file); [hg_cop_win E c] - [c] cops have an initial placement
      and a horizon from which they catch the robber wherever he starts (same file);
      [hg_is_cop_number E c] - [c] cops win and no smaller number of cops does, i.e. [c] is
      the cop number (same file).
    Notes: MODELLING CHOICES.  (1) The game is the finite-horizon cop-win closure on
      positions: [hg_win] is a Boolean fixpoint on the number of remaining rounds, [hg_cop_win]
      existentially quantifies the horizon, so "the cops have a winning strategy" is a purely
      finite, axiom-free predicate (no infinite play, no strategy objects).  The graph-theory-misc
      package carries a structurally identical game on graphs for Meyniel's conjecture.
      (2) Cops move first and catch the robber the instant one of them lands on his vertex
      (the [hg_caught C' r] disjunct inside [hg_win]); the robber then moves along a hyperedge
      or stays.  The cops' positions are a finite function ['I_c -> T], so several cops may
      share a vertex.  (3) [O(sqrt(n/k))] is rendered as a SINGLE absolute constant [C],
      quantified outermost and independent of the hypergraph, of [k] and of [n]; the square
      root is cleared by squaring, giving [c^2 * k <= C^2 * n].  This is the reading the source
      uses when it observes that the conjecture implies Meyniel's conjecture at [k = 2].
      (4) GUARD [k <= #|T|]: an edgeless hypergraph on ONE vertex is vacuously [k]-uniform for
      EVERY [k] and connected, and its cop number is 1, so without this guard the conclusion
      would read [k <= C^2] for all [k] and the statement would be refutable
      (grounding_X217.v, [x217_k_le_n_guard_has_teeth]).  Every hypergraph with at least one
      hyperedge satisfies [k <= n], so the guard removes no genuine k-graph.
      (5) The cop number enters as a HYPOTHESIS [hg_is_cop_number E c] rather than as a
      function: the least [c] with [hg_cop_win E c] exists mathematically (some [c] wins, see
      [hg_cop_win_card]) but is not constructively definable from a [Prop]-valued predicate.
      At most one [c] satisfies the hypothesis, so this is the usual repository pattern
      (compare [x6_matching_number], [x209_is_max_r_cut]). *)
Definition hypergraph_cop_number_sqrt_n_over_k_statement : Prop :=
  exists C : nat,
    0 < C /\
    forall (T : finType) (E : {set {set T}}) (k c : nat),
      0 < k ->
      k <= #|T| ->
      hg_uniform E k ->
      hg_connected E ->
      hg_is_cop_number E c ->
      c ^ 2 * k <= C ^ 2 * #|T|.
