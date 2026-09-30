(** * GTMisc.conjectures.X217 -- cops and robbers rows (wave X217, 2026-09-23) *)

From GTBase Require Export base.
From GTMisc.foundations Require Export cops.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The whole cops-and-robbers vocabulary of this wave lives in
    [GTMisc.foundations.cops] (shared with the hypergraph-theory half of X217);
    this file adds no local vocabulary. *)

(** ** X217 statements *****************************************************)

(** Corpus row: others:meyniels-conjecture
    Site: https://graph-theory-ai.github.io/graph-conjectures/others/meyniels-conjecture/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/others_reviews/meyniels-conjecture.json
    English statement: (Meyniel 1985, reported by Frankl 1987; Meyniel's conjecture on the
      cop number)
      There is one constant C, chosen before the graph, such that in every connected finite
      simple graph G with at least one vertex some number j of cops with j at most C times
      the least integer whose square is at least the number of vertices of G have a winning
      strategy in the Cops and Robbers game on G: the j cops have a starting placement from
      which, whatever vertex the robber starts on and however he answers, they capture him
      after finitely many rounds, the two sides alternating, cops first, each piece either
      staying put or moving to an adjacent vertex.
    Definitions: [cop_number_le G k] - some j at most k such that j cops win on G, i.e. the
      cop number of G is at most k (GTMisc foundations/cops.v); [cops_win G j] - the j cops
      capture after finitely many rounds, [exists t, cops_win_within G j t] (same file);
      [cops_win_within G j t] - some starting placement of the j cops captures every robber
      start within t cop moves, a boolean predicate over the finite types
      [{ffun 'I_j -> G}] and [G] (same file); [cops_capture], [cop_move], [robber_move],
      [captured] - one round of the game and the capture test (same file); [sqrt_ceil n] -
      the least s with n <= s^2, i.e. the integer square root rounded up (GTBase
      asymptotics.v); [connected] (coq-graph-theory connectivity.v).
    Notes: modelling choices.  (1) FINITE HORIZON.  "k cops have a winning strategy" is
      formalised as "there is a round bound t such that, from one starting placement, the
      cops force a capture within t cop moves against every robber start and every robber
      answer".  For a fixed t this is a decidable boolean predicate (all quantifiers range
      over the finite types [{ffun 'I_k -> G}] and [G]) and it is monotone in t
      ([cops_capture_mono]), so the existential over t is exactly the standard winning
      condition "a cop occupies the robber's vertex after finitely many rounds"; no bound on
      t is postulated (a horizon of [#|{ffun 'I_k -> G}| * #|G|] positions would do, but
      that equivalence is a theorem we neither need nor assume, and the unbounded form is
      the weaker reading for the cops).  (2) CAPTURE ON LANDING.  The cops move first and a
      cop that steps onto the robber's vertex ends the play before the robber answers (the
      [captured C' r] disjunct of [cops_capture]).  (3) c(G) <= k WITHOUT A MINIMUM.
      [cop_number_le G k] is "some j <= k such that j cops win", which is literally "the
      least winning number of cops is at most k"; it needs neither a minimisation operator
      nor monotonicity of the game in the number of cops.  The cop number is always defined
      ([cop_number_le_card]: #|G| cops win by sitting on every vertex).  (4) THE SQRT.
      [sqrt_ceil n] is ceil(sqrt n), so [C * sqrt_ceil n] is at least C*sqrt(n) and at most
      C*(sqrt(n)+1) <= 2*C*sqrt(n) for n >= 1; since C is existentially quantified before
      the graph, "c(G) <= C * sqrt_ceil #|G| for some C" is equivalent to the source's
      c(G) <= C sqrt(n), i.e. to c(n) = O(sqrt n).  (5) The guard [0 < #|G|] excludes the
      empty graph, on which the game is degenerate (every quantifier over vertices is
      vacuous); the source speaks of graphs on n vertices with a cop number, i.e. n >= 1.
      Corpus status: partial - the conjecture itself is open, only weaker upper bounds
      (Lu-Peng 2012, Scott-Sudakov 2011) and special classes are known. *)
Definition meyniel_cop_number_sqrt_statement : Prop :=
  exists C : nat,
    forall G : sgraph,
      0 < #|G| -> connected [set: G] ->
      cop_number_le G (C * sqrt_ceil #|G|).
