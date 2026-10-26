(** * Topological.conjectures.X202 -- v2 genus cop-number asymptotic row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X202 vocabulary ***********************************************)

(** The standard game of Cops and Robbers (Mohar, arXiv:1710.11281, l.46 of the e-print: "standard
    terminology"): the cops take any vertices, then the robber takes any vertex; a round is a move
    of the cops, each cop independently staying put or moving to a neighbour, followed by a move of
    the robber; a cop on the robber's vertex captures, after either half of a round.  The bodies
    are those of X197's game (graph-theory-misc X197.v) with x202_ names. *)
Definition x202_cop_position (G : sgraph) (cops : nat) := 'I_cops -> G.

Definition x202_captured (G : sgraph) (cops : nat)
    (C : x202_cop_position G cops) (r : G) : bool :=
  [exists i : 'I_cops, C i == r].

Definition x202_cop_move (G : sgraph) (cops : nat)
    (C C' : x202_cop_position G cops) : Prop :=
  forall i : 'I_cops, (C i == C' i) || (C i -- C' i).

Definition x202_robber_move (G : sgraph) (r r' : G) : Prop :=
  (r == r') || (r -- r').

(** From the cops' position C, cops to move, against a robber at r, the cops capture within t
    rounds: a cop landing on the robber captures in that round, and a robber moving onto a cop is
    captured too (the first disjunct one level down). *)
Fixpoint x202_cops_win_in (G : sgraph) (cops t : nat)
    (C : x202_cop_position G cops) (r : G) {struct t} : Prop :=
  x202_captured C r \/
  if t is t'.+1 then
    exists C' : x202_cop_position G cops,
      x202_cop_move C C' /\
      (x202_captured C' r \/
       forall r' : G, x202_robber_move r r' -> x202_cops_win_in t' C' r')
  else False.

Definition x202_cops_can_win (G : sgraph) (cops : nat) : Prop :=
  exists (t : nat) (C0 : x202_cop_position G cops),
    forall r0 : G, x202_cops_win_in t C0 r0.

(** The cop number c(G) (l.49): the least number of cops that win. *)
Definition x202_cop_number (G : sgraph) (k : nat) : Prop :=
  x202_cops_can_win G k /\ forall k' : nat, k' < k -> ~ x202_cops_can_win G k'.

(** c(g) < g^(1/2 + p/q), with c(g) the maximum cop number of the connected graphs of orientable
    genus at most g (l.53, l.55): every such graph has c(G)^(2q) < g^(q + 2p). *)
Definition x202_cop_number_upper (g p q : nat) : Prop :=
  forall (G : sgraph) (k : nat), connected [set: G] -> surface_embeddable g G ->
    x202_cop_number G k -> k ^ (2 * q) < g ^ (q + 2 * p).

(** g^(1/2 - p/q) < c(g): some connected graph of orientable genus at most g has
    g^(q - 2p) < c(G)^(2q); the guard 2p < q of the statement keeps the subtraction q - 2p exact. *)
Definition x202_cop_number_lower (g p q : nat) : Prop :=
  exists (G : sgraph) (k : nat),
    [/\ connected [set: G], surface_embeddable g G, x202_cop_number G k & g ^ (q - 2 * p) < k ^ (2 * q)].

(** ** Sanity lemmas ********************************************************)

Lemma x202_cop_number_functional (G : sgraph) (k k' : nat) :
  x202_cop_number G k -> x202_cop_number G k' -> k = k'.
Proof.
move=> [w m] [w' m']; case: (ltngtP k k') => // [lt|lt].
- by case: (m' k lt w).
- by case: (m k' lt w').
Qed.

Lemma x202_no_cop_never_wins (G : sgraph) (t : nat) (C : x202_cop_position G 0) (r : G) :
  ~ x202_cops_win_in t C r.
Proof.
elim: t C r => [|t IH] C r /=.
  by case=> //; case/existsP => -[].
case=> [/existsP [[]]//|[C' [_ [/existsP [[]]//|h]]]].
by apply: (IH C' r); apply: h; rewrite /x202_robber_move eqxx.
Qed.

Lemma x202_K2_captured (C : x202_cop_position 'K_2 1) (r : 'K_2) :
  x202_captured C r = (C ord0 == r).
Proof. by apply/existsP/idP => [[i]|h]; [rewrite (ord1 i) | exists ord0]. Qed.

(** A cop landing on the robber captures: one cop wins on K_2, so c(K_2) = 1. *)
Lemma x202_K2_one_cop_wins : x202_cops_can_win 'K_2 1.
Proof.
have adj : forall (x y : 'K_2), (x -- y) = (x != y) by [].
exists 1, (fun _ => ord0) => r0 /=.
case: (eqVneq (ord0 : 'K_2) r0) => [e|ne]; first by left; rewrite x202_K2_captured e.
right; exists (fun _ => r0); split; last by left; rewrite x202_K2_captured.
by move=> i; rewrite adj ne orbT.
Qed.

Lemma x202_K2_cop_number_one : x202_cop_number 'K_2 1.
Proof.
split; first exact: x202_K2_one_cop_wins.
move=> k'; rewrite ltnS leqn0 => /eqP -> [t [C0 h]].
by apply: (@x202_no_cop_never_wins _ t C0 ord0); apply: h.
Qed.

(** The guards are satisfiable: K_1 is connected and planar, with cop number 1. *)
Lemma x202_K1_guards_cop_number :
  [/\ connected [set: 'K_1], surface_embeddable 0 'K_1 & x202_cop_number 'K_1 1].
Proof.
split; last split.
- have -> : [set: 'K_1] = [set ord0] by apply/setP => x; rewrite !inE (ord1 x) eqxx.
  exact: connected1.
- exact: surface_embeddable_K1.
- by exists 0, (fun _ => ord0) => r0 /=; left; apply/existsP; exists ord0; rewrite (ord1 r0).
- move=> k'; rewrite ltnS leqn0 => /eqP -> [t [C0 h]].
  by apply: (@x202_no_cop_never_wins _ t C0 ord0); apply: h.
Qed.

(** #|G| cops, one on each vertex, win at once: every graph has a winning number of cops. *)
Lemma x202_all_vertices_win (G : sgraph) : x202_cops_can_win G #|G|.
Proof.
exists 0, (fun i => enum_val i) => r0 /=; left.
by apply/existsP; exists (enum_rank r0); rewrite enum_rankK.
Qed.

(** The connected guard is load-bearing: the edgeless graph on n + 1 vertices is planar for
    [surface_embeddable] and has cop number n + 1. *)
Definition x202_edgeless (n : nat) : sgraph :=
  @SGraph 'I_n (fun _ _ => false) (fun _ _ => erefl) (fun _ => erefl).

Lemma x202_edgeless_no_dart (n : nat) (d : surface_dart (x202_edgeless n)) : False.
Proof. by case: d => [[x y]]. Qed.

Lemma x202_edgeless_planar (n : nat) : surface_embeddable 0 (x202_edgeless n.+1).
Proof. by apply: surface_embeddable_edgeless (@x202_edgeless_no_dart n.+1) _; rewrite card_ord. Qed.

Lemma x202_edgeless_stuck (n k : nat) (r : x202_edgeless n) (t : nat)
    (C : x202_cop_position (x202_edgeless n) k) :
  ~~ x202_captured C r -> ~ x202_cops_win_in t C r.
Proof.
elim: t C => [|t IH] C nc /=.
  by case=> [h|[]]; move: nc; rewrite h.
case=> [h|[C' [mv hw]]]; first by move: nc; rewrite h.
have eqi : forall i, C' i = C i by move=> i; case/orP: (mv i) => [/eqP -> //|].
have nc' : ~~ x202_captured C' r.
  apply/negP => /existsP [i /eqP e]; move/negP: nc; apply; apply/existsP; exists i.
  by rewrite -(eqi i) e.
case: hw => [h|hw]; first by move: nc'; rewrite h.
apply: (IH C' nc'); apply: hw; by rewrite /x202_robber_move eqxx.
Qed.

Lemma x202_edgeless_needs_cops (n k : nat) : k < n -> ~ x202_cops_can_win (x202_edgeless n) k.
Proof.
move=> kn [t [C0 h]].
have [r rn] : exists r : x202_edgeless n, r \notin [set C0 i | i in 'I_k].
  apply/existsP; rewrite -negb_forall; apply/negP => /forallP all.
  have sub : [set: x202_edgeless n] \subset [set C0 i | i in 'I_k] by apply/subsetP => x _; exact: all.
  move: (subset_leq_card sub); rewrite cardsT card_ord => le.
  move: (leq_trans le (leq_imset_card _ _)); rewrite card_ord => nk.
  by move: kn; rewrite ltnNge nk.
apply: (x202_edgeless_stuck (t:=t) (C:=C0) (r:=r)) (h r).
apply/negP => /existsP [i /eqP e]; apply/negP: rn; rewrite -e.
by rewrite negbK; apply/imsetP; exists i.
Qed.

Lemma x202_edgeless_cop_number (n : nat) : x202_cop_number (x202_edgeless n.+1) n.+1.
Proof.
split; last by move=> k' lt; exact: x202_edgeless_needs_cops.
by have := x202_all_vertices_win (x202_edgeless n.+1); rewrite card_ord.
Qed.

(** ** X202 statements *****************************************************)

(** Corpus row: arxiv:1710.11281#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1710.11281__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1710.11281__00.json
    English statement: (Mohar 2017, "Notes on Cops and Robber game on graphs", arXiv:1710.11281,
      Conjecture (Mohar, 2009))
      c(g) = g^(1/2 + o(1)) and c~(g) = g^(1/2 + o(1)): for every eps > 0 there is g0 such that
      for every g >= g0, g^(1/2 - eps) < c(g) < g^(1/2 + eps) and g^(1/2 - eps) < c~(g) <
      g^(1/2 + eps), where c(g) (resp. c~(g)) is the largest cop number of a connected graph of
      orientable (resp. nonorientable) genus at most g.  The first half, for c(g), is encoded.
    Definitions: [x202_cop_position], [x202_captured], [x202_cop_move], [x202_robber_move],
      [x202_cops_win_in] - the standard game: cops occupy vertices, each round every cop stays
      put or moves along an edge, then the robber does, and a cop on the robber's vertex
      captures after either half of a round (this file); [x202_cops_can_win G k] - some start of
      k cops captures every robber within some number of rounds (this file);
      [x202_cop_number G k] - k is the least such number, c(G) (this file);
      [x202_cop_number_upper g p q] - every connected G with surface_embeddable g G has
      c(G)^(2q) < g^(q+2p), i.e. c(g) < g^(1/2 + p/q) (this file); [x202_cop_number_lower g p q]
      - some connected G with surface_embeddable g G has g^(q-2p) < c(G)^(2q), i.e.
      g^(1/2 - p/q) < c(g) (this file); [surface_embeddable g G] - G admits a rotation system of
      orientable genus at most g (GTBase surface.v); [connected [set: G]] - G is connected.
    Notes: PARTIAL: the row is two-sided for BOTH c(g) and c~(g); only c(g) is encoded.  The
      nonorientable half c~(g) (crosscap number, l.53, l.55) is not: the corpus has no audited
      embeds-in-N_k predicate (topological-graph-theory foundations/signed_embedding.v measures
      the Euler genus and warns itself, l.94-100, with an open hardening TODO, l.22-29).
      RE-ENCODED 2026-10-26 (coordination/PROGRAMME.md A1; record
      meta/STATEMENT_IMPROVEMENTS.md; the row is frozen by no migration family; routing by
      Lancelot, design agreed 13:01:34Z; reviewer Marcol).  The source is the e-print
      (sha256 8ee90219..., CopsandRobberNotes.tex sha256 a78f168a...): the standard game l.46,
      c(G) l.49, the genus g(G) and the nonorientable genus l.53, c(g) and c~(g) as maxima over
      genus AT MOST g l.55, the corollary l.142-153 (via Bollobas, Kun and Leader: c(g) >=
      g^(1/2 (1 - o(1))), so the lower half for c(g) is a stated theorem), the conjecture
      l.159-164.  The earlier body had five defects: one-sided (the lower bound dropped); its
      remaining bound eps_den * cops^2 <= (eps_den + eps_num) * (g + 1) much stronger than
      c(g) < g^(1/2 + eps); c~(g) absent; capture tested only after the robber's move (one cop
      never caught the robber on K_2); and no connected guard, under which it was false (the
      edgeless graph on n + 1 vertices is planar for [surface_embeddable] and has cop number
      n + 1: [x202_edgeless_planar], [x202_edgeless_cop_number]).  The maximum c(g) is finite
      only over connected graphs, and [surface_embeddable] understates the genus of a
      disconnected graph, hence the guard [connected [set: G]]; for a connected G,
      [surface_embeddable g G] is g(G) <= g of l.53 (a minimum-genus embedding is cellular).
      c(g) < B iff every such graph has c(G) < B, and B < c(g) iff some such graph has
      c(G) > B.  eps = p/q is rational with 0 < 2p < q: the window widens with eps, so the
      small rationals give every real eps > 0; k < g^((q+2p)/(2q)) iff k^(2q) < g^(q+2p), and
      g^((q-2p)/(2q)) < k iff g^(q-2p) < k^(2q).  The game's bodies equal X197's; one shared
      copy is a library-migration candidate.  Sanity: [x202_K2_cop_number_one] (a cop landing on
      the robber captures), [x202_K1_guards_cop_number] (the guards are satisfiable),
      [x202_all_vertices_win] (every graph has a cop number, so the upper half is not vacuous),
      [x202_cop_number_functional].  The row's upstream status is open (pinned review). *)
Definition genus_cop_number_sqrt_asymptotic_statement : Prop :=
  forall p q : nat, 0 < p -> 2 * p < q ->
    exists g0 : nat, forall g : nat, g0 <= g ->
      x202_cop_number_lower g p q /\ x202_cop_number_upper g p q.
