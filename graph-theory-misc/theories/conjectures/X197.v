(** * GTMisc.conjectures.X197 -- v2 planar cops capture time row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X197 vocabulary ***********************************************)

(** The game of Cops and Robbers (Bonato and Mohar, arXiv:1709.09050, l.78-81 of the e-print): the
    cops take any vertices, then the robber takes any vertex; a round is a move of the cops, each cop
    independently staying put or moving to a neighbour, followed by a move of the robber; a capture
    is a cop on the robber's vertex, after either half of a round. *)
Definition x197_cop_position (G : sgraph) (cops : nat) := 'I_cops -> G.

Definition x197_captured (G : sgraph) (cops : nat)
    (C : x197_cop_position G cops) (r : G) : bool :=
  [exists i : 'I_cops, C i == r].

Definition x197_cop_move (G : sgraph) (cops : nat)
    (C C' : x197_cop_position G cops) : Prop :=
  forall i : 'I_cops, (C i == C' i) || (C i -- C' i).

Definition x197_robber_move (G : sgraph) (r r' : G) : Prop :=
  (r == r') || (r -- r').

(** From the cops' position C, cops to move, against a robber at r, the cops capture within t
    rounds: a cop landing on the robber captures in that round, and a robber moving onto a cop is
    captured too (the first disjunct one level down). Rounds are counted after the initial
    placement (l.144). *)
Fixpoint x197_cops_win_in (G : sgraph) (cops t : nat)
    (C : x197_cop_position G cops) (r : G) {struct t} : Prop :=
  x197_captured C r \/
  if t is t'.+1 then
    exists C' : x197_cop_position G cops,
      x197_cop_move C C' /\
      (x197_captured C' r \/
       forall r' : G, x197_robber_move r r' -> x197_cops_win_in t' C' r')
  else False.

Definition x197_cops_can_win (G : sgraph) (cops : nat) : Prop :=
  exists (t : nat) (C0 : x197_cop_position G cops),
    forall r0 : G, x197_cops_win_in t C0 r0.

(** The cop number c(G): the least number of cops that win. *)
Definition x197_cop_number (G : sgraph) (k : nat) : Prop :=
  x197_cops_can_win G k /\ forall k' : nat, k' < k -> ~ x197_cops_can_win G k'.

(** capt_k(G) = t (l.144-148): some starting position of k cops captures every robber within t
    rounds, and for every t' < t EVERY starting position fails against some robber. *)
Definition x197_capture_time (G : sgraph) (cops t : nat) : Prop :=
  (exists C0 : x197_cop_position G cops, forall r0 : G, x197_cops_win_in t C0 r0) /\
  forall t' : nat, t' < t ->
    forall C0 : x197_cop_position G cops, exists r0 : G, ~ x197_cops_win_in t' C0 r0.

(** The capture time is a function of the graph and the number of cops. *)
Lemma x197_capture_time_functional (G : sgraph) (k t t' : nat) :
  x197_capture_time G k t -> x197_capture_time G k t' -> t = t'.
Proof.
move=> [[C1 h1] m1] [[C2 h2] m2].
case: (ltngtP t t') => // [lt|lt].
- by have [r0 /(_ (h1 r0))] := m2 t lt C1.
- by have [r0 /(_ (h2 r0))] := m1 t' lt C2.
Qed.

Lemma x197_K2_captured (C : x197_cop_position 'K_2 1) (r : 'K_2) :
  x197_captured C r = (C ord0 == r).
Proof. by apply/existsP/idP => [[i]|h]; [rewrite (ord1 i) | exists ord0]. Qed.

(** A cop landing on the robber captures: one cop catches the robber on K_2 in one round, and not
    in zero. *)
Lemma x197_K2_capture_time_one : x197_capture_time 'K_2 1 1.
Proof.
have adj : forall (x y : 'K_2), (x -- y) = (x != y) by [].
split.
  exists (fun _ => ord0) => r0 /=.
  case: (eqVneq (ord0 : 'K_2) r0) => [e|ne]; first by left; rewrite x197_K2_captured e.
  right; exists (fun _ => r0); split; last by left; rewrite x197_K2_captured.
  by move=> i; rewrite adj ne orbT.
move=> t'; rewrite ltnS leqn0 => /eqP -> C0 /=.
case: (eqVneq (C0 ord0) ord0) => [e|ne].
  by exists ord_max; rewrite x197_K2_captured e; case.
by exists ord0; rewrite x197_K2_captured (negbTE ne); case.
Qed.

Lemma x197_no_cop_never_wins (G : sgraph) (t : nat) (C : x197_cop_position G 0) (r : G) :
  ~ x197_cops_win_in t C r.
Proof.
elim: t C r => [|t IH] C r /=.
  by case=> //; case/existsP => -[].
case=> [/existsP [[]]//|[C' [_ [/existsP [[]]//|h]]]].
by apply: (IH C' r); apply: h; rewrite /x197_robber_move eqxx.
Qed.

(** The guards are satisfiable: K_1 is connected and planar, with cop number 1 and capture time 0. *)
Lemma x197_K1_guards : connected [set: 'K_1] /\ wagner_planar 'K_1.
Proof.
split.
  have -> : [set: 'K_1] = [set ord0] by apply/setP => x; rewrite !inE (ord1 x) eqxx.
  exact: connected1.
rewrite /wagner_planar; split => /minor_card; rewrite card_ord //=.
- by rewrite card_ord.
- by rewrite card_sum !card_ord.
Qed.

Lemma x197_K1_cop_number_one : x197_cop_number 'K_1 1.
Proof.
split.
  exists 0, (fun _ => ord0) => r0 /=; left; apply/existsP; exists ord0.
  by rewrite (ord1 r0).
move=> k'; rewrite ltnS leqn0 => /eqP -> [t [C0 h]].
by apply: (@x197_no_cop_never_wins _ t C0 ord0); apply: h.
Qed.

Lemma x197_K1_capture_time_zero : x197_capture_time 'K_1 1 0.
Proof.
split; last by [].
exists (fun _ => ord0) => r0 /=; left; apply/existsP; exists ord0.
by rewrite (ord1 r0).
Qed.

(** The empty graph is no witness: its capture time is 0, for every number of cops. *)
Lemma x197_K0_capture_time_zero (k t : nat) : x197_capture_time 'K_0 k t -> t = 0.
Proof.
move=> [[C0 _] m]; case: t m => // t m.
have [r0 _] := m 0 isT C0; by case: r0.
Qed.

(** ** X197 statements *****************************************************)

(** Corpus row: arxiv:1709.09050#02
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1709.09050__02/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1709.09050__02.json
    English statement: (Bonato and Mohar 2017, "Topological directions in Cops and Robbers",
      arXiv:1709.09050, the second question of the row)
      There is a connected planar finite simple graph G of order n with capt(G) > n, where
      capt(G) is the capture time of G with c(G) cops, c(G) its cop number.
    Definitions: [x197_cop_position G cops] - a placement of the cops, a map from cop indices
      to vertices (this file); [x197_captured C r] - some cop occupies the robber's vertex
      (this file); [x197_cop_move] / [x197_robber_move] - each cop, resp. the robber, stays put
      or moves to an adjacent vertex (this file); [x197_cops_win_in t C r] - from position C,
      cops to move, against a robber at r, the cops capture within t rounds, a cop landing on
      the robber or the robber moving onto a cop being a capture (this file);
      [x197_cops_can_win G k] - some starting position of k cops captures every robber in some
      number of rounds (this file); [x197_cop_number G k] - k is the least such number, c(G)
      (this file); [x197_capture_time G k t] - some starting position of k cops captures every
      robber within t rounds and, for every t' < t, every starting position fails against some
      robber (this file); [wagner_planar] - combinatorial Wagner planarity (GTBase);
      [connected [set: G]] - G is connected.
    Notes: PARTIAL: the row asks two questions; the second, the precise sentence of the source
      ("even providing an example of a planar graph satisfying capt(G) > n remains open"), is
      encoded; the first ("is the bound capt_3(G) <= 2n tight?") has no fixed meaning and is
      not.  RE-ENCODED 2026-10-26 (coordination/PROGRAMME.md A1; record
      meta/STATEMENT_IMPROVEMENTS.md; the row is frozen by no migration family; routing by
      Lancelot, message 30; reviewer Marcol).  The earlier body had four defects: the
      minimality of its capture time was relative to the chosen start (a bad start witnessed
      any large t); capture was checked only after the robber's move, so a cop landing on the
      robber did not capture (one cop then never caught the robber on K_2); it used three cops
      where capt(G) uses c(G) cops (for c(G) <= 2, capt_3(G) <= capt(G)); and it asked for
      arbitrarily large graphs where the source asks for one.  The game follows the source
      (e-print sha256 737a9d65, topCR_0422.tex sha256 f0b1b4dc, l.78-81 and l.144-148): the
      cops place first, then the robber; a round is the cops' move, each cop independently,
      then the robber's; the length counts rounds after the initial placement; the capture time
      is the minimum over the cops' strategies, the robber evading as long as possible.  The
      guard connected [set: G] loses no witness: on a disconnected G each component H needs its
      own c(H) cops, c(G) is their sum, the components play independently, and capt(G) is the
      largest capt(H), so the component H with capt(H) = capt(G) > n >= |H| is a connected
      witness.  The empty graph is no witness ([x197_K0_capture_time_zero]); K_1 meets every
      guard ([x197_K1_guards], [x197_K1_cop_number_one], [x197_K1_capture_time_zero]); a cop
      landing on the robber captures ([x197_K2_capture_time_one]); the capture time is a
      function of G and k ([x197_capture_time_functional]). *)
Definition planar_cops_capture_time_linear_tight_statement : Prop :=
  exists (G : sgraph) (k t : nat),
    [/\ connected [set: G], wagner_planar G, x197_cop_number G k,
        x197_capture_time G k t & #|G| < t].
