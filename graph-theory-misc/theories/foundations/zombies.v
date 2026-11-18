(** * GTMisc.foundations.zombies -- the deterministic game of Zombies and Survivors on a finite simple graph

    The game of Fitzpatrick, Howell, Messinger and Pike, "A deterministic version of the game of zombies and
    survivors on graphs", Discrete Applied Mathematics 213 (2016) 1-12 (FHMP16; line numbers below are those of the
    deposited text coordination/sources/fhmp16-source-mac-20261117/paper.txt), with one survivor, as also restated
    in arXiv:2008.03587v3 (main.tex l.167-185).  Axiom-free, generic over [G : sgraph], needing only [GTBase.base];
    its form follows [GTMisc.foundations.cops].

    ** The rules, and where each is encoded

    - The board is a finite connected graph with one survivor (FHMP16 l.94-96; 2008.03587 l.182-184).  The
      definitions below make sense on every finite graph; the statements that use them assume connectivity, as both
      sources do (on a disconnected graph a zombie with no shortest path to the survivor has no legal move and
      freezes the play: [zombies_stuck]).
    - Round zero: the zombies choose their vertices, then the survivor chooses one (FHMP16 l.57-61, l.266-267);
      several zombies may share a vertex (l.343-346).  [zombies_win_within]: some placement [Z0] beats every
      survivor start [s0].
    - A round: the zombies move, then the survivor (l.58-60, l.267-270).  [zombies_capture] alternates them.
    - The zombies' move: EVERY zombie moves, none may pass (l.114-119), along a geodesic towards the survivor, that
      is to a neighbour one step closer (l.80-81, l.119-121).  [zombie_move s Z Z']: each [Z' i] is a neighbour of
      [Z i] strictly closer to [s] in [graph_dist]; in a connected graph a neighbour is at most one step closer, so
      "strictly closer" is "the next vertex of a geodesic".
    - The survivor's move: a neighbour, or rest (l.524-525, l.348).  [survivor_move].
    - Capture: a zombie moves onto the survivor's vertex (l.81-82; 2008.03587 l.174-175), with the winning
      conditions of Cops and Robber (l.82-83, l.61-64).  [zombies_capture] counts a capture at placement, right
      after the zombies' move (before the survivor answers), and when the survivor steps onto a zombie (the
      survivor "will never move onto a vertex currently occupied by a zombie", l.104, and resting is always
      allowed, so counting it changes no outcome).
    - Deterministic, worst case for the survivor: the zombies choose their placement and, among several geodesics,
      their moves (abstract l.40-45; l.100-103): the zombies' choices are existential, the survivor's universal.
    - The zombies win when they capture after finitely many rounds: [zombies_win k := exists t, ...], the bounded
      horizon of [GTMisc.foundations.cops] (monotone in [t]: [zombies_capture_mono]).
    - z(G), "the minimum number of zombies required to win" (l.105; 2008.03587 l.184-185): [zombie_number G k]
      holds when [k] zombies win and no smaller number does; it is functional ([zombie_number_functional]), and
      between 1 and #|G| on a nonempty graph ([not_zombies_win_0], [zombies_win_card]).

    Interface: [zombie_position], [zombie_caught], [zombie_move], [survivor_move], [zombies_capture],
    [zombies_win_within], [zombies_win], [zombie_number]; laws [zombie_dist_refl], [zombie_dist_gt0],
    [zombie_move_no_pass], [zombies_capture_mono], [zombies_win_card], [zombie_caught0], [zombies_capture0],
    [not_zombies_win_0], [zombie_number_functional], [zombies_win_dominating], [zombies_stuck]; the ground example
    [zombie_number_K1]. *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The distance from a vertex to itself is 0, and to any other vertex positive. *)
Lemma zombie_dist_refl (G : sgraph) (x : G) : graph_dist x x = 0.
Proof.
rewrite /graph_dist; case: ex_minnP => m _ min; apply/eqP; rewrite -leqn0.
by apply: min; rewrite /= inE eqxx.
Qed.

Lemma zombie_dist_gt0 (G : sgraph) (x y : G) : x != y -> 0 < graph_dist x y.
Proof.
move=> xy; rewrite /graph_dist; case: ex_minnP => m Pm _.
rewrite lt0n; apply/eqP => m0; move: Pm; rewrite m0 /= inE eq_sym (negbTE xy) /=.
move/eqP/esym/card0_eq/(_ x); by rewrite inE.
Qed.

Section ZombiesAndSurvivors.
Variable G : sgraph.

(** A placement of [k] zombies: one vertex per zombie index. *)
Definition zombie_position (k : nat) := {ffun 'I_k -> G}.

(** The survivor at [s] is caught when some zombie occupies [s]. *)
Definition zombie_caught (k : nat) (Z : zombie_position k) (s : G) : bool :=
  [exists i : 'I_k, Z i == s].

(** One zombie move against a survivor at [s]: every zombie steps to a neighbour strictly closer to [s]. *)
Definition zombie_move (k : nat) (s : G) (Z Z' : zombie_position k) : bool :=
  [forall i : 'I_k, (Z i -- Z' i) && (graph_dist (Z' i) s < graph_dist (Z i) s)].

(** One survivor move: rest, or step to a neighbour. *)
Definition survivor_move (s s' : G) : bool := (s == s') || (s -- s').

(** [zombies_capture t Z s]: zombies at [Z], survivor at [s], the zombies to move, at most [t] zombie moves left --
    the zombies can force a capture.  A capture as the zombies move ([zombie_caught Z' s]) ends the play before the
    survivor answers. *)
Fixpoint zombies_capture (k t : nat) (Z : zombie_position k) (s : G) {struct t} : bool :=
  zombie_caught Z s ||
  (if t is t'.+1 then
     [exists Z' : zombie_position k,
        zombie_move s Z Z' &&
        (zombie_caught Z' s ||
         [forall s' : G, survivor_move s s' ==> zombies_capture t' Z' s'])]
   else false).

(** [k] zombies win within [t] rounds: some placement beats every survivor start. *)
Definition zombies_win_within (k t : nat) : bool :=
  [exists Z0 : zombie_position k, [forall s0 : G, zombies_capture t Z0 s0]].

(** [k] zombies win: they capture after finitely many rounds. *)
Definition zombies_win (k : nat) : Prop := exists t : nat, zombies_win_within k t.

(** The zombie number z(G) is [k]: [k] zombies win and fewer do not. *)
Definition zombie_number (k : nat) : Prop :=
  zombies_win k /\ forall j : nat, j < k -> ~ zombies_win j.

(** ** Laws *)

(** No zombie passes. *)
Lemma zombie_move_no_pass (k : nat) (s : G) (Z Z' : zombie_position k) :
  zombie_move s Z Z' -> forall i : 'I_k, Z' i != Z i.
Proof.
move=> /forallP h i; have /andP [e _] := h i.
by apply: contraTneq e => ->; rewrite sg_irrefl.
Qed.

(** More rounds never hurt the zombies. *)
Lemma zombies_capture_mono (k t t' : nat) : t <= t' ->
  forall (Z : zombie_position k) (s : G), zombies_capture t Z s -> zombies_capture t' Z s.
Proof.
elim: t t' => [|t IH] t' le Z s /=.
- rewrite orbF => Hc; by case: t' le => [|t'] _ /=; rewrite Hc.
- case: t' le => // t' le /=.
  case/orP => [->//|/existsP[Z' /andP[Hmv Hin]]].
  apply/orP; right; apply/existsP; exists Z'; rewrite Hmv /=.
  case/orP: Hin => [->//|/forallP Hall]; apply/orP; right.
  apply/forallP => s'; apply/implyP => Hs.
  by apply: (IH t' le); apply: (implyP (Hall s')).
Qed.

(** A zombie on every vertex captures at round zero. *)
Lemma zombies_win_card : zombies_win #|G|.
Proof.
exists 0; apply/existsP; exists [ffun i => enum_val i]; apply/forallP => s0.
rewrite /= orbF; apply/existsP; exists (enum_rank s0).
by rewrite ffunE enum_rankK.
Qed.

(** Zero zombies never capture, so on a nonempty graph they never win. *)
Lemma zombie_caught0 (Z : zombie_position 0) (s : G) : zombie_caught Z s = false.
Proof. by apply/negbTE/existsPn => -[]. Qed.

Lemma zombies_capture0 (t : nat) (Z : zombie_position 0) (s : G) : zombies_capture t Z s = false.
Proof.
elim: t Z s => [|t IH] Z s /=; rewrite zombie_caught0 //=.
apply/negbTE/existsPn => Z'; rewrite negb_and; apply/orP; right.
rewrite zombie_caught0 /=; apply/negP => /forallP/(_ s).
by rewrite /survivor_move eqxx /= IH.
Qed.

Lemma not_zombies_win_0 : 0 < #|G| -> ~ zombies_win 0.
Proof.
move=> H0 [t /existsP[Z0 /forallP Hw]].
by move: (Hw (enum_val (Ordinal H0))); rewrite zombies_capture0.
Qed.

(** The zombie number is a function of the graph. *)
Lemma zombie_number_functional (k k' : nat) :
  zombie_number k -> zombie_number k' -> k = k'.
Proof.
move=> [w m] [w' m']; case: (ltngtP k k') => // lt.
- by case: (m' k lt w).
- by case: (m k' lt w').
Qed.

(** One zombie on a vertex adjacent to every other vertex catches the survivor in one round. *)
Lemma zombies_win_dominating (v : G) : (forall u : G, u != v -> v -- u) -> zombies_win 1.
Proof.
move=> Hv; exists 1; apply/existsP; exists [ffun _ => v]; apply/forallP => s0 /=.
have [<-|ne] := eqVneq v s0.
  by apply/orP; left; apply/existsP; exists ord0; rewrite ffunE.
apply/orP; right; apply/existsP; exists [ffun _ => s0]; apply/andP; split.
  apply/forallP => i; have sv : s0 != v by rewrite eq_sym.
  rewrite !ffunE (Hv s0 sv) /=.
  by rewrite zombie_dist_refl zombie_dist_gt0.
by apply/orP; left; apply/existsP; exists ord0; rewrite ffunE.
Qed.

(** A zombie with no neighbour closer to the survivor stops the play: the zombies cannot move at all. *)
Lemma zombies_stuck (k t : nat) (Z : zombie_position k) (s : G) (i : 'I_k) :
  (forall w : G, Z i -- w -> graph_dist (Z i) s <= graph_dist w s) ->
  zombies_capture t Z s = zombie_caught Z s.
Proof.
move=> h; case: t => [|t] /=; first by rewrite orbF.
suff -> : [exists Z' : zombie_position k, zombie_move s Z Z' &&
           (zombie_caught Z' s || [forall s', survivor_move s s' ==> zombies_capture t Z' s'])] = false.
  by rewrite orbF.
apply/negbTE/existsPn => Z'; apply/negP => /andP [/forallP /(_ i) /andP [e lt] _].
by move: (h _ e); rewrite leqNgt lt.
Qed.

End ZombiesAndSurvivors.

(** ** A ground example: one zombie catches the survivor on K_1, and zero zombies do not (FHMP16 Observation 2 (4),
    l.146, at n = 1). *)
Lemma zombie_number_K1 : zombie_number 'K_1 1.
Proof.
split.
  by apply: (@zombies_win_dominating 'K_1 ord0) => u; rewrite (ord1 u) eqxx.
by move=> j; rewrite ltnS leqn0 => /eqP ->; apply: not_zombies_win_0; rewrite card_ord.
Qed.
