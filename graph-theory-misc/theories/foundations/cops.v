(** * GTMisc.foundations.cops -- the finite Cops and Robbers game on a simple graph

    A self-contained, axiom-free formalisation of the pursuit game of Nowakowski-Winkler
    and Quilliot on a FINITE simple graph [G : sgraph], written so that any package can
    reuse it (it is generic over [G] and needs nothing but [GTBase.base]).

    ** The game

    [k] cops choose their starting vertices; then the robber chooses a vertex; then the
    two sides alternate, the COPS moving first.  In one cop move each cop either stays
    put or slides along an edge; in one robber move the robber either stays put or slides
    along an edge.  The cops win as soon as some cop occupies the robber's vertex; since
    the cops move first, a cop that steps ONTO the robber captures him before he may
    answer (this is the [captured C' r] disjunct inside [cops_capture]).

    ** Why a bounded horizon is a definable, decidable formulation

    For a FIXED number [t] of remaining cop moves, "the cops capture within [t] rounds"
    is a BOOLEAN predicate [cops_capture t C r]: all its quantifiers range over the
    finite types [{ffun 'I_k -> G}] and [G], so it is decidable by evaluation, and it is
    monotone in [t] ([cops_capture_mono]).  "The cops win" is then the standard
    "capture after finitely many rounds":

        [cops_win G k := exists t : nat, cops_win_within G k t].

    This is exactly the usual winning condition of the game on a finite graph (a play is
    won by the cops iff a capture occurs after finitely many moves), it needs no
    well-founded-strategy machinery, and the least such [t] is the capture time.  No
    a-priori bound on [t] is postulated: one COULD pin the horizon at the number of game
    positions [#|{ffun 'I_k -> G}| * #|G|] and obtain a fully boolean predicate, but that
    equivalence is a theorem we do not need and do not assume, so the existential form is
    used instead -- it is the weaker, i.e. the safer, reading for the cops.

    ** The cop number

    [c(G) <= k] is stated WITHOUT a minimisation operator and WITHOUT appealing to
    monotonicity in the number of cops:

        [cop_number_le G k := exists j, j <= k /\ cops_win G j]

    which is literally "the least number of cops that win is at most [k]".

    Interface exported by this file (all with [G : sgraph] explicit):
      [cop_position G k]      -- a placement of [k] cops, [{ffun 'I_k -> G}];
      [captured C r]          -- some cop sits on the robber's vertex (bool);
      [cop_move C C']         -- every cop stays put or slides along an edge (bool);
      [robber_move r r']      -- the robber stays put or slides along an edge (bool);
      [cops_capture t C r]    -- bool: from [(C,r)], cops to move, capture within [t] moves;
      [cops_win_within G k t] -- bool: some start position of [k] cops captures every
                                 robber start within [t] moves;
      [cops_win G k]          -- Prop: [exists t, cops_win_within G k t];
      [cop_number_le G k]     -- Prop: [exists j <= k] such that [j] cops win.
    Structural laws: [cops_capture_mono], [cops_win_dominating], [cops_win_card],
    [cop_number_le_card], [cops_capture0], [not_cops_win_0], [cop_number_le_mono]. *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section CopsAndRobbers.
Variable G : sgraph.

(** A placement of [k] cops: one vertex per cop index. *)
Definition cop_position (k : nat) := {ffun 'I_k -> G}.

(** The robber at [r] is caught when some cop occupies [r]. *)
Definition captured (k : nat) (C : cop_position k) (r : G) : bool :=
  [exists i : 'I_k, C i == r].

(** One cop move: each cop stays put or slides along an edge. *)
Definition cop_move (k : nat) (C C' : cop_position k) : bool :=
  [forall i : 'I_k, (C i == C' i) || (C i -- C' i)].

(** One robber move: stay put or slide along an edge. *)
Definition robber_move (r r' : G) : bool := (r == r') || (r -- r').

(** [cops_capture t C r]: cops at [C], robber at [r], the cops to move, at most [t]
    cop moves left -- the cops can force a capture.  A capture that happens as the cops
    move ([captured C' r]) ends the play before the robber answers. *)
Fixpoint cops_capture (k t : nat) (C : cop_position k) (r : G) {struct t} : bool :=
  captured C r ||
  (if t is t'.+1 then
     [exists C' : cop_position k,
        cop_move C C' &&
        (captured C' r ||
         [forall r' : G, robber_move r r' ==> cops_capture t' C' r'])]
   else false).

(** [k] cops win within [t] rounds: some starting placement beats every robber start. *)
Definition cops_win_within (k t : nat) : bool :=
  [exists C0 : cop_position k, [forall r0 : G, cops_capture t C0 r0]].

(** [k] cops win: they capture after finitely many rounds. *)
Definition cops_win (k : nat) : Prop := exists t : nat, cops_win_within k t.

(** The cop number of [G] is at most [k]. *)
Definition cop_number_le (k : nat) : Prop := exists j : nat, (j <= k)%N /\ cops_win j.

(** ** Structural laws *)

(** More rounds never hurt the cops. *)
Lemma cops_capture_mono (k t t' : nat) : (t <= t')%N ->
  forall (C : cop_position k) (r : G), cops_capture t C r -> cops_capture t' C r.
Proof.
elim: t t' => [|t IH] t' le C r /=.
- rewrite orbF => Hc; by case: t' le => [|t'] _ /=; rewrite Hc.
- case: t' le => // t' le /=.
  case/orP => [->//|/existsP[C' /andP[Hmv Hin]]].
  apply/orP; right; apply/existsP; exists C'; rewrite Hmv /=.
  case/orP: Hin => [->//|/forallP Hall]; apply/orP; right.
  apply/forallP => r'; apply/implyP => Hr.
  by apply: (IH t' le); apply: (implyP (Hall r')).
Qed.

(** One cop on a dominating vertex wins in one round. *)
Lemma cops_win_dominating (v : G) :
  (forall u : G, u != v -> v -- u) -> cops_win 1.
Proof.
move=> Hv; exists 1; apply/existsP; exists [ffun _ => v]; apply/forallP => r0.
have [->|Hne] := eqVneq r0 v.
  by apply/orP; left; apply/existsP; exists ord0; rewrite ffunE.
apply/orP; right; apply/existsP; exists [ffun _ => r0].
apply/andP; split.
  by apply/forallP => i; rewrite !ffunE (Hv r0 Hne) orbT.
by apply/orP; left; apply/existsP; exists ord0; rewrite ffunE.
Qed.

(** A cop on every vertex captures immediately: the cop number is always defined. *)
Lemma cops_win_card : cops_win #|G|.
Proof.
exists 0; apply/existsP; exists [ffun i => enum_val i]; apply/forallP => r0.
rewrite /= orbF; apply/existsP; exists (enum_rank r0).
by rewrite ffunE enum_rankK.
Qed.

Lemma cop_number_le_card : cop_number_le #|G|.
Proof. by exists #|G|; split; [|exact: cops_win_card]. Qed.

Lemma cop_number_le_mono (j k : nat) : (j <= k)%N -> cop_number_le j -> cop_number_le k.
Proof. by move=> le [i [le_i Hi]]; exists i; split; [exact: leq_trans le|]. Qed.

(** Zero cops never capture anybody. *)
Lemma captured0 (C : cop_position 0) (r : G) : captured C r = false.
Proof.
rewrite /captured; apply/negbTE/existsPn => i.
by move: (ltn_ord i); rewrite ltn0.
Qed.

Lemma cops_capture0 (t : nat) (C : cop_position 0) (r : G) : cops_capture t C r = false.
Proof.
elim: t C r => [|t IH] C r /=; rewrite captured0 /=; first by [].
apply/negbTE/existsPn => C'; rewrite negb_and; apply/orP; right.
rewrite captured0 /=; apply/negP => /forallP/(_ r).
by rewrite /robber_move eqxx /= IH.
Qed.

(** The robber escapes zero cops on any nonempty graph: the guard has teeth. *)
Lemma not_cops_win_0 : (0 < #|G|)%N -> ~ cops_win 0.
Proof.
move=> H0 [t /existsP[C0 /forallP Hw]].
by move: (Hw (enum_val (Ordinal H0))); rewrite cops_capture0.
Qed.

Lemma not_cop_number_le_0 : (0 < #|G|)%N -> ~ cop_number_le 0.
Proof.
move=> H0 [j [Hj0 Hj]]; move: Hj0; rewrite leqn0 => /eqP Hj_eq.
by move: Hj; rewrite Hj_eq; exact: (not_cops_win_0 H0).
Qed.

End CopsAndRobbers.

Arguments cop_position : clear implicits.
Arguments cops_win_within : clear implicits.
Arguments cops_win : clear implicits.
Arguments cop_number_le : clear implicits.
