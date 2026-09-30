(** * Atlas.foundations.cops_bridge -- graph and hypergraph cops-and-robbers

    (1) The graph game of [GTMisc.foundations.cops] is decided at a finite
    horizon (fixpoint stabilisation), so [cops_win] is decidable and the least
    winning number of cops exists constructively.  (2) A simple graph is the
    2-uniform hypergraph [E(G)] of [Hypergraph.foundations.hypergraph]: same
    moves ([hg_move_edges]), same finite-horizon game ([hg_win_edges]), same
    winning predicate ([hg_cop_win_edges]). *)

From GTBase Require Import base.
From GTMisc.foundations Require Import cops.
From Hypergraph.foundations Require Import hypergraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Stabilisation.
Variables (G : sgraph) (k : nat).

(** Positions (cops, robber) from which the cops capture within [t] rounds. *)
Definition cc_set (t : nat) : {set cop_position G k * G} :=
  [set p | cops_capture t p.1 p.2].

Lemma cc_set_step t t' : cc_set t = cc_set t' -> cc_set t.+1 = cc_set t'.+1.
Proof.
move=> e; apply/setP => -[C r]; rewrite !inE /=; congr (_ || _).
apply: eq_existsb => C'; congr (_ && (_ || _)).
apply: eq_forallb => r'; congr (_ ==> _).
by move/setP: e => /(_ (C', r')); rewrite !inE.
Qed.

Lemma cc_set_mono t t' : t <= t' -> cc_set t \subset cc_set t'.
Proof.
move=> tt; apply/subsetP => -[C r]; rewrite !inE /=; exact: cops_capture_mono.
Qed.

Lemma cc_set_stable t : cc_set t = cc_set t.+1 -> forall s, t <= s -> cc_set s = cc_set t.
Proof.
move=> e; elim=> [|s IH]; first by rewrite leqn0 => /eqP ->.
rewrite leq_eqVlt => /orP [/eqP <-//|ts].
by rewrite (cc_set_step (IH ts)) -e.
Qed.

Definition cc_bound := #|{: cop_position G k * G}|.

Lemma cc_set_fix : exists2 t, t <= cc_bound & cc_set t = cc_set t.+1.
Proof.
case: (boolP [exists t : 'I_cc_bound.+1, cc_set t == cc_set t.+1]).
  by case/existsP => t /eqP e; exists t => //; rewrite -ltnS ltn_ord.
rewrite negb_exists => /forallP H.
have grow t : t <= cc_bound.+1 -> t <= #|cc_set t|.
  elim: t => [//|t IH] tl.
  have tl' : t < cc_bound.+1 by [].
  have := H (Ordinal tl'); rewrite /= eqEsubset cc_set_mono //= => ne.
  apply: leq_ltn_trans (IH (ltnW tl)) _; apply: proper_card.
  by rewrite properE cc_set_mono //= ne.
have := grow _ (leqnn _).
by rewrite ltnNge max_card.
Qed.

Lemma cc_set_le_bound t : cc_set t \subset cc_set cc_bound.
Proof.
have [t0 t0b e] := cc_set_fix.
case: (leqP t cc_bound) => tb; first exact: cc_set_mono.
by rewrite (cc_set_stable e (ltnW (leq_ltn_trans t0b tb))) cc_set_mono.
Qed.

(** The unbounded-horizon game is decided at horizon [cc_bound]: the sets of
    winning positions increase with the horizon and stabilise once two
    consecutive ones agree, which happens before [#positions] rounds. *)
Lemma cops_win_bounded : cops_win G k <-> cops_win_within G k cc_bound.
Proof.
split=> [[t /existsP [C0 /forallP h]]|h]; last by exists cc_bound.
apply/existsP; exists C0; apply/forallP => r0.
have := subsetP (cc_set_le_bound t) (C0, r0); rewrite !inE; apply; exact: h.
Qed.

End Stabilisation.

(** A simple graph as a 2-uniform hypergraph: same moves, same game. *)
Section Bridge.
Variable G : sgraph.

Lemma hg_link_edges (u v : G) : u != v -> hg_link E(G) u v = (u -- v).
Proof.
move=> uv; apply/idP/idP.
- case/existsP => e /andP [/edgesP [a [b [-> ab]]]].
  rewrite !inE => /andP [/orP [] /eqP eu /orP [] /eqP ev]; subst u v;
    first [ by rewrite eqxx in uv | by [] | by rewrite sg_sym ].
- move=> h; apply/existsP; exists [set u; v].
  by rewrite in_edges h !inE !eqxx orbT.
Qed.

Lemma hg_move_edges (u v : G) : hg_move E(G) u v = robber_move u v.
Proof.
rewrite /hg_move /robber_move; case: (eqVneq u v) => //= uv.
exact: hg_link_edges.
Qed.

Lemma hg_win_edges c m (C : {ffun 'I_c -> G}) (r : G) :
  hg_win E(G) m C r = cops_capture m C r.
Proof.
elim: m C r => [|m IH] C r //=.
congr (_ || _); apply: eq_existsb => C'; congr (_ && (_ || _)).
- by apply: eq_forallb => i; rewrite hg_move_edges.
- by apply: eq_forallb => r'; rewrite hg_move_edges IH.
Qed.

Lemma hg_cop_win_edges c : hg_cop_win E(G) c <-> cops_win G c.
Proof.
split.
- case=> m [C h]; exists m; apply/existsP; exists C; apply/forallP => r.
  by rewrite -hg_win_edges.
- case=> t /existsP [C /forallP h]; exists t, C => r; rewrite hg_win_edges; exact: h.
Qed.

(** Hence the cop number of a graph, seen as the 2-uniform hypergraph [E(G)],
    exists (least element of a decidable predicate). *)
Lemma hg_is_cop_number_edges : exists c, hg_is_cop_number E(G) c.
Proof.
pose b c := cops_win_within G c (cc_bound G c).
have ex : exists c, b c by exists #|G|; apply/cops_win_bounded; exact: cops_win_card.
exists (ex_minn ex); split.
- apply/hg_cop_win_edges/cops_win_bounded; by case: ex_minnP.
- move=> c' /hg_cop_win_edges /cops_win_bounded h; case: ex_minnP => m _; exact.
Qed.

End Bridge.
