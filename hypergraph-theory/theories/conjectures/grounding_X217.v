(** * Hypergraph.conjectures.grounding_X217 -- grounding lemmas for wave X217

    Qed-closed, axiom-free sanity results for
    [hypergraph_cop_number_sqrt_n_over_k_statement] and for the cops-and-robbers
    primitives it uses ([hg_win], [hg_cop_win], [hg_is_cop_number], defined in
    [Hypergraph.foundations.hypergraph]).

    - NON-VACUITY: the hypotheses are simultaneously satisfiable -- the 2-vertex
      hypergraph with a single hyperedge is 2-uniform, connected, has [k <= n],
      and its cop number is exactly 1; its instance of the conclusion holds with
      the constant [C = 1].
    - GUARD-HAS-TEETH: the [k <= #|T|] guard is load-bearing.  The EDGELESS
      hypergraph on one vertex is vacuously [k]-uniform for EVERY [k], is
      connected and has cop number 1, so without that guard the body would
      demand [k <= C^2] for every [k] and the statement would be refutable.
    - The game itself is not degenerate: zero cops never catch anybody
      ([hg_win_no_cop] / [hg_cop_win_no_cop] in the foundation), which is what
      makes "cop number 1" above a real minimality claim. *)

From GTBase Require Import base.
From Hypergraph.foundations Require Import hypergraph.
From Hypergraph.conjectures Require Import X217.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The 2-vertex hypergraph with one hyperedge *)

Definition x217_K2 : {set {set 'I_2}} := [set [set: 'I_2]].

Lemma x217_K2_uniform : hg_uniform x217_K2 2.
Proof. by move=> e; rewrite inE => /eqP->; rewrite cardsT card_ord. Qed.

Lemma x217_K2_link (u v : 'I_2) : hg_link x217_K2 u v.
Proof. by apply: (@hg_linkP _ x217_K2 [set: 'I_2]); rewrite !inE. Qed.

Lemma x217_K2_connected : hg_connected x217_K2.
Proof. by move=> u v; apply: connect1; apply: x217_K2_link. Qed.

Lemma x217_K2_cop_win : hg_cop_win x217_K2 1.
Proof.
apply: (hg_cop_win1 (v0 := ord0)) => u.
by rewrite /hg_move x217_K2_link orbT.
Qed.

Lemma x217_K2_cop_number : hg_is_cop_number x217_K2 1.
Proof.
split; first exact: x217_K2_cop_win.
case=> [W|c' _] //.
by case: (hg_cop_win_no_cop ord0 W).
Qed.

(** NON-VACUITY: every hypothesis of the body is satisfied at once, and the
    conclusion then holds with [C = 1] -- the statement is not empty. *)
Lemma x217_hypotheses_satisfiable :
  [/\ 0 < 2, 2 <= #|'I_2|, hg_uniform x217_K2 2, hg_connected x217_K2 &
      hg_is_cop_number x217_K2 1].
Proof.
split => //; [by rewrite card_ord | exact: x217_K2_uniform |
  exact: x217_K2_connected | exact: x217_K2_cop_number].
Qed.

Lemma x217_conclusion_at_K2 : 1 ^ 2 * 2 <= 1 ^ 2 * #|'I_2|.
Proof. by rewrite card_ord. Qed.

(** ** The edgeless one-vertex hypergraph: the [k <= n] guard has teeth *)

Definition x217_edgeless : {set {set 'I_1}} := set0.

Lemma x217_edgeless_uniform k : hg_uniform x217_edgeless k.
Proof. by move=> e; rewrite inE. Qed.

Lemma x217_edgeless_connected : hg_connected x217_edgeless.
Proof. by move=> u v; rewrite (ord1 u) (ord1 v) connect0. Qed.

Lemma x217_edgeless_cop_number : hg_is_cop_number x217_edgeless 1.
Proof.
split.
  apply: (hg_cop_win1 (v0 := ord0)) => u.
  by rewrite /hg_move (ord1 u) eqxx.
case=> [W|c' _] //.
by case: (hg_cop_win_no_cop ord0 W).
Qed.

(** GUARD-HAS-TEETH: drop [k <= #|T|] and the body becomes refutable.  For
    every constant [C] the edgeless one-vertex hypergraph satisfies every other
    hypothesis at [k = C^2 + 1] and violates the conclusion. *)
Lemma x217_k_le_n_guard_has_teeth (C : nat) :
  exists k : nat,
    [/\ 0 < k,
        hg_uniform x217_edgeless k,
        hg_connected x217_edgeless,
        hg_is_cop_number x217_edgeless 1 &
        ~~ (1 ^ 2 * k <= C ^ 2 * #|'I_1|)].
Proof.
exists (C ^ 2).+1; split.
- by [].
- exact: x217_edgeless_uniform.
- exact: x217_edgeless_connected.
- exact: x217_edgeless_cop_number.
- by rewrite card_ord muln1 exp1n mul1n ltnn.
Qed.

(** The guard is harmless: a hypergraph with a hyperedge always has [k <= n]. *)
Lemma x217_k_le_n_automatic (T : finType) (E : {set {set T}}) (k : nat) :
  hg_uniform E k -> E != set0 -> k <= #|T|.
Proof.
move=> uni /set0Pn[e eE]; rewrite -(uni e eE).
by apply: subset_leq_card; apply/subsetP => x _; rewrite inE.
Qed.

Print Assumptions hypergraph_cop_number_sqrt_n_over_k_statement.
Print Assumptions x217_K2_cop_number.
Print Assumptions x217_k_le_n_guard_has_teeth.
Print Assumptions x217_k_le_n_automatic.
