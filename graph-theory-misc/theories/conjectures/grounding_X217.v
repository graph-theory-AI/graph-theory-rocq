(** * GTMisc.conjectures.grounding_X217 -- grounding lemmas for wave X217

    Qed-closed sanity results for the cops-and-robbers vocabulary of
    [GTMisc.foundations.cops] and for [meyniel_cop_number_sqrt_statement]:

    - NON-VACUITY of the game primitive: one cop wins on every complete graph
      ['K_n.+1] and on the tree ['K_1,2] (the path on three vertices), and the
      hypothesis class of the statement is inhabited (['K_3] is nonempty and
      connected, and satisfies the conclusion with C = 1).
    - THE GUARD HAS TEETH: the robber escapes ZERO cops on every nonempty graph,
      so [cop_number_le G 0] is false there and the constant C = 0 refutes the
      body of the statement -- the statement is not satisfied by the degenerate
      constant.
    - THE SQRT IS THE CONTENT: [cop_number_le G #|G|] holds for EVERY graph, so
      the same statement with the bound [#|G|] instead of [C * sqrt_ceil #|G|]
      would be a theorem; what is open is the order of magnitude of the bound. *)

From GTBase Require Import base.
From GTMisc.foundations Require Import cops.
From GTMisc.conjectures Require Import X217.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Carriers *)

(** Complete graphs are connected. *)
Lemma connected_Kn (n : nat) : connected [set: 'K_n].
Proof.
move=> x y _ _; have [->|Hne] := eqVneq x y; first exact: connect0.
by apply: connect1; rewrite /= !inE /=.
Qed.

Lemma card_Kn (n : nat) : #|'K_n| = n.
Proof. exact: card_ord. Qed.

(** ** One cop suffices on a graph with a dominating vertex *)

(** One cop wins on every complete graph. *)
Lemma cops_win_Kn (n : nat) : cops_win 'K_n.+1 1.
Proof.
apply: (@cops_win_dominating 'K_n.+1 ord0) => u Hu.
by rewrite /edge_rel /= eq_sym.
Qed.

(** One cop wins on the star ['K_1,2], i.e. on the path on three vertices (a tree). *)
Lemma cops_win_K12 : cops_win 'K_1,2 1.
Proof.
apply: (@cops_win_dominating 'K_1,2 (inl ord0)) => u Hu.
case: u Hu => [x|y] Hu; last by rewrite /edge_rel /=.
by move: Hu; rewrite (ord1 x) eqxx.
Qed.

(** The tree carrier is connected, as the source's graphs are. *)
Lemma connected_K12 : connected [set: 'K_1,2].
Proof. exact: Knm_connected. Qed.

(** ** The cop number is always defined, and the trivial bound is provable *)

(** Every graph has a cop number: [#|G|] cops win by occupying every vertex. *)
Lemma meyniel_trivial_bound (G : sgraph) : cop_number_le G #|G|.
Proof. exact: cop_number_le_card. Qed.

(** ** The guard has teeth *)

(** The robber escapes zero cops on any nonempty graph. *)
Lemma robber_escapes_no_cops (G : sgraph) : 0 < #|G| -> ~ cops_win G 0.
Proof. exact: not_cops_win_0. Qed.

Lemma not_cop_number_le_0_K3 : ~ cop_number_le 'K_3 0.
Proof. by apply: not_cop_number_le_0; rewrite card_Kn. Qed.

(** C = 0 refutes the body of Meyniel's statement: the constant is load-bearing. *)
Lemma meyniel_body_C0_false :
  ~ (forall G : sgraph, 0 < #|G| -> connected [set: G] ->
       cop_number_le G (0 * sqrt_ceil #|G|)).
Proof.
move=> H; apply: not_cop_number_le_0_K3.
have H3 : 0 < #|'K_3| by rewrite card_Kn.
by move: (H 'K_3 H3 (@connected_Kn 3)); rewrite mul0n.
Qed.

(** ** A settled instance of the conclusion *)

(** [sqrt_ceil] of a positive number is positive. *)
Lemma sqrt_ceil_gt0 (n : nat) : 0 < n -> 0 < sqrt_ceil n.
Proof.
move=> Hn; case E : (sqrt_ceil n) => [|s] //.
move: (sqrt_ceil_spec n); rewrite E exp0n // leqn0.
by move/eqP => Hn0; rewrite Hn0 in Hn.
Qed.

(** The cop number of ['K_3] obeys the conjectured bound with C = 1. *)
Lemma meyniel_instance_K3 : cop_number_le 'K_3 (1 * sqrt_ceil #|'K_3|).
Proof.
exists 1; split; last exact: (@cops_win_Kn 2).
by rewrite mul1n card_Kn; apply: sqrt_ceil_gt0.
Qed.

(** The hypothesis class of the statement is inhabited. *)
Lemma meyniel_hypotheses_inhabited :
  exists G : sgraph, 0 < #|G| /\ connected [set: G].
Proof. by exists 'K_3; split; [rewrite card_Kn|exact: (@connected_Kn 3)]. Qed.

Print Assumptions cops_win_Kn.
Print Assumptions cops_win_K12.
Print Assumptions meyniel_trivial_bound.
Print Assumptions meyniel_body_C0_false.
Print Assumptions meyniel_instance_K3.
Print Assumptions meyniel_hypotheses_inhabited.
