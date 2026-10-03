(** A18 inclusion-maximal cliques (chromatic): the frozen X181 nontrivial maximal clique, its three reaching
    chains (colourability, window, high probability) and row, and X181's complete row.  Baseline, hashes and exact
    substitutions are recorded in meta/migration_reports/maximal_cliques.spec.json.
    - [Legacy]: X181's Boolean [[&& 1 < #|S|, cliqueb S & ...]] equals [GTBase.maximal_cliques.nontrivial_maximal_clique S]
      by the unconditional Boolean equality [nontrivial_maximal_cliqueE]; the size guard stays in the helper.
    - [X181Legacy]: the chains and the row over the frozen helper; C8's live [x181_monochromatic] stays live there.
      The ffun colouring, the ordinal [k], the exact G(n,1/2) weight and its positive-mass [fg_whp], the floor logarithms,
      the natural subtractions and every quantifier order are verbatim; the documented partial upper-window defect is kept.
    - [X181Original]: the complete row (texts at C8's baseline 47eed16), composing the frozen helper with C8's frozen
      monochromatic body through all three chains.  C8's module is aliased, not imported; the bridges reuse C8's
      colourability certificate. *)
From Corelib Require Import Setoid Morphisms.
From GTBase Require Import base maximal_cliques.
From Chromatic.conjectures Require Import X181.
From Chromatic.migration Require monochromatic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** C8's certificate module, aliased without Import: its module names coincide with this file's. *)
Module C8 := Chromatic.migration.monochromatic.

Module Legacy.

Definition x181_maximal_clique (G : sgraph) (S : {set G}) : bool :=
  [&& 1 < #|S|, cliqueb S
    & [forall T : {set G}, (S \proper T) ==> ~~ cliqueb T]].

End Legacy.

Module X181Legacy.

Definition x181_clique_colourable (G : sgraph) (k : nat) : bool :=
  [exists col : {ffun G -> 'I_k},
    [forall S : {set G},
      Legacy.x181_maximal_clique S ==> ~~ x181_monochromatic (fun v => col v) S]].

Definition x181_clique_chromatic_window
    (a b n : nat) (E : {set {set 'I_n}}) : bool :=
  let G := fg_labelled_sgraph E in
  [exists k : 'I_n.+1,
    [&& X181Legacy.x181_clique_colourable G k,
        (b - a) * (trunc_log 2 n) <= b * (2 * k)
      & b * (2 * k) <= (b + a) * (trunc_log 2 n).+1]].

Definition x181_random_graph_clique_chromatic_constant : Prop :=
  forall a b : nat, 0 < a -> a <= b ->
    @fg_whp (fun n : nat => {set {set 'I_n}})
      (fun n => @fg_gnp_weight 1 2 n)
      (X181Legacy.x181_clique_chromatic_window a b).

Definition random_graph_clique_chromatic_tight_constant_statement : Prop :=
  X181Legacy.x181_random_graph_clique_chromatic_constant.

End X181Legacy.

Module X181Original.

Definition x181_clique_colourable (G : sgraph) (k : nat) : bool :=
  [exists col : {ffun G -> 'I_k},
    [forall S : {set G},
      Legacy.x181_maximal_clique S ==> ~~ C8.X181Legacy.x181_monochromatic (fun v => col v) S]].

Definition x181_clique_chromatic_window
    (a b n : nat) (E : {set {set 'I_n}}) : bool :=
  let G := fg_labelled_sgraph E in
  [exists k : 'I_n.+1,
    [&& X181Original.x181_clique_colourable G k,
        (b - a) * (trunc_log 2 n) <= b * (2 * k)
      & b * (2 * k) <= (b + a) * (trunc_log 2 n).+1]].

Definition x181_random_graph_clique_chromatic_constant : Prop :=
  forall a b : nat, 0 < a -> a <= b ->
    @fg_whp (fun n : nat => {set {set 'I_n}})
      (fun n => @fg_gnp_weight 1 2 n)
      (X181Original.x181_clique_chromatic_window a b).

Definition random_graph_clique_chromatic_tight_constant_statement : Prop :=
  X181Original.x181_random_graph_clique_chromatic_constant.

End X181Original.

Lemma x181_maximal_clique_compat (G : sgraph) (S : {set G}) :
  Legacy.x181_maximal_clique S = x181_maximal_clique S.
Proof.
by rewrite /x181_maximal_clique nontrivial_maximal_cliqueE.
Qed.

Lemma x181_clique_colourable_compat (G : sgraph) k :
  X181Legacy.x181_clique_colourable G k = x181_clique_colourable G k.
Proof.
rewrite /X181Legacy.x181_clique_colourable /x181_clique_colourable.
by apply: eq_existsb => col; apply: eq_forallb => S; rewrite x181_maximal_clique_compat.
Qed.

Lemma x181_clique_chromatic_window_compat a b n E :
  @X181Legacy.x181_clique_chromatic_window a b n E = @x181_clique_chromatic_window a b n E.
Proof.
rewrite /X181Legacy.x181_clique_chromatic_window /x181_clique_chromatic_window.
by apply: eq_existsb => k; rewrite x181_clique_colourable_compat.
Qed.

Lemma x181_event_weight_compat a b n :
  fg_event_weight (@fg_gnp_weight 1 2 n) (@X181Legacy.x181_clique_chromatic_window a b n) =
  fg_event_weight (@fg_gnp_weight 1 2 n) (@x181_clique_chromatic_window a b n).
Proof.
by apply: eq_bigl => E; exact: x181_clique_chromatic_window_compat.
Qed.

(** The same threshold [N] and the same event weights in both directions. *)
Lemma x181_random_graph_clique_chromatic_constant_compat :
  X181Legacy.x181_random_graph_clique_chromatic_constant <->
  x181_random_graph_clique_chromatic_constant.
Proof.
rewrite /X181Legacy.x181_random_graph_clique_chromatic_constant /x181_random_graph_clique_chromatic_constant /fg_whp /eventually.
split=> h a b a0 ab c d c0 cd; have [N hn] := h a b a0 ab c d c0 cd; exists N => n Nn.
- by move: (hn n Nn); rewrite x181_event_weight_compat.
- by move: (hn n Nn); rewrite x181_event_weight_compat.
Qed.

Lemma random_graph_clique_chromatic_tight_constant_statement_compat :
  X181Legacy.random_graph_clique_chromatic_tight_constant_statement <->
  random_graph_clique_chromatic_tight_constant_statement.
Proof.
exact: x181_random_graph_clique_chromatic_constant_compat.
Qed.

(** Complete X181: C8's frozen monochromatic body is kept; only the maximal clique is rewritten, then C8's certificate. *)
Lemma x181_clique_colourable_original_compat (G : sgraph) k :
  X181Original.x181_clique_colourable G k = x181_clique_colourable G k.
Proof.
rewrite -C8.x181_clique_colourable_compat /X181Original.x181_clique_colourable /C8.X181Legacy.x181_clique_colourable.
by apply: eq_existsb => col; apply: eq_forallb => S; rewrite x181_maximal_clique_compat.
Qed.

Lemma x181_clique_chromatic_window_original_compat a b n E :
  @X181Original.x181_clique_chromatic_window a b n E = @x181_clique_chromatic_window a b n E.
Proof.
rewrite /X181Original.x181_clique_chromatic_window /x181_clique_chromatic_window.
by apply: eq_existsb => k; rewrite x181_clique_colourable_original_compat.
Qed.

Lemma x181_event_weight_original_compat a b n :
  fg_event_weight (@fg_gnp_weight 1 2 n) (@X181Original.x181_clique_chromatic_window a b n) =
  fg_event_weight (@fg_gnp_weight 1 2 n) (@x181_clique_chromatic_window a b n).
Proof.
by apply: eq_bigl => E; exact: x181_clique_chromatic_window_original_compat.
Qed.

Lemma x181_random_graph_clique_chromatic_constant_original_compat :
  X181Original.x181_random_graph_clique_chromatic_constant <->
  x181_random_graph_clique_chromatic_constant.
Proof.
rewrite /X181Original.x181_random_graph_clique_chromatic_constant /x181_random_graph_clique_chromatic_constant /fg_whp /eventually.
split=> h a b a0 ab c d c0 cd; have [N hn] := h a b a0 ab c d c0 cd; exists N => n Nn.
- by move: (hn n Nn); rewrite x181_event_weight_original_compat.
- by move: (hn n Nn); rewrite x181_event_weight_original_compat.
Qed.

Lemma random_graph_clique_chromatic_tight_constant_statement_original_compat :
  X181Original.random_graph_clique_chromatic_tight_constant_statement <->
  random_graph_clique_chromatic_tight_constant_statement.
Proof.
exact: x181_random_graph_clique_chromatic_constant_original_compat.
Qed.
