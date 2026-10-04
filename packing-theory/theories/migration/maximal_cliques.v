(** A18 inclusion-maximal cliques (packing): the frozen XE1 maximal clique, its two reaching chains (clique
    transversal and its attained minimum) and the #151 row.  Baseline, hashes and exact substitutions are recorded in
    meta/migration_reports/maximal_cliques.spec.json.
    - [Legacy]: XE1's Prop [clique K /\ forall L, K \proper L -> ~ clique L] is reflected by
      [GTBase.maximal_cliques.maximal_cliqueP] (an iff, not a conversion); no size or nonempty guard is added, and the
      [2 <= #|K|] guard stays in the transversal chain.
    - [XE1Legacy]: the chains and the row over the frozen helper: the attained minimal transversal size, the whole
      greatest-guarantee hypothesis and the natural subtraction are verbatim.  XE1 has no older frozen history for these
      declarations, so this row is also its complete row. *)
From Corelib Require Import Setoid Morphisms.
From GTBase Require Import base maximal_cliques.
From Packing.conjectures Require Import XE1.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition xe1_maximal_clique (G : sgraph) (K : {set G}) : Prop :=
  clique K /\
  forall L : {set G}, K \proper L -> ~ clique L.

End Legacy.

Module XE1Legacy.

Definition xe1_clique_transversal (G : sgraph) (X : {set G}) : Prop :=
  forall K : {set G}, Legacy.xe1_maximal_clique K -> 2 <= #|K| -> X :&: K != set0.

Definition xe1_clique_transversal_number (G : sgraph) (t : nat) : Prop :=
  (exists X : {set G}, XE1Legacy.xe1_clique_transversal X /\ #|X| = t) /\
  forall u : nat, (exists X : {set G}, XE1Legacy.xe1_clique_transversal X /\ #|X| = u) -> t <= u.

Definition erdos_151_statement : Prop :=
  forall (G : sgraph) (n h t : nat),
    #|G| = n ->
    xe1_triangle_free_independence_guarantee n h ->
    XE1Legacy.xe1_clique_transversal_number G t ->
    t <= n - h.

End XE1Legacy.

(** Not a conversion: the Prop presentation against the Boolean [maxset cliqueb], by reflection. *)
Lemma xe1_maximal_clique_compat (G : sgraph) (K : {set G}) :
  Legacy.xe1_maximal_clique K <-> xe1_maximal_clique K.
Proof.
exact: (rwP (maximal_cliqueP K)).
Qed.

Lemma xe1_clique_transversal_compat (G : sgraph) (X : {set G}) :
  XE1Legacy.xe1_clique_transversal X <-> xe1_clique_transversal X.
Proof.
rewrite /XE1Legacy.xe1_clique_transversal /xe1_clique_transversal.
by setoid_rewrite xe1_maximal_clique_compat.
Qed.

Lemma xe1_clique_transversal_number_compat (G : sgraph) (t : nat) :
  XE1Legacy.xe1_clique_transversal_number G t <-> xe1_clique_transversal_number G t.
Proof.
rewrite /XE1Legacy.xe1_clique_transversal_number /xe1_clique_transversal_number.
by setoid_rewrite xe1_clique_transversal_compat.
Qed.

Lemma erdos_151_statement_compat :
  XE1Legacy.erdos_151_statement <-> erdos_151_statement.
Proof.
rewrite /XE1Legacy.erdos_151_statement /erdos_151_statement.
by setoid_rewrite xe1_clique_transversal_number_compat.
Qed.
