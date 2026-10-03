(** A13 multigraph regularity (chromatic): the frozen U5 incidence regularity [regular_m] and its cubic
    case, the reached chain [is_universal_sts] and the two U5 rows.  Baseline, hashes and exact substitutions are
    recorded in meta/migration_reports/mregular.spec.json.  The bodies count incident edges ([#|edges_at v|], a
    loop once) and convert to [GTBase.base.mregular]/[mcubic].  U5's cubic carries NO loopless guard, and the
    three-edge-colouring row's conclusion keeps its unguarded cubic [H]: both are frozen exactly. *)
From GTBase Require Import base.
From GraphTheory Require Import mgraph.
From Chromatic.conjectures Require Import U5.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition regular_m (G : mgraph) (r : nat) : Prop := forall v : G, #|edges_at v| = r.

Definition cubic (G : mgraph) : Prop := Legacy.regular_m G 3.

End Legacy.

Module U5Legacy.

Definition is_universal_sts (S : sts) : Prop :=
  forall G : mgraph, loopless G -> Legacy.cubic G -> sts_edge_colourable G S.

Definition three_edge_coloring_statement : Prop :=
  forall G : mgraph,
    loopless G -> Legacy.cubic G -> mconnected G -> 2 < #|G| -> edge_colourable G 3 ->
    exists (e : edge G) (H : mgraph),
      [/\ Legacy.cubic H,
          homeomorphic_s (usimple (remove_edge e)) (usimple H)
        & edge_colourable H 3].

Definition universal_steiner_triple_systems_statement : Prop :=
  exists S : sts, sts_valid S /\ U5Legacy.is_universal_sts S.

End U5Legacy.

Lemma regular_m_compat (G : mgraph) (r : nat) :
  Legacy.regular_m G r <->
  regular_m G r.
Proof. exact: iff_refl. Qed.

Lemma cubic_compat (G : mgraph) :
  Legacy.cubic G <->
  cubic G.
Proof. exact: iff_refl. Qed.

Lemma is_universal_sts_compat (S : sts) :
  U5Legacy.is_universal_sts S <->
  is_universal_sts S.
Proof. exact: iff_refl. Qed.

Lemma three_edge_coloring_statement_compat :
  U5Legacy.three_edge_coloring_statement <->
  three_edge_coloring_statement.
Proof. exact: iff_refl. Qed.

Lemma universal_steiner_triple_systems_statement_compat :
  U5Legacy.universal_steiner_triple_systems_statement <->
  universal_steiner_triple_systems_statement.
Proof. exact: iff_refl. Qed.
