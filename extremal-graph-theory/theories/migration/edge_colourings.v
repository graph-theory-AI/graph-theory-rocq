(** * Extremal.migration.edge_colourings -- frozen proper edge colourings (C6, 2026-10-03)

    Family: "proper_edge_colouring" (meta/library_primitives/proper-edge-colouring.json);
    extremal rows of D2chr (star chromatic index) and X229.  Canonical
    primitives: [GTBase.edge_colourings.proper_pair_edge_colouring] (pair
    maps symmetric on all ordered pairs) and
    [GTBase.edge_colourings.proper_edge_colouring] (set maps), both over an
    [eqType] palette; public client base/theories/examples/edge_colourings.v;
    generated report meta/migration_reports/proper_edge_colouring.md (from
    proper_edge_colouring.spec.json); record meta/LIBRARY_MIGRATION_C6.md.

    ** Frozen sources

    [Legacy] freezes verbatim, as they stood at 3011c28:
    - the conjecture-local [proper_ec] of D2chr.v (a pair map into a finite
      palette, symmetric on all pairs);
    - the PUBLIC foundation source [proper_ecolouring] of
      theories/foundations/edge_colourings.v (a set map into an [eqType]
      palette, endpoint form), which stays public under its old name as a
      transparent adapter of the canonical.
    Both live names are now aliases of the canonical predicates, so both
    helper certificates are kernel-checked conversions.

    [D2chrLegacy] freezes the D2chr chain with its unprefixed names copied as
    [d2chr_*] and every reference to a frozen name replaced by its frozen
    copy: [star_edge_colouring] (proper plus the no-bichromatic-P4/C4
    clauses, which stay live), [star_edge_k_colourable] and
    [is_star_chromatic_index] (the LEAST-index clause), and the row.
    [X229Legacy] freezes the X229 row over [Legacy.proper_ecolouring];
    [colour_class] and [x229_robust_sublinear_expander] reach no helper of
    this family and are used live.  D2chr's [K_1 = 1] convention (a total pair
    map still colours the pair [(ord0, ord0)]) is a property of the pair-map
    domain and is preserved exactly ([proper_pair_edge_colouring_K1],
    [no_pair_map_into_empty_palette] in GTBase.edge_colourings).

    Axiom-free: no Axiom/Parameter/Admitted; Print Assumptions at the end. *)

From GTBase Require Import base edge_colourings.
From Extremal.foundations Require Import edge_colourings.
From Extremal.conjectures Require Import D2chr X229.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

(** D2chr.v lines 353-355 at 3011c28, verbatim. *)
Definition proper_ec (G : sgraph) (C : finType) (f : G -> G -> C) : Prop :=
  (forall x y : G, f x y = f y x) /\
  (forall x y z : G, x -- y -> x -- z -> y != z -> f x y != f x z).

(** theories/foundations/edge_colourings.v lines 108-109 at 3011c28, verbatim. *)
Definition proper_ecolouring (G : sgraph) (C : eqType) (col : {set G} -> C) : Prop :=
  forall x y z : G, x -- y -> x -- z -> y != z -> col [set x; y] != col [set x; z].

End Legacy.

(** ** Helper certificates (conversions) *)

Lemma proper_ec_compat (G : sgraph) (C : finType) (f : G -> G -> C) :
  Legacy.proper_ec f <-> proper_ec f.
Proof. exact: iff_refl. Qed.

Lemma proper_ecolouring_compat (G : sgraph) (C : eqType) (col : {set G} -> C) :
  Legacy.proper_ecolouring col <-> proper_ecolouring col.
Proof. exact: iff_refl. Qed.

(** ** D2chr: the chain and the row *)

Module D2chrLegacy.

(** D2chr.v lines 382-390 at 3011c28 with [proper_ec] -> [Legacy.proper_ec]
    and the unprefixed chain names copied as [d2chr_*]. *)
Definition d2chr_star_edge_colouring (G : sgraph) (C : finType) (f : G -> G -> C) : Prop :=
  [/\ Legacy.proper_ec f, no_bichromatic_P4 f & no_bichromatic_C4 f].

Definition d2chr_star_edge_k_colourable (G : sgraph) (k : nat) : Prop :=
  exists f : G -> G -> 'I_k, d2chr_star_edge_colouring f.

Definition d2chr_is_star_chromatic_index (G : sgraph) (k : nat) : Prop :=
  d2chr_star_edge_k_colourable G k /\
  (forall k', d2chr_star_edge_k_colourable G k' -> (k <= k')%N).

(** D2chr.v lines 410-413 at 3011c28 with [is_star_chromatic_index] ->
    [d2chr_is_star_chromatic_index]. *)
Definition star_chromatic_index_of_complete_graphs_statement : Prop :=
  exists c N : nat,
    forall (n k : nat),
      (N <= n)%N -> d2chr_is_star_chromatic_index (complete n) k -> (k <= c * n)%N.

End D2chrLegacy.

Lemma star_edge_colouring_compat (G : sgraph) (C : finType) (f : G -> G -> C) :
  D2chrLegacy.d2chr_star_edge_colouring f <-> star_edge_colouring f.
Proof. exact: iff_refl. Qed.

Lemma star_edge_k_colourable_compat (G : sgraph) (k : nat) :
  D2chrLegacy.d2chr_star_edge_k_colourable G k <-> star_edge_k_colourable G k.
Proof. exact: iff_refl. Qed.

Lemma is_star_chromatic_index_compat (G : sgraph) (k : nat) :
  D2chrLegacy.d2chr_is_star_chromatic_index G k <-> is_star_chromatic_index G k.
Proof. exact: iff_refl. Qed.

(** opg:star_chromatic_index_of_complete_graphs (open, unchanged). *)
Lemma star_chromatic_index_of_complete_graphs_statement_compat :
  D2chrLegacy.star_chromatic_index_of_complete_graphs_statement <->
  star_chromatic_index_of_complete_graphs_statement.
Proof. exact: iff_refl. Qed.

(** ** X229: the row *)

Module X229Legacy.

(** X229.v lines 85-94 at 3011c28 with [proper_ecolouring] ->
    [Legacy.proper_ecolouring]. *)
Definition expander_proper_colouring_two_connected_palettes_statement : Prop :=
  exists C : nat,
    0 < C /\
    forall (G : sgraph) (Col : finType) (col : {set G} -> Col),
      x229_robust_sublinear_expander G ->
      Legacy.proper_ecolouring col ->
      (forall L : nat, 2 ^ L <= #|G| -> C * (#|G| * L) <= 2 * #|E(G)|) ->
      exists P : pred Col,
        connected [set: colour_class col P] /\
        connected [set: colour_class col (predC P)].

End X229Legacy.

(** arxiv:2309.04460#01 (open, unchanged). *)
Lemma expander_proper_colouring_two_connected_palettes_statement_compat :
  X229Legacy.expander_proper_colouring_two_connected_palettes_statement <->
  expander_proper_colouring_two_connected_palettes_statement.
Proof. exact: iff_refl. Qed.

Print Assumptions proper_ec_compat.
Print Assumptions proper_ecolouring_compat.
Print Assumptions star_edge_colouring_compat.
Print Assumptions star_edge_k_colourable_compat.
Print Assumptions is_star_chromatic_index_compat.
Print Assumptions star_chromatic_index_of_complete_graphs_statement_compat.
Print Assumptions expander_proper_colouring_two_connected_palettes_statement_compat.
