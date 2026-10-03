(** * Infinite.migration.proper_colouring -- C5 frozen supplied colourings

    Frozen at a6db537. Supplied function carriers and palettes are unchanged.
    Boolean source bridges are equalities; Prop source bridges are iff. Counts
    still enumerate labelled finite functions. No surjectivity or positivity
    guard is added. The ten full statements retain their existing readings and
    statuses, including the unrelated blocked X162 Kempe-step defect.
    X64Original combines the pre-M1/A3 graph chain with frozen colouring;
    X83Original combines the B3 induced-path chain with frozen colouring.
    Historical migration bodies are imported unchanged. *)

From GTBase Require Import base colourings.
From Infinite.conjectures Require Import D4doa.
From mathcomp Require Import all_algebra.
Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition is_proper3 (G : sgraph) (c : {ffun G -> 'I_3}) : bool :=
  [forall x, [forall y, (x -- y) ==> (c x != c y)]].

End Legacy.

Module D4doaLegacy.

Definition n3colorings (G : sgraph) : nat :=
  #|[set c : {ffun G -> 'I_3} | Legacy.is_proper3 c]|.

Definition counting_3_colorings_of_the_hex_lattice_statement : Prop :=
  persite_cauchy (fun k => D4doaLegacy.n3colorings (hex_torus k)) (fun k => #|hex_torus k|).

End D4doaLegacy.

(** ** Unconditional source, chain and full-statement certificates. *)

Lemma is_proper3_compat (G : sgraph) (c : {ffun G -> 'I_3}) :
  Legacy.is_proper3 c = is_proper3 c.
Proof. by rewrite /Legacy.is_proper3 /is_proper3 proper_colouringE. Qed.

Lemma n3colorings_compat (G : sgraph) :
  D4doaLegacy.n3colorings G = n3colorings G.
Proof.
rewrite /D4doaLegacy.n3colorings /n3colorings.
apply: eq_card=> c.
by rewrite !inE is_proper3_compat.
Qed.

Lemma counting_3_colorings_of_the_hex_lattice_statement_compat :
  D4doaLegacy.counting_3_colorings_of_the_hex_lattice_statement <->
  counting_3_colorings_of_the_hex_lattice_statement.
Proof.
split=> h R eps ep; have [N hn] := h R eps ep;
  exists N => m k Nm Nk sm sk sm0 sk0 hm hk;
  apply: (hn m k Nm Nk sm sk sm0 sk0).
- by rewrite n3colorings_compat.
- by rewrite n3colorings_compat.
- by rewrite -n3colorings_compat.
- by rewrite -n3colorings_compat.
Qed.
