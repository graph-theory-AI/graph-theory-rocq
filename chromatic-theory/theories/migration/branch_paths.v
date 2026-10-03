(** Frozen C17 helpers, widespread chain and three complete blocked rows.
    Baseline 311fdcb. Every missing inducedness/disjointness condition and the
    X185 line-graph target remain unchanged; these certificates do not repair
    or unblock the statements. No prior frozen snapshot reaches this family. *)
From GTBase Require Import base.
From Chromatic.foundations Require Import branch_paths.
From Chromatic.conjectures Require Import X177 X185 X186.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module X177Legacy.

Definition x177_contains_induced_long_subdivision
    (G H : sgraph) (ell : nat) : Prop :=
  exists branch : H -> G,
    injective branch /\
    forall x y : H,
      x -- y ->
      exists p : seq G,
        [/\ path (--) (branch x) p,
            last (branch x) p = branch y,
            ell <= size p,
            uniq (branch x :: p) &
            forall z : G,
              z \in p -> z != branch y -> forall u : H, z != branch u].

Definition forest_of_lanterns_pervasive_statement : Prop :=
  forall (H : sgraph) (nu ell : nat),
    x177_forest_of_lanterns H ->
    exists c : nat,
      forall G : sgraph,
        ω([set: G]) <= nu ->
        c < χ([set: G]) ->
        X177Legacy.x177_contains_induced_long_subdivision G H ell.

End X177Legacy.

Module X185Legacy.

Definition x185_contains_induced_long_subdivision
    (G H : sgraph) (ell : nat) : Prop :=
  exists branch : H -> G,
    injective branch /\
    forall x y : H,
      x -- y ->
      exists p : seq G,
        [/\ path (--) (branch x) p,
            last (branch x) p = branch y,
            ell <= size p,
            uniq (branch x :: p) &
            forall z : G,
              z \in p -> z != branch y -> forall u : H, z != branch u].

Definition x185_widespread (H : mgraph) : Prop :=
  forall nu ell : nat,
    exists c : nat,
      forall G : sgraph,
        ω([set: G]) <= nu ->
        c < χ([set: G]) ->
        X185Legacy.x185_contains_induced_long_subdivision G (line_graph H) ell.

Definition every_multigraph_widespread_statement : Prop :=
  forall H : mgraph, loopless H -> X185Legacy.x185_widespread H.

End X185Legacy.

Module X186Legacy.

Definition x186_contains_induced_subdivision (G J : sgraph) : Prop :=
  exists branch : J -> G,
    injective branch /\
    forall x y : J,
      x -- y ->
      exists p : seq G,
        [/\ path (--) (branch x) p,
            last (branch x) p = branch y,
            uniq (branch x :: p) &
            forall z : G,
              z \in p -> z != branch y -> forall u : J, z != branch u].

Definition subdivision_or_local_chi_two_statement : Prop :=
  forall (J : sgraph) (tau : nat),
    exists c : nat,
      forall G : sgraph,
        c < χ([set: G]) ->
        X186Legacy.x186_contains_induced_subdivision G J \/ tau < x186_chi2 G.

End X186Legacy.

Lemma x177_contains_induced_long_subdivision_compat (G H : sgraph) (ell : nat) :
  X177Legacy.x177_contains_induced_long_subdivision G H ell <->
  Chromatic.conjectures.X177.x177_contains_induced_long_subdivision G H ell.
Proof. exact: iff_refl. Qed.

Lemma x185_contains_induced_long_subdivision_compat (G H : sgraph) (ell : nat) :
  X185Legacy.x185_contains_induced_long_subdivision G H ell <->
  Chromatic.conjectures.X185.x185_contains_induced_long_subdivision G H ell.
Proof. exact: iff_refl. Qed.

Lemma x186_contains_induced_subdivision_compat (G J : sgraph) :
  X186Legacy.x186_contains_induced_subdivision G J <->
  Chromatic.conjectures.X186.x186_contains_induced_subdivision G J.
Proof. exact: (iff_sym (branch_paths_zeroE G J)). Qed.

Lemma x185_widespread_compat (H : mgraph) :
  X185Legacy.x185_widespread H <-> Chromatic.conjectures.X185.x185_widespread H.
Proof. exact: iff_refl. Qed.

Lemma forest_of_lanterns_pervasive_statement_compat :
  X177Legacy.forest_of_lanterns_pervasive_statement <->
  Chromatic.conjectures.X177.forest_of_lanterns_pervasive_statement.
Proof. exact: iff_refl. Qed.

Lemma every_multigraph_widespread_statement_compat :
  X185Legacy.every_multigraph_widespread_statement <->
  Chromatic.conjectures.X185.every_multigraph_widespread_statement.
Proof. exact: iff_refl. Qed.

Lemma subdivision_or_local_chi_two_statement_compat :
  X186Legacy.subdivision_or_local_chi_two_statement <->
  Chromatic.conjectures.X186.subdivision_or_local_chi_two_statement.
Proof.
split=> h J tau; case: (h J tau) => c hc; exists c => G chiG.
- case: (hc G chiG) => [model|localchi]; last by right.
  left; exact: (proj1 (x186_contains_induced_subdivision_compat G J) model).
- case: (hc G chiG) => [model|localchi]; last by right.
  left; exact: (proj2 (x186_contains_induced_subdivision_compat G J) model).
Qed.
