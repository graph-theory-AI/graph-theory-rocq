(** A16 clique number (minor): the frozen X121 clique-number helper, the current row and the complete row.
    Baseline, hashes and exact substitutions are recorded in meta/migration_reports/clique_number.spec.json.
    - [Legacy]: X121's helper is already upstream [ω([set: G])] (a conversion).
    - [X121Legacy]: the row over the frozen helper; C13's live treewidth and tree-alpha helpers stay live, and the
      unguarded class and the two class-uniform witnesses are kept verbatim.
    - [X121Original]: the complete row, composing the frozen helper with C13's frozen treewidth, decomposition and
      tree-alpha bodies (text at 58d6d60).  C13's module is aliased, not imported; the bridge reuses C13's
      certificate. *)
From GTBase Require Import base.
From Minor.conjectures Require Import X27 X121.
From Minor.migration Require bag_decompositions.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** C13's certificate module, aliased without Import: its module names coincide with this file's. *)
Module C13 := Minor.migration.bag_decompositions.

Module Legacy.

Definition x121_omega (G : sgraph) : nat := ω([set: G]).

End Legacy.

Module X121Legacy.

Definition dallard_milanic_storgel_tw_omega_tree_alpha_statement : Prop :=
  forall C : sgraph -> Prop,
    (exists f : nat -> nat,
       forall G : sgraph, C G -> x27_treewidth_at_most G (f (Legacy.x121_omega G)))
    <->
    (exists k : nat,
       forall G : sgraph, C G -> x121_tree_alpha_le G k).

End X121Legacy.

Module X121Original.

Definition dallard_milanic_storgel_tw_omega_tree_alpha_statement : Prop :=
  forall C : sgraph -> Prop,
    (exists f : nat -> nat,
       forall G : sgraph, C G -> C13.Legacy.x27_treewidth_at_most G (f (Legacy.x121_omega G)))
    <->
    (exists k : nat,
       forall G : sgraph, C G -> C13.Legacy.x121_tree_alpha_le G k).

End X121Original.

Lemma x121_omega_compat (G : sgraph) :
  Legacy.x121_omega G = x121_omega G.
Proof. by []. Qed.

Lemma dallard_milanic_storgel_tw_omega_tree_alpha_statement_compat :
  X121Legacy.dallard_milanic_storgel_tw_omega_tree_alpha_statement <-> dallard_milanic_storgel_tw_omega_tree_alpha_statement.
Proof. exact: iff_refl. Qed.

(** Complete X121: a conversion to C13's frozen row, then C13's certificate. *)
Lemma dallard_milanic_storgel_tw_omega_tree_alpha_statement_original_compat :
  X121Original.dallard_milanic_storgel_tw_omega_tree_alpha_statement <-> dallard_milanic_storgel_tw_omega_tree_alpha_statement.
Proof. exact: C13.dallard_milanic_storgel_tw_omega_tree_alpha_statement_compat. Qed.
