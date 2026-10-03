(** * GTMisc.migration.simple_path — frozen simple-path chains (library migration B6)

    Batch B, family [simple-path] (meta/library_primitives/simple-path.json).
    [Legacy] freezes the helper [x14_genuine_path] verbatim as it stood at 95cba2c;
    the live helper now unfolds to [GTBase.walks_paths.seq_simple_path p], whose
    body is the same match, so the certificates are kernel-checked conversions.
    [X14Legacy] freezes the rainbow path (its edge list [x14_path_edges] is the
    unchanged live one) and Andersen's statement (exactly [n.-1] vertices, a
    singleton when [n = 2]); [X62Legacy] the cross-module edge-cover row (a cover,
    not a disjoint decomposition).
    Source hashes, the exact substitutions and the per-row theorem names are
    recorded in meta/migration_reports/simple_path.md. *)

From GTBase Require Import base.
From GTMisc.conjectures Require Import X14 X62.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x14_genuine_path (G : sgraph) (p : seq G) : Prop :=
  match p with
  | [::] => False
  | x :: q => uniq p /\ path (--) x q
  end.

End Legacy.

Module X14Legacy.

Definition rainbow_path
    (G : sgraph) (C : finType) (col : {set G} -> C) (p : seq G) : Prop :=
  @Legacy.x14_genuine_path G p /\ uniq (map col (@x14_path_edges G p)).

Definition andersen_rainbow_path_statement : Prop :=
  forall (n : nat) (C : finType) (col : {set complete n} -> C),
    2 <= n ->
    @x14_proper_edge_colouring (complete n) C col ->
    exists p : seq (complete n),
      @rainbow_path (complete n) C col p /\ size p = n.-1.

End X14Legacy.

Module X62Legacy.

Definition rainbow_paths_linear_edge_cover_statement : Prop :=
  exists c : nat,
    forall (G : sgraph) (C : finType) (col : {set G} -> C),
      x14_proper_edge_colouring col ->
      exists paths : seq (seq G),
        size paths <= c * #|G| /\
        (forall p : seq G, p \in paths -> X14Legacy.rainbow_path col p) /\
        x62_edges_covered_by_paths paths.

End X62Legacy.

(** ** Certificates *)

Lemma x14_genuine_path_compat (G : sgraph) (p : seq G) :
  Legacy.x14_genuine_path p = x14_genuine_path p.
Proof. by []. Qed.

Lemma x14_rainbow_path_compat (G : sgraph) (C : finType) (col : {set G} -> C) (p : seq G) :
  @X14Legacy.rainbow_path G C col p <-> @x14_rainbow_path G C col p.
Proof. exact: iff_refl. Qed.

Lemma andersen_rainbow_path_statement_compat :
  X14Legacy.andersen_rainbow_path_statement <-> andersen_rainbow_path_statement.
Proof. exact: iff_refl. Qed.

Lemma rainbow_paths_linear_edge_cover_statement_compat :
  X62Legacy.rainbow_paths_linear_edge_cover_statement <-> rainbow_paths_linear_edge_cover_statement.
Proof. exact: iff_refl. Qed.
