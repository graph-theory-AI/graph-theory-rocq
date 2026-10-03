(** * Extremal.migration.induced_free -- frozen induced-free certificates

    Batch A, family [induced_free].  [Legacy] freezes the six conjecture-local
    helpers verbatim as they stood at 9e03072, before the migration.  Each
    [XnnLegacy] module freezes the affected dependency chain of one statement,
    the statement included, with every reference to a helper of this family
    replaced by its frozen copy: X57 through [x57_sparse_strong_eh_property],
    X61 through [x61_induced_saturated].  The live helpers now unfold to
    [GTBase.common.induced_free]; the theorems below prove each frozen body
    equivalent to its live counterpart.

    [X61Original] goes one step further back: its chain also uses M1's frozen
    edge set ([simple_edges.Legacy.edge_set], the comprehension [x60_edge_set]
    had before M1), so [x61_statement_original_compat] relates the statement
    body from before both migrations to the live one.

    The cross-file consumer implications_X223.v keeps its statements; only the
    e076 proof step that opened the old [inhabited] wrapper changed.  Source
    hashes and the per-row theorem names are recorded in
    meta/migration_reports/induced_free.md. *)

From GTBase Require Import base.
From Extremal.conjectures Require Import X49 X56 X57 X58 X60 X61 X118 X120.
From Extremal.migration Require simple_edges.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition x56_induced_free (G H : sgraph) : Prop :=
  forall S : {set G}, ~ inhabited (induced S ≃ H).

Definition x57_induced_free (G H : sgraph) : Prop :=
  forall S : {set G}, ~ inhabited (induced S ≃ H).

Definition x58_induced_free (G H : sgraph) : Prop :=
  forall S : {set G}, ~ inhabited (induced S ≃ H).

Definition x61_induced_free (G H : sgraph) : Prop :=
  forall S : {set G}, ~ inhabited (induced S ≃ H).

Definition x118_induced_free (G H : sgraph) : Prop :=
  forall S : {set G}, ~ inhabited (induced S ≃ H).

Definition x120_induced_free (G H : sgraph) : Prop :=
  forall S : {set G}, ~ inhabited (induced S ≃ H).

End Legacy.

Lemma x56_induced_free_compat (G H : sgraph) :
  Legacy.x56_induced_free G H <-> x56_induced_free G H.
Proof. exact: iff_sym (induced_free_inhabited G H). Qed.

Lemma x57_induced_free_compat (G H : sgraph) :
  Legacy.x57_induced_free G H <-> x57_induced_free G H.
Proof. exact: iff_sym (induced_free_inhabited G H). Qed.

Lemma x58_induced_free_compat (G H : sgraph) :
  Legacy.x58_induced_free G H <-> x58_induced_free G H.
Proof. exact: iff_sym (induced_free_inhabited G H). Qed.

Lemma x61_induced_free_compat (G H : sgraph) :
  Legacy.x61_induced_free G H <-> x61_induced_free G H.
Proof. exact: iff_sym (induced_free_inhabited G H). Qed.

Lemma x118_induced_free_compat (G H : sgraph) :
  Legacy.x118_induced_free G H <-> x118_induced_free G H.
Proof. exact: iff_sym (induced_free_inhabited G H). Qed.

Lemma x120_induced_free_compat (G H : sgraph) :
  Legacy.x120_induced_free G H <-> x120_induced_free G H.
Proof. exact: iff_sym (induced_free_inhabited G H). Qed.

(** ** X56 *)

Module X56Legacy.

Definition statement : Prop :=
  exists c : nat,
    0 < c /\
    forall G : sgraph,
      0 < #|G| ->
      Legacy.x56_induced_free G (cycle_graph 8) ->
      Legacy.x56_induced_free G (x56_complement (cycle_graph 8)) ->
      exists S : {set G},
        x56_homogeneous_set S /\
        #|G| <= (#|S|) ^ c.

End X56Legacy.

Lemma x56_statement_compat :
  X56Legacy.statement <-> c8_complement_c8_erdos_hajnal_statement.
Proof.
split=> -[c [c0 bound]]; exists c; split=> // G G0 c8 cc8.
- by apply: bound G0 _ _; apply/x56_induced_free_compat.
- by apply: bound G0 _ _; apply/x56_induced_free_compat.
Qed.

(** ** X57 *)

Module X57Legacy.

Definition sparse_strong_eh_property (H : sgraph) : Prop :=
  exists eps_num eps_den : nat,
    0 < eps_num /\ eps_num <= eps_den /\
    forall G : sgraph,
      2 <= #|G| ->
      Legacy.x57_induced_free G H ->
      (exists v : G, eps_num * #|G| <= eps_den * #|N(v)|) \/
      (exists A B : {set G},
        x57_anticomplete A B /\
        eps_num * #|G| <= eps_den * #|A| /\
        eps_num * #|G| <= eps_den * #|B|).

Definition statement : Prop :=
  forall H : sgraph,
    sparse_strong_eh_property H <-> is_forest [set: H].

End X57Legacy.

Lemma x57_sparse_strong_eh_property_compat (H : sgraph) :
  X57Legacy.sparse_strong_eh_property H <-> x57_sparse_strong_eh_property H.
Proof.
split=> -[n [d [n0 [nd prop]]]]; exists n, d; do 2!split=> //; move=> G G2 free.
- by apply: prop G2 _; apply/x57_induced_free_compat.
- by apply: prop G2 _; apply/x57_induced_free_compat.
Qed.

Lemma x57_statement_compat :
  X57Legacy.statement <-> sparse_strong_eh_iff_forest_statement.
Proof.
split=> statement H.
- exact: iff_trans (iff_sym (x57_sparse_strong_eh_property_compat H)) (statement H).
- exact: iff_trans (x57_sparse_strong_eh_property_compat H) (statement H).
Qed.

(** ** X58 *)

Module X58Legacy.

Definition statement : Prop :=
  forall H : sgraph,
    exists eps_num eps_den : nat,
      0 < eps_num /\ eps_num <= eps_den /\
      forall G : sgraph,
        1 < #|G| ->
        Legacy.x58_induced_free G H ->
        x58_epsilon_bounded G eps_num eps_den ->
        exists A B : {set G},
          x58_anticomplete A B /\
          eps_num ^ eps_den * #|G| ^ eps_num <= eps_den ^ eps_den * #|A| ^ eps_den /\
          eps_num * #|G| <= eps_den * #|B|.

End X58Legacy.

Lemma x58_statement_compat :
  X58Legacy.statement <-> epsilon_bounded_h_free_anticomplete_pair_statement.
Proof.
split=> statement H; have [n [d [n0 [nd bound]]]] := statement H;
  exists n, d; do 2!split=> //; move=> G G1 free eps.
- by apply: bound G1 _ eps; apply/x58_induced_free_compat.
- by apply: bound G1 _ eps; apply/x58_induced_free_compat.
Qed.

(** ** X61 *)

Module X61Legacy.

Definition induced_saturated (H G : sgraph) : Prop :=
  Legacy.x61_induced_free G H /\
  (forall a b : G,
    a != b ->
    ~~ (a -- b) ->
    Legacy.x61_induced_free (@x49_add_edge_graph G a b) H -> False) /\
  forall e : {set G},
    e \in x60_edge_set G ->
    Legacy.x61_induced_free (@x60_delete_edge_graph G e) H -> False.

Definition statement : Prop :=
  exists F : sgraph -> Prop,
    x61_infinite_family F /\
    forall H : sgraph,
      F H ->
      x61_neither_clique_nor_stable H /\
      forall G : sgraph, ~ induced_saturated H G.

End X61Legacy.

Lemma x61_induced_saturated_compat (H G : sgraph) :
  X61Legacy.induced_saturated H G <-> x61_induced_saturated H G.
Proof.
split=> -[free [add del]]; (split; [|split]).
- exact/x61_induced_free_compat.
- by move=> a b ab nab /x61_induced_free_compat; exact: add.
- by move=> e eE /x61_induced_free_compat; exact: del.
- exact/x61_induced_free_compat.
- by move=> a b ab nab /x61_induced_free_compat; exact: add.
- by move=> e eE /x61_induced_free_compat; exact: del.
Qed.

Lemma x61_statement_compat :
  X61Legacy.statement <-> infinite_family_without_finite_induced_saturation_statement.
Proof.
split=> -[F [inf members]]; exists F; split=> // H FH;
  have [neither nosat] := members H FH; split=> // G /x61_induced_saturated_compat;
  exact: nosat.
Qed.

Module X61Original.

Definition induced_saturated (H G : sgraph) : Prop :=
  Legacy.x61_induced_free G H /\
  (forall a b : G,
    a != b ->
    ~~ (a -- b) ->
    Legacy.x61_induced_free (@x49_add_edge_graph G a b) H -> False) /\
  forall e : {set G},
    e \in simple_edges.Legacy.edge_set G ->
    Legacy.x61_induced_free (@x60_delete_edge_graph G e) H -> False.

Definition statement : Prop :=
  exists F : sgraph -> Prop,
    x61_infinite_family F /\
    forall H : sgraph,
      F H ->
      x61_neither_clique_nor_stable H /\
      forall G : sgraph, ~ induced_saturated H G.

End X61Original.

Lemma x61_induced_saturated_original_compat (H G : sgraph) :
  X61Original.induced_saturated H G <-> x61_induced_saturated H G.
Proof.
rewrite -x61_induced_saturated_compat /X61Original.induced_saturated.
by rewrite /X61Legacy.induced_saturated simple_edges.x60_edge_set_compat.
Qed.

Lemma x61_statement_original_compat :
  X61Original.statement <-> infinite_family_without_finite_induced_saturation_statement.
Proof.
split=> -[F [inf members]]; exists F; split=> // H FH;
  have [neither nosat] := members H FH; split=> // G /x61_induced_saturated_original_compat;
  exact: nosat.
Qed.

(** ** X118 *)

Module X118Legacy.

Definition statement : Prop :=
  forall H : sgraph,
    exists e1 e2 s1 s2 : nat,
      [/\ 0 < e1, 0 < e2, 0 < s1 & 0 < s2] /\
      forall G : sgraph,
        1 < #|G| ->
        Legacy.x118_induced_free G H ->
        forall c1 c2 : nat,
          0 < c2 -> 2 * c1 <= c2 ->
          exists A B : {set G},
            [/\ [disjoint A & B],
                e1 ^ s2 * c1 ^ s1 * #|G| ^ s2 <= e2 ^ s2 * c2 ^ s1 * #|A| ^ s2,
                e1 * #|G| <= e2 * #|B|
              & (c2 * x118_edges_between A B <= c1 * (#|A| * #|B|) \/
                 (c2 - c1) * (#|A| * #|B|) <= c2 * x118_edges_between A B)].

End X118Legacy.

Lemma x118_statement_compat :
  X118Legacy.statement <-> conlon_fox_sudakov_dense_pair_statement.
Proof.
split=> statement H; have [e1 [e2 [s1 [s2 [pos bound]]]]] := statement H;
  exists e1, e2, s1, s2; split=> // G G1 free.
- by apply: bound G1 _; apply/x118_induced_free_compat.
- by apply: bound G1 _; apply/x118_induced_free_compat.
Qed.

(** ** X120 *)

Module X120Legacy.

Definition statement : Prop :=
  forall H : sgraph,
    exists a1 a2 b1 b2 : nat,
      [/\ 0 < a1, 0 < a2, 0 < b1 & 0 < b2] /\
      forall G : sgraph,
        2 <= #|G| ->
        Legacy.x120_induced_free G H ->
        forall xn xd : nat,
          0 < xn -> 2 * xn < xd ->
          exists A B : {set G},
            [/\ [disjoint A & B],
                xn ^ (a1 * b2) * #|G| ^ (b1 * a2)
                  <= xd ^ (a1 * b2) * #|A| ^ (a2 * b2),
                xn ^ (a1 * b2) * #|G| ^ (b1 * a2)
                  <= xd ^ (a1 * b2) * #|B| ^ (a2 * b2)
              & (xd * x120_edges_between A B <= xn * (#|A| * #|B|) \/
                 xd * x120_nonedges_between A B <= xn * (#|A| * #|B|))].

End X120Legacy.

Lemma x120_statement_compat :
  X120Legacy.statement <-> conlon_fox_sudakov_sparse_pair_statement.
Proof.
split=> statement H; have [a1 [a2 [b1 [b2 [pos bound]]]]] := statement H;
  exists a1, a2, b1, b2; split=> // G G2 free.
- by apply: bound G2 _; apply/x120_induced_free_compat.
- by apply: bound G2 _; apply/x120_induced_free_compat.
Qed.
