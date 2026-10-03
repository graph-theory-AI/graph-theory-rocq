(** A8 ordered pair counts: the four frozen extremal counts, the two X223 chains and the four
    corpus rows, then the complete X118/X120 rows over A1's frozen induced-free helpers.
    Baseline, hashes and exact substitutions are recorded in
    meta/migration_reports/edges_between.spec.json.
    - [Legacy]: the four counts at the baseline.  X118/X120 already had the bodies of
      [edges_between] / [nonedges_between] (conversions); X223 associates [&&] the other way
      ([x223_edges_between_compat], by [andbA]).
    - [X118Legacy], [X120Legacy], [X223Legacy]: the chains and rows over these frozen counts; A1's
      induced-free helpers stay live there.
    - [X118Original], [X120Original]: the 9e03072 rows, pre-A1 and pre-A8. *)
From Corelib Require Import Setoid Morphisms.
From GTBase Require Import base.
From Extremal.conjectures Require Import X118 X120 X223.
From Extremal.migration Require induced_free.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A1's certificate module, aliased without Import: its [Legacy] module name coincides with
    this file's. *)
Module A1 := Extremal.migration.induced_free.

#[local] Instance and3_iff_morphism : Proper (iff ==> iff ==> iff ==> iff) and3.
Proof. by move=> a a' ha b b' hb c c' hc; split=> -[x y z]; split; by [apply/ha|apply/hb|apply/hc]. Qed.

#[local] Instance and4_iff_morphism : Proper (iff ==> iff ==> iff ==> iff ==> iff) and4.
Proof.
by move=> a a' ha b b' hb c c' hc d d' hd; split=> -[x y z w]; split;
  by [apply/ha|apply/hb|apply/hc|apply/hd].
Qed.

Module Legacy.

Definition x118_edges_between (G : sgraph) (A B : {set G}) : nat :=
  #|[set p : G * G | [&& p.1 \in A, p.2 \in B & p.1 -- p.2]]|.

Definition x120_edges_between (G : sgraph) (A B : {set G}) : nat :=
  #|[set p : G * G | [&& p.1 \in A, p.2 \in B & p.1 -- p.2]]|.

Definition x120_nonedges_between (G : sgraph) (A B : {set G}) : nat :=
  #|[set p : G * G | [&& p.1 \in A, p.2 \in B & ~~ (p.1 -- p.2)]]|.

Definition x223_edges_between (G : sgraph) (A B : {set G}) : nat :=
  #|[set uv : G * G | (uv.1 \in A) && (uv.2 \in B) && (uv.1 -- uv.2)]|.

End Legacy.

Module X118Legacy.

Definition conlon_fox_sudakov_dense_pair_statement : Prop :=
  forall H : sgraph,
    exists e1 e2 s1 s2 : nat,
      [/\ 0 < e1, 0 < e2, 0 < s1 & 0 < s2] /\
      forall G : sgraph,
        1 < #|G| ->
        x118_induced_free G H ->
        forall c1 c2 : nat,
          0 < c2 -> 2 * c1 <= c2 ->
          exists A B : {set G},
            [/\ [disjoint A & B],
                e1 ^ s2 * c1 ^ s1 * #|G| ^ s2 <= e2 ^ s2 * c2 ^ s1 * #|A| ^ s2,
                e1 * #|G| <= e2 * #|B|
              & (c2 * Legacy.x118_edges_between A B <= c1 * (#|A| * #|B|) \/
                 (c2 - c1) * (#|A| * #|B|) <= c2 * Legacy.x118_edges_between A B)].

End X118Legacy.

Module X120Legacy.

Definition conlon_fox_sudakov_sparse_pair_statement : Prop :=
  forall H : sgraph,
    exists a1 a2 b1 b2 : nat,
      [/\ 0 < a1, 0 < a2, 0 < b1 & 0 < b2] /\
      forall G : sgraph,
        2 <= #|G| ->
        x120_induced_free G H ->
        forall xn xd : nat,
          0 < xn -> 2 * xn < xd ->
          exists A B : {set G},
            [/\ [disjoint A & B],
                xn ^ (a1 * b2) * #|G| ^ (b1 * a2)
                  <= xd ^ (a1 * b2) * #|A| ^ (a2 * b2),
                xn ^ (a1 * b2) * #|G| ^ (b1 * a2)
                  <= xd ^ (a1 * b2) * #|B| ^ (a2 * b2)
              & (xd * Legacy.x120_edges_between A B <= xn * (#|A| * #|B|) \/
                 xd * Legacy.x120_nonedges_between A B <= xn * (#|A| * #|B|))].

End X120Legacy.

Module X223Legacy.

Definition sparse_pair (G : sgraph) (A B : {set G}) (a b : nat) : Prop :=
  [disjoint A & B] /\
  b * Legacy.x223_edges_between A B <= a * (#|A| * #|B|).

Definition ct_sparse (Gamma : sgraph) (a b t : nat) : Prop :=
  forall A B : {set Gamma}, t <= #|A| -> t <= #|B| ->
    b * Legacy.x223_edges_between A B <= (b - a) * (#|A| * #|B|).

Definition h_free_eps_bounded_sparse_pair_statement : Prop :=
  forall H : sgraph,
    exists p d s : nat,
      [/\ 0 < p, p <= d, 0 < s &
          forall G : sgraph,
            1 < #|G| ->
            induced_free G H ->
            x223_eps_bounded G p d ->
            forall a b : nat, 0 < b -> a <= b ->
              exists A B : {set G},
                [/\ sparse_pair A B a b,
                    a ^ s * (p * #|G|) <= d * (b ^ s * #|A|) &
                    p * #|G| <= d * #|B|]].

Definition induced_turan_even_cycle_sparse_statement : Prop :=
  forall a b l : nat,
    0 < a -> a <= b -> 0 < l ->
    exists C : nat,
      1 < C /\
      forall (Gamma : sgraph) (t : nat),
        ct_sparse Gamma a b t ->
        forall F : {set {set Gamma}},
          induced_free (del_edge_set Gamma F) (cycle_graph (2 * l)) ->
          #|E(del_edge_set Gamma F)| ^ l <= C ^ l * (t ^ l.-1 * #|Gamma| ^ l.+1).

End X223Legacy.

Module X118Original.

Definition conlon_fox_sudakov_dense_pair_statement : Prop :=
  forall H : sgraph,
    exists e1 e2 s1 s2 : nat,
      [/\ 0 < e1, 0 < e2, 0 < s1 & 0 < s2] /\
      forall G : sgraph,
        1 < #|G| ->
        A1.Legacy.x118_induced_free G H ->
        forall c1 c2 : nat,
          0 < c2 -> 2 * c1 <= c2 ->
          exists A B : {set G},
            [/\ [disjoint A & B],
                e1 ^ s2 * c1 ^ s1 * #|G| ^ s2 <= e2 ^ s2 * c2 ^ s1 * #|A| ^ s2,
                e1 * #|G| <= e2 * #|B|
              & (c2 * Legacy.x118_edges_between A B <= c1 * (#|A| * #|B|) \/
                 (c2 - c1) * (#|A| * #|B|) <= c2 * Legacy.x118_edges_between A B)].

End X118Original.

Module X120Original.

Definition conlon_fox_sudakov_sparse_pair_statement : Prop :=
  forall H : sgraph,
    exists a1 a2 b1 b2 : nat,
      [/\ 0 < a1, 0 < a2, 0 < b1 & 0 < b2] /\
      forall G : sgraph,
        2 <= #|G| ->
        A1.Legacy.x120_induced_free G H ->
        forall xn xd : nat,
          0 < xn -> 2 * xn < xd ->
          exists A B : {set G},
            [/\ [disjoint A & B],
                xn ^ (a1 * b2) * #|G| ^ (b1 * a2)
                  <= xd ^ (a1 * b2) * #|A| ^ (a2 * b2),
                xn ^ (a1 * b2) * #|G| ^ (b1 * a2)
                  <= xd ^ (a1 * b2) * #|B| ^ (a2 * b2)
              & (xd * Legacy.x120_edges_between A B <= xn * (#|A| * #|B|) \/
                 xd * Legacy.x120_nonedges_between A B <= xn * (#|A| * #|B|))].

End X120Original.

Lemma x118_edges_between_compat (G : sgraph) (A B : {set G}) : Legacy.x118_edges_between A B = x118_edges_between A B.
Proof. by []. Qed.

Lemma x120_edges_between_compat (G : sgraph) (A B : {set G}) : Legacy.x120_edges_between A B = x120_edges_between A B.
Proof. by []. Qed.

Lemma x120_nonedges_between_compat (G : sgraph) (A B : {set G}) : Legacy.x120_nonedges_between A B = x120_nonedges_between A B.
Proof. by []. Qed.

Lemma x223_edges_between_compat (G : sgraph) (A B : {set G}) : Legacy.x223_edges_between A B = x223_edges_between A B.
Proof.
rewrite /Legacy.x223_edges_between /x223_edges_between /edges_between.
by apply: eq_card => p; rewrite !inE andbA.
Qed.

Lemma conlon_fox_sudakov_dense_pair_statement_compat :
  X118Legacy.conlon_fox_sudakov_dense_pair_statement <-> conlon_fox_sudakov_dense_pair_statement.
Proof. exact: iff_refl. Qed.

Lemma conlon_fox_sudakov_sparse_pair_statement_compat :
  X120Legacy.conlon_fox_sudakov_sparse_pair_statement <-> conlon_fox_sudakov_sparse_pair_statement.
Proof. exact: iff_refl. Qed.

Lemma sparse_pair_compat (G : sgraph) (A B : {set G}) (a b : nat) :
  X223Legacy.sparse_pair A B a b <-> x223_sparse_pair A B a b.
Proof.
rewrite /X223Legacy.sparse_pair /x223_sparse_pair x223_edges_between_compat.
exact: iff_refl.
Qed.

Lemma ct_sparse_compat (Gamma : sgraph) (a b t : nat) :
  X223Legacy.ct_sparse Gamma a b t <-> x223_ct_sparse Gamma a b t.
Proof.
split=> h A B tA tB; move: (h A B tA tB); by rewrite x223_edges_between_compat.
Qed.

Lemma h_free_eps_bounded_sparse_pair_statement_compat :
  X223Legacy.h_free_eps_bounded_sparse_pair_statement <-> h_free_eps_bounded_sparse_pair_statement.
Proof.
rewrite /X223Legacy.h_free_eps_bounded_sparse_pair_statement /h_free_eps_bounded_sparse_pair_statement; setoid_rewrite sparse_pair_compat; reflexivity.
Qed.

Lemma induced_turan_even_cycle_sparse_statement_compat :
  X223Legacy.induced_turan_even_cycle_sparse_statement <-> induced_turan_even_cycle_sparse_statement.
Proof.
rewrite /X223Legacy.induced_turan_even_cycle_sparse_statement /induced_turan_even_cycle_sparse_statement; setoid_rewrite ct_sparse_compat; reflexivity.
Qed.

Lemma conlon_fox_sudakov_dense_pair_statement_original_compat :
  X118Original.conlon_fox_sudakov_dense_pair_statement <-> conlon_fox_sudakov_dense_pair_statement.
Proof.
split=> statement H; have [e1 [e2 [s1 [s2 [pos bound]]]]] := statement H;
  exists e1, e2, s1, s2; split=> // G G1 free.
- by apply: bound G1 _; apply/A1.x118_induced_free_compat.
- by apply: bound G1 _; apply/A1.x118_induced_free_compat.
Qed.

Lemma conlon_fox_sudakov_sparse_pair_statement_original_compat :
  X120Original.conlon_fox_sudakov_sparse_pair_statement <-> conlon_fox_sudakov_sparse_pair_statement.
Proof.
split=> statement H; have [a1 [a2 [b1 [b2 [pos bound]]]]] := statement H;
  exists a1, a2, b1, b2; split=> // G G2 free.
- by apply: bound G2 _; apply/A1.x120_induced_free_compat.
- by apply: bound G2 _; apply/A1.x120_induced_free_compat.
Qed.
