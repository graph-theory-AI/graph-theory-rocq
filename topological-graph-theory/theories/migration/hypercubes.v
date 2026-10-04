(** A23 hypercubes (topological): the frozen D3cr hypercube and the crossing-number row over it.  Baseline, hashes
    and exact substitutions are recorded in meta/migration_reports/hypercubes.spec.json.
    - [Legacy]: the local Fixpoint equals [GTBase.hypercubes.product_hypercube d] as a graph, by induction on the
      dimension.
    - [D3crLegacy]: both positive error inputs, the threshold, the existential achievable crossing count in the window
      and the universal lower bound, over the frozen cube; the split-planarization proxy and the partial status are
      unchanged. *)
From Corelib Require Import Setoid Morphisms.
From GTBase Require Import base hypercubes.
From Topological Require Import foundations.crossing.
From Topological.conjectures Require Import D3cr.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Fixpoint hypercube (d : nat) : sgraph :=
  match d with
  | 0 => 'K_1
  | d'.+1 => cartesian_product 'K_2 (hypercube d')
  end.

End Legacy.

Module D3crLegacy.

Definition the_crossing_number_of_the_hypercube_statement : Prop :=
  forall (eps_num eps_den : nat),
    (0 < eps_num)%N -> (0 < eps_den)%N ->
    exists N : nat,
      forall d : nat,
        (N <= d)%N ->
        (exists k : nat,
            crossing_planar_in k (Legacy.hypercube d) /\
            (eps_den * ((32 * k - 5 * 4 ^ d) + (5 * 4 ^ d - 32 * k))
               < eps_num * (32 * 4 ^ d))%N) /\
        (forall k : nat,
            crossing_planar_in k (Legacy.hypercube d) ->
            (eps_den * (5 * 4 ^ d)
               < eps_den * (32 * k) + eps_num * (32 * 4 ^ d))%N).

End D3crLegacy.

(** The same graph record: the frozen Fixpoint against [GTBase.hypercubes.product_hypercube], by induction. *)
Lemma hypercube_compat (d : nat) :
  Legacy.hypercube d = hypercube d.
Proof.
elim: d => [//|d IH].
by rewrite /= IH.
Qed.

Lemma the_crossing_number_of_the_hypercube_statement_compat :
  D3crLegacy.the_crossing_number_of_the_hypercube_statement <->
  the_crossing_number_of_the_hypercube_statement.
Proof.
rewrite /D3crLegacy.the_crossing_number_of_the_hypercube_statement.
setoid_rewrite hypercube_compat.
reflexivity.
Qed.
