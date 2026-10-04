(** A23 hypercubes (packing): the frozen U9 hypercube with its complete construction support, U9's copy/saturation
    chains and two rows, and X226's seven subcube-partition chains and row.  Baseline, hashes and exact substitutions
    are recorded in meta/migration_reports/hypercubes.spec.json.
    - [Legacy]: U9's [Section Hypercube] verbatim -- [hc_rel], the complete [hc_sym]/[hc_irrefl] proofs and
      [hypercube := SGraph hc_sym hc_irrefl] -- with its Section discharge over [d].  It and
      [GTBase.hypercubes.tuple_hypercube d] have the same [d.-tuple bool] carrier and the same adjacency (exactly one
      differing coordinate), but different opaque proof fields: they are related by pointwise adjacency and the
      identity isomorphism, not by an equation between graph records.
    - [U9Legacy]: the injective, edge-preserving Q_3 copy through the supplied edge, weak saturation (with
      [take i.+1], the pair-cardinality guard and the unique missing-edge enumeration), the attained minimum, the
      matching row (the same supplied M, [2 <= d], the Hamilton cycle c and [M \subset cycle_edgesG]) and the
      weak-saturation PROXY row ([8 <= n], well-definedness only).
    - [X226Legacy]: the subcubes of option-coordinate assignments read through [tnth] on the frozen tuples, the
      partitions, [x226_f], [x226_f_dim_le2] and the row (positive q, a threshold d0, then every d >= d0, the natural
      predecessor and powers); the independent [x226_subcube_dim] stays live.
    The frozen chains and rows are convertible to the live ones: same carrier and convertible adjacency. *)
From Corelib Require Import Setoid Morphisms.
From GTBase Require Import base hypercubes.
From Packing.conjectures Require Import U9 X226.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Section Hypercube.
Variable d : nat.
Definition hc_rel : rel (d.-tuple bool) :=
  fun x y => #|[set i : 'I_d | tnth x i != tnth y i]| == 1.
Lemma hc_sym : symmetric hc_rel.
Proof.
move=> x y; rewrite /hc_rel.
have -> : [set i : 'I_d | tnth x i != tnth y i]
        = [set i : 'I_d | tnth y i != tnth x i]
  by apply/setP=> i; rewrite !inE eq_sym.
by [].
Qed.
Lemma hc_irrefl : irreflexive hc_rel.
Proof.
move=> x; rewrite /hc_rel.
have -> : [set i : 'I_d | tnth x i != tnth x i] = set0
  by apply/setP=> i; rewrite !inE eqxx.
by rewrite cards0.
Qed.
Definition hypercube : sgraph := SGraph hc_sym hc_irrefl.
End Hypercube.

End Legacy.

Module U9Legacy.

Definition copy_Q3_through (n : nat) (E : {set {set 'I_n}}) (e : {set 'I_n}) : Prop :=
  exists f : Legacy.hypercube 3 -> 'I_n,
    [/\ injective f,
        (forall x y : Legacy.hypercube 3, x -- y -> [set f x; f y] \in E)
      & (exists x y : Legacy.hypercube 3, x -- y /\ [set f x; f y] = e)].

Definition weakly_saturates (n : nat) (F : {set {set 'I_n}}) : Prop :=
  (forall e : {set 'I_n}, e \in F -> #|e| == 2) /\
  exists s : seq {set 'I_n},
    [/\ uniq s,
        (forall e : {set 'I_n}, (e \in s) = ((#|e| == 2) && (e \notin F)))
      & (forall i : nat, i < size s ->
           U9Legacy.copy_Q3_through (F :|: [set x in take i.+1 s]) (nth set0 s i))].

Definition is_wsat (n : nat) (m : nat) : Prop :=
  (exists F : {set {set 'I_n}}, U9Legacy.weakly_saturates F /\ #|F| = m) /\
  (forall F : {set {set 'I_n}}, U9Legacy.weakly_saturates F -> m <= #|F|).

Definition matchings_extends_to_hamilton_cycles_in_hypercubes_statement : Prop :=
  forall (d : nat) (M : {set {set Legacy.hypercube d}}),
    2 <= d -> is_matching_edges M ->
    exists c : seq (Legacy.hypercube d),
      hamiltonian_cycleG (Legacy.hypercube d) c /\
      M \subset cycle_edgesG (Legacy.hypercube d) c.

Definition weak_saturation_of_the_cube_in_the_clique_statement : Prop :=
  forall n : nat, 8 <= n -> exists m : nat, U9Legacy.is_wsat n m.

End U9Legacy.

Module X226Legacy.

Definition x226_subcube (d : nat) (c : {ffun 'I_d -> option bool}) :
    {set Legacy.hypercube d} :=
  [set x : Legacy.hypercube d | [forall i : 'I_d, oapp (fun b => tnth x i == b) true (c i)]].

Definition x226_is_subcube (d : nat) (S : {set Legacy.hypercube d}) : bool :=
  [exists c : {ffun 'I_d -> option bool}, S == X226Legacy.x226_subcube c].

Definition x226_is_subcube_dim_le (d k : nat) (S : {set Legacy.hypercube d}) : bool :=
  [exists c : {ffun 'I_d -> option bool},
      (S == X226Legacy.x226_subcube c) && (x226_subcube_dim c <= k)].

Definition x226_subcube_partitions (d : nat) : {set {set {set Legacy.hypercube d}}} :=
  [set P : {set {set Legacy.hypercube d}} |
     partition P [set: Legacy.hypercube d] && [forall S in P, X226Legacy.x226_is_subcube S]].

Definition x226_subcube_partitions_dim_le (d k : nat) :
    {set {set {set Legacy.hypercube d}}} :=
  [set P in X226Legacy.x226_subcube_partitions d | [forall S in P, @X226Legacy.x226_is_subcube_dim_le d k S]].

Definition x226_f (d : nat) : nat := #|X226Legacy.x226_subcube_partitions d|.

Definition x226_f_dim_le2 (d : nat) : nat := #|X226Legacy.x226_subcube_partitions_dim_le d 2|.

Definition subcube_partition_count_ratio_subexponential_statement : Prop :=
  forall q : nat,
    0 < q ->
    exists d0 : nat,
      forall d : nat, d0 <= d ->
        X226Legacy.x226_f d ^ q <= 2 ^ (2 ^ d.-1) * X226Legacy.x226_f_dim_le2 d ^ q.

End X226Legacy.

(** The frozen construction and [GTBase.hypercubes.tuple_hypercube]: the same carrier, the same adjacency, and the
    identity isomorphism -- not an equation between their opaque proof fields. *)
Lemma hypercube_compat (d : nat) :
  @edge_rel (Legacy.hypercube d) =2 @edge_rel (hypercube d).
Proof.
by [].
Qed.

Lemma hypercube_diso (d : nat) : Legacy.hypercube d ≃ hypercube d.
Proof. by rewrite /Legacy.hypercube /hypercube /tuple_hypercube; apply: eq_diso => x y. Qed.

Lemma copy_Q3_through_compat (n : nat) (E : {set {set 'I_n}}) (e : {set 'I_n}) :
  U9Legacy.copy_Q3_through E e <-> copy_Q3_through E e.
Proof.
rewrite /U9Legacy.copy_Q3_through.
reflexivity.
Qed.

Lemma weakly_saturates_compat (n : nat) (F : {set {set 'I_n}}) :
  U9Legacy.weakly_saturates F <-> weakly_saturates F.
Proof.
rewrite /U9Legacy.weakly_saturates.
reflexivity.
Qed.

Lemma is_wsat_compat (n m : nat) :
  U9Legacy.is_wsat n m <-> is_wsat n m.
Proof.
rewrite /U9Legacy.is_wsat.
reflexivity.
Qed.

Lemma matchings_extends_to_hamilton_cycles_in_hypercubes_statement_compat :
  U9Legacy.matchings_extends_to_hamilton_cycles_in_hypercubes_statement <->
  matchings_extends_to_hamilton_cycles_in_hypercubes_statement.
Proof.
rewrite /U9Legacy.matchings_extends_to_hamilton_cycles_in_hypercubes_statement.
reflexivity.
Qed.

Lemma weak_saturation_of_the_cube_in_the_clique_statement_compat :
  U9Legacy.weak_saturation_of_the_cube_in_the_clique_statement <->
  weak_saturation_of_the_cube_in_the_clique_statement.
Proof.
rewrite /U9Legacy.weak_saturation_of_the_cube_in_the_clique_statement.
setoid_rewrite is_wsat_compat.
reflexivity.
Qed.

(** X226: the same subcubes, partitions and natural counts over the frozen tuples. *)
Lemma x226_subcube_compat (d : nat) (c : {ffun 'I_d -> option bool}) :
  X226Legacy.x226_subcube c = x226_subcube c.
Proof.
by [].
Qed.

Lemma x226_is_subcube_compat (d : nat) (S : {set hypercube d}) :
  X226Legacy.x226_is_subcube S = x226_is_subcube S.
Proof.
by [].
Qed.

Lemma x226_is_subcube_dim_le_compat (d k : nat) (S : {set hypercube d}) :
  X226Legacy.x226_is_subcube_dim_le k S = x226_is_subcube_dim_le k S.
Proof.
by [].
Qed.

Lemma x226_subcube_partitions_compat (d : nat) :
  X226Legacy.x226_subcube_partitions d = x226_subcube_partitions d.
Proof.
by [].
Qed.

Lemma x226_subcube_partitions_dim_le_compat (d k : nat) :
  X226Legacy.x226_subcube_partitions_dim_le d k = x226_subcube_partitions_dim_le d k.
Proof.
by [].
Qed.

Lemma x226_f_compat (d : nat) :
  X226Legacy.x226_f d = x226_f d.
Proof.
by [].
Qed.

Lemma x226_f_dim_le2_compat (d : nat) :
  X226Legacy.x226_f_dim_le2 d = x226_f_dim_le2 d.
Proof.
by [].
Qed.

Lemma subcube_partition_count_ratio_subexponential_statement_compat :
  X226Legacy.subcube_partition_count_ratio_subexponential_statement <->
  subcube_partition_count_ratio_subexponential_statement.
Proof.
rewrite /X226Legacy.subcube_partition_count_ratio_subexponential_statement.
setoid_rewrite x226_f_compat.
setoid_rewrite x226_f_dim_le2_compat.
reflexivity.
Qed.


(** Combined B11/C25/A23 complete history. The existing per-row snapshots stay
    unchanged. This full row uses the actual frozen matching and cycle-edge
    providers plus A23's frozen tuple graph; only carrier/adjacency conversion
    is used to reuse C25's proved whole iff, never graph-record equality. *)
Require Packing.migration.matching Packing.migration.cycle_edges.
Module CM := Packing.migration.matching.
Module CE := Packing.migration.cycle_edges.

Module U9Original.

Definition matchings_extends_to_hamilton_cycles_in_hypercubes_statement : Prop := forall (d : nat) (M : {set {set Legacy.hypercube d}}), 2 <= d -> CM.U9MatchingLegacy.is_matching_edges M -> exists c : seq (Legacy.hypercube d), hamiltonian_cycleG (Legacy.hypercube d) c /\ M \subset CE.Legacy.cycle_edgesG (Legacy.hypercube d) c.

End U9Original.

Lemma matchings_extends_to_hamilton_cycles_in_hypercubes_statement_original_compat :
  U9Original.matchings_extends_to_hamilton_cycles_in_hypercubes_statement <->
  matchings_extends_to_hamilton_cycles_in_hypercubes_statement.
Proof.
exact: CM.matchings_extends_to_hamilton_cycles_in_hypercubes_statement_original_compat.
Qed.

Print Assumptions matchings_extends_to_hamilton_cycles_in_hypercubes_statement_original_compat.
