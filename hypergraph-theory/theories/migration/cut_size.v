(** A9 cut sizes: the frozen X209 cut-edge test and coloured cut count, its three chains and its row.
    Baseline, hashes and exact substitutions are recorded in meta/migration_reports/cut_size.spec.json.
    The cut count is over an ARBITRARY supplied family and colour map; no uniformity, nonemptiness or
    palette premise is added.  The minimum's documented carrier defect is frozen verbatim: it binds a
    fresh [T'] but its [E'] ranges over families on the OUTER carrier [T], so [T'] is unused. *)
From Corelib Require Import Setoid Morphisms.
From GTBase Require Import base.
From Hypergraph.conjectures Require Import X209.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

#[local] Instance and3_iff_morphism : Proper (iff ==> iff ==> iff ==> iff) and3.
Proof. by move=> a a' ha b b' hb c c' hc; split=> -[x y z]; split; by [apply/ha|apply/hb|apply/hc]. Qed.

#[local] Instance and4_iff_morphism : Proper (iff ==> iff ==> iff ==> iff ==> iff) and4.
Proof.
by move=> a a' ha b b' hb c c' hc d d' hd; split=> -[x y z w]; split;
  by [apply/ha|apply/hb|apply/hc|apply/hd].
Qed.

Module Legacy.

Definition x209_cut_edge
    (T : finType) (r : nat) (col : T -> 'I_r) (e : {set T}) : bool :=
  [exists x in e, [exists y in e, col x != col y]].

Definition x209_cut_size
    (T : finType) (E : {set {set T}}) (r : nat) (col : T -> 'I_r) : nat :=
  #|[set e in E | Legacy.x209_cut_edge col e]|.

End Legacy.

Module X209Legacy.

Definition is_max_r_cut
    (T : finType) (E : {set {set T}}) (r c : nat) : Prop :=
  exists col : T -> 'I_r,
    Legacy.x209_cut_size E col = c /\
    forall col' : T -> 'I_r, Legacy.x209_cut_size E col' <= c.

Definition scaled_excess
    (T : finType) (E : {set {set T}}) (r k x : nat) : Prop :=
  exists c : nat,
    is_max_r_cut E r c /\
    x = x209_expected_den r k * c - (x209_expected_den r k).-1 * #|E|.

Definition is_min_scaled_excess (r k m x : nat) : Prop :=
  exists (T : finType) (E : {set {set T}}),
    [/\ x209_uniform E k, #|E| = m, scaled_excess E r k x &
        forall (T' : finType) (E' : {set {set T}}) (y : nat),
          x209_uniform E' k ->
          #|E'| = m ->
          scaled_excess E' r k y ->
          x <= y].

Definition hypergraph_cut_excess_theta_sqrt_statement : Prop :=
  forall r k : nat,
    2 <= r ->
    r <= k ->
    exists excess : nat -> nat,
      (forall m : nat, is_min_scaled_excess r k m (excess m)) /\
      big_Theta_nat (fun m => (excess m) ^ 2) (fun m => m).

End X209Legacy.

(** Not a conversion: the existential pair of differently coloured elements is the negated
    monochromatic predicate of C8 ([non_monochromatic_onP]). *)
Lemma x209_cut_edge_compat (T : finType) (r : nat) (col : T -> 'I_r) (e : {set T}) :
  Legacy.x209_cut_edge col e = x209_cut_edge col e.
Proof.
apply/idP/non_monochromatic_onP => [/existsP[x /andP[xe /existsP[y /andP[ye xy]]]]|[x [y [xe ye xy]]]].
  by exists x, y.
by apply/existsP; exists x; rewrite xe; apply/existsP; exists y; rewrite ye.
Qed.

Lemma x209_cut_size_compat (T : finType) (E : {set {set T}}) (r : nat) (col : T -> 'I_r) :
  Legacy.x209_cut_size E col = x209_cut_size E col.
Proof.
rewrite /Legacy.x209_cut_size /x209_cut_size /non_monochromatic_count.
by apply: eq_card => e; rewrite !inE x209_cut_edge_compat.
Qed.

Lemma x209_is_max_r_cut_compat (T : finType) (E : {set {set T}}) (r c : nat) :
  @X209Legacy.is_max_r_cut T E r c <-> @x209_is_max_r_cut T E r c.
Proof. rewrite /X209Legacy.is_max_r_cut /x209_is_max_r_cut; setoid_rewrite x209_cut_size_compat; reflexivity. Qed.

Lemma x209_scaled_excess_compat (T : finType) (E : {set {set T}}) (r k x : nat) :
  @X209Legacy.scaled_excess T E r k x <-> @x209_scaled_excess T E r k x.
Proof. rewrite /X209Legacy.scaled_excess /x209_scaled_excess; setoid_rewrite x209_is_max_r_cut_compat; reflexivity. Qed.

Lemma x209_is_min_scaled_excess_compat (r k m x : nat) :
  @X209Legacy.is_min_scaled_excess r k m x <-> @x209_is_min_scaled_excess r k m x.
Proof. rewrite /X209Legacy.is_min_scaled_excess /x209_is_min_scaled_excess; setoid_rewrite x209_scaled_excess_compat; reflexivity. Qed.

Lemma hypergraph_cut_excess_theta_sqrt_statement_compat :
  X209Legacy.hypergraph_cut_excess_theta_sqrt_statement <-> hypergraph_cut_excess_theta_sqrt_statement.
Proof. rewrite /X209Legacy.hypergraph_cut_excess_theta_sqrt_statement /hypergraph_cut_excess_theta_sqrt_statement; setoid_rewrite x209_is_min_scaled_excess_compat; reflexivity. Qed.
