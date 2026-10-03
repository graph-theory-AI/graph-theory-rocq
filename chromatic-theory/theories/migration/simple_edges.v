(** * Chromatic.migration.simple_edges -- frozen edge-helper certificates *)

From GTBase Require Import base.
From GTBase Require Import edge_colourings.
From Chromatic.conjectures Require Import X33 X34 X35 X43 X63 X64 X100 X142 XE1.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition exists_edge_set (G : sgraph) : {set {set G}} :=
  [set e : {set G} |
      [exists x : G, [exists y : G, (x -- y) && (e == [set x; y])]]].

Definition clique_edge_set (G : sgraph) : {set {set G}} :=
  [set e : {set G} | (#|e| == 2) && cliqueb e].

End Legacy.

Lemma x33_edge_set_compat (G : sgraph) :
  Legacy.exists_edge_set G = x33_edge_set G.
Proof. by rewrite /x33_edge_set sg_edge_setE. Qed.

Lemma x34_edge_set_compat (G : sgraph) :
  Legacy.exists_edge_set G = x34_edge_set G.
Proof. by rewrite /x34_edge_set sg_edge_setE. Qed.

Lemma x35_edge_set_compat (G : sgraph) :
  Legacy.exists_edge_set G = x35_edge_set G.
Proof. by rewrite /x35_edge_set sg_edge_setE. Qed.

Lemma x43_edge_set_compat (G : sgraph) :
  Legacy.exists_edge_set G = x43_edge_set G.
Proof. by rewrite /x43_edge_set sg_edge_setE. Qed.

Lemma x64_edge_set_compat (G : sgraph) :
  Legacy.exists_edge_set G = x64_edge_set G.
Proof. by rewrite /x64_edge_set sg_edge_setE. Qed.

Lemma x100_edge_set_compat (G : sgraph) :
  Legacy.clique_edge_set G = x100_edge_set G.
Proof. by rewrite /x100_edge_set sg_edge_set_cliqueE. Qed.

Lemma x142_edge_set_compat (G : sgraph) :
  Legacy.exists_edge_set G = x142_edge_set G.
Proof. by rewrite /x142_edge_set sg_edge_setE. Qed.

Lemma xe1_edge_set_compat (G : sgraph) :
  Legacy.exists_edge_set G = xe1_edge_set G.
Proof. by rewrite /xe1_edge_set sg_edge_setE. Qed.

Module X64Legacy.

Definition bridgeless (G : sgraph) : Prop :=
  forall e : {set G},
    e \in Legacy.exists_edge_set G ->
    connected [set: @x64_delete_edge_graph G e].

Definition statement : Prop :=
  exists N : nat,
    forall G : sgraph,
      connected [set: G] ->
      regular G 3 ->
      bridgeless G ->
      N <= #|G| ->
      x63_k_homogeneous_colouring G 2.

End X64Legacy.

Lemma x64_bridgeless_compat (G : sgraph) :
  X64Legacy.bridgeless G <-> x64_bridgeless G.
Proof. by rewrite /X64Legacy.bridgeless /x64_bridgeless x64_edge_set_compat. Qed.

Lemma x64_statement_compat :
  X64Legacy.statement <->
  finite_bridgeless_cubic_two_homogeneous_exceptions_statement.
Proof.
split=> -[N bound]; exists N => G conn reg bridgeless size.
- exact: bound conn reg ((x64_bridgeless_compat G).2 bridgeless) size.
- exact: bound conn reg ((x64_bridgeless_compat G).1 bridgeless) size.
Qed.

Module X142Legacy.

Definition edges_incident (G : sgraph) (v : G) : {set {set G}} :=
  [set e in Legacy.exists_edge_set G | v \in e].

Definition incident_sum
    (G : sgraph) (k : nat) (col : {set G} -> 'I_k) (v : G) : nat :=
  \sum_(e in edges_incident v) (val (col e)).+1.

Definition proper_edge_colouring
    (G : sgraph) (k : nat) (col : {set G} -> 'I_k) : Prop :=
  forall e f : {set G},
    e \in Legacy.exists_edge_set G ->
    f \in Legacy.exists_edge_set G ->
    e != f ->
    e :&: f != set0 ->
    col e != col f.

Definition neighbour_sum_distinguishing
    (G : sgraph) (k : nat) (col : {set G} -> 'I_k) : Prop :=
  forall x y : G,
    x -- y ->
    incident_sum col x != incident_sum col y.

Definition neighbour_sum_edge_colourable (G : sgraph) (k : nat) : Prop :=
  exists col : {set G} -> 'I_k,
    proper_edge_colouring col /\
    neighbour_sum_distinguishing col.

Definition statement : Prop :=
  forall G : sgraph,
    connected [set: G] ->
    3 <= #|G| ->
    ~ inhabited (G ≃ cycle_graph 5) ->
    neighbour_sum_edge_colourable G (Delta G + 2).

End X142Legacy.

Lemma x142_edges_incident_compat (G : sgraph) (v : G) :
  X142Legacy.edges_incident v = x142_edges_incident v.
Proof.
by rewrite /X142Legacy.edges_incident /x142_edges_incident x142_edge_set_compat.
Qed.

Lemma x142_incident_sum_compat
    (G : sgraph) (k : nat) (col : {set G} -> 'I_k) (v : G) :
  X142Legacy.incident_sum col v = x142_incident_sum col v.
Proof.
by rewrite /X142Legacy.incident_sum /x142_incident_sum x142_edges_incident_compat.
Qed.

Lemma x142_proper_edge_colouring_compat
    (G : sgraph) (k : nat) (col : {set G} -> 'I_k) :
  X142Legacy.proper_edge_colouring col <-> x142_proper_edge_colouring col.
Proof.
rewrite /X142Legacy.proper_edge_colouring x142_edge_set_compat
  /x142_proper_edge_colouring.
exact: iff_sym (proper_edge_colouring_edgesP col).
Qed.

Lemma x142_neighbour_sum_distinguishing_compat
    (G : sgraph) (k : nat) (col : {set G} -> 'I_k) :
  X142Legacy.neighbour_sum_distinguishing col <->
  x142_neighbour_sum_distinguishing col.
Proof.
by split=> distinct x y xy; move: (distinct x y xy);
  rewrite !x142_incident_sum_compat.
Qed.

Lemma x142_neighbour_sum_edge_colourable_compat (G : sgraph) (k : nat) :
  X142Legacy.neighbour_sum_edge_colourable G k <->
  x142_neighbour_sum_edge_colourable G k.
Proof.
split=> -[col [proper distinct]]; exists col; split.
- exact/(x142_proper_edge_colouring_compat col).1.
- exact/(x142_neighbour_sum_distinguishing_compat col).1.
- exact/(x142_proper_edge_colouring_compat col).2.
- exact/(x142_neighbour_sum_distinguishing_compat col).2.
Qed.

Lemma x142_statement_compat :
  X142Legacy.statement <->
  flandrin_neighbour_sum_distinguishing_edge_colouring_statement.
Proof.
split=> statement G conn size notC5.
- exact: (x142_neighbour_sum_edge_colourable_compat G (Delta G + 2)).1
           (statement G conn size notC5).
- exact: (x142_neighbour_sum_edge_colourable_compat G (Delta G + 2)).2
           (statement G conn size notC5).
Qed.

Module X100Legacy.

Definition col_deg
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (v : G) (c : 'I_q) : nat :=
  \sum_(e in Legacy.clique_edge_set G | (v \in e) && (col e == c)) 1.

Definition modular_edge_colouring
    (G : sgraph) (k q : nat) (col : {set G} -> 'I_q) : Prop :=
  forall (v : G) (c : 'I_q),
    col_deg col v c = 0 \/ col_deg col v c %% k = 1.

Definition modular_edge_colourable (G : sgraph) (k q : nat) : Prop :=
  exists col : {set G} -> 'I_q, @modular_edge_colouring G k q col.

Definition statement : Prop :=
  forall k : nat,
    2 <= k ->
    exists C : nat,
      forall G : sgraph,
        modular_edge_colourable G k (k + C).

End X100Legacy.

Lemma x100_col_deg_compat
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (v : G) (c : 'I_q) :
  X100Legacy.col_deg col v c = x100_col_deg col v c.
Proof.
rewrite /X100Legacy.col_deg /x100_col_deg.
apply: eq_bigl=> e.
have edgeE :
    (e \in Legacy.clique_edge_set G) = (e \in x100_edge_set G).
  by rewrite x100_edge_set_compat.
by rewrite edgeE.
Qed.

Lemma x100_modular_edge_colouring_compat
    (G : sgraph) (k q : nat) (col : {set G} -> 'I_q) :
  X100Legacy.modular_edge_colouring k col <->
  x100_modular_edge_colouring k col.
Proof.
split=> modular v c; move: (modular v c).
all: by rewrite x100_col_deg_compat.
Qed.

Lemma x100_modular_edge_colourable_compat (G : sgraph) (k q : nat) :
  X100Legacy.modular_edge_colourable G k q <->
  x100_modular_edge_colourable G k q.
Proof.
split=> -[col modular]; exists col.
- exact/(x100_modular_edge_colouring_compat (G := G) k (q := q) col).1.
- exact/(x100_modular_edge_colouring_compat (G := G) k (q := q) col).2.
Qed.

Lemma x100_statement_compat :
  X100Legacy.statement <-> modular_edge_colouring_k_plus_constant_statement.
Proof.
split=> statement k k_ge2; move: (statement k k_ge2)=> [C bound].
all: exists C=> G.
- apply/(@x100_modular_edge_colourable_compat G k (k + C)).1.
  exact: bound G.
- apply/(@x100_modular_edge_colourable_compat G k (k + C)).2.
  exact: bound G.
Qed.
