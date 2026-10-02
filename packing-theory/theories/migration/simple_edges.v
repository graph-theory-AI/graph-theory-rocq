(** * Packing.migration.simple_edges -- frozen edge-helper certificates *)

From GTBase Require Import base.
From Packing.conjectures Require Import X5 X15 X25 X47 XE1.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Legacy.

Definition edge_set (G : sgraph) : {set {set G}} :=
  [set e : {set G} |
      [exists x : G, [exists y : G, (x -- y) && (e == [set x; y])]]].

End Legacy.

Lemma x5_edge_set_compat (G : sgraph) :
  Legacy.edge_set G = x5_edge_set G.
Proof. by rewrite /x5_edge_set sg_edge_setE. Qed.

Lemma x15_edge_set_compat (G : sgraph) :
  Legacy.edge_set G = x15_edge_set G.
Proof. by rewrite /x15_edge_set sg_edge_setE. Qed.

Lemma x25_edge_set_compat (G : sgraph) :
  Legacy.edge_set G = x25_edge_set G.
Proof. by rewrite /x25_edge_set sg_edge_setE. Qed.

Lemma x47_edge_set_compat (G : sgraph) :
  Legacy.edge_set G = x47_edge_set G.
Proof. by rewrite /x47_edge_set sg_edge_setE. Qed.

Lemma xe1_edge_set_compat (G : sgraph) :
  Legacy.edge_set G = xe1_edge_set G.
Proof. by rewrite /xe1_edge_set sg_edge_setE. Qed.

Module X25Legacy.

Definition perfect_matching (G : sgraph) (M : {set {set G}}) : Prop :=
  M \subset Legacy.edge_set G /\
  forall v : G, #|[set e in M | v \in e]| = 1.

Definition cycle_edge_seq (G : sgraph) (c : seq G) : seq {set G} :=
  map (fun p : G * G => [set p.1; p.2]) (zip c (rot 1 c)).

Definition hamiltonian_edge_set
    (G : sgraph) (F : {set {set G}}) : Prop :=
  exists c : seq G,
    ucycle (--) c /\
    size c = #|G| /\
    F = [set e : {set G} | e \in cycle_edge_seq c].

Definition perfect_one_factorization
    (n : nat) (col : {set 'K_n} -> 'I_(n.-1)) : Prop :=
  (forall i : 'I_(n.-1),
      perfect_matching [set e in Legacy.edge_set 'K_n | col e == i]) /\
  forall i j : 'I_(n.-1), i != j ->
    hamiltonian_edge_set
      ([set e in Legacy.edge_set 'K_n | (col e == i) || (col e == j)]).

Definition statement : Prop :=
  forall n : nat,
    2 < n ->
    ~~ odd n ->
    exists col : {set 'K_n} -> 'I_(n.-1),
      perfect_one_factorization col.

End X25Legacy.

Lemma x25_perfect_matching_compat (G : sgraph) (M : {set {set G}}) :
  X25Legacy.perfect_matching M <-> x25_perfect_matching M.
Proof.
by rewrite /X25Legacy.perfect_matching /x25_perfect_matching x25_edge_set_compat.
Qed.

Lemma x25_perfect_one_factorization_compat
    (n : nat) (col : {set 'K_n} -> 'I_(n.-1)) :
  X25Legacy.perfect_one_factorization col <->
  x25_perfect_one_factorization col.
Proof.
rewrite /X25Legacy.perfect_one_factorization /x25_perfect_one_factorization
  x25_edge_set_compat.
split=> -[matchings cycles]; split=> [i | i j ij].
- exact: (x25_perfect_matching_compat _).1 (matchings i).
- exact: cycles i j ij.
- exact: (x25_perfect_matching_compat _).2 (matchings i).
- exact: cycles i j ij.
Qed.

Lemma x25_statement_compat :
  X25Legacy.statement <-> kotzig_perfect_one_factorization_statement.
Proof.
split=> statement n n2 even; have [col factor] := statement n n2 even;
  exists col.
- exact: (x25_perfect_one_factorization_compat col).1 factor.
- exact: (x25_perfect_one_factorization_compat col).2 factor.
Qed.
