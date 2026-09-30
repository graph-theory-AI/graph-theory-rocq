(** * GTMisc.conjectures.X91 -- v2 avoidable path row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X91 vocabulary ************************************************)

Definition x91_consecutive_in_path (G : sgraph) (p : seq G) (u v : G) : Prop :=
  (u, v) \in zip p (behead p) \/ (v, u) \in zip p (behead p).

Definition x91_induced_path (G : sgraph) (p : seq G) : Prop :=
  match p with
  | [::] => False
  | x :: q =>
      uniq p /\
      path (--) x q /\
      forall u v : G,
        u \in p -> v \in p -> u -- v -> u != v ->
        x91_consecutive_in_path p u v
  end.

Definition x91_consecutive_in_cycle (G : sgraph) (c : seq G) (u v : G) : Prop :=
  (u, v) \in zip c (rot 1 c) \/ (v, u) \in zip c (rot 1 c).

Definition x91_induced_cycle (G : sgraph) (c : seq G) : Prop :=
  ucycle (--) c /\
  3 <= size c /\
  forall u v : G,
    u \in c -> v \in c -> u -- v -> u != v ->
    x91_consecutive_in_cycle c u v.

Definition x91_sequence_contained (G : sgraph) (p c : seq G) : Prop :=
  forall v : G, v \in p -> v \in c.

Definition x91_avoidable_path (G : sgraph) (p : seq G) : Prop :=
  x91_induced_path p /\
  forall u v : G,
    x91_induced_path (u :: rcons p v) ->
    exists c : seq G,
      x91_induced_cycle c /\ x91_sequence_contained (u :: rcons p v) c.

Definition x91_Pk_free (G : sgraph) (k : nat) : Prop :=
  forall p : seq G, size p = k -> ~ x91_induced_path p.

(** ** X91 statements ******************************************************)

(** Corpus row: studies:std_beisegel_chudnovsky_gurvich_milani_servatius_con
    Site: none
    Review: none
    English statement: (Beisegel, Chudnovsky, Gurvich, Milanic and Servatius, conjecture on
      avoidable paths)
      For every k >= 1, every finite simple graph G either contains no induced path on k
      vertices, or contains an induced path p on k vertices that is avoidable: every induced
      path obtained by adding one vertex at each end of p is contained in an induced cycle.
    Definitions: [x91_consecutive_in_path] / [x91_consecutive_in_cycle] - being consecutive in
      a sequence, resp. cyclically (this file); [x91_induced_path p] - p is a non-empty
      sequence of distinct vertices, consecutive ones adjacent and no other pair adjacent (this
      file); [x91_induced_cycle c] - c is a uniform closed adjacency-walk on at least three
      vertices with no chords (this file); [x91_sequence_contained p c] - every vertex of p
      occurs in c (this file); [x91_avoidable_path p] - p is induced and every induced
      two-sided extension of p lies inside an induced cycle (this file); [x91_Pk_free G k] - no
      induced path on k vertices (this file); [ucycle] - MathComp uniform cycle.
    Notes: paths are measured by their number of vertices, so P_k is a path on k vertices.
      Avoidability is spelled out by the standard extension property (every induced extension
      u :: p ++ [v] lies in an induced cycle) rather than by the neighbourhood formulation;
      the two are the usual equivalent definitions. *)
Definition avoidable_path_or_pk_free_statement : Prop :=
  forall k : nat,
    0 < k ->
    forall G : sgraph,
      x91_Pk_free G k \/
      exists p : seq G, size p = k /\ x91_avoidable_path p.
