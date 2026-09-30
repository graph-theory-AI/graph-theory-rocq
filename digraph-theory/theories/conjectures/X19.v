(** * Digraph.conjectures.X19 -- v2 directed-cycle packing/girth rows *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented dipath.
From Digraph.conjectures Require Import classic_core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X19 vocabulary ************************************************)

Definition x19_loopless (D : diGraphType) : Prop :=
  forall v : D, ~~ (v --> v).

Definition x19_directed_girth_at_least (D : diGraphType) (g : nat) : Prop :=
  forall c : seq D, dicycle c -> g <= size c.

Definition x19_cycle_vertices (D : diGraphType) (c : seq D) : {set D} :=
  [set v | v \in c].

Definition x19_vertex_disjoint_dicycles
    (D : diGraphType) (cs : seq (seq D)) : Prop :=
  all (@dicycle D) cs /\
  forall c d : seq D, c \in cs -> d \in cs -> c != d ->
    [disjoint x19_cycle_vertices c & x19_cycle_vertices d].

Definition x19_distinct_cycle_lengths (D : diGraphType) (cs : seq (seq D)) : Prop :=
  uniq (map size cs).

(** ** X19 statements ******************************************************)

(** Corpus row: studies:std_behzad_chartrand_wall_conjecture_girth_of_regula
    Site: none
    Review: none
    English statement: (Behzad, Chartrand and Wall, girth of regular digraphs)
      For all r >= 1 and g >= 1 and every nonempty finite loopless digraph D, if D is r-regular
      (every vertex has in-degree and out-degree exactly r) and every directed cycle of D has at
      least g vertices, then D has at least r * (g - 1) + 1 vertices.
    Definitions: [x19_loopless D] - no loop (this file); [x19_directed_girth_at_least D g] -
      every directed cycle has at least g vertices (this file); [diregular D r]
      (conjectures/classic_core.v); [dicycle] (core/dipath.v).
    Notes: Girth at least g is stated as a lower bound on the size of every directed cycle, so a
      digraph with no directed cycle satisfies it for every g; the r-regularity hypothesis then
      still forces enough vertices. *)
Definition behzad_chartrand_wall_girth_regular_digraph_statement : Prop :=
  forall (r g : nat) (D : diGraphType),
    0 < r -> 0 < g -> 0 < #|D| ->
    x19_loopless D ->
    diregular D r ->
    x19_directed_girth_at_least D g ->
    (r * (g - 1) + 1 <= #|D|)%N.

(** Corpus row: studies:std_lichiardopol_s_conjecture
    Site: none
    Review: none
    English statement: (Lichiardopol, distinct-length directed-cycle packing conjecture)
      For every k there is a bound g such that every nonempty finite loopless digraph in which
      every vertex has out-degree at least g contains k pairwise vertex-disjoint directed cycles
      whose lengths are pairwise distinct.
    Definitions: [x19_vertex_disjoint_dicycles cs] - all members are directed cycles and any two
      distinct members have disjoint vertex sets (this file); [x19_distinct_cycle_lengths cs] -
      the list of sizes is duplicate-free (this file); [x19_loopless] (this file); [dicycle]
      (core/dipath.v).
    Notes: Disjointness is stated for distinct members of the list (c != d), and the
      duplicate-freeness of the lengths already forbids repeated members. Cycle length is
      counted in vertices. *)
Definition lichiardopol_distinct_length_dicycle_packing_statement : Prop :=
  forall k : nat, exists g : nat,
    forall D : diGraphType,
      0 < #|D| ->
      x19_loopless D ->
      (forall v : D, g <= outdeg v) ->
      exists cs : seq (seq D),
        size cs = k /\
        x19_vertex_disjoint_dicycles cs /\
        x19_distinct_cycle_lengths cs.
