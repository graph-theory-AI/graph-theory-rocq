(** * GTMisc.conjectures.grounding_X232 -- grounding certificates of wave X232.

    The row of X232.v gets a [g232_hp_hyp_inhabited] certificate: for every r, the graph G(q)
    of applications/heavy_path_disproof.v (q = 2r + 3) with its hole C and M = {x, y_0, y_1,
    y_2} meets the three hypotheses of the row at ell = 7, and the row then promises a path of
    C that catches M. It also gets a [g232_hp_not_trivially_true] certificate: at r = 0 no path
    of C with at most 2 edges catches M, so the row forces a bound b >= 3 at ell = 7. Two
    helper-sanity certificates pin the x232 helpers: a path of C is a window of consecutive
    positions, no vertex of C is C-major while x and the y_k are, C is a long odd hole for
    every ell up to its size and the shortest one at ell = 7.

    Import direction: unlike grounding_X231.v, this file imports the applications module, whose
    hole classification of G(q) is needed for "C is a shortest long odd hole"; the proof is kept
    in one place. The row itself is refuted in applications/heavy_path_disproof.v. Everything
    is closed by [Qed]; see the [Print Assumptions] audit at the end. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries digraph sgraph.
From GTBase Require Import base induced_cycles.
From GTMisc.conjectures Require Import X232.
From GTMisc.applications Require Import heavy_path_disproof.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition g232_hp_hyp_claim : Prop :=
  (forall r : nat,
     [/\ x232_shortest_long_odd_hole 7 (hC r),
         forall v, v \in hM r -> x232_major (hC r) v
       & exists2 m0, m0 \in hM r & forall v, v \in hM r -> v != m0 -> ~~ (m0 -- v)]) /\
  (heavy_path_extension_statement ->
     forall r : nat, exists b : nat, exists p,
       [/\ x232_cycle_path (hC r) p, (size p).-1 <= b
         & forall v, v \in hM r -> exists2 u, u \in p & v -- u]).

Theorem g232_hp_hyp_inhabited : g232_hp_hyp_claim.
Proof.
have hyp : forall r : nat,
    [/\ x232_shortest_long_odd_hole 7 (hC r),
        forall v, v \in hM r -> x232_major (hC r) v
      & exists2 m0, m0 \in hM r & forall v, v \in hM r -> v != m0 -> ~~ (m0 -- v)].
  move=> r; split; [exact: shortest_hC | exact: majors_hM |].
  by exists (xv r); [rewrite /hM !inE eqxx | exact: x_alone].
split=> // H r; have [b Hb] := H 7 isT; exists b.
by have [sh mj m0] := hyp r; apply: Hb.
Qed.

Definition g232_hp_ntt_claim : Prop :=
  (forall p, x232_cycle_path (hC 0) p ->
     (forall v, v \in hM 0 -> exists2 u, u \in p & v -- u) -> 3 <= (size p).-1) /\
  (heavy_path_extension_statement -> exists2 b : nat, 3 <= b &
     forall (G : sgraph) (c : seq G) (M : {set G}),
       x232_shortest_long_odd_hole 7 c ->
       (forall v, v \in M -> x232_major c v) ->
       (exists2 m0, m0 \in M & forall v, v \in M -> v != m0 -> ~~ (m0 -- v)) ->
       exists p, [/\ x232_cycle_path c p, (size p).-1 <= b
                   & forall v, v \in M -> exists2 u, u \in p & v -- u]).

Theorem g232_hp_not_trivially_true : g232_hp_ntt_claim.
Proof.
have low : forall p, x232_cycle_path (hC 0) p ->
    (forall v, v \in hM 0 -> exists2 u, u \in p & v -- u) -> 3 <= (size p).-1.
  move=> p [i [m [ml ep]]] pc; rewrite size_hC in ml.
  have sp : size p = m.+1 by rewrite ep size_takel // size_rot size_hC.
  rewrite sp /=; apply: (@catch_bound 0 i m ml) => k.
  by rewrite -ep; apply: pc; exact: y_in_hM.
split=> // H; have [b Hb] := H 7 isT; exists b => //.
have m0 : exists2 m0, m0 \in hM 0 & forall v, v \in hM 0 -> v != m0 -> ~~ (m0 -- v).
  by exists (xv 0); [rewrite /hM !inE eqxx | exact: x_alone].
have [p [cp pb pc]] := Hb (HG 0) (hC 0) (hM 0) (shortest_hC 0) (@majors_hM 0) m0.
exact: leq_trans (low p cp pc) pb.
Qed.

Definition g232_path_major_claim : Prop :=
  [/\ forall (r : nat) p, x232_cycle_path (hC r) p -> exists i m, m < size (hC r) /\
        forall v, v \in p -> exists2 j, j <= m & v = cv r ((i0of r i + j) %% size (hC r)),
      forall (r : nat) v, v \in hC r -> ~ x232_major (hC r) v
    & forall r : nat, x232_major (hC r) (xv r) /\ forall k, x232_major (hC r) (yv r k)].

Theorem g232_path_major_sanity : g232_path_major_claim.
Proof.
split.
- move=> r p [i [m [ml ep]]]; exists i, m; split=> // v; rewrite ep size_hC.
  by apply: mem_sub_hC; rewrite -(size_hC r).
- by move=> r v vC []; rewrite vC.
- move=> r; split; first by apply: majors_hM; rewrite /hM !inE eqxx.
  by move=> k; apply: majors_hM; exact: y_in_hM.
Qed.

Definition g232_long_hole_claim : Prop :=
  (forall (r : nat) ell, ell <= size (hC r) -> x232_long_odd_hole ell (hC r)) /\
  (forall r : nat, x232_shortest_long_odd_hole 7 (hC r)).

Theorem g232_long_hole_sanity : g232_long_hole_claim.
Proof.
split; last exact: shortest_hC.
by move=> r ell le; split; [exact: hole_hC | exact: odd_hC |].
Qed.

Print Assumptions g232_hp_hyp_inhabited.
Print Assumptions g232_hp_not_trivially_true.
Print Assumptions g232_path_major_sanity.
Print Assumptions g232_long_hole_sanity.
