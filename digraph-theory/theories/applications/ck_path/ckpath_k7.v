(** * The Cheng--Keevash directed-path conjecture at out-degree seven

    This assembly isolates the remaining finite trust boundary.  Its five
    refutation arguments are precisely the pending checked certificate
    families for the C12 cover, the nineteen orbit-reduced C12 low-endpoint
    instances, and the three orbit-union C13 cover formulas.  The C11
    certificate is already replayed by [ckpath_cert_graph_k7_c11]. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented dipath strong lemma7
  ckpath_kernel_cases ckpath_kernel_prefix_adapters
  ckpath_even_gateway ckpath_odd_gateway ckpath_k7_tight
  ckpath_cnf ckpath_cert_k7_base
  ckpath_k7_orbits ckpath_cert_k7_c12_low3_reduction
  ckpath_cert_k7_c13_orbit_union
  ckpath_cert_graph_k7_c11 ckpath_cert_graph_k7_c12
  ckpath_cert_graph_k7_c12_low ckpath_cert_graph_k7_c13_semantics
  ckpath_k6.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section FromFiniteRefutations.

Hypothesis Hc12Cover4 :
  forall rho, satisfies_cnf rho (c12_k7_cover_base 4) -> False.
Hypothesis Hc12Low :
  forall mask rho,
    List.In mask (orbit_representatives 12 3) ->
    satisfies_cnf rho (c12_k7_low3_instance mask) -> False.
Hypothesis Hc13Cover3 :
  forall rho, satisfies_cnf rho (c13_k7_orbit_union_base 3) -> False.
Hypothesis Hc13Cover4 :
  forall rho, satisfies_cnf rho (c13_k7_orbit_union_base 4) -> False.
Hypothesis Hc13Cover5 :
  forall rho, satisfies_cnf rho (c13_k7_orbit_union_base 5) -> False.

(** A nonempty strong seven-outregular oriented digraph cannot have all
    directed paths shorter than fourteen arcs, assuming only the five
    explicitly displayed finite-refutation families. *)
Theorem no_short_strong7_from_finite_refutations (H : orientedDigraph) :
  (forall v : H, outdeg v = 7) -> 0 < #|H| -> strongb H ->
  ell H < 14 -> False.
Proof.
move=> hreg hn hstr hell.
have hmin6 : forall v : H, 6 <= outdeg v.
  by move=> v; rewrite hreg.
have hLlow : 12 <= ell H := ck_conj1_delta6 hn hmin6.
have [x [p [a [u [r [hfacts hwit hshape]]]]]] :=
  ckpath_kernel_cases7 hreg hn hstr hell hLlow.
have hfacts_saved := hfacts.
case: hfacts => hAB hA2 [hpath hcycle hB hclose hcount].
case: hcycle => dcC sizeC cardC.
have SsubRaw : ckS x p a \subset [set z in ckC x p a].
  apply/subsetP=> z.
  rewrite /ckS => /imsetP[b bB ->].
  rewrite inE mem_prev.
  move: bB; rewrite inE => /andP[].
  by [].
have SsubOdd : ckS x p a \subset odd_cycle_set (ckC x p a).
  apply/subsetP=> z zS.
  have zC := subsetP SsubRaw z zS.
  move: zC.
  by rewrite /odd_cycle_set !inE.
have SsubEven : ckS x p a \subset even_cycle_set (ckC x p a).
  apply/subsetP=> z zS.
  have zC := subsetP SsubRaw z zS.
  move: zC.
  by rewrite /even_cycle_set !inE.
have SclosedOdd : forall b z, b \in ckS x p a -> b --> z ->
    z \in odd_cycle_set (ckC x p a).
  move=> b z bS abz.
  rewrite /odd_cycle_set inE.
  exact: hclose bS abz.
have SclosedEven : forall b z, b \in ckS x p a -> b --> z ->
    z \in even_cycle_set (ckC x p a).
  move=> b z bS abz.
  rewrite /even_cycle_set inE.
  exact: hclose bS abz.
have horder : 2 * 7 + 1 <= #|H|.
  apply: oriented_card => // v.
  by rewrite hreg.

have noC12Cover (c0 : seq H) (S0 : {set H}) :
    ell H = 12 -> dicycle c0 -> size c0 = 12 -> #|S0| = 7 ->
    S0 \subset even_cycle_set c0 ->
    (forall b z, b \in S0 -> b --> z -> z \in even_cycle_set c0) ->
    False.
  move=> ell12 dc0 csize0 Scard0 Ssub0 Sclosed0.
  have [rho sat] :=
    @ckpath_c12_graph_base_satisfied H c0 S0 hreg hstr ell12 dc0
      csize0 Scard0 Ssub0 Sclosed0 horder.
  exact: Hc12Cover4 rho sat.
have noC12Low (c0 : seq H) (S0 : {set H}) (v0 v1 : H) :
    ell H = 13 -> dicycle c0 -> size c0 = 12 -> #|S0| = 7 ->
    ckpath_prefix2_data c0 S0 v0 v1 -> False.
  move=> ell13 dc0 csize0 Scard0 prefix0.
  have [mask [rho [maskRep sat]]] :=
    @ckpath_k7_c12_low_graph_low3_instance_satisfied H c0 S0 v0 v1 hreg
      ell13 dc0 csize0 Scard0 prefix0.
  exact: Hc12Low mask rho maskRep sat.
have noC13 (c0 : seq H) (S0 : {set H}) :
    dicycle c0 -> size c0 = 13 -> #|S0| = 7 ->
    S0 \subset odd_cycle_set c0 ->
    (forall b z, b \in S0 -> b --> z -> z \in odd_cycle_set c0) ->
    False.
  move=> dc0 csize0 Scard0 Ssub0 Sclosed0.
  have [m [rho [mcase cardA sat]]] :=
    @ckpath_k7_c13_graph_satisfies_orbit_union_base H c0 S0 hreg hstr hell
      dc0 csize0 Scard0 Ssub0 Sclosed0 horder.
  case: mcase => [m3 | [m4 | m5]].
  - have sat3 : satisfies_cnf rho (c13_k7_orbit_union_base 3).
      by rewrite -m3.
    exact: Hc13Cover3 rho sat3.
  - have sat4 : satisfies_cnf rho (c13_k7_orbit_union_base 4).
      by rewrite -m4.
    exact: Hc13Cover4 rho sat4.
  - have sat5 : satisfies_cnf rho (c13_k7_orbit_union_base 5).
      by rewrite -m5.
    exact: Hc13Cover5 rho sat5.

case: hshape =>
  [shape1 | [shape2 | [shape3 | [shape4 | [shape5 |
   [shape6 | [shape7 | [shape8 | [shape9 | [shape10 | shape11]]]]]]]]]].
- case: shape1 => [L12 [S7 [r2 a1]]].
  have csize : size (ckC x p a) = 12.
    by rewrite sizeC L12 a1.
  exact: (@noC12Cover (ckC x p a) (ckS x p a)
            L12 dcC csize S7 SsubEven SclosedEven).
- case: shape2 => [L12 [S7 [r3 a1]]].
  have csize : size (ckC x p a) = 12.
    by rewrite sizeC L12 a1.
  exact: (@noC12Cover (ckC x p a) (ckS x p a)
            L12 dcC csize S7 SsubEven SclosedEven).
- case: shape3 => [L12 [S7 [r3 a2]]].
  have csize : size (ckC x p a) = 11.
    by rewrite sizeC L12 a2.
  apply: (no_tight_cycle11_seven_set dcC csize SsubRaw S7).
  * by move=> v _; rewrite hreg.
  * exact: hclose.
- case: shape4 => [L13 [S5 [r2 a4]]].
  have csize : size (ckC x p a) = 10.
    by rewrite sizeC L13 a4.
  apply: (no_tight_cycle10_five_set dcC csize SsubRaw S5).
  * by move=> v _; rewrite hreg.
  * exact: hclose.
- case: shape5 => [L13 [S6 [r2 a3]]].
  subst a.
  have csize : size (ckC x p 3) = 11.
    by rewrite sizeC L13.
  have prefix := ckpath_kernel_prefix3_adapter hfacts_saved.
  exact: (@ckpath_k7_c11_graph_certificate_impossible H
            (ckC x p 3) (ckS x p 3)
            x (nth x (x :: p) 1) (nth x (x :: p) 2)
            hreg L13 dcC csize S6 prefix).
- case: shape6 => [L13 [S7 [r1 a1]]].
  have csize : size (ckC x p a) = 13.
    by rewrite sizeC L13 a1.
  exact: (@noC13 (ckC x p a) (ckS x p a)
            dcC csize S7 SsubOdd SclosedOdd).
- case: shape7 => [L13 [S7 [r2 a1]]].
  have csize : size (ckC x p a) = 13.
    by rewrite sizeC L13 a1.
  exact: (@noC13 (ckC x p a) (ckS x p a)
            dcC csize S7 SsubOdd SclosedOdd).
- case: shape8 => [L13 [S7 [r2 a2]]].
  subst a.
  have csize : size (ckC x p 2) = 12.
    by rewrite sizeC L13.
  have prefix := ckpath_kernel_prefix2_adapter hfacts_saved.
  exact: (@noC12Low (ckC x p 2) (ckS x p 2)
            x (nth x (x :: p) 1) L13 dcC csize S7 prefix).
- case: shape9 => [L13 [S7 [r3 a1]]].
  have csize : size (ckC x p a) = 13.
    by rewrite sizeC L13 a1.
  exact: (@noC13 (ckC x p a) (ckS x p a)
            dcC csize S7 SsubOdd SclosedOdd).
- case: shape10 => [L13 [S7 [r3 a2]]].
  subst a.
  have csize : size (ckC x p 2) = 12.
    by rewrite sizeC L13.
  have prefix := ckpath_kernel_prefix2_adapter hfacts_saved.
  exact: (@noC12Low (ckC x p 2) (ckS x p 2)
            x (nth x (x :: p) 1) L13 dcC csize S7 prefix).
- case: shape11 => [L13 [S7 [r3 a3]]].
  have csize : size (ckC x p a) = 11.
    by rewrite sizeC L13 a3.
  apply: (no_tight_cycle11_seven_set dcC csize SsubRaw S7).
  * by move=> v _; rewrite hreg.
  * exact: hclose.
Qed.

(** Conjecture 1 at minimum out-degree seven, relative to the same finite
    refutation boundary. *)
Theorem ck_conj1_delta7_from_finite_refutations (D : orientedDigraph) :
  0 < #|D| -> (forall v : D, 7 <= outdeg v) -> 14 <= ell D.
Proof.
move=> n0 dmin.
rewrite ltnNge; apply/negP=> hell13.
have [W [hn0 hstr hreg hell hcard]] := reduction n0 dmin.
have hshort : ell (induced_oriented W) < 14 :=
  leq_ltn_trans (leq_trans hell hell13) (ltnSn 13).
exact: (no_short_strong7_from_finite_refutations hreg hn0 hstr hshort).
Qed.

(** Explicit simple directed path with fourteen arcs. *)
Corollary ck_conj1_delta7_path_from_finite_refutations
    (D : orientedDigraph) :
  0 < #|D| -> (forall v : D, 7 <= outdeg v) ->
  exists x : D, exists s : seq D, dipath x s /\ size s = 14.
Proof.
move=> n0 dmin.
have h14 : 14 <= ell D.
  exact: (ck_conj1_delta7_from_finite_refutations n0 dmin).
have [x [s [ps sE]]] := ellP n0.
exists x, (take 14 s); split.
- exact: dipath_take.
- by rewrite size_takel // sE.
Qed.

(** Conjecture-1-shaped alias. *)
Corollary ck_conj1_at_7_from_finite_refutations (D : orientedDigraph) :
  0 < #|D| -> (forall v : D, 7 <= outdeg v) -> 2 * 7 <= ell D.
Proof.
exact: ck_conj1_delta7_from_finite_refutations.
Qed.

End FromFiniteRefutations.
