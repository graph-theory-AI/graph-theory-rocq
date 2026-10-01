(** * The Cheng--Keevash directed-path conjecture at out-degree six. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented dipath strong lemma7
  ckpath_kernel_cases ckpath_even_gateway ckpath_tight_cycles
  ckpath_odd_gateway ckpath_cert_graph_odd
  ckpath_kernel_c10_adapter ckpath_cert_graph_c10.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A nonempty strong 6-outregular oriented digraph cannot have all
    directed paths shorter than twelve arcs. *)
Lemma no_short_strong6 (H : orientedDigraph) :
  (forall v : H, outdeg v = 6) -> 0 < #|H| -> strongb H ->
  ell H < 12 -> False.
Proof.
move=> hreg hn hstr hell.
have [x [p [a [u [r [hfacts hwit hshape]]]]]] :=
  ckpath_kernel_cases6 hreg hn hstr hell.
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
have horder : 2 * 6 + 1 <= #|H|.
  apply: oriented_card => // v.
  by rewrite hreg.
case: hshape => [shape10 | shape9 | shape11r1 | shapeTail].
- case: shape10 => L10 S6 r2 a1.
  have csize : size (ckC x p a) = 10.
    by rewrite sizeC L10 a1.
  exact: (no_even_gateway6_c10 hreg hstr L10 dcC csize S6
            SsubEven SclosedEven horder).
- case: shape9 => L11 S5 r2 a3.
  have csize : size (ckC x p a) = 9.
    by rewrite sizeC L11 a3.
  apply: (no_tight_cycle9_five_set dcC csize SsubRaw S5).
  * by move=> v _; rewrite hreg.
  * exact: hclose.
- case: shape11r1 => L11 S6 r1 a1.
  have csize : size (ckC x p a) = 11.
    by rewrite sizeC L11 a1.
  exact: (ckpath_c11_graph_certificate_impossible hreg hstr hell dcC
            csize S6 SsubOdd SclosedOdd horder).
- case: shapeTail => [shape11r2 | shape10a2].
  * case: shape11r2 => L11 S6 r2 a1.
    have csize : size (ckC x p a) = 11.
      by rewrite sizeC L11 a1.
    exact: (ckpath_c11_graph_certificate_impossible hreg hstr hell dcC
              csize S6 SsubOdd SclosedOdd horder).
  * case: shape10a2 => L11 S6 r2 a2.
    subst a.
    have csize : size (ckC x p 2) = 10.
      by rewrite sizeC L11.
    have prefix := ckpath_kernel_c10_adapter hfacts_saved.
    case: prefix => v0R v1R v0Dv1 v0v1 v1next Ssub10 Sclosed10.
    exact: (ckpath_c10_graph_certificate_impossible hreg L11 dcC csize
              S6 Ssub10 Sclosed10 horder v0R v1R v0Dv1 v0v1 v1next).
Qed.

(** Conjecture 1 at minimum out-degree six. *)
Theorem ck_conj1_delta6 (D : orientedDigraph) :
  0 < #|D| -> (forall v : D, 6 <= outdeg v) -> 12 <= ell D.
Proof.
move=> n0 dmin.
rewrite ltnNge; apply/negP=> hell11.
have [W [hn0 hstr hreg hell hcard]] := reduction n0 dmin.
apply: (no_short_strong6 hreg hn0 hstr).
exact: leq_ltn_trans (leq_trans hell hell11) (ltnSn 11).
Qed.

(** Explicit simple directed path with twelve arcs. *)
Corollary ck_conj1_delta6_path (D : orientedDigraph) :
  0 < #|D| -> (forall v : D, 6 <= outdeg v) ->
  exists x : D, exists s : seq D, dipath x s /\ size s = 12.
Proof.
move=> n0 dmin.
have h12 : 12 <= ell D by exact: ck_conj1_delta6.
have [x [s [ps sE]]] := ellP n0.
exists x, (take 12 s); split.
- exact: dipath_take.
- by rewrite size_takel // sE.
Qed.

(** Conjecture-1-shaped alias. *)
Corollary ck_conj1_at_6 (D : orientedDigraph) :
  0 < #|D| -> (forall v : D, 6 <= outdeg v) -> 2 * 6 <= ell D.
Proof. exact: ck_conj1_delta6. Qed.
