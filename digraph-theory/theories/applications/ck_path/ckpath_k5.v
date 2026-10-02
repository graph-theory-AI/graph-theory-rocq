(** * The Cheng--Keevash directed-path conjecture at out-degree five. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented dipath strong lemma7
  ckpath_kernel_cases ckpath_tight_cycles ckpath_odd_gateway
  ckpath_cert_graph_odd.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A nonempty strong 5-outregular oriented digraph cannot have all
    directed paths shorter than ten arcs. *)
Lemma no_short_strong5 (H : orientedDigraph) :
  (forall v : H, outdeg v = 5) -> 0 < #|H| -> strongb H ->
  ell H < 10 -> False.
Proof.
move=> hreg hn hstr hell.
have [x [p [a [u [r [hfacts hwit hshape]]]]]] :=
  ckpath_kernel_cases5 hreg hn hstr hell.
case: hfacts => hAB hA2 [hpath hcycle hB hclose hcount].
case: hcycle => dcC sizeC cardC.
have SsubC : ckS x p a \subset odd_cycle_set (ckC x p a).
  apply/subsetP=> z.
  rewrite /ckS => /imsetP[b bB ->].
  rewrite /odd_cycle_set inE mem_prev.
  move: bB; rewrite inE => /andP[].
  by [].
have Sclosed : forall b z, b \in ckS x p a -> b --> z ->
    z \in odd_cycle_set (ckC x p a).
  move=> b z bS abz.
  rewrite /odd_cycle_set inE.
  exact: hclose bS abz.
have horder : 2 * 5 + 1 <= #|H|.
  apply: oriented_card => // v.
  by rewrite hreg.
case: hshape => [[L8 S5 r2 a1] | [L9 S5 r1 a1]
                  | [L9 S5 r2 a1] | [L9 S5 r2 a2]].
- have csize : size (ckC x p a) = 8.
    by rewrite sizeC L8 a1.
  apply: (no_tight_cycle8_five_set dcC csize SsubC S5).
  - by move=> v _; rewrite hreg.
  - exact: hclose.
- have csize : size (ckC x p a) = 9.
    by rewrite sizeC L9 a1.
  exact: (ckpath_c9_graph_certificate_impossible hreg hstr hell dcC csize
            S5 SsubC Sclosed horder).
- have csize : size (ckC x p a) = 9.
    by rewrite sizeC L9 a1.
  exact: (ckpath_c9_graph_certificate_impossible hreg hstr hell dcC csize
            S5 SsubC Sclosed horder).
- have csize : size (ckC x p a) = 8.
    by rewrite sizeC L9 a2.
  apply: (no_tight_cycle8_five_set dcC csize SsubC S5).
  - by move=> v _; rewrite hreg.
  - exact: hclose.
Qed.

(** Conjecture 1 at minimum out-degree five. *)
Theorem ck_conj1_delta5 (D : orientedDigraph) :
  0 < #|D| -> (forall v : D, 5 <= outdeg v) -> 10 <= ell D.
Proof.
move=> n0 dmin.
rewrite ltnNge; apply/negP=> hell9.
have [W [hn0 hstr hreg hell hcard]] := reduction n0 dmin.
apply: (no_short_strong5 hreg hn0 hstr).
exact: leq_ltn_trans (leq_trans hell hell9) (ltnSn 9).
Qed.

(** Explicit simple directed path with ten arcs. *)
Corollary ck_conj1_delta5_path (D : orientedDigraph) :
  0 < #|D| -> (forall v : D, 5 <= outdeg v) ->
  exists x : D, exists s : seq D, dipath x s /\ size s = 10.
Proof.
move=> n0 dmin.
have h10 : 10 <= ell D by exact: ck_conj1_delta5.
have [x [s [ps sE]]] := ellP n0.
exists x, (take 10 s); split.
- exact: dipath_take.
- by rewrite size_takel // sE.
Qed.

(** Conjecture-1-shaped alias. *)
Corollary ck_conj1_at_5 (D : orientedDigraph) :
  0 < #|D| -> (forall v : D, 5 <= outdeg v) -> 2 * 5 <= ell D.
Proof. exact: ck_conj1_delta5. Qed.
