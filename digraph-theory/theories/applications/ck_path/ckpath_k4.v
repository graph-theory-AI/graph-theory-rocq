(** * The Cheng--Keevash directed-path conjecture at out-degree four. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented dipath strong lemma7
  ckpath_kernel_cases ckpath_odd_gateway.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A nonempty strong 4-outregular oriented digraph cannot have all
    directed paths shorter than eight arcs. *)
Lemma no_short_strong4 (H : orientedDigraph) :
  (forall v : H, outdeg v = 4) -> 0 < #|H| -> strongb H ->
  ell H < 8 -> False.
Proof.
move=> hreg hn hstr hell.
have [x [p [a [u [r [hfacts hwit hshape]]]]]] :=
  ckpath_kernel_cases4 hreg hn hstr hell.
case: hfacts => hAB hA2 [hpath hcycle hB hclose hcount].
case: hcycle => dcC sizeC cardC.
case: hshape => L7 S4 r1 a1.
have csize : size (ckC x p a) = 2 * 4 - 1.
  by rewrite sizeC L7 a1.
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
have horder : 2 * 4 + 1 <= #|H|.
  apply: oriented_card => // v.
  by rewrite hreg.
exact: (@odd_gateway_d4_impossible H 4 (ckC x p a) (ckS x p a)
  isT hreg hstr hell dcC csize S4 SsubC Sclosed horder erefl).
Qed.

(** Conjecture 1 at minimum out-degree four. *)
Theorem ck_conj1_delta4 (D : orientedDigraph) :
  0 < #|D| -> (forall v : D, 4 <= outdeg v) -> 8 <= ell D.
Proof.
move=> n0 dmin.
rewrite ltnNge; apply/negP=> hell7.
have [W [hn0 hstr hreg hell hcard]] := reduction n0 dmin.
apply: (no_short_strong4 hreg hn0 hstr).
exact: leq_ltn_trans (leq_trans hell hell7) (ltnSn 7).
Qed.

(** Explicit simple directed path with eight arcs. *)
Corollary ck_conj1_delta4_path (D : orientedDigraph) :
  0 < #|D| -> (forall v : D, 4 <= outdeg v) ->
  exists x : D, exists s : seq D, dipath x s /\ size s = 8.
Proof.
move=> n0 dmin.
have h8 : 8 <= ell D by exact: ck_conj1_delta4.
have [x [s [ps sE]]] := ellP n0.
exists x, (take 8 s); split.
- exact: dipath_take.
- by rewrite size_takel // sE.
Qed.

(** Conjecture-1-shaped alias. *)
Corollary ck_conj1_at_4 (D : orientedDigraph) :
  0 < #|D| -> (forall v : D, 4 <= outdeg v) -> 2 * 4 <= ell D.
Proof. exact: ck_conj1_delta4. Qed.
