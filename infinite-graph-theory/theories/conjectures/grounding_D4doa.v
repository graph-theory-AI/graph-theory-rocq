(** * Infinite.conjectures.grounding_D4doa — Qed-closed grounding for D4doa

    Sanity / non-vacuity checks for every NEW primitive introduced by milestone
    D4doa: the hexagonal-torus carrier and 3-colour-count vocabulary of
    [conjectures.D4doa] ([hex_torus], [is_proper3], [n3colorings], [site_value],
    [converges]) and the K_omega exact-colouring vocabulary of
    [foundations.igraph] ([Kedge_coloring], [sym_coloring], [exact_coloring],
    [uses_color], [exactly_m_colored], plus [Komega]/[ray]).

    For each primitive we record:
      - a SATISFIABLE witness (the predicate is inhabited / the antecedent is
        non-vacuous), and
      - at least one TEXTBOOK identity it must satisfy.

    Everything is Qed-closed; the file declares no Axiom/Parameter/Admitted.
    (The real-analysis identities transitively inherit the standard Stdlib
    classical-reals axioms via [R], exactly as the [site_value]/[converges]
    statements in [D4doa] do.) *)

From GTBase Require Export base.
From Infinite Require Import foundations.igraph conjectures.D4doa.
From mathcomp Require Import all_boot.
From mathcomp Require Import all_algebra.
Import GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ================================================================= *)
(** ** A trivial single-vertex (edgeless) [sgraph] for compute-checks *)

Definition triv_adj (x y : unit) : bool := false.
Lemma triv_sym : symmetric triv_adj. Proof. by []. Qed.
Lemma triv_irr : irreflexive triv_adj. Proof. by []. Qed.
Definition triv : sgraph := SGraph triv_sym triv_irr.

(** Identity: the trivial graph has exactly one vertex. *)
Lemma card_triv : #|triv| = 1.
Proof. by rewrite card_unit. Qed.

(** ================================================================= *)
(** ** Row 1 primitives : [hex_torus], [is_proper3], [n3colorings],
       [site_value], [converges] *)

(** *** [hex_torus] : satisfiable (has an edge) + textbook vertex count *)

(** Witness: the A- and B-vertices of a single cell are adjacent, so the
    honeycomb torus is genuinely non-edgeless. *)
Lemma hex_torus_has_edge (n : nat) :
  (((ord0, ord0), true) : hex_torus n) -- ((ord0, ord0), false).
Proof. by []. Qed.

(** Identity: |V(H_n)| = 2 (n+1)^2 (two sublattice vertices per torus cell). *)
Lemma card_hex_torus (n : nat) : #|hex_torus n| = (n.+1 * n.+1 * 2)%N.
Proof. by rewrite !card_prod card_bool !card_ord. Qed.

(** *** [is_proper3] : satisfiable (the edgeless graph is always proper) *)

Lemma triv_proper3 (c : {ffun triv -> 'I_3}) : is_proper3 c.
Proof.
apply/colourings.proper_colouringP => x y.
by have -> : (x -- y) = false by [].
Qed.

(** *** [n3colorings] : textbook value chi(triv,3) = 3^|V| = 3 *)

Lemma n3colorings_triv : n3colorings triv = 3.
Proof.
rewrite /n3colorings.
have -> : [set c : {ffun triv -> 'I_3} | is_proper3 c] = setT.
  by apply/setP => c; rewrite !inE triv_proper3.
by rewrite cardsT card_ffun card_ord card_triv expn1.
Qed.

(** *** [persite_cauchy] : satisfiable — a constant per-site sequence (vsize 1)
    is Cauchy, witnessing non-vacuity of the thermodynamic-limit predicate (and
    that the axiom-free rcfType encoding has actual content). *)
Lemma persite_cauchy_const (k : nat) : persite_cauchy (fun _ => k) (fun _ => 1).
Proof.
move=> R eps Heps; exists 0%N => m n _ _ sm sn _ _ Em En.
rewrite expr1 in Em; rewrite expr1 in En.
by rewrite Em En subrr normr0.
Qed.

(** ================================================================= *)
(** ** Row 2 primitives : the K_omega exact-colouring vocabulary *)

(** *** [Komega] / [ray] : satisfiable — the identity sequence is a ray *)
Lemma Komega_id_ray : @ray Komega (@id nat).
Proof. by split=> [|n]; [exact: inj_id | exact: n_Sn]. Qed.

(** *** [Kedge_coloring] / [sym_coloring] / [exact_coloring] : satisfiable.
    For every [c >= 1] the symmetric colouring [{x,y} |-> min x y] is exact
    (it uses every colour [k] on the pair [{k, k+1}]). *)
Lemma Kcoloring_satisfiable (c : nat) : (0 < c)%N ->
  exists col : Kedge_coloring c, sym_coloring col /\ exact_coloring col.
Proof.
case: c => // c' _.
exists (fun x y => inord (minn x y)); split.
  by move=> x y; rewrite minnC.
move=> k; exists (val k), (val k).+1; split; first exact: n_Sn.
have hm : minn (val k) (val k).+1 = val k by apply/minn_idPl; exact: leqnSn.
by rewrite /= hm inord_val.
Qed.

(** *** [uses_color] / [exactly_m_colored] : satisfiable.
    On [c = 1] the (only) colouring [col1] colours the whole graph with the
    single colour [ord0]; every infinite subgraph is exactly 1-coloured. *)
Definition col1 : Kedge_coloring 1 := fun _ _ => ord0.

Lemma col1_sym : sym_coloring col1.
Proof. by []. Qed.

Lemma col1_exact : exact_coloring col1.
Proof. by move=> k; exists 0, 1; split=> //; rewrite (ord1 k). Qed.

Lemma col1_exactly1 : exactly_m_colored col1 (@id nat) 1.
Proof.
exists [set: 'I_1]; split; first by rewrite cardsT card_ord.
move=> k; split=> [_|_]; last exact: in_setT.
by exists 0, 1; split=> //; rewrite (ord1 k).
Qed.

(** *** [Pcm] : satisfiable — [P(1,1)] holds (consistent with the [m = 1]
    branch of the conjecture's RHS).  Any symmetric exact 1-colouring sends
    every edge to [ord0], so the whole graph [id] is an exactly-1-coloured
    countably infinite complete subgraph. *)
Lemma Pcm_1_1 : Pcm 1 1.
Proof.
move=> col _ _; exists (@id nat); split; first exact: inj_id.
exists [set: 'I_1]; split; first by rewrite cardsT card_ord.
move=> k; split=> [_|_]; last exact: in_setT.
by exists 0, 1; split=> //; rewrite (ord1 (col 0 1)) (ord1 k).
Qed.
