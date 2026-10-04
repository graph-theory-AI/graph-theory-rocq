(** Downstream use of the two Petersen views without corpus imports: ten vertices in both views, literal outer, spoke
    and inner edges and non-edges of the drawn table, the natural relation's out-of-range and no-loop facts,
    disjoint and intersecting Kneser pairs, the inverse labelling maps with their adjacency equivalence, and the
    isomorphism with an invariant it transports. *)
From GTBase Require Import base petersen.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Notation V i := (@Ordinal 10 i isT).

Example petersen_ten_vertices : #|petersen_ord| = 10 /\ #|petersen_kneser| = 10.
Proof. by rewrite card_ord card_kneser52V. Qed.

(** The drawn table: an outer edge, a spoke and an inner (pentagram) edge; two non-edges. *)
Example petersen_ord_edges :
  [/\ (V 0 : petersen_ord) -- V 1, (V 0 : petersen_ord) -- V 5, (V 5 : petersen_ord) -- V 7,
      ~~ ((V 0 : petersen_ord) -- V 2) & ~~ ((V 5 : petersen_ord) -- V 6)].
Proof. by []. Qed.

(** The natural relation behind the table: false outside [0..9] and on equal ends, and symmetric. *)
Example petersen_conn_facts (a b : nat) :
  [/\ petersen_conn 10 b = false, petersen_conn a a = false & petersen_conn a b = petersen_conn b a].
Proof. by rewrite petersen_conn_out // petersen_conn_refl petersen_connC. Qed.

(** Kneser pairs: disjoint two-sets are adjacent, intersecting ones are not. *)
Local Notation O5 i := (@Ordinal 5 i isT).

Lemma card_pair01 : #|[set O5 0; O5 1]| == 2. Proof. by rewrite cards2. Qed.
Lemma card_pair23 : #|[set O5 2; O5 3]| == 2. Proof. by rewrite cards2. Qed.
Lemma card_pair12 : #|[set O5 1; O5 2]| == 2. Proof. by rewrite cards2. Qed.

Definition kp01 : kneser52V := Sub [set O5 0; O5 1] card_pair01.
Definition kp23 : kneser52V := Sub [set O5 2; O5 3] card_pair23.
Definition kp12 : kneser52V := Sub [set O5 1; O5 2] card_pair12.

Example kneser_pairs : (kp01 : petersen_kneser) -- kp23 /\ ~~ ((kp01 : petersen_kneser) -- kp12).
Proof. by rewrite !petersen_kneser_edgeE /kp01 /kp23 /kp12 !SubK !disjoint_set2. Qed.

(** The explicit labelling and its inverse, with adjacency matched in both directions. *)
Example petersen_labelling (x y : 'I_10) (v : kneser52V) :
  [/\ petersen_kinv (petersen_kmap x) = x, petersen_kmap (petersen_kinv v) = v
    & kneser52_adj (petersen_kmap x) (petersen_kmap y) = petersen_ord_adj x y].
Proof. by rewrite petersen_kinvK petersen_kmapK petersen_kmap_adj. Qed.

(** The isomorphism transports invariants, e.g. the number of edges. *)
Example petersen_views_edges : #|E(petersen_ord)| = #|E(petersen_kneser)|.
Proof. exact: diso_card_edge petersen_ord_kneser_diso. Qed.

Print Assumptions petersen_ten_vertices.
Print Assumptions petersen_ord_edges.
Print Assumptions petersen_conn_facts.
Print Assumptions kneser_pairs.
Print Assumptions petersen_labelling.
Print Assumptions petersen_views_edges.
