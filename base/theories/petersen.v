(** * GTBase.petersen -- the Petersen graph in two named views

    [petersen_ord] is the drawn graph on ['I_10]: the literal ordered table [petersen_edge_table] of fifteen natural
    pairs (outer 5-cycle [0..4], spokes [i ~ i+5], inner pentagram [5-7-9-6-8-5]), the natural relation
    [petersen_conn] (a pair or its reverse is listed; false when either end is outside [0..9] or on equal ends) and
    [petersen_ord_adj x y := (x != y) && petersen_conn (val x) (val y)].  [petersen_kneser] is the Kneser graph
    KG(5,2): its carrier [kneser52V] is the exact subtype of the two-element subsets of ['I_5], adjacency is
    disjointness ([kneser52_adj]).  The two views are different graph records on different carriers, related by the
    explicit isomorphism [petersen_ord_kneser_diso], built from the labelling [petersen_label] (outer vertex [i] to a
    pair, inner vertex to the complementary disjoint pair; the table below is the contract) and its inverse.  An
    isomorphism is not an equality of graphs or carriers.
    Registry: meta/library_primitives/petersen.json (A24). *)
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The ordinal view *)

(** Outer 5-cycle, spokes, inner pentagram: order and orientation are part of the table. *)
Definition petersen_edge_table : seq (nat * nat) :=
  [:: (0,1); (1,2); (2,3); (3,4); (4,0);
      (0,5); (1,6); (2,7); (3,8); (4,9);
      (5,7); (7,9); (9,6); (6,8); (8,5) ]%N.

Definition petersen_conn (a b : nat) : bool := ((a, b) \in petersen_edge_table) || ((b, a) \in petersen_edge_table).

Definition petersen_ord_adj (x y : 'I_10) : bool := (x != y) && petersen_conn (val x) (val y).

Lemma petersen_ord_adj_sym : symmetric petersen_ord_adj.
Proof. by move=> x y; rewrite /petersen_ord_adj /petersen_conn eq_sym orbC. Qed.

Lemma petersen_ord_adj_irrefl : irreflexive petersen_ord_adj.
Proof. by move=> x; rewrite /petersen_ord_adj eqxx. Qed.

Definition petersen_ord : sgraph := SGraph petersen_ord_adj_sym petersen_ord_adj_irrefl.

Lemma petersen_ord_edgeE (x y : petersen_ord) : x -- y = (x != y) && petersen_conn (val x) (val y).
Proof. by []. Qed.

(** The natural relation is symmetric, false on equal ends and outside [0..9]. *)
Lemma petersen_connC (a b : nat) : petersen_conn a b = petersen_conn b a.
Proof. by rewrite /petersen_conn orbC. Qed.

Lemma petersen_conn_out (a b : nat) : (9 < a)%N -> petersen_conn a b = false.
Proof.
move=> a9; have H : all (fun p : nat * nat => (p.1 <= 9) && (p.2 <= 9))%N petersen_edge_table by [].
apply/negbTE; rewrite negb_or; apply/andP; split; apply/negP.
  by move/(allP H) => /andP [] /=; rewrite leqNgt a9.
by move/(allP H) => /andP [] /= _; rewrite leqNgt a9.
Qed.

Lemma petersen_conn_refl (a : nat) : petersen_conn a a = false.
Proof.
have H : all (fun p : nat * nat => p.1 != p.2) petersen_edge_table by [].
by apply/negbTE; rewrite /petersen_conn orbb; apply/negP => /(allP H) /=; rewrite eqxx.
Qed.

(** ** The Kneser view KG(5,2) *)

(** The exact cardinality-two subtype of the subsets of ['I_5]. *)
Definition kneser52V : finType := {x : {set 'I_5} | #|x| == 2}.

Definition kneser52_adj (x y : kneser52V) : bool := [disjoint val x & val y].

Lemma kneser52_adj_sym : symmetric kneser52_adj.
Proof. by move=> x y; rewrite /kneser52_adj disjoint_sym. Qed.

Lemma kneser52_adj_irrefl : irreflexive kneser52_adj.
Proof.
move=> x; apply/negP; rewrite /kneser52_adj -setI_eq0 setIid => /eqP Hx.
by move: (valP x); rewrite Hx cards0.
Qed.

Definition petersen_kneser : sgraph := SGraph kneser52_adj_sym kneser52_adj_irrefl.

Lemma petersen_kneser_edgeE (x y : petersen_kneser) : x -- y = [disjoint val x & val y].
Proof. by []. Qed.

Lemma card_kneser52V : #|kneser52V| = 10.
Proof. by rewrite card_sig -cardsE card_draws card_ord. Qed.

(** ** The explicit isomorphism *)

Local Notation O5 i := (@Ordinal 5 i isT).

(** The labelling of the drawn vertices by two-subsets of ['I_5]: this table is the contract. *)
Definition petersen_label (i : 'I_10) : {set 'I_5} :=
  match val i with
  | 0 => [set O5 0; O5 1]
  | 1 => [set O5 2; O5 3]
  | 2 => [set O5 0; O5 4]
  | 3 => [set O5 1; O5 2]
  | 4 => [set O5 3; O5 4]
  | 5 => [set O5 2; O5 4]
  | 6 => [set O5 1; O5 4]
  | 7 => [set O5 1; O5 3]
  | 8 => [set O5 0; O5 3]
  | _ => [set O5 0; O5 2]
  end.

Lemma petersen_label_card2 (i : 'I_10) : #|petersen_label i| == 2%N.
Proof. by case: i => -[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]] Hi //=; rewrite cards2. Qed.

Definition petersen_kmap (i : 'I_10) : kneser52V := Sub (petersen_label i) (petersen_label_card2 i).

Lemma val_petersen_kmap (i : 'I_10) : val (petersen_kmap i) = petersen_label i.
Proof. by rewrite /petersen_kmap SubK. Qed.

(** Disjointness of two two-sets, lowered to ordinal inequalities. *)
Lemma disjoint_set2 (T : finType) (a b c d : T) :
  [disjoint [set a; b] & [set c; d]] = [&& a != c, a != d, b != c & b != d].
Proof. by rewrite disjoints_subset subUset !sub1set !in_setC !in_set2 !negb_or -andbA. Qed.

(** Edges both ways: the drawn adjacency matches Kneser disjointness under the labelling, on every ordered pair. *)
Lemma petersen_kmap_adj (x y : 'I_10) : kneser52_adj (petersen_kmap x) (petersen_kmap y) = petersen_ord_adj x y.
Proof.
rewrite /kneser52_adj !val_petersen_kmap /petersen_ord_adj /petersen_conn /petersen_label.
case: x => -[|[|[|[|[|[|[|[|[|[|nx]]]]]]]]]] Hx //=;
  case: y => -[|[|[|[|[|[|[|[|[|[|ny]]]]]]]]]] Hy //=;
  rewrite disjoint_set2; by vm_compute.
Qed.

Lemma petersen_label_inj_bool (x y : 'I_10) : (petersen_label x == petersen_label y) = (x == y).
Proof.
rewrite /petersen_label.
case: x => -[|[|[|[|[|[|[|[|[|[|nx]]]]]]]]]] Hx //=;
  case: y => -[|[|[|[|[|[|[|[|[|[|ny]]]]]]]]]] Hy //=;
  rewrite eqEsubset !subUset !sub1set !in_set2; by vm_compute.
Qed.

Lemma petersen_kmap_inj : injective petersen_kmap.
Proof.
move=> x y /(f_equal val); rewrite !val_petersen_kmap => /eqP H.
by apply/eqP; rewrite -petersen_label_inj_bool.
Qed.

Lemma codom_petersen_kmap (v : kneser52V) : v \in codom petersen_kmap.
Proof.
have le : (#|kneser52V| <= #|'I_10|)%N by rewrite card_kneser52V card_ord.
have [g _ cg] := inj_card_bij petersen_kmap_inj le.
by apply/codomP; exists (g v); rewrite cg.
Qed.

Definition petersen_kinv (v : kneser52V) : 'I_10 := iinv (codom_petersen_kmap v).

Lemma petersen_kmapK : cancel petersen_kinv petersen_kmap.
Proof. by move=> v; rewrite /petersen_kinv f_iinv. Qed.

Lemma petersen_kinvK : cancel petersen_kmap petersen_kinv.
Proof. by move=> x; apply: petersen_kmap_inj; rewrite petersen_kmapK. Qed.

(** The two views of the Petersen graph are isomorphic simple graphs. *)
Definition petersen_ord_kneser_diso : petersen_ord ≃ petersen_kneser :=
  @Diso' petersen_ord petersen_kneser petersen_kmap petersen_kinv petersen_kinvK petersen_kmapK petersen_kmap_adj.
