(** * GTBase.hypercubes -- the d-dimensional hypercube Q_d in two named views

    [product_hypercube d] is the iterated cartesian-product graph: [Q_0 = 'K_1] (one vertex and no edge, not the
    empty graph) and [Q_(d+1) = 'K_2 □ Q_d], over [GTBase.base.cartesian_product], on the nested ordinal/product
    carrier.  [tuple_hypercube d] is the Boolean-tuple graph: its vertices are the [d.-tuple bool], two of them
    adjacent iff exactly one coordinate differs.  The two views are different graph records on different carriers.
    They are related, for every dimension and without any positive-dimension guard, by the explicit isomorphism
    [product_tuple_hypercube_diso], built from the mutually inverse coordinate maps [product_to_tuple] and
    [tuple_to_product].  An isomorphism is not an equality of graphs: a statement that pins a graph by equality keeps
    its own view and carrier.
    Registry: meta/library_primitives/hypercube.json (A23). *)
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The iterated cartesian-product view *)

Fixpoint product_hypercube (d : nat) : sgraph :=
  match d with
  | 0 => 'K_1
  | d'.+1 => cartesian_product 'K_2 (product_hypercube d')
  end.

Lemma product_hypercube0 : product_hypercube 0 = 'K_1.
Proof. by []. Qed.

Lemma product_hypercubeS (d : nat) : product_hypercube d.+1 = cartesian_product 'K_2 (product_hypercube d).
Proof. by []. Qed.

Lemma card_product_hypercube (d : nat) : #|product_hypercube d| = 2 ^ d.
Proof.
elim: d => [|d IH] /=; first by rewrite expn0 card_ord.
by rewrite card_prod IH card_ord expnS.
Qed.

(** Q_0 has its single vertex and no edge. *)
Lemma product_hypercube0_edge (x y : product_hypercube 0) : x -- y = false.
Proof. by rewrite (ord1 x) (ord1 y) sg_irrefl. Qed.

(** ** The Boolean-tuple view *)

Section TupleHypercube.
Variable d : nat.

Definition tuple_hypercube_rel : rel (d.-tuple bool) :=
  fun x y => #|[set i : 'I_d | tnth x i != tnth y i]| == 1.

Lemma tuple_hypercube_sym : symmetric tuple_hypercube_rel.
Proof.
move=> x y; rewrite /tuple_hypercube_rel.
suff -> : [set i : 'I_d | tnth x i != tnth y i] = [set i : 'I_d | tnth y i != tnth x i] by [].
by apply/setP => i; rewrite !inE eq_sym.
Qed.

Lemma tuple_hypercube_irrefl : irreflexive tuple_hypercube_rel.
Proof.
move=> x; rewrite /tuple_hypercube_rel.
suff -> : [set i : 'I_d | tnth x i != tnth x i] = set0 by rewrite cards0.
by apply/setP => i; rewrite !inE eqxx.
Qed.

Definition tuple_hypercube : sgraph := SGraph tuple_hypercube_sym tuple_hypercube_irrefl.

End TupleHypercube.

Lemma tuple_hypercube_edgeE (d : nat) (x y : tuple_hypercube d) :
  x -- y = (#|[set i : 'I_d | tnth x i != tnth y i]| == 1).
Proof. by []. Qed.

Lemma card_tuple_hypercube (d : nat) : #|tuple_hypercube d| = 2 ^ d.
Proof. by rewrite card_tuple card_bool. Qed.

(** Two tuples are adjacent iff they differ at exactly one coordinate. *)
Lemma tuple_hypercube_edgeP (d : nat) (x y : tuple_hypercube d) :
  reflect (exists i : 'I_d, tnth x i != tnth y i /\ forall j : 'I_d, j != i -> tnth x j = tnth y j) (x -- y).
Proof.
rewrite tuple_hypercube_edgeE; apply: (iffP cards1P) => [[i Di]|[i [xyi same]]].
  exists i; split=> [|j ji]; first by have := set11 i; rewrite -Di inE.
  apply/eqP; apply: contraNT ji => xyj.
  have : j \in [set i : 'I_d | tnth x i != tnth y i] by rewrite inE.
  by rewrite Di inE.
exists i; apply/setP => j; rewrite !inE.
by have [->|ji] := eqVneq j i; rewrite ?xyi ?same ?eqxx.
Qed.

Lemma tuple_hypercube0_edge (x y : tuple_hypercube 0) : x -- y = false.
Proof. by rewrite (tuple0 x) (tuple0 y) sg_irrefl. Qed.

(** The tuples differing from [x] are counted coordinate by coordinate. *)
Lemma tuple_hypercube_diff_cons (d : nat) (p q : bool) (u v : d.-tuple bool) :
  #|[set i : 'I_d.+1 | tnth [tuple of p :: u] i != tnth [tuple of q :: v] i]| =
  (p != q) + #|[set i : 'I_d | tnth u i != tnth v i]|.
Proof.
rewrite -!sum1_card big_mkcond [in RHS]big_mkcond big_ord_recl /= inE !tnth0; congr (_ + _).
by apply: eq_bigr => i _; rewrite !inE !tnthS.
Qed.

Lemma tuple_hypercube_diff_eq0 (d : nat) (u v : d.-tuple bool) :
  (#|[set i : 'I_d | tnth u i != tnth v i]| == 0) = (u == v).
Proof.
rewrite cards_eq0; apply/eqP/eqP => [D0|->]; last by apply/setP => i; rewrite !inE eqxx.
apply: eq_from_tnth => i; apply/eqP; rewrite -[_ == _]negbK; apply/negP => uv.
by have := in_set0 i; rewrite -D0 inE uv.
Qed.

(** Adjacency of extended tuples: the first coordinates agree and the tails are adjacent, or the tails agree and the
    first coordinates differ -- the cartesian-product rule. *)
Lemma tuple_hypercube_edge_cons (d : nat) (p q : bool) (u v : d.-tuple bool) :
  ([tuple of p :: u] : tuple_hypercube d.+1) -- [tuple of q :: v] =
  ((p == q) && ((u : tuple_hypercube d) -- v)) || ((u == v) && (p != q)).
Proof.
rewrite tuple_hypercube_edgeE tuple_hypercube_diff_cons tuple_hypercube_edgeE.
have [_|_] /= := eqVneq p q; first by rewrite andbF orbF.
by rewrite ?add1n eqSS tuple_hypercube_diff_eq0 andbT.
Qed.

(** ** The explicit isomorphism between the two views *)

(** A vertex of [K_2] as a bit, and back. *)
Definition K2_bit (a : 'I_2) : bool := val a == 1.

Definition bit_K2 (b : bool) : 'I_2 := @Ordinal 2 b (leq_b1 b).

Lemma K2_bitK : cancel K2_bit bit_K2.
Proof. by move=> [[|[|m]] Hm]; apply: val_inj. Qed.

Lemma bit_K2K : cancel bit_K2 K2_bit.
Proof. by case. Qed.

(** The coordinate maps: a vertex of the product view is a nested pair whose [K_2] components, read as bits, are
    the tuple's coordinates in order. *)
Fixpoint product_to_tuple (d : nat) : product_hypercube d -> tuple_hypercube d :=
  match d with
  | 0 => fun _ => [tuple] : 0.-tuple bool
  | d'.+1 => fun v : 'K_2 * product_hypercube d' =>
      [tuple of K2_bit v.1 :: (product_to_tuple v.2 : d'.-tuple bool)] : d'.+1.-tuple bool
  end.

Fixpoint tuple_to_product (d : nat) : tuple_hypercube d -> product_hypercube d :=
  match d with
  | 0 => fun _ => (ord0 : 'K_1)
  | d'.+1 => fun t : d'.+1.-tuple bool =>
      ((bit_K2 (thead t), tuple_to_product (behead_tuple t : d'.-tuple bool)) : 'K_2 * product_hypercube d')
  end.

Lemma product_to_tupleK (d : nat) : cancel (@product_to_tuple d) (@tuple_to_product d).
Proof.
elim: d => [|d IH] v; first by rewrite (ord1 v).
case: v => a w; rewrite /= theadE K2_bitK.
have -> : behead_tuple [tuple of K2_bit a :: product_to_tuple w] = product_to_tuple w by apply: val_inj.
by rewrite IH.
Qed.

Lemma tuple_to_productK (d : nat) : cancel (@tuple_to_product d) (@product_to_tuple d).
Proof.
elim: d => [|d IH] t; first by rewrite [RHS]tuple0.
apply: val_inj; rewrite /= bit_K2K IH [in RHS](tuple_eta t).
by [].
Qed.

Lemma product_to_tuple_edge (d : nat) : {mono @product_to_tuple d : x y / x -- y}.
Proof.
elim: d => [|d IH] x y; first by rewrite (ord1 x) (ord1 y) !sg_irrefl.
case: x => a w; case: y => b z.
rewrite [_ -- _]tuple_hypercube_edge_cons IH (inj_eq (can_inj K2_bitK)) (inj_eq (can_inj (@product_to_tupleK d))).
by [].
Qed.

(** The two views of Q_d are isomorphic, for every dimension. *)
Definition product_tuple_hypercube_diso (d : nat) : product_hypercube d ≃ tuple_hypercube d :=
  Diso' (@product_to_tupleK d) (@tuple_to_productK d) (@product_to_tuple_edge d).

(** Q_1 is K_2: the [K_1] component is constant, so only the [K_2] component moves. *)
Definition product_hypercube1_diso : product_hypercube 1 ≃ 'K_2.
Proof.
pose f : product_hypercube 1 -> 'K_2 := fun v : 'K_2 * 'K_1 => v.1.
pose g : 'K_2 -> product_hypercube 1 := fun a : 'K_2 => (a, ord0) : 'K_2 * 'K_1.
have fK : cancel f g by move=> [a u]; rewrite /f /g /= (ord1 u).
have gK : cancel g f by [].
apply: (@Diso' (product_hypercube 1) 'K_2 f g fK gK) => -[a u] [b v].
rewrite /f /= (ord1 u) (ord1 v); apply/idP/idP => [ab|]; first by apply/orP; right; rewrite eqxx.
by case/orP => /andP [] // _ ->.
Defined.
