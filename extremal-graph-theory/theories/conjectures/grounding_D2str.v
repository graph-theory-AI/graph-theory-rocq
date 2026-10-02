(** * Extremal.conjectures.grounding_D2str — grounding lemmas for milestone D2str

    Qed-closed, axiom-free sanity results for the NEW primitives introduced in
    [Extremal.conjectures.D2str].  For each new primitive we give:
      - a SATISFIABLE witness (the predicate is inhabited / non-contradictory);
      - at least one textbook IDENTITY it must satisfy.

    Witness models used:
      - [unit] as a one-point [finType] — grounds the order-dimension primitives
        ([is_linear_order]/[order_extends]/[realizer]/[poset_dim_le]) on the
        textbook fact that a finite linear order is its own size-1 realizer.
      - [set0] hyperedge families — vacuous witnesses for the hypergraph
        predicates ([linear_hypergraph]/[uniform_hypergraph]/[plane_represents]).
      - [cycle_graph 1] (one vertex, edge-less) — grounds the weighted-walk
        primitives ([wlen]/[edge_length]/[shortest_walk]): the only walk is the
        empty one, so it is trivially shortest.
      - [cycle_graph 0] (empty graph) — grounds the cover primitives
        ([eq_covers]/[is_eq_cover_number]) and [peripheral_cycle] on the empty
        cycle ([eq] number = 0).
      - the empty cycle [[::]] — a [ucycle] for [geodesic_cycle]/[induced_cycle].
      - [cycle_graph 3] — a genuine edge for [cyc_rel]/[cycle_graph] adjacency.
      - the diagonal [eq_op] — the trivial equivalence subgraph (each vertex its
        own class) for [equivalence_graph]. *)

From GTBase Require Import base.
From mathcomp Require Import all_algebra.
From Extremal.conjectures Require Import D2str.

Import GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ================================================================= *)
(** ** Row 1 — order dimension: [is_linear_order], [order_extends],
       [realizer], [poset_dim_le] *)

(** Identity (projection): a linear order is reflexive. *)
Lemma is_linear_order_refl (X : finType) (l : rel X) :
  is_linear_order l -> reflexive l.
Proof. by case. Qed.

(** Witness: the one-point order is a linear order. *)
Lemma is_linear_order_unit : is_linear_order (fun _ _ : unit => true).
Proof. by split=> // -[] []. Qed.

(** Identity: every relation extends itself. *)
Lemma order_extends_refl (X : finType) (l : rel X) : order_extends l l.
Proof. by []. Qed.

(** Textbook identity: a finite linear order is its own size-1 realizer. *)
Lemma realizer_self (X : finType) (l : rel X) :
  is_linear_order l -> realizer l [:: l].
Proof.
move=> Hlin; split.
- by move=> i; rewrite /= ltnS leqn0 => /eqP ->; split.
- by move=> x y; split => [Hl i|H]; [rewrite ltnS leqn0 => /eqP -> | apply: (H 0)].
Qed.

(** Witness: a linear order has order dimension [<= 1]. *)
Lemma poset_dim_le_self (X : finType) (l : rel X) :
  is_linear_order l -> poset_dim_le l 1.
Proof. by move=> Hlin; exists [:: l]; split=> //; apply: realizer_self. Qed.

(** Concrete satisfiable witness: the one-point poset has dimension [<= 1]. *)
Lemma poset_dim_le_unit : poset_dim_le (fun _ _ : unit => true) 1.
Proof. by apply: poset_dim_le_self; apply: is_linear_order_unit. Qed.

(** Textbook identity: order dimension is monotone in the bound. *)
Lemma poset_dim_le_mono (X : finType) (l : rel X) (d d' : nat) :
  poset_dim_le l d -> (d <= d')%N -> poset_dim_le l d'.
Proof. by move=> [ls [sz Hr]] dd'; exists ls; split=> //; apply: leq_trans dd'. Qed.

(** ================================================================= *)
(** ** Row 1 — plane objects: [in_seg], [in_tri], [in_obj] *)

Section GeomGround.
Variable R : realFieldType.
Local Open Scope ring_scope.
Implicit Types a b c p : R * R.

(** Witness + identity: an endpoint lies on its segment ([t = 0]). *)
Lemma in_seg_left a b : in_seg a b a.
Proof. by exists 0; split; rewrite ?ler01 ?mul0r ?addr0. Qed.

(** Identity: the other endpoint lies on the segment ([t = 1]). *)
Lemma in_seg_right a b : in_seg a b b.
Proof.
exists 1; split; rewrite ?ler01 ?mul1r //.
- by rewrite addrC subrK.
- by rewrite addrC subrK.
Qed.

(** Witness + identity: a vertex lies in its triangle ([l1 = 1]). *)
Lemma in_tri_vertex a b c : in_tri a b c a.
Proof.
exists 1, 0, 0; split; rewrite ?ler01 ?addr0 //.
by split; rewrite !mul1r !mul0r !addr0.
Qed.

(** Witness: an endpoint lies in the segment object. *)
Lemma in_obj_seg_left a b : in_obj (PSeg a b) a.
Proof. exact: in_seg_left. Qed.

(** Witness: a vertex lies in the triangle object. *)
Lemma in_obj_tri_vertex a b c : in_obj (PTri a b c) a.
Proof. exact: in_tri_vertex. Qed.

End GeomGround.

(** ================================================================= *)
(** ** Row 1 — hypergraph incidence: [linear_hypergraph], [inc_le],
       [incidence_poset_dim_le], [plane_represents] *)

(** Witness: the empty hyperedge family is linear (vacuously). *)
Lemma linear_hypergraph0 (T : finType) : linear_hypergraph (@set0 {set T}).
Proof. by move=> e f; rewrite in_set0. Qed.

(** Textbook identity: linearity is inherited by subfamilies. *)
Lemma linear_hypergraph_sub (T : finType) (E E' : {set {set T}}) :
  E' \subset E -> linear_hypergraph E -> linear_hypergraph E'.
Proof. by move=> sub H e f /(subsetP sub) eE /(subsetP sub) fE; apply: H. Qed.

(** Textbook identity: the incidence-poset order is reflexive. *)
Lemma inc_le_refl (T : finType) (E : {set {set T}}) : reflexive (inc_le E).
Proof. by move=> -[v|e] /=; rewrite eqxx. Qed.

(** Identity: the incidence poset orients vertices below their hyperedges only. *)
Lemma inc_le_inrl (T : finType) (E : {set {set T}}) (e : {set T}) (v : T) :
  inc_le E (inr e) (inl v) = false.
Proof. by []. Qed.

(** Witness + identity: incidence-poset dimension is monotone in the bound. *)
Lemma incidence_poset_dim_le_mono (T : finType) (E : {set {set T}}) (d d' : nat) :
  incidence_poset_dim_le E d -> (d <= d')%N -> incidence_poset_dim_le E d'.
Proof. exact: poset_dim_le_mono. Qed.

(** Witness: the empty hyperedge family is (vacuously) plane-representable. *)
Lemma plane_represents0 (R : realFieldType) (T : finType) :
  plane_represents R (@set0 {set T}).
Proof.
exists (fun _ => (0, 0)%R), (fun _ => PSeg (0, 0)%R (0, 0)%R).
by move=> e; rewrite in_set0.
Qed.

(** ================================================================= *)
(** ** Row 2 — weighted geodesic cycles: [cyc_edge], [on_cycle_walk],
       [wlen], [edge_length], [shortest_walk], [geodesic_cycle],
       [induced_cycle], [peripheral_cycle] *)

(** Textbook identity: the cyclic edge relation is symmetric. *)
Lemma cyc_edge_sym (G : sgraph) (c : seq G) (x y : G) :
  cyc_edge c x y = cyc_edge c y x.
Proof. by rewrite /cyc_edge /seq_cyclic_consecutiveb orbC. Qed.

(** Witness: the empty walk is on any cycle. *)
Lemma on_cycle_walk_nil (G : sgraph) (c : seq G) (u : G) : on_cycle_walk c u [::].
Proof. by []. Qed.

(** Textbook identity: the empty walk has length zero. *)
Lemma wlen_nil (R : realFieldType) (G : sgraph) (ell : G -> G -> R) (u : G) :
  wlen ell u [::] = 0%R.
Proof. by rewrite /wlen /= big_nil. Qed.

(** Witness: the constant-1 assignment is a valid edge length (over any field). *)
Lemma edge_length_const1 (R : realFieldType) (G : sgraph) :
  edge_length (fun (_ _ : G) => (1%R : R)).
Proof. by split=> [x y _|//]; apply: ltr01. Qed.

(** The one-vertex cycle graph [cycle_graph 1] is edge-less. *)
Lemma C1_edgeless (x y : cycle_graph 1) : (x -- y) = false.
Proof. by rewrite /edge_rel /= /cyc_rel [x]ord1 [y]ord1 eqxx. Qed.

(** Hence its only walk is the empty one. *)
Lemma C1_path_nil (u : cycle_graph 1) (p : seq (cycle_graph 1)) :
  path (--) u p -> p = [::].
Proof. by case: p => // a l /andP[]; rewrite C1_edgeless. Qed.

(** Witness: on [cycle_graph 1] the empty walk is a shortest walk. *)
Lemma shortest_walk_C1 (R : realFieldType)
    (ell : cycle_graph 1 -> cycle_graph 1 -> R) (u : cycle_graph 1) :
  shortest_walk ell u u [::].
Proof.
split=> // q pq _.
by rewrite (C1_path_nil pq).
Qed.

(** Witness: the empty cycle is (vacuously) [ell]-geodesic. *)
Lemma geodesic_cycle_nil (R : realFieldType) (G : sgraph) (ell : G -> G -> R) :
  geodesic_cycle ell [::].
Proof. by split=> [|u v]; rewrite ?in_nil. Qed.

(** Identity (projection): a geodesic cycle is a [ucycle]. *)
Lemma geodesic_cycle_ucycle (R : realFieldType) (G : sgraph)
    (ell : G -> G -> R) (c : seq G) :
  geodesic_cycle ell c -> ucycle (--) c.
Proof. by case. Qed.

(** Witness: the empty cycle is (vacuously) induced. *)
Lemma induced_cycle_nil (G : sgraph) : induced_cycle (G := G) [::].
Proof. by split=> [|x y]; rewrite ?in_nil. Qed.

(** Identity (projection): an induced cycle is a [ucycle]. *)
Lemma induced_cycle_ucycle (G : sgraph) (c : seq G) :
  induced_cycle c -> ucycle (--) c.
Proof. by case. Qed.

(** Every vertex set of the empty graph [cycle_graph 0] is connected. *)
Lemma connected_C0 (A : {set cycle_graph 0}) : connected A.
Proof. by move=> x; case: (x : 'I_0). Qed.

(** Witness: on the empty graph the empty cycle is peripheral. *)
Lemma peripheral_cycle_C0_nil : peripheral_cycle (G := cycle_graph 0) [::].
Proof. by split; [apply: induced_cycle_nil | apply: connected_C0]. Qed.

(** Identity (projection): a peripheral cycle is induced. *)
Lemma peripheral_cycle_induced (G : sgraph) (c : seq G) :
  peripheral_cycle c -> induced_cycle c.
Proof. by case. Qed.

(** ================================================================= *)
(** ** Row 3 — regular subgraphs: [k_regular_subgraph] *)

(** Witness: the empty subgraph is [0]-regular. *)
Lemma k_regular_subgraph0 (G : sgraph) :
  k_regular_subgraph (@set0 G) (fun _ _ => false) 0.
Proof. by split=> // v; rewrite in_set0. Qed.

(** Identity (projection): a regular subgraph's adjacency is symmetric. *)
Lemma k_regular_subgraph_sym (G : sgraph) (S : {set G}) (adj : rel G) (k : nat) :
  k_regular_subgraph S adj k -> symmetric adj.
Proof. by case. Qed.

(** ================================================================= *)
(** ** Row 4 — simultaneous partition: [uniform_hypergraph], [rainbow] *)

(** Witness: the empty family is [r]-uniform (vacuously). *)
Lemma uniform_hypergraph0 (T : finType) (r : nat) :
  uniform_hypergraph (@set0 {set T}) r.
Proof. by move=> e; rewrite in_set0. Qed.

(** Textbook identity: uniformity is inherited by subfamilies. *)
Lemma uniform_hypergraph_sub (T : finType) (E E' : {set {set T}}) (r : nat) :
  E' \subset E -> uniform_hypergraph E r -> uniform_hypergraph E' r.
Proof. by move=> sub H e /(subsetP sub) eE; apply: H. Qed.

(** Witness: with a single part ([r = 1]), any nonempty edge is rainbow. *)
Lemma rainbow_r1 (T : finType) (part : T -> 'I_1) (v0 : T) (e : {set T}) :
  v0 \in e -> rainbow part e.
Proof.
move=> v0e; apply/forallP => j; apply/existsP; exists v0.
by rewrite v0e /= [part v0]ord1 [j]ord1 eqxx.
Qed.

(** Identity: a rainbow edge meets every class. *)
Lemma rainbow_meets (T : finType) (r : nat) (part : T -> 'I_r) (e : {set T}) :
  rainbow part e -> forall j : 'I_r, exists v, (v \in e) && (part v == j).
Proof. by move=> /forallP H j; apply/existsP; apply: H. Qed.

(** ================================================================= *)
(** ** Row 5 — covering powers of cycles: [cyc_rel], [cycle_graph],
       [equivalence_graph], [eq_covers], [is_eq_cover_number] *)

(** Witness: [cycle_graph 3] has a genuine cyclic edge. *)
Lemma cyc_rel_edge3 : cyc_rel (@Ordinal 3 0 isT) (@Ordinal 3 1 isT).
Proof. by []. Qed.

(** Witness: the corresponding [sgraph] adjacency holds in [cycle_graph 3]. *)
Lemma cycle_graph_edge3 :
  (@Ordinal 3 0 isT : cycle_graph 3) -- (@Ordinal 3 1 isT).
Proof. exact: cyc_rel_edge3. Qed.

(** Witness: the diagonal (equality) is an equivalence subgraph of any graph. *)
Lemma equivalence_graph_eq (G : sgraph) :
  equivalence_graph (G := G) (fun x y => x == y).
Proof.
split.
- exact: eqxx.
- by move=> x y; rewrite eq_sym.
- by move=> y x z /eqP -> /eqP ->.
- by move=> x y ne /eqP eq; rewrite eq eqxx in ne.
Qed.

(** Identity (projection): an equivalence subgraph relation is reflexive. *)
Lemma equivalence_graph_refl (G : sgraph) (e : rel G) :
  equivalence_graph e -> reflexive e.
Proof. by case. Qed.

(** Witness: the empty family covers the (edge-less) empty graph. *)
Lemma eq_covers_C0_nil : eq_covers (G := cycle_graph 0) [::].
Proof. by split=> [i|x]; [rewrite ltn0 | case: (x : 'I_0)]. Qed.

(** Witness: the empty graph has equivalence covering number [0]. *)
Lemma is_eq_cover_number_C0 : is_eq_cover_number (cycle_graph 0) 0.
Proof.
split; first by exists [::]; split=> //; apply: eq_covers_C0_nil.
by move=> es _.
Qed.

(** Textbook identity: the equivalence covering number is well-defined (unique). *)
Lemma is_eq_cover_number_uniq (G : sgraph) (m1 m2 : nat) :
  is_eq_cover_number G m1 -> is_eq_cover_number G m2 -> m1 = m2.
Proof.
move=> [[es1 [c1 sz1]] L1] [[es2 [c2 sz2]] L2].
apply/eqP; rewrite eqn_leq.
have h1 := L1 _ c2; have h2 := L2 _ c1.
by rewrite sz2 in h1; rewrite sz1 in h2; rewrite h1 h2.
Qed.
