(** * Supplied bag decompositions of simple graphs

    Library migration, batch C family "tree_decomposition"
    (meta/library_primitives/tree-decomposition.json).  A bag decomposition is
    SUPPLIED data: a graph [G], an index graph [T] and a bag map
    [bag : T -> {set G}].  The raw contract has three clauses and no guard:
    - vertex coverage: every vertex of [G] lies in some bag;
    - edge coverage: both ends of every edge of [G] lie in a common bag;
    - connected fibres: for every vertex [v] the set of indices whose bag
      contains [v] is connected in [T].
    [bag_decomposition] states the clauses with Boolean existential witnesses
    (the corpus spelling of X126 and X27); [bag_decompositionP] is the
    Prop-witness spelling (X189), an unconditional equivalence, not a
    conversion.  [tree_bag_decomposition] adds the explicit [is_tree [set: T]]
    conjunct of X169 and nothing else.

    Nothing is imposed on the supplied index by the raw contract: [T] may be
    empty when [G] is ([bag_decomposition_K0]), it may carry unused or empty
    bags ([bag_decomposition_unused_empty_bag]), it may even be cyclic
    ([bag_decomposition_K3_index]), and only the tree-guarded variant rejects
    the cyclic index ([not_tree_bag_decomposition_K3_index]).  A nonempty [G]
    forces an inhabited [T] through vertex coverage alone.  Each clause has
    teeth: a missing vertex ([not_bag_decomposition_K1_empty_bag]), a missing
    edge ([not_bag_decomposition_K2_singleton_bags]) or a disconnected fibre
    ([not_bag_decomposition_two_isolated]) refutes the contract.

    Upstream [sdecomp T G bag] (GraphTheory.treewidth) is the same contract on
    a supplied FOREST [T], with Prop witnesses, a Boolean [&&] edge witness and
    predicate-restricted connectivity.  [bag_decomposition_sdecompP] transports
    between the two on the SAME supplied forest ([restrict_bag] exchanges the
    predicate and set restrictions of the fibre relation), and
    [bag_decomposition_forest_sdecompP] packages an arbitrary index graph with
    an explicit [is_forest] proof.  No forest or connectedness guard enters the
    raw contract.  Quantitative widths (treewidth, pathwidth, tree-alpha, ...)
    are separate contracts; the width-parameter foundation of minor-theory is
    left unchanged.  This focused module has no conjecture import and no base
    re-export; consumers import it. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries digraph sgraph treewidth.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The raw supplied-index contract and its tree-guarded variant *)

Definition bag_decomposition (G T : sgraph) (bag : T -> {set G}) : Prop :=
  (forall v : G, [exists t : T, v \in bag t]) /\
  (forall x y : G, x -- y -> [exists t : T, (x \in bag t) && (y \in bag t)]) /\
  forall v : G, connected [set t : T | v \in bag t].

Definition tree_bag_decomposition (G T : sgraph) (bag : T -> {set G}) : Prop :=
  is_tree [set: T] /\ bag_decomposition bag.

Section API.
Variables (G T : sgraph) (bag : T -> {set G}).

Lemma bag_decomposition_cover :
  bag_decomposition bag -> forall v : G, exists t : T, v \in bag t.
Proof. by move=> [cov _] v; have /existsP[t vt] := cov v; exists t. Qed.

Lemma bag_decomposition_edge :
  bag_decomposition bag ->
  forall x y : G, x -- y -> exists t : T, x \in bag t /\ y \in bag t.
Proof.
by move=> [_ [edg _]] x y xy; have /existsP[t /andP[xt yt]] := edg x y xy; exists t.
Qed.

Lemma bag_decomposition_fibre :
  bag_decomposition bag -> forall v : G, connected [set t : T | v \in bag t].
Proof. by move=> [_ [_ fib]]. Qed.

(** The Prop-witness presentation (X189's spelling). *)
Lemma bag_decompositionP :
  bag_decomposition bag <->
  (forall v : G, exists t : T, v \in bag t) /\
  (forall x y : G, x -- y -> exists t : T, x \in bag t /\ y \in bag t) /\
  (forall v : G, connected [set t : T | v \in bag t]).
Proof.
split=> [dec|[cov [edg fib]]].
- split; first exact: bag_decomposition_cover.
  by split; [exact: bag_decomposition_edge | exact: bag_decomposition_fibre].
- split=> [v|]; first by have [t vt] := cov v; apply/existsP; exists t.
  split=> // x y xy; have [t [xt yt]] := edg x y xy.
  by apply/existsP; exists t; rewrite xt yt.
Qed.

(** The tree-guarded variant in the Prop-witness presentation (X169's spelling). *)
Lemma tree_bag_decompositionP :
  tree_bag_decomposition bag <->
  is_tree [set: T] /\
  (forall v : G, exists t : T, v \in bag t) /\
  (forall x y : G, x -- y -> exists t : T, x \in bag t /\ y \in bag t) /\
  (forall v : G, connected [set t : T | v \in bag t]).
Proof.
by split=> -[tr dec]; split=> //; [apply/bag_decompositionP | apply/bag_decompositionP].
Qed.

(** The predicate and set spellings of "the indices whose bag contains [v]". *)
Lemma restrict_bag (v : G) :
  restrict [pred t : T | v \in bag t] (@sedge T)
    =2 restrict [set t : T | v \in bag t] (@sedge T).
Proof. by move=> a b; rewrite /restrict_mem /= !inE. Qed.

End API.

(** ** Transport to upstream [sdecomp] on the same supplied forest *)

Section Upstream.
Variables (G : sgraph) (T : forest) (bag : T -> {set G}).

Lemma bag_decomposition_sdecompP : bag_decomposition bag <-> sdecomp T G bag.
Proof.
split=> [[cov [edg fib]]|dec].
- split=> [x|x y xy|x t1 t2 h1 h2].
  + by have /existsP[t xt] := cov x; exists t.
  + by have /existsP[t xyt] := edg x y xy; exists t.
  + rewrite (eq_connect (@restrict_bag G T bag x)).
    by apply: (fib x); rewrite inE.
- split=> [v|]; first by have [t vt] := sbag_cover dec v; apply/existsP; exists t.
  split=> [x y xy|v t1 t2 h1 h2].
  + by have [t xyt] := sbag_edge dec xy; apply/existsP; exists t.
  + rewrite inE in h1; rewrite inE in h2.
    rewrite -(eq_connect (@restrict_bag G T bag v)).
    exact: (sbag_conn dec h1 h2).
Qed.

End Upstream.

(** An arbitrary index graph with an explicit forest proof. *)
Lemma bag_decomposition_forest_sdecompP (G T : sgraph) (tf : is_forest [set: T])
    (bag : T -> {set G}) :
  bag_decomposition bag <-> sdecomp (Forest tf) G bag.
Proof. exact: (@bag_decomposition_sdecompP G (Forest tf) bag). Qed.

(** ** Grounding *)

Section Grounding.

(** The empty graph with the empty index: every bag map qualifies. *)
Lemma bag_decomposition_K0 (bag : 'K_0 -> {set 'K_0}) : bag_decomposition bag.
Proof.
split=> [v|]; first by have := ltn_ord v; rewrite ltn0.
by split=> [x y _|v]; [have := ltn_ord x | have := ltn_ord v]; rewrite ltn0.
Qed.

(** One bag holding everything, indexed by a single vertex: [K_1] and [K_2]. *)
Lemma bag_decomposition_K1_one_bag : bag_decomposition (fun _ : 'K_1 => [set: 'K_1]).
Proof.
split=> [v|]; first by apply/existsP; exists ord0; rewrite inE.
split=> [x y xy|v]; first by apply/existsP; exists ord0; rewrite !inE.
have ->: [set t : 'K_1 | v \in [set: 'K_1]] = [set ord0].
  by apply/setP => t; rewrite !inE (fintype.ord1 t).
exact: connected1.
Qed.

Lemma bag_decomposition_K2_one_bag : bag_decomposition (fun _ : 'K_1 => [set: 'K_2]).
Proof.
split=> [v|]; first by apply/existsP; exists ord0; rewrite inE.
split=> [x y xy|v]; first by apply/existsP; exists ord0; rewrite !inE.
have ->: [set t : 'K_1 | v \in [set: 'K_2]] = [set ord0].
  by apply/setP => t; rewrite !inE (fintype.ord1 t).
exact: connected1.
Qed.

(** Missing vertex coverage: the empty bag does not cover [K_1]. *)
Lemma not_bag_decomposition_K1_empty_bag :
  ~ bag_decomposition (fun _ : 'K_1 => (set0 : {set 'K_1})).
Proof. by move=> [cov _]; have /existsP[t] := cov ord0; rewrite inE. Qed.

(** Missing edge coverage: singleton bags cover the vertices of [K_2] but not
    its edge. *)
Lemma not_bag_decomposition_K2_singleton_bags :
  ~ bag_decomposition (fun t : 'K_2 => [set t]).
Proof.
move=> [_ [edg _]].
have /existsP[t /andP[]] := edg ord0 ord_max isT.
by rewrite !inE => /eqP <- /eqP /(congr1 val).
Qed.

(** A two-vertex edgeless index graph. *)
Definition two_isolated : sgraph :=
  @SGraph 'I_2 rel0 preliminaries.rel0_sym preliminaries.rel0_irrefl.

(** A disconnected fibre: both isolated indices hold the single vertex of
    [K_1], so its fibre is the disconnected whole index. *)
Lemma not_bag_decomposition_two_isolated :
  ~ bag_decomposition (fun _ : two_isolated => [set: 'K_1]).
Proof.
move=> [_ [_ fib]].
have fibT : [set t : two_isolated | ord0 \in [set: 'K_1]] = [set: two_isolated].
  by apply/setP => t; rewrite !inE.
have := fib ord0; rewrite fibT => /(_ ord0 ord_max (in_setT _) (in_setT _)).
case/connectP => -[|a p] /= pth eq; first by have := congr1 val eq.
by move: pth => /andP[rel _]; move: rel; rewrite /restrict_mem /= !inE /=.
Qed.

(** A cyclic index graph satisfies the raw contract ... *)
Lemma bag_decomposition_K3_index : bag_decomposition (fun _ : 'K_3 => [set: 'K_1]).
Proof.
split=> [v|]; first by apply/existsP; exists ord0; rewrite inE.
split=> [x y xy|v]; first by apply/existsP; exists ord0; rewrite !inE.
have ->: [set t : 'K_3 | v \in [set: 'K_1]] = [set: 'K_3].
  by apply/setP => t; rewrite !inE.
move=> x y _ _; case: (eqVneq x y) => [->|xy]; first exact: connect0.
have xy' : x -- y := xy.
by apply: connect1; rewrite /= !inE.
Qed.

(** ... but not the tree-guarded variant: the triangle is no forest. *)
Lemma not_tree_bag_decomposition_K3_index :
  ~ tree_bag_decomposition (fun _ : 'K_3 => [set: 'K_1]).
Proof.
move=> [[tf _] _]; have card3 : 2 < #|'K_3| by rewrite card_ord.
by have [x [y [xy nadj]]] := forest3 tf card3; rewrite /edge_rel /= xy in nadj.
Qed.

(** An unused empty bag is allowed. *)
Lemma bag_decomposition_unused_empty_bag :
  bag_decomposition (fun t : 'K_2 => if t == ord0 then [set: 'K_1] else set0).
Proof.
split=> [v|]; first by apply/existsP; exists ord0; rewrite eqxx inE.
split=> [x y xy|v]; first by apply/existsP; exists ord0; rewrite eqxx !inE.
have ->: [set t : 'K_2 | v \in (if t == ord0 then [set: 'K_1] else set0)] = [set ord0].
  by apply/setP => t; rewrite !inE; case: (t == ord0); rewrite !inE.
exact: connected1.
Qed.

End Grounding.

(** Vertex coverage alone forces an index when the supplied graph is nonempty. *)
Lemma bag_decomposition_nonempty_index (G T : sgraph) (bag : T -> {set G}) :
  bag_decomposition bag -> 0 < #|G| -> 0 < #|T|.
Proof.
move=> dec /card_gt0P[v _]; have [t _] := bag_decomposition_cover dec v.
by apply/card_gt0P; exists t; rewrite inE.
Qed.

(** The explicit tree guard does not itself require an inhabited index. *)
Lemma tree_bag_decomposition_K0 (bag : 'K_0 -> {set 'K_0}) :
  tree_bag_decomposition bag.
Proof.
split; last exact: bag_decomposition_K0.
by split; [move=> [] | move=> []].
Qed.
