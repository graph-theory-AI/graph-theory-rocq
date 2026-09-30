(** * Minor.foundations.width_params -- width parameters shared by the minor-theory waves

    All of them are phrased with coq-graph-theory's [sdecomp] (tree decomposition over a
    [forest] index) and [width] (= the maximum BAG SIZE, NOT decremented), so "treewidth at
    most k" is [width D <= k.+1].

    - [tw_le G k] / [tw_ge G k] : treewidth at most / at least [k] (X220, X228).
    - [tree_alpha_le G k] : tree-independence number at most [k] -- some tree decomposition
      has [α(B_t) <= k] for every bag (X220).
    - [induced_matching M] and [tree_mu_le G m] : induced matching treewidth (tree-mu) at most
      [m] -- some tree decomposition bounds by [m] the size of every induced matching all of
      whose edges have an endpoint in one common bag (X220).
    - [layering L] and [layered_tw_le G l] : layered treewidth at most [l] -- a layering
      together with a tree decomposition each of whose bags meets every layer in at most [l]
      vertices (X228).
    - [queue_number_le G k] : queue number at most [k] -- a vertex order and an assignment of
      the edges to [k] queues with no two nested edges in one queue (X228). *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Treewidth ***********************************************************)

(** Treewidth at most [k]: a tree decomposition all of whose bags have at most [k+1]
    vertices ([width] is the maximum bag size, undecremented). *)
Definition tw_le (G : sgraph) (k : nat) : Prop :=
  exists (T : forest) (D : T -> {set G}), sdecomp T G D /\ width D <= k.+1.

(** Treewidth at least [k], stated as a lower bound on every admissible width
    (avoids a minimum operator; same device as X201). *)
Definition tw_ge (G : sgraph) (k : nat) : Prop := forall m : nat, tw_le G m -> k <= m.

(** Non-vacuity: a graph with few vertices has small treewidth. *)
Lemma tw_le_card (G : sgraph) (k : nat) : #|G| <= k.+1 -> tw_le G k.
Proof. by move=> le; have [T [D [dec w]]] := decomp_small le; exists T, D. Qed.

(** Guard has teeth: treewidth 0 forces the graph to have no edge. *)
Lemma tw_le0_edgeless (G : sgraph) (x y : G) : tw_le G 0 -> ~~ (x -- y).
Proof.
case=> T [D [dec w]]; apply/negP => xy.
have [t /andP[xt yt]] := sbag_edge dec xy.
have xy' : x != y by apply: contraTneq xy => ->; rewrite sgP.
have : #|[set x; y]| <= #|D t| by apply: subset_leq_card; rewrite subUset !sub1set xt yt.
rewrite cards2 xy' /= => le2.
have bt : #|D t| <= width D by rewrite /width; exact: leq_bigmax.
by move: le2; rewrite ltnNge (leq_trans bt w).
Qed.

(** Monotone in the bound. *)
Lemma tw_leW (G : sgraph) (k k' : nat) : k <= k' -> tw_le G k -> tw_le G k'.
Proof.
move=> le [T [D [dec w]]]; exists T, D; split; first exact: dec.
have h : k.+1 <= k'.+1 by rewrite ltnS.
exact: leq_trans w h.
Qed.

(** *** From a FOREST index to a TREE index *******************************

    [tw_le] indexes its tree decomposition by a [forest], while other encodings
    of treewidth in the corpus (X27's [x27_treewidth_at_most], X42) ask for a
    decomposition indexed by a TREE.  The two are equivalent, and the nontrivial
    direction is this one: joining every component of the index forest to one
    fresh node carrying the EMPTY bag yields a CONNECTED forest -- a tree -- with
    the same width.  The library supplies the forest part ([tlink] /
    [link_is_forest] / [decomp_link]); what is done here is the choice of one
    representative per component ([frep], constant on components because [pick]
    depends only on the extension of its predicate, [eq_pick]) and the
    connectedness of the result.

    [tw_le_tree] is the reusable half of the bridge F1; the [x27]-shaped wrapper
    lives with the edges that need it (Minor.conjectures.implications_X42). *)

Section ForestRep.
Variable T : sgraph.

Definition frep (t : T) : T := odflt t [pick s : T | connect (@sedge T) s t].

Lemma frep_connect (t : T) : connect (@sedge T) (frep t) t.
Proof. rewrite /frep; case: pickP => [s cs|_] //=; exact: connect0. Qed.

Lemma frep_eq (t t' : T) : connect (@sedge T) t t' -> frep t = frep t'.
Proof.
move=> tt'.
have pe : [pick s : T | connect (@sedge T) s t]
        = [pick s : T | connect (@sedge T) s t'].
  apply: eq_pick => s /=; apply/idP/idP => h.
  - exact: connect_trans h tt'.
  - by apply: connect_trans h _; rewrite sconnect_sym.
rewrite /frep -pe; case: pickP => [s _|hn] //=.
by move: (hn t); rewrite connect0.
Qed.

Definition freps : {set T} := [set t : T | frep t == t].

Lemma frep_mem (t : T) : frep t \in freps.
Proof. by rewrite inE; apply/eqP; apply: frep_eq; exact: frep_connect. Qed.

Lemma freps_disc :
  {in freps &, forall x y : T, x != y -> ~~ connect (@sedge T) x y}.
Proof.
move=> x y; rewrite !inE => /eqP hx /eqP hy xy; apply/negP => c.
by move: (frep_eq c); rewrite hx hy => /eqP; rewrite (negbTE xy).
Qed.

End ForestRep.

Lemma connect_add_node (T : sgraph) (U : {set T}) (x y : T) :
  connect (@sedge T) x y -> connect (@sedge (add_node T U)) (Some x) (Some y).
Proof.
case/connectP => p pth ->; apply/connectP.
exists (map Some p); last by rewrite last_map.
elim: p x pth => [//|a l IH] x /= /andP[xa pl].
by rewrite (IH a pl) andbT.
Qed.

Lemma connect_add_node_None (T : sgraph) (U : {set T}) (t u : T) :
  u \in U -> connect (@sedge T) u t ->
  connect (@sedge (add_node T U)) None (Some t).
Proof.
move=> uU ut; apply: (@connect_trans _ _ (Some u)).
- by apply: connect1; exact: uU.
- exact: connect_add_node.
Qed.

Lemma tw_le_tree (G : sgraph) (k : nat) :
  tw_le G k ->
  exists (T : forest) (D : T -> {set G}),
    [/\ sdecomp T G D, width D <= k.+1 & connected [set: T]].
Proof.
case=> T [D [dec w]].
have U_disc := @freps_disc T.
exists (@tlink T (freps T) U_disc), (decompL D set0); split.
- by apply: (@decomp_link T (freps T) U_disc G D set0); [exact: sub0set|exact: dec].
- rewrite /width; apply/bigmax_leqP => t _.
  case: t => [t|]; last by rewrite cards0.
  apply: leq_trans w; rewrite /width; exact: leq_bigmax.
- apply: connectedTI => x y.
  have hN : forall t : T, connect (@sedge (add_node T (freps T))) None (Some t).
    by move=> t; exact: (connect_add_node_None (frep_mem t) (frep_connect t)).
  have hN' : forall t : T, connect (@sedge (add_node T (freps T))) (Some t) None.
    by move=> t; rewrite sconnect_sym; exact: hN.
  case: x => [x|]; case: y => [y|].
  + exact: (@connect_trans _ _ None _ _ (hN' x) (hN y)).
  + exact: hN' x.
  + exact: hN y.
  + exact: connect0.
Qed.

Print Assumptions tw_le_tree.

(** ** Tree-independence number ********************************************)

(** Tree-alpha at most [k]: some tree decomposition has independence number at most
    [k] in every bag. *)
Definition tree_alpha_le (G : sgraph) (k : nat) : Prop :=
  exists (T : forest) (D : T -> {set G}), sdecomp T G D /\ forall t : T, α(D t) <= k.

(** Non-vacuity: the one-bag decomposition works whenever [α(G) <= k]. *)
Lemma tree_alpha_le_all (G : sgraph) (k : nat) : α([set: G]) <= k -> tree_alpha_le G k.
Proof. by move=> le; exists tunit, (fun _ => [set: G]); split=> //; exact: triv_sdecomp. Qed.

(** Monotone in the bound: a decomposition witnessing [k] witnesses every [k' >= k]. *)
Lemma tree_alpha_leW (G : sgraph) (k k' : nat) :
  k <= k' -> tree_alpha_le G k -> tree_alpha_le G k'.
Proof.
by move=> le [T [D [dec ab]]]; exists T, D; split=> // t; exact: leq_trans (ab t) le.
Qed.

(** Guard has teeth: tree-alpha 0 forces the graph to have no vertex, since every
    vertex lies in a bag and a bag with a vertex has independence number at least 1. *)
Lemma tree_alpha_le0_empty (G : sgraph) : tree_alpha_le G 0 -> #|G| = 0.
Proof.
case=> T [D [dec a0]]; apply/eqP; rewrite -leqn0 leqNgt.
apply/negP => /card_gt0P [x _].
have [t xt] := sbag_cover dec x.
have h0 : α(D t) == 0 by rewrite -leqn0 a0.
by move: h0; rewrite alpha_eq0 => /eqP D0; rewrite D0 inE in xt.
Qed.

(** ** Induced matching treewidth (tree-mu) ********************************)

(** An INDUCED matching: a set of edges, pairwise disjoint, with no edge of [G]
    between the ends of two distinct members. *)
Definition induced_matching (G : sgraph) (M : {set {set G}}) : Prop :=
  {subset M <= E(G)} /\
  forall (e f : {set G}) (x y : G),
    e \in M -> f \in M -> e != f -> x \in e -> y \in f -> (x != y) && ~~ (x -- y).

(** Tree-mu at most [m]: some tree decomposition bounds by [m] the size of every induced
    matching for which ONE bag contains at least one endpoint of each of its edges. *)
Definition tree_mu_le (G : sgraph) (m : nat) : Prop :=
  exists (T : forest) (D : T -> {set G}), sdecomp T G D /\
    forall M : {set {set G}},
      induced_matching M ->
      (exists t : T, forall e : {set G}, e \in M -> exists2 x : G, x \in e & x \in D t) ->
      #|M| <= m.

(** Monotone in the bound. *)
Lemma tree_mu_leW (G : sgraph) (m m' : nat) :
  m <= m' -> tree_mu_le G m -> tree_mu_le G m'.
Proof.
move=> le [T [D [dec bnd]]]; exists T, D; split=> // M im cov.
exact: leq_trans (bnd M im cov) le.
Qed.

(** Guard has teeth: [tree_mu_le G 0] rules out every edge, since a single edge is an
    induced matching of size 1 and lies in a bag. *)
Lemma tree_mu_le0_edgeless (G : sgraph) (x y : G) : tree_mu_le G 0 -> ~~ (x -- y).
Proof.
case=> T [D [dec bnd]]; apply/negP => xy.
have [t /andP[xt yt]] := sbag_edge dec xy.
have im : induced_matching [set [set x; y]].
  split=> [e|e f a b]; first by rewrite inE => /eqP->; rewrite in_edges.
  by rewrite !inE => /eqP-> /eqP->; rewrite eqxx.
have cov : exists t0 : T, forall e : {set G}, e \in [set [set x; y]] ->
    exists2 z : G, z \in e & z \in D t0.
  by exists t => e; rewrite inE => /eqP->; exists x; rewrite ?set21.
by have := bnd _ im cov; rewrite cards1.
Qed.

(** ** Layered treewidth ***************************************************)

(** A LAYERING: adjacent vertices lie in the same or in consecutive layers. *)
Definition layering (G : sgraph) (L : G -> nat) : Prop :=
  forall u v : G, u -- v -> (L u <= (L v).+1) /\ (L v <= (L u).+1).

(** Layered treewidth at most [l]: a layering plus a tree decomposition each of whose
    bags contains at most [l] vertices of each layer. *)
Definition layered_tw_le (G : sgraph) (l : nat) : Prop :=
  exists (L : G -> nat) (T : forest) (D : T -> {set G}),
    [/\ layering L, sdecomp T G D &
        forall (t : T) (i : nat), #|[set v in D t | L v == i]| <= l].

(** Non-vacuity: the constant layering and the one-bag decomposition give layered
    treewidth at most [#|G|]. *)
Lemma layered_tw_le_card (G : sgraph) : layered_tw_le G #|G|.
Proof.
exists (fun _ => 0), tunit, (fun _ => [set: G]); split.
- by [].
- exact: triv_sdecomp.
- by move=> t i; rewrite (leq_trans (max_card _)) // cardsT.
Qed.

(** Guard has teeth: layered treewidth 0 forces the graph to have no vertex. *)
Lemma layered_tw_le0_empty (G : sgraph) : layered_tw_le G 0 -> #|G| = 0.
Proof.
case=> L [T] [D] [_ dec bnd]; apply/eqP; rewrite -leqn0 leqNgt.
apply/negP => /card_gt0P [x _].
have [t xt] := sbag_cover dec x.
have : (0 < #|[set v in D t | L v == L x]|)%N.
  by apply/card_gt0P; exists x; rewrite !inE xt eqxx.
by rewrite ltnNge bnd.
Qed.

(** ** Queue number ********************************************************)

(** Queue number at most [k]: an injective vertex order and an assignment of every edge
    to one of [k] queues such that no queue contains two NESTED edges (an edge [ab] with
    [ord a < ord c < ord d < ord b] nesting an edge [cd]). *)
Definition queue_number_le (G : sgraph) (k : nat) : Prop :=
  exists (ord : G -> nat) (q : {set G} -> nat),
    [/\ injective ord,
        (forall e : {set G}, e \in E(G) -> q e < k) &
        forall a b c d : G,
          a -- b -> c -- d -> q [set a; b] = q [set c; d] ->
          ord a < ord c -> ord c < ord d -> ord d < ord b -> False].

(** Guard has teeth: with no queue at all the graph must be edgeless. *)
Lemma queue_number_le0_edgeless (G : sgraph) (x y : G) : queue_number_le G 0 -> ~~ (x -- y).
Proof.
case=> ord [q] [_ qlt _]; apply/negP => xy.
by have := qlt [set x; y]; rewrite in_edges => /(_ xy).
Qed.

Print Assumptions tree_alpha_leW.
Print Assumptions tree_mu_leW.
Print Assumptions tw_leW.
