(** * Minor.foundations.containment -- containment models shared by the minor-theory waves

    Vocabulary for "G contains H" in the three senses the X214 / X220 / X228 waves need,
    all built on coq-graph-theory / GTBase primitives:

    - [has_induced_copy G H] : G has an INDUCED subgraph isomorphic to H.  This is the
      library's [isubgraph] ([H ⇀ G] : injective + [{mono : x y / x -- y}]) wrapped in
      [inhabited] to land in Prop; it is the positive form of GTBase's [induced_free].
    - [has_subdivision G H] : G contains a SUBDIVISION of H (H is a topological minor of G):
      injective branch vertices plus internally disjoint paths for the edges of H.  This is
      the undirected counterpart of digraph-theory's [contains_subdivision].
    - [is_subdivision_of H K] : H IS a subdivision of K, i.e. H carries a subdivision model
      of K that is SPANNING (every vertex of H is a branch vertex or an interior path vertex)
      and EXACT (every edge of H joins two consecutive vertices of one subdivision path).

    Auxiliary constructions: [el_graph n es] (the simple graph on ['I_n] given by an edge
    list, used to name the small forbidden graphs of the waves) and [sline_graph G] (the line
    graph of a SIMPLE graph; GTBase's [line_graph] is the multigraph one).  [sline_graph] is a
    verbatim copy of reconstruction-theory/theories/conjectures/U11.v's [sline_graph], which
    carries a [@MOVE-to-base] marker: minor-theory is the second area to need it. *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Small graphs from an edge list ***************************************

    [el_graph n es] has vertex set ['I_n]; [i] and [j] are adjacent when they are distinct
    and the pair of their values occurs in [es] in one order or the other.  The [i != j]
    guard makes irreflexivity structural, so a list may mention a loop without harm. *)

Section EdgeListGraph.
Variables (n : nat) (es : seq (nat * nat)).

Definition el_rel (i j : 'I_n) : bool :=
  (i != j) && (((val i, val j) \in es) || ((val j, val i) \in es)).

Lemma el_sym : symmetric el_rel.
Proof. by move=> i j; rewrite /el_rel eq_sym orbC. Qed.

Lemma el_irrefl : irreflexive el_rel.
Proof. by move=> i; rewrite /el_rel eqxx. Qed.

Definition el_graph : sgraph := SGraph el_sym el_irrefl.
End EdgeListGraph.

Lemma el_graphE (n : nat) (es : seq (nat * nat)) (i j : el_graph n es) :
  (i -- j) = (i != j) && (((val i, val j) \in es) || ((val j, val i) \in es)).
Proof. by []. Qed.

(** ** Induced containment **************************************************)

(** [G] has an induced subgraph isomorphic to [H].  [isubgraph] lands in [Type],
    so it is wrapped in [inhabited]. *)
Definition has_induced_copy (G H : sgraph) : Prop := inhabited (H ⇀ G).

Lemma has_induced_copy_refl (G : sgraph) : has_induced_copy G G.
Proof. by split; exists id => // x y. Qed.

(** Guard has teeth: an induced copy never has more vertices than its host. *)
Lemma has_induced_copy_card (G H : sgraph) : has_induced_copy G H -> #|H| <= #|G|.
Proof. by case=> i; exact: (@leq_card _ _ (isubgraph_fun i) (isubgraph_inj i)). Qed.

(** ** Line graph of a simple graph *****************************************)

Section SLine.
Variable G : sgraph.
Definition sline_rel : rel {e : {set G} | e \in E(G)} :=
  fun e1 e2 => (val e1 != val e2) && (val e1 :&: val e2 != set0).
Lemma sline_sym : symmetric sline_rel.
Proof. by move=> e1 e2; rewrite /sline_rel eq_sym setIC. Qed.
Lemma sline_irrefl : irreflexive sline_rel.
Proof. by move=> e; rewrite /sline_rel eqxx. Qed.
Definition sline_graph : sgraph := SGraph sline_sym sline_irrefl.
End SLine.

(** ** Subdivision models ***************************************************

    [sd_path a b p]: [p] is the list of INTERIOR vertices of a path from [a] to [b],
    i.e. [a :: rcons p b] is a walk all of whose vertices are distinct.  Note that
    [sd_path a b [::]] is [(a -- b) && (a != b)], so an unsubdivided edge is allowed. *)

Definition sd_path (G : sgraph) (a b : G) (p : seq G) : bool :=
  path (--) a (rcons p b) && uniq (a :: rcons p b).

Lemma sd_path_nil (G : sgraph) (a b : G) : sd_path a b [::] = (a -- b) && (a != b).
Proof. by rewrite /sd_path /= !andbT mem_seq1. Qed.

Lemma sd_path_edge (G : sgraph) (a b : G) : a -- b -> sd_path a b [::].
Proof. by move=> ab; rewrite sd_path_nil ab /=; apply: contraTneq ab => ->; rewrite sgP. Qed.

(** Consecutive vertices of the walk [a :: rcons p b] (in either order). *)
Definition sd_consec (G : sgraph) (a b : G) (p : seq G) (x y : G) : bool :=
  let s := a :: rcons p b in
  ((x, y) \in zip s (behead s)) || ((y, x) \in zip s (behead s)).

Lemma sd_consec_nil (G : sgraph) (a b x y : G) :
  sd_consec a b [::] x y = ((x, y) == (a, b)) || ((y, x) == (a, b)).
Proof. by rewrite /sd_consec /= !mem_seq1. Qed.

(** A subdivision model of [H] inside [G]: injective branch vertices, an interior
    vertex list per edge of [H] (reversed when the edge is read backwards), interior
    vertices distinct from every branch vertex, and interiors of distinct edges
    pairwise disjoint. *)
Record subdiv_model (H G : sgraph) := SubdivModel {
  sdm_branch : H -> G;
  sdm_inj : injective sdm_branch;
  sdm_path : H -> H -> seq G;
  sdm_pathP : forall u v : H, u -- v -> sd_path (sdm_branch u) (sdm_branch v) (sdm_path u v);
  sdm_pathC : forall u v : H, u -- v -> sdm_path v u = rev (sdm_path u v);
  sdm_avoid : forall (u v w : H) (x : G),
      u -- v -> x \in sdm_path u v -> x != sdm_branch w;
  sdm_disj : forall (u v u' v' : H) (x : G),
      u -- v -> u' -- v' -> x \in sdm_path u v -> x \in sdm_path u' v' ->
      [set u; v] = [set u'; v']
}.

(** [G] contains a subdivision of [H] (H is a topological minor of G). *)
Definition has_subdivision (G H : sgraph) : Prop := inhabited (subdiv_model H G).

(** The identity model: every graph contains a subdivision of itself (no edge subdivided). *)
Definition triv_subdiv_model (G : sgraph) : subdiv_model G G.
Proof.
apply: (@SubdivModel G G id (@inj_id G) (fun _ _ => [::])).
- by move=> u v uv; exact: sd_path_edge.
- by [].
- by move=> u v w x _; rewrite in_nil.
- by move=> u v u' v' x _ _; rewrite in_nil.
Defined.

Lemma has_subdivision_refl (G : sgraph) : has_subdivision G G.
Proof. by split; exact: triv_subdiv_model. Qed.

(** Guard has teeth: a subdivision model embeds the branch vertices injectively. *)
Lemma has_subdivision_card (G H : sgraph) : has_subdivision G H -> #|H| <= #|G|.
Proof. by case=> m; exact: (@leq_card _ _ (sdm_branch m) (@sdm_inj _ _ m)). Qed.

(** *** Being a subdivision ************************************************)

Section IsSubdivision.
Variables (K H : sgraph) (m : subdiv_model K H).

(** [x] is a model vertex: a branch vertex, or interior to one subdivision path. *)
Definition sdm_covers (x : H) : Prop :=
  (exists u : K, sdm_branch m u = x) \/
  (exists u v : K, u -- v /\ x \in sdm_path m u v).

(** [x -- y] is a model edge: [x] and [y] are consecutive on one subdivision path. *)
Definition sdm_realises (x y : H) : Prop :=
  exists u v : K, u -- v /\
    sd_consec (sdm_branch m u) (sdm_branch m v) (sdm_path m u v) x y.

(** The model uses ALL of [H] and NONE but the subdivision edges. *)
Definition subdiv_rep : Prop :=
  (forall x : H, sdm_covers x) /\ (forall x y : H, x -- y -> sdm_realises x y).
End IsSubdivision.

(** [H] is a subdivision of [K]. *)
Definition is_subdivision_of (H K : sgraph) : Prop :=
  exists m : subdiv_model K H, subdiv_rep m.

(** Non-vacuity: every graph is a subdivision of itself. *)
Lemma is_subdivision_of_refl (G : sgraph) : is_subdivision_of G G.
Proof.
exists (triv_subdiv_model G); split=> [x|x y xy]; first by left; exists x.
by exists x, y; split=> //=; rewrite sd_consec_nil eqxx.
Qed.

(** A subdivision of [K] contains a subdivision of [K] (forgetting spanning/exactness). *)
Lemma is_subdivision_ofW (H K : sgraph) : is_subdivision_of H K -> has_subdivision H K.
Proof. by case=> m _; split. Qed.

(** Guard has teeth: a subdivision of [K] has at least as many vertices as [K]. *)
Lemma is_subdivision_of_card (H K : sgraph) : is_subdivision_of H K -> #|K| <= #|H|.
Proof. by move/is_subdivision_ofW/has_subdivision_card. Qed.

(** ** Small toolkit reused by the grounding files ************************)

(** A duplicate-free sequence over a finite type is no longer than the type.
    (MathComp gap: [card_uniqP] + [max_card].) *)
Lemma uniq_size_card (T : finType) (s : seq T) : uniq s -> size s <= #|T|.
Proof. by move/card_uniqP => <-; exact: max_card. Qed.

(** The induced subgraph on [S] has [#|S|] vertices. *)
Lemma card_induced (G : sgraph) (S : {set G}) : #|induced S| = #|S|.
Proof. by rewrite card_sig; apply: eq_card => x; rewrite !inE. Qed.

(** Isomorphic graphs have the same number of vertices. *)
Lemma diso_card (G H : sgraph) : diso G H -> #|G| = #|H|.
Proof.
move=> d; apply/eqP; rewrite eqn_leq; apply/andP; split.
- by case: (iso_subgraph d) => f finj _; exact: (@leq_card _ _ f finj).
- by case: (iso_subgraph (diso_sym d)) => f finj _; exact: (@leq_card _ _ f finj).
Qed.

(** Every graph contains an induced copy of the empty graph. *)
Lemma has_induced_copy_empty (G H : sgraph) : #|H| = 0 -> has_induced_copy G H.
Proof.
move=> H0; have hf : forall x : H, False.
  move=> x; have hx : 0 < #|H| by apply/card_gt0P; exists x.
  by rewrite H0 in hx.
split; unshelve eexists (fun x : H => match hf x with end);
  by move=> x; case: (hf x).
Qed.

(** A subdivision model transports one edge of the model graph to an edge of the host. *)
Lemma has_subdivision_edge (G H : sgraph) (u v : H) :
  has_subdivision G H -> u -- v -> exists x y : G, x -- y.
Proof.
case=> m uv; move: (sdm_pathP m uv); rewrite /sd_path.
case: (sdm_path m u v) => [|c p] /= /andP[].
- by rewrite andbT => e _; exists (sdm_branch m u), (sdm_branch m v).
- by case/andP => e _ _; exists (sdm_branch m u), c.
Qed.

(** The line graph of a graph with an edge has a vertex. *)
Lemma sline_graph_card_gt0 (W : sgraph) (x y : W) : x -- y -> 0 < #|sline_graph W|.
Proof.
move=> xy; apply/card_gt0P.
have hE : [set x; y] \in E(W) by rewrite in_edges.
by exists (exist (fun e : {set W} => e \in E(W)) [set x; y] hE).
Qed.

(** ** Decidability of [has_induced_copy], and monotonicity for ['K_t,t] ****

    [has_induced_copy G H] is [inhabited (H ⇀ G)], a [Prop]; on finite simple
    graphs it is DECIDABLE, because an [isubgraph] is a function [H -> G] (a
    finite type once tabulated as a [{ffun ...}]) subject to two Boolean
    conditions.  [has_induced_copyP] is the reflection; it is what lets a maximum
    over the [t] with an induced ['K_t,t] be formed by [ex_maxn] (the induced
    biclique number of X220) without any classical axiom. *)

Definition isubgraphb (H G : sgraph) : bool :=
  [exists f : {ffun H -> G},
     injectiveb f && [forall x : H, forall y : H, (f x -- f y) == (x -- y)]].

Lemma has_induced_copyP (G H : sgraph) :
  reflect (has_induced_copy G H) (isubgraphb H G).
Proof.
apply: (iffP idP) => [/existsP[f /andP[/injectiveP finj /forallP mono]]|[i]].
- have mono' : {mono (f : H -> G) : x y / x -- y >-> x -- y}.
    by move=> x y; apply/eqP; move: (mono x) => /forallP /(_ y).
  by split; exact: (@ISubgraph H G (f : H -> G) finj mono').
- apply/existsP; exists (finfun (isubgraph_fun i)); apply/andP; split.
  + apply/injectiveP => x y; rewrite !ffunE; exact: (isubgraph_inj i).
  + apply/forallP => x; apply/forallP => y; rewrite !ffunE; apply/eqP.
    exact: isubgraph_mono.
Qed.

(** ['K_n,m] has [n + m] vertices. *)
Lemma card_KB (n m : nat) : #|KB n m| = n + m.
Proof. by rewrite card_sum !card_ord. Qed.

(** ['K_t,t] is an induced subgraph of ['K_s,s] for [t <= s]: widen both sides. *)
Lemma isubgraph_KB (t s : nat) : t <= s -> (KB t t) ⇀ (KB s s).
Proof.
move=> ts.
pose f (u : KB t t) : KB s s :=
  match u with inl i => inl (widen_ord ts i) | inr i => inr (widen_ord ts i) end.
have finj : injective f by move=> [a|a] [b|b] //= [] /val_inj ->.
by apply: (@ISubgraph _ _ f finj) => [[a|a] [b|b]].
Qed.

Lemma has_induced_copy_KB_le (G : sgraph) (t s : nat) :
  t <= s -> has_induced_copy G (KB s s) -> has_induced_copy G (KB t t).
Proof.
by move=> ts [i]; split; exact: (@isubgraph_comp _ _ _ (isubgraph_KB ts) i).
Qed.

Print Assumptions has_induced_copyP.
Print Assumptions has_induced_copy_KB_le.
