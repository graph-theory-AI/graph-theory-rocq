(** * Minor.conjectures.X200 -- v2 Erdos-Posa planar model bound row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X200 vocabulary ***********************************************)

Definition x200_minor_model (G H : sgraph) (branch : H -> {set G}) : Prop :=
  (forall h : H, branch h != set0) /\
  (forall h : H, connected (branch h)) /\
  (forall h1 h2 : H, h1 != h2 -> branch h1 :&: branch h2 = set0) /\
  (forall h1 h2 : H, h1 -- h2 ->
    exists x y : G, [/\ x \in branch h1, y \in branch h2 & x -- y]).

Definition x200_model_vertices (G H : sgraph) (branch : H -> {set G}) : {set G} :=
  \bigcup_(h : H) branch h.

Definition x200_k_disjoint_H_models (G H : sgraph) (k : nat) : Prop :=
  exists branch : 'I_k -> H -> {set G},
    (forall i : 'I_k, @x200_minor_model G H (branch i)) /\
    forall i j : 'I_k, i != j ->
      @x200_model_vertices G H (branch i) :&:
      @x200_model_vertices G H (branch j) = set0.

Definition x200_H_model_hitting_set (G H : sgraph) (X : {set G}) : Prop :=
  forall branch : H -> {set G},
    @x200_minor_model G H branch -> @x200_model_vertices G H branch :&: X != set0.

Definition x200_H_model_erdos_posa_oklogk (H : sgraph) : Prop :=
  exists C : nat,
    forall (G : sgraph) (k : nat),
      1 <= k ->
      x200_k_disjoint_H_models G H k \/
      exists X : {set G},
        #|X| <= C * k * (trunc_log 2 k.+1).+1 /\ @x200_H_model_hitting_set G H X.

(** ** X200 statements *****************************************************)

(** Corpus row: arxiv:1710.06282#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1710.06282__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1710.06282__00.json
    English statement: (Aboulker, Fiorini, Huynh, Joret, Raymond and Sau 2018, "A tight
      Erdos-Posa function for wheel minors", Conjecture 1.2)
      For every planar graph H there is a constant C such that for every finite simple graph G
      and every k at least 1, either G contains k H-models with pairwise disjoint vertex sets,
      or G has a set of at most C times k times (one plus the base-2 logarithm of k+1, rounded
      down) vertices meeting the vertex set of every H-model of G.
    Definitions: [x200_minor_model G H branch] - an assignment of nonempty, connected, pairwise
      disjoint branch sets to the vertices of H with an edge of G between the branch sets of any
      two adjacent vertices of H (minor-theory/theories/conjectures/X200.v);
      [x200_model_vertices branch] - the union of the branch sets (same file);
      [x200_k_disjoint_H_models G H k] - k H-models whose vertex sets are pairwise disjoint
      (same file); [x200_H_model_hitting_set G H X] - X meets the vertex set of every H-model of
      G (same file); [x200_H_model_erdos_posa_oklogk H] - the Erdos-Posa dichotomy above with
      bounding function C * k * (trunc_log 2 (k+1)).+1 (same file); [wagner_planar H] - H has
      neither K_5 nor K_(3,3) as a minor, i.e. planarity by Wagner's theorem
      (base/theories/base.v); [trunc_log 2 n] - the base-2 logarithm rounded down (MathComp).
    Notes: the O(k log k) bounding function is realised by the explicit finite envelope
      C * k * (1 + trunc_log 2 (k+1)), with C chosen after H and before G and k; the "+1"
      keeps the factor positive at k = 1.  Planarity is the combinatorial Wagner predicate, so
      the statement is axiom-free.  The corpus records this row as solved (Cames van Batenburg,
      Huynh, Joret and Raymond, arXiv:1807.04969). *)
Definition planar_H_model_erdos_posa_oklogk_statement : Prop :=
  forall H : sgraph,
    wagner_planar H ->
    x200_H_model_erdos_posa_oklogk H.
