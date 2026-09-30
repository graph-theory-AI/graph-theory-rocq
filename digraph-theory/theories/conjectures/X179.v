(** * Digraph.conjectures.X179 -- v2 kappa-maderian digraph row *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X179 vocabulary ***********************************************)

Definition x179_strongly_connected_after_deleting (G : diGraphType) (S : {set G}) : Prop :=
  forall x y : G,
    x \notin S -> y \notin S ->
    connect (fun u v => (u --> v) && (u \notin S) && (v \notin S)) x y.

Definition x179_k_vertex_strongly_connected (G : diGraphType) (k : nat) : Prop :=
  forall S : {set G}, #|S| < k -> x179_strongly_connected_after_deleting S.

Definition x179_out_cut (G : diGraphType) (S : {set G}) : {set G * G} :=
  [set e : G * G | (e.1 \in S) && (e.2 \notin S) && (e.1 --> e.2)].

Definition x179_k_arc_strongly_connected (G : diGraphType) (k : nat) : Prop :=
  forall S : {set G}, S != set0 -> S != [set: G] -> k <= #|x179_out_cut S|.

Definition x179_directed_path (G : diGraphType) (s t : G) (p : seq G) : Prop :=
  path (fun x y => x --> y) s p /\ last s p = t /\ uniq (s :: p).

Definition x179_directed_subdivision (G D : diGraphType) : Prop :=
  exists branch : D -> G,
    injective branch /\
    forall x y : D,
      x --> y ->
      exists p : seq G,
        x179_directed_path (branch x) (branch y) p /\
        forall z : G, z \in p -> z != branch y -> forall u : D, z != branch u.

Definition x179_kappa_maderian (D : diGraphType) : Prop :=
  exists k : nat,
    forall G : diGraphType,
      x179_k_vertex_strongly_connected G k -> x179_directed_subdivision G D.

Definition x179_arc_kappa_maderian (D : diGraphType) : Prop :=
  exists k : nat,
    forall G : diGraphType,
      x179_k_arc_strongly_connected G k -> x179_directed_subdivision G D.

(** ** X179 statements *****************************************************)

(** Corpus row: arxiv:1610.00876#05
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1610.00876__05/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1610.00876__05.json
    English statement: (Aboulker, Cohen, Havet, Lochet, Moura, Thomasse 2016, arXiv:1610.00876, Problem 16)
      Every finite digraph D is kappa-maderian and kappa-prime-maderian: there is a k such that
      every k-strongly-connected digraph contains a subdivision of D, and there is a k such that
      every k-arc-strongly-connected digraph contains a subdivision of D.
    Definitions: [x179_k_vertex_strongly_connected G k] - deleting fewer than k vertices leaves
      every remaining ordered pair mutually reachable (this file);
      [x179_k_arc_strongly_connected G k] - every nonempty proper vertex set has out-cut at
      least k (this file); [x179_directed_subdivision G D] - injective branch vertices in G
      with, for every arc of D, an internally-branch-free directed path (this file);
      [x179_kappa_maderian] / [x179_arc_kappa_maderian] (this file).
    Notes: The corpus poses two questions (are all digraphs kappa-maderian,
      kappa-prime-maderian); the body encodes the conjunction of the two affirmative answers.
      The subdivision notion here requires only that internal vertices avoid branch vertices;
      unlike [contains_subdivision] of conjectures/X2.v it does not require the interiors of
      distinct replacement paths to be pairwise disjoint, so the containment is weaker and the
      statement correspondingly weaker. *)
Definition digraph_kappa_maderian_statement : Prop :=
  forall D : diGraphType,
    x179_kappa_maderian D /\ x179_arc_kappa_maderian D.
