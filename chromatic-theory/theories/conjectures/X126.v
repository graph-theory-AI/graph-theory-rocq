(** * Chromatic.conjectures.X126 -- v2 Thue choice number / pathwidth row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X126 vocabulary ***********************************************)

(** A genuine (non-empty, simple) path: distinct vertices forming a walk. *)
Definition x126_genuine_path (G : sgraph) (p : seq G) : Prop :=
  match p with
  | [::] => False
  | x :: q => uniq p /\ path (--) x q
  end.

(** [col] is a nonrepetitive colouring: on every path of even length [2h] the
    colour sequence of the first half differs from that of the second half (no
    path spells a "square").  The [h = 1] instance already forces properness on
    edges, so nonrepetitive colourings are in particular proper. *)
Definition x126_nonrepetitive (G : sgraph) (C : finType) (col : G -> C) : Prop :=
  forall (p : seq G) (h : nat),
    x126_genuine_path p ->
    size p = 2 * h ->
    0 < h ->
    map col (take h p) != map col (take h (drop h p)).

(** A nonrepetitive L-colouring: pick each vertex's colour from its list [L v]
    so that the resulting colouring is nonrepetitive. *)
Definition x126_nonrepetitive_list_colouring
    (G : sgraph) (C : finType) (L : G -> {set C}) : Prop :=
  exists col : G -> C,
    (forall v : G, col v \in L v) /\ x126_nonrepetitive col.

(** [x126_thue_choosable G k]: for EVERY list assignment [L] whose lists all
    have size at least [k], [G] admits a nonrepetitive L-colouring.  Thus
    [x126_thue_choosable G k] says the Thue choice number [π_l(G)] is at most
    [k]. *)
Definition x126_thue_choosable (G : sgraph) (k : nat) : Prop :=
  forall (C : finType) (L : G -> {set C}),
    (forall v : G, k <= #|L v|) -> x126_nonrepetitive_list_colouring L.

(** [x126_is_thue_choice_number G k]: [k] is the Thue choice number [π_l(G)] —
    the least list size that guarantees a nonrepetitive L-colouring.  Stated
    relationally (as [is_choice_number] is in base) to stay proof-free. *)
Definition x126_is_thue_choice_number (G : sgraph) (k : nat) : Prop :=
  x126_thue_choosable G k /\
  (forall k' : nat, x126_thue_choosable G k' -> k <= k').

(** Path-decompositions and pathwidth, replicated from the corpus
    tree-decomposition apparatus (minor-theory X27 / X95): a path-decomposition
    is a tree-decomposition whose indexing tree is a PATH (a tree of maximum
    degree ≤ 2). *)
Definition x126_tree_decomposition
    (G T : sgraph) (bag : T -> {set G}) : Prop :=
  (forall v : G, [exists t : T, v \in bag t]) /\
  (forall x y : G, x -- y -> [exists t : T, (x \in bag t) && (y \in bag t)]) /\
  forall v : G, connected [set t : T | v \in bag t].

Definition x126_path_index_graph (T : sgraph) : Prop :=
  is_tree [set: T] /\ Delta T <= 2.

Definition x126_pathwidth_at_most (G : sgraph) (k : nat) : Prop :=
  exists (T : sgraph) (bag : T -> {set G}),
    x126_path_index_graph T /\
    x126_tree_decomposition bag /\
    forall t : T, #|bag t| <= k.+1.

(** ** X126 statements *****************************************************)

(** Corpus row: studies:std_dujmovi_et_al_question_thue_choice_number_bounde
    Site: none
    Review: none
    English statement: (Dujmovic, Frankl, Joret, Kundgen and Wood, studies slice of the corpus)
      There is a function f from naturals to naturals such that every finite simple graph of
      pathwidth at most p is Thue f(p)-choosable, i.e. for every assignment of lists of at least
      f(p) colours there is a nonrepetitive colouring picking each vertex's colour from its list;
      equivalently the Thue choice number is bounded by a function of the pathwidth.
    Definitions: [x126_nonrepetitive col] - no path with an even number 2h > 0 of vertices has the
      colour sequence of its first half equal to that of its second half, so no path spells a square
      (this file); [x126_genuine_path p] - a nonempty list of distinct vertices forming a walk (this
      file); [x126_nonrepetitive_list_colouring L] - a nonrepetitive colouring picking colours from
      the lists (this file); [x126_thue_choosable G k] - every list assignment with all lists of
      size at least k admits one (this file); [x126_is_thue_choice_number G k] - the least such k,
      stated relationally (this file); [x126_pathwidth_at_most G k] - there is a tree-decomposition
      whose index graph is a tree of maximum degree at most 2 and whose bags have at most k+1
      vertices (this file); [x126_tree_decomposition] (this file).
    Notes: This row has no site or review page in the corpus, hence the literal "none" above. The
      corpus row is a QUESTION; the Rocq body is its affirmative reading. The quantifier order is
      load-bearing and follows the corpus idiom: the single function f is chosen BEFORE the
      pathwidth p and the graph G, so the bound is uniform. The h = 1 instance of nonrepetitiveness
      already forces properness. *)
Definition dujmovic_thue_choice_number_pathwidth_statement : Prop :=
  exists f : nat -> nat,
    forall (p : nat) (G : sgraph),
      x126_pathwidth_at_most G p ->
      x126_thue_choosable G (f p).
