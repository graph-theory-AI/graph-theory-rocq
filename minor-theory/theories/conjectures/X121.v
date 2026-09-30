(** * Minor.conjectures.X121 -- v2 (tw,ω)-bounded ↔ bounded tree-α row *)

From GTBase Require Export base.
From Minor.conjectures Require Import X27.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X121 vocabulary ***********************************************)

(** Clique number ω(G): the size of a largest clique, taken over the whole
    vertex set [set: G].  [ω(A)] is the corpus (coq-graph-theory) clique number
    of the subgraph induced on [A]. *)
Definition x121_omega (G : sgraph) : nat := ω([set: G]).

(** Tree-independence-number bound.  [x121_tree_alpha_le G k] holds iff G admits
    a valid tree-decomposition all of whose bags [B] satisfy α(G[B]) ≤ k, where
    [α(bag t)] is the independence number of the subgraph of G induced on the
    bag [bag t] — i.e. a maximum stable subset of [bag t] under G's adjacency.

    The tree-independence number tree-α(G) is the MIN over tree-decompositions T
    of the MAX over bags B of α(G[B]); "tree-α(G) ≤ k" is exactly the existence
    of one tree-decomposition whose every bag has α ≤ k, which is the clean
    corpus encoding (identical to GTMisc.X102's [x102_tree_alpha_at_most]) and
    avoids a literal minimum. *)
Definition x121_tree_alpha_le (G : sgraph) (k : nat) : Prop :=
  exists (T : sgraph) (bag : T -> {set G}),
    is_tree [set: T] /\
    x27_tree_decomposition bag /\
    forall t : T, α(bag t) <= k.

(** ** X121 statements *****************************************************)

(** Corpus row: studies:std_dallard_milani_torgel_conjecture
    Site: none
    Review: none
    English statement: (Dallard, Milanic and Storgel, conjecture)
      For every class C of finite simple graphs the following two properties are equivalent.
      First, C is (treewidth, clique-number)-bounded: there is a single function f from the
      naturals to the naturals such that every graph G in C has treewidth at most f applied to
      the clique number of G.  Second, C has bounded tree-independence number: there is a
      single natural number k such that every graph G in C has tree-independence number at
      most k.
    Definitions: [x121_omega G] - the clique number of G, i.e. the coq-graph-theory clique
      number taken on the full vertex set (minor-theory/theories/conjectures/X121.v);
      [x121_tree_alpha_le G k] - G admits a tree-decomposition every one of whose bags B has
      independence number at most k, which is exactly "tree-alpha(G) <= k" (same file);
      [x27_treewidth_at_most G m] - G admits a tree-decomposition all of whose bags have at
      most m+1 vertices, i.e. treewidth at most m (minor-theory/theories/conjectures/X27.v);
      [x27_tree_decomposition bag] - every vertex lies in some bag, every edge has both ends in
      a common bag, and the bags containing a fixed vertex form a connected set of the index
      tree (same file).
    Notes: on both sides the existential witness is chosen before the graph is quantified, so
      one f and one k must serve the whole class.  "tree-alpha(G) <= k" is encoded as the
      existence of one decomposition with all bags of independence number at most k, which
      avoids a literal minimum over decompositions and agrees with the minimum-based
      definition.  The class C is an arbitrary predicate on [sgraph]; no hereditary or
      induced-minor-closure assumption is imposed, whereas the literature states the
      conjecture for hereditary classes, so the encoding is at least as strong as the source
      (see meta/STATEMENT_IMPROVEMENTS.md). *)
Definition dallard_milanic_storgel_tw_omega_tree_alpha_statement : Prop :=
  forall C : sgraph -> Prop,
    (exists f : nat -> nat,
       forall G : sgraph, C G -> x27_treewidth_at_most G (f (x121_omega G)))
    <->
    (exists k : nat,
       forall G : sgraph, C G -> x121_tree_alpha_le G k).
