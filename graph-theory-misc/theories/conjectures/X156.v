(** * GTMisc.conjectures.X156 -- v2 random block-tree diameter row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X156 vocabulary ***********************************************)

Definition x156_two_connected_piece (G : sgraph) (B : {set G}) : Prop :=
  2 <= #|B| /\
  connected B /\
  forall v : G, v \in B -> connected (B :\ v).

Definition x156_block_tree_certificate (G : sgraph) (diam : nat) : Prop :=
  exists (T : sgraph) (block : T -> {set G}) (cut : T -> option G),
    [/\ is_tree [set: T],
        (forall v : G, exists t : T, v \in block t),
        (forall t : T, is_forest (block t) \/ x156_two_connected_piece (block t)),
        (forall t u : T, t -- u ->
          exists x : G, cut t = Some x /\ x \in block t /\ x \in block u) &
        forall t u : T, @graph_dist T t u <= diam].

Definition x156_random_block_stable_model
    (R : nat -> finType) (obs : forall n : nat, R n -> sgraph) : Prop :=
  forall (n : nat) (x : R n), #|obs n x| = n.

Definition x156_random_block_tree_diameter_bound
    (R : nat -> finType) (obs : forall n : nat, R n -> sgraph)
    (f : nat -> nat) : Prop :=
  exists good : forall n : nat, pred (R n),
    @fg_whp R (fun _ _ => 1) good /\
    forall (n : nat) (x : R n),
      good n x -> x156_block_tree_certificate (obs n x) (sqrt_ceil n * f n).

(** ** X156 statements *****************************************************)

(** Corpus row: arxiv:1408.4257#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1408.4257__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1408.4257__00.json
    English statement: (McDiarmid and Scott 2014, "Random graphs from a block-stable class",
      informal conjecture on the diameter bound)
      For every family of finite sets of labelled objects R with an observation map sending an
      object of R n to a graph on n vertices, and for every f such that for all N there is an
      n >= N with f(n) >= N, with high probability the observed graph admits a block-tree
      certificate of diameter at most ceil(sqrt n) * f(n).
    Definitions: [x156_two_connected_piece G B] - B has at least two vertices, is connected and
      stays connected after deleting any one of its vertices (this file);
      [x156_block_tree_certificate G diam] - a tree T with a block map and a cut-vertex map
      such that the blocks cover V(G), each block is a forest or 2-connected, adjacent tree
      nodes share a designated cut vertex, and the tree has diameter at most diam (this file);
      [x156_random_block_stable_model obs] - every object of R n is observed as a graph on
      exactly n vertices (this file); [x156_random_block_tree_diameter_bound obs f] - some
      predicate holds with high probability and forces that certificate (this file);
      [fg_whp] - the exact finite "with high probability" vocabulary, cross-multiplied natural
      weights eventually covering all but a ratio a/b of the total weight (GTBase
      finite_graph.v); [eventually] - holds for all sufficiently large n (GTBase
      asymptotics.v); [sqrt_ceil n] - the least s with n <= s^2 (GTBase asymptotics.v);
      [is_tree], [is_forest], [connected], [graph_dist] - coq-graph-theory / GTBase.
    Notes: KNOWN UNFAITHFUL, row leg is blocked (faithfulness audit 2026-07-17,
      meta/BLOCKED_RETARGETING_AUDIT.md).  The hypothesis on f, "for all N there is an n >= N
      with N <= f n", says that f is UNBOUNDED, whereas the conjecture assumes f TENDS TO
      infinity.  Being the weaker hypothesis, it makes the statement strictly stronger, and in
      fact false: an f that dips to 0 at infinitely many n still satisfies it, forcing
      certificate diameter 0 at those n, which the cofinite [eventually] inside [fg_whp] cannot
      accommodate.  Further modelling choices: the random model is any weighted family of
      finite labelled objects rather than the block-stable class of the paper, and all weights
      are 1 here, so "with high probability" is uniform counting.  Recorded in
      meta/STATEMENT_IMPROVEMENTS.md. *)
Definition block_tree_diameter_bound_improvement_statement : Prop :=
  forall (R : nat -> finType) (obs : forall n : nat, R n -> sgraph) (f : nat -> nat),
    x156_random_block_stable_model obs ->
    (forall N : nat, exists n : nat, N <= n /\ N <= f n) ->
    x156_random_block_tree_diameter_bound obs f.
