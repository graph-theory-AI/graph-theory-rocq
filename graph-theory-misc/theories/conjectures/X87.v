(** * GTMisc.conjectures.X87 -- v2 ordered-graph speed-gap row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X87 vocabulary ************************************************)

Definition x87_edge_fun (n : nat) := {ffun 'I_n * 'I_n -> bool}.

Definition x87_edge (n : nat) (E : x87_edge_fun n) (i j : 'I_n) : bool :=
  E (i, j).

Definition x87_sgraph_edge (n : nat) (E : x87_edge_fun n) : bool :=
  [forall i : 'I_n, ~~ x87_edge E i i] &&
  [forall i : 'I_n, [forall j : 'I_n, x87_edge E i j == x87_edge E j i]].

Definition x87_ordered_class := forall n : nat, x87_edge_fun n -> bool.

Definition x87_order_preserving (m n : nat) (f : 'I_m -> 'I_n) : Prop :=
  forall i j : 'I_m, (i < j)%N -> (f i < f j)%N.

Definition x87_induced_edge
    (m n : nat) (E : x87_edge_fun n) (f : 'I_m -> 'I_n)
    : x87_edge_fun m :=
  [ffun p : 'I_m * 'I_m => x87_edge E (f p.1) (f p.2)].

Definition x87_hereditary (C : x87_ordered_class) : Prop :=
  forall (m n : nat) (E : x87_edge_fun n) (f : 'I_m -> 'I_n),
    injective f ->
    x87_order_preserving f ->
    C n E ->
    C m (x87_induced_edge E f).

Definition x87_speed (C : x87_ordered_class) (n : nat) : nat :=
  #|[set E : x87_edge_fun n | x87_sgraph_edge E && C n E]|.

Definition x87_is_hereditary_ordered_graph_speed (speed : nat -> nat) : Prop :=
  exists C : x87_ordered_class,
    x87_hereditary C /\ forall n : nat, speed n = x87_speed C n.

Definition x87_at_most_exponential (speed : nat -> nat) : Prop :=
  exists c N : nat, forall n : nat, N <= n -> speed n <= 2 ^ (c * n).

Definition x87_at_least_half_factorial (speed : nat -> nat) : Prop :=
  forall q : nat,
    3 <= q ->
    exists N : nat,
      forall n : nat,
        N <= n ->
        n ^ ((n * (q - 2)) %/ (2 * q)) <= speed n.

(** ** X87 statements ******************************************************)

(** Corpus row: studies:std_balogh_bollob_s_morris_conjecture_speed_gap_for
    Site: none
    Review: none
    English statement: (Balogh, Bollobas and Morris, speed-gap conjecture for ordered graphs)
      For every function speed that counts, for each n, the graphs on the ordered vertex set
      {0, ..., n-1} belonging to some hereditary class of ordered graphs, either speed(n) is
      eventually at most 2^(c*n) for some constant c, or for every q >= 3 it is eventually at
      least n^(n*(q-2)/(2q)); that is, the speed is either at most 2^O(n) or at least
      n^(n/2+o(n)).
    Definitions: [x87_edge_fun n] - a boolean adjacency table on the ordered vertex set of size
      n (this file); [x87_sgraph_edge E] - E is irreflexive and symmetric, i.e. a simple graph
      (this file); [x87_ordered_class] - a class given by a predicate at every size (this
      file); [x87_order_preserving f] - f is strictly increasing (this file);
      [x87_induced_edge E f] - the ordered induced subgraph along f (this file);
      [x87_hereditary C] - C is closed under order-preserving injective induced subgraphs (this
      file); [x87_speed C n] - the number of simple ordered graphs of size n in C (this file);
      [x87_is_hereditary_ordered_graph_speed speed] - speed is the speed of some hereditary
      ordered class (this file); [x87_at_most_exponential], [x87_at_least_half_factorial] - the
      two branches above (this file).
    Notes: ordered graphs are represented on the canonical ordered vertex set of size n, so
      counting labelled adjacency tables in the class counts ordered isomorphism types by their
      unique increasing relabelling - which is why no quotient is needed.  The lower branch
      n^(n/2+o(n)) is rendered in the rational-epsilon form: for each q >= 3, eventually
      n^(n*(q-2) div (2q)) <= speed(n), the exponent being an integer division. *)
Definition hereditary_ordered_graph_speed_gap_statement : Prop :=
  forall speed : nat -> nat,
    x87_is_hereditary_ordered_graph_speed speed ->
    x87_at_most_exponential speed \/ x87_at_least_half_factorial speed.
