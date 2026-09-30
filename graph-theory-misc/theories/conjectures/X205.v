(** * GTMisc.conjectures.X205 -- v2 distributed list-colouring rounds row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X205 vocabulary ***********************************************)

Definition x205_delta_list_assignment (G : sgraph) :=
  G -> {set 'I_(Delta G).+1}.

Definition x205_valid_delta_lists (G : sgraph) (L : x205_delta_list_assignment G) : Prop :=
  forall v : G, (Delta G).+1 <= #|L v|.

Definition x205_list_colouring_output
    (G : sgraph) (L : x205_delta_list_assignment G) (col : G -> 'I_(Delta G).+1) : Prop :=
  (forall v : G, col v \in L v) /\
  (forall x y : G, x -- y -> col x != col y).

Record x205_randomized_local_algorithm (G : sgraph) (rounds : nat) := {
  x205_seed_space : finType;
  x205_output : x205_seed_space -> x205_delta_list_assignment G -> G -> 'I_(Delta G).+1;
  x205_success :
    forall L : x205_delta_list_assignment G,
      x205_valid_delta_lists L ->
      exists good : pred x205_seed_space,
        @fg_event_at_least_ratio x205_seed_space (fun _ => 1) good 2 3 /\
        forall s : x205_seed_space,
          good s -> x205_list_colouring_output L (x205_output s L)
}.

Definition x205_randomized_distributed_delta_list_colouring_fast
    (G : sgraph) (C : nat) : Prop :=
  exists rounds : nat,
    rounds <= C * (trunc_log 2 #|G|).+1 + C /\
    exists _ : x205_randomized_local_algorithm G rounds, True.

(** ** X205 statements *****************************************************)

(** Corpus row: arxiv:1802.05582#01
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1802.05582__01/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1802.05582__01.json
    English statement: (Aboulker, Bonamy, Bousquet and Esperet 2018, "Distributed coloring in
      sparse graphs with fewer colors", question on randomized list-colouring round complexity)
      There is a constant C such that every finite simple graph G admits a number of rounds at
      most C * (floor(log2 |V(G)|) + 1) + C together with a randomized local algorithm which,
      for every assignment of lists of at least Delta(G)+1 colours to the vertices, succeeds
      with probability at least 2/3 in producing a proper colouring choosing each vertex's
      colour from its own list.
    Definitions: [x205_delta_list_assignment G] - a list of colours per vertex, taken inside
      Delta(G)+1 colours (this file); [x205_valid_delta_lists L] - every list has at least
      Delta(G)+1 colours (this file); [x205_list_colouring_output L col] - col picks each
      vertex's colour from its own list and is proper (this file);
      [x205_randomized_local_algorithm G rounds] - a record with a finite seed space and an
      output map such that, for every valid list assignment, a set of seeds of weight ratio at
      least 2/3 yields a correct colouring (this file);
      [x205_randomized_distributed_delta_list_colouring_fast G C] - such a record exists for
      some round count within the logarithmic bound (this file);
      [fg_event_at_least_ratio] - the exact finite "probability at least num/den" vocabulary,
      cross-multiplied natural weights (GTBase finite_graph.v); [Delta] - maximum degree
      (GTBase); [trunc_log] - MathComp integer logarithm.
    Notes: KNOWN UNFAITHFUL, row leg is blocked (faithfulness audit 2026-07-17,
      meta/BLOCKED_RETARGETING_AUDIT.md).  The subject of the question - the ROUND COMPLEXITY
      of a randomized DISTRIBUTED algorithm, and whether it can avoid a factor polynomial in
      Delta - is not encoded: the [rounds] argument of the record
      [x205_randomized_local_algorithm] is a phantom parameter appearing in the type signature
      and in the bound but in none of the record's fields, so nothing ties the algorithm's
      behaviour to a number of communication rounds and no locality constraint is imposed on
      [x205_output].  Recorded in meta/STATEMENT_IMPROVEMENTS.md. *)
Definition randomized_distributed_delta_list_colouring_no_poly_delta_statement : Prop :=
  exists C : nat,
    forall G : sgraph,
      x205_randomized_distributed_delta_list_colouring_fast G C.
