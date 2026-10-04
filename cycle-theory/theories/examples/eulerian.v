(** Downstream use of the public Eulerian API of [Cycle.foundations], without
    conjecture imports: the projections and the introduction rule of
    [eulerian], the Boolean form of its degree conjunct, and the recorded
    corner cases (the empty multigraph, an isolated vertex, loops, two parallel
    arcs pointing the same way; a single edge, two isolated vertices and a loop
    beside an isolated vertex).  Degrees count arc ends; no nonempty, loopless
    or tour premise is assumed. *)
From GraphTheory Require Import mgraph.
From GTBase Require Import base.
From Cycle.foundations Require Import connectivity eulerian.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Example projections (G : mgraph) (e : eulerian G) :
  mconnected G /\ forall v : G, ~~ odd (mdeg v).
Proof. by split; [exact: eulerian_mconnected e | exact: eulerian_even_degrees e]. Qed.

Example introduction (G : mgraph) :
  mconnected G -> (forall v : G, ~~ odd (mdeg v)) -> eulerian G.
Proof. exact: eulerianI. Qed.

Example boolean_degree_conjunct (G : mgraph) :
  eulerian G -> [forall v : G, ~~ odd (mdeg v)].
Proof. exact: eulerian_even_degreesb. Qed.

Example reflected_degree_conjunct (G : mgraph) :
  reflect (forall v : G, ~~ odd (mdeg v)) (even_degreesb G).
Proof. exact: even_degreesP. Qed.

Example the_empty_multigraph_is_eulerian : eulerian empty_mgraph := eulerian_empty.

Example an_isolated_vertex_is_eulerian : eulerian isolated_vertex := eulerian_isolated_vertex.

Example a_loop_is_eulerian : eulerian one_loop := eulerian_one_loop.

Example two_loops_are_eulerian : eulerian two_loops := eulerian_two_loops.

Example two_parallel_arcs_pointing_the_same_way : eulerian parallel_pair := eulerian_parallel_pair.

Example a_single_edge_is_not_eulerian : ~ eulerian one_edge := not_eulerian_one_edge.

Example two_isolated_vertices_are_not_eulerian : ~ eulerian two_vertices := not_eulerian_two_vertices.

Example even_but_disconnected :
  even_degrees loop_and_vertex /\ ~ eulerian loop_and_vertex.
Proof. by split; [exact: even_degrees_loop_and_vertex | exact: not_eulerian_loop_and_vertex]. Qed.
