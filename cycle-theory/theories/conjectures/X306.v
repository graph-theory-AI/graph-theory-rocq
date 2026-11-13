(** * Cycle.conjectures.X306 -- v2 row: the Jaeger-Linial-Payan-Tarsi conjecture, every 5-edge-connected graph is
      Z_3-connected (record arXiv:2205.07498) *)

(** CARRIER: an undirected MULTIGRAPH, coq-graph-theory's [mgraph], the carrier of the flow rows of [D1.v] and of
    [X228.v]; each edge carries one arc whose [source]/[target] split is a reference orientation without content
    (the carrier convention of [Cycle.foundations.connectivity]).  IMPORT ORDER: [mgraph] before [base], the mathcomp
    algebra layer after [base] (the order of [D1.v] and [X228.v]). *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import mgraph.
From GTBase Require Import base.
From Cycle.foundations Require Import connectivity.
From mathcomp Require Import all_algebra.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X306 vocabulary *****************************************************)

(** G is Z_3-connected (Jaeger, Linial, Payan and Tarsi; as Dvorak and Mohar define it, arXiv:2205.07498v3,
    flowcrit.tex l.80-89 and l.190-191): for every Z_3-boundary [beta], a map from the vertices to Z_3 with zero
    sum, there is a nowhere-zero Z_3-flow [f] with boundary [beta]: at every vertex v, the sum of [f] over the edges
    leaving v minus the sum over the edges entering v is [beta v].  The source's antisymmetric function on the
    symmetric orientation is [f] on the reference orientation ([f e] on the arc from [source e] to [target e], its
    negative on the reverse arc), so reversing an edge negates its value and the notion does not depend on the
    reference orientation.  A loop at v adds [f e] to both sums at v and cancels.  The source asks for a zero sum on
    each component; one total sum is the same condition on a connected graph, the only graphs X306 quantifies
    ([jlpt_z3_connectivity_statement]'s Notes). *)
Definition x306_z3_connected (G : mgraph) : Prop :=
  forall beta : G -> 'Z_3, (\sum_(v : G) beta v = 0)%R ->
    exists f : edge G -> 'Z_3,
      (forall e : edge G, f e != 0%R) /\
      (forall v : G, (\sum_(e | source e == v) f e - \sum_(e | target e == v) f e)%R = beta v).

(** ** X306 statement ******************************************************)

(** Corpus row: studies:std_jaeger_linial_payan_tarsi_z_connectivity_conject
    Site: none
    Review: none
    English statement: (Jaeger, Linial, Payan and Tarsi; studies slice of the corpus, record arXiv:2205.07498)
      Every 5-edge-connected graph is Z_3-connected.
    Definitions: [edge_connected G k] - deleting any edge set of size less than k leaves every pair of vertices
      joined by a walk (cycle-theory/theories/foundations/connectivity.v); [x306_z3_connected G] - for every map
      beta from the vertices to Z_3 with zero sum, some map f from the edges to Z_3 that is never 0 has, at every
      vertex v, the sum of f over the edges leaving v minus the sum over the edges entering v equal to beta v
      (X306.v); 'Z_3 - the integers modulo 3 (mathcomp), the group Z_3.
    Notes: encoded as stated, with the record's definitions.  The record (Dvorak and Mohar, arXiv:2205.07498v3,
      flowcrit.tex l.196-198, Conjecture 1.8) states it in the pinned words and attributes it to Jaeger, Linial,
      Payan and Tarsi (JCTB 56, 1992).  Graphs have parallel edges and no loops (l.79); mgraph also allows loops,
      which change nothing: a loop cancels in both sums at its vertex and takes any nonzero value, and no walk needs
      one, so a multigraph satisfies the hypothesis, and the conclusion, iff its loopless part does (D1.v's
      convention for three_flow_statement).  The source's boundaries have zero sum on every component (l.80-81);
      edge_connected G 5 applied to the empty edge set makes G connected, so one total sum is the same condition
      here.  k-edge-connected is the standard notion (the source does not define it), the one D1.v uses.  No guard:
      a graph with no vertex or with one vertex is Z_3-connected (the empty flow; the value 1 on every loop), and an
      edgeless graph with two or more vertices is not 5-edge-connected, so no small graph needs excluding (D1.v's
      guard 0 < #|edge G| is the 3-flow row's wording, absent here).  Open: the record proves it for planar and
      projective-planar graphs and for graphs made planar by deleting at most three edges (l.200-207); Lovasz,
      Thomassen, Wu and Zhang proved Z_3-connectivity for 6-edge-connected graphs (l.192-193).  It implies Tutte's
      3-flow conjecture (D1.v's three_flow_statement) through Kochol's reduction to 5-edge-connected graphs
      (l.200-201); that implication is not encoded here. *)
Definition jlpt_z3_connectivity_statement : Prop :=
  forall G : mgraph, edge_connected G 5 -> x306_z3_connected G.
