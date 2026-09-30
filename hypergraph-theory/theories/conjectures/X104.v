(** * Hypergraph.conjectures.X104 -- v2 Brown-Erdos-Sos row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X104 vocabulary ***********************************************)

Definition x104_uniform (T : finType) (E : {set {set T}}) (r : nat) : Prop :=
  forall e : {set T}, e \in E -> #|e| = r.

Definition x104_span (T : finType) (F : {set {set T}}) : {set T} :=
  [set v : T | [exists e : {set T}, (e \in F) && (v \in e)]].

Definition x104_brown_erdos_sos_free
    (T : finType) (E : {set {set T}}) (e : nat) : Prop :=
  forall F : {set {set T}},
    F \subset E ->
    #|F| = e ->
    e + 3 < #|x104_span F|.

(** ** X104 statements *****************************************************)

(** Corpus row: studies:std_brown_erd_s_s_s_conjecture
    Site: none
    Review: none
    English statement: (Brown, Erdos and Sos, conjecture)
      For every fixed e at least 3 the extremal number f(n, e+3, e) is o(n^2): for every
      positive rational epsilon there is a threshold N such that every 3-uniform hypergraph on
      at least N vertices in which no e hyperedges span at most e+3 vertices has at most epsilon
      times the square of its number of vertices hyperedges.
    Definitions: [x104_uniform E r] - every hyperedge has exactly r vertices
      (hypergraph-theory/theories/conjectures/X104.v); [x104_span F] - the set of vertices
      covered by the subfamily F (same file); [x104_brown_erdos_sos_free E e] - every subfamily
      of exactly e hyperedges spans more than e+3 vertices, i.e. E contains no e hyperedges on
      at most e+3 vertices (same file).
    Notes: f(n, e+3, e) is the maximum number of hyperedges of a 3-uniform hypergraph on n
      vertices containing no e hyperedges spanning at most e+3 vertices; rather than forming
      that maximum, the bound is asserted for every qualifying hypergraph, which is equivalent.
      "o(n^2)" is the standard finite reading: for every positive rational eps_num/eps_den the
      bound holds for all large enough n, cross-multiplied as
      eps_den * #|E| <= eps_num * #|T|^2.  Note the threshold N is chosen after the epsilon
      and before the hypergraph. *)
Definition brown_erdos_sos_three_uniform_statement : Prop :=
  forall e eps_num eps_den : nat,
    3 <= e ->
    0 < eps_num ->
    0 < eps_den ->
    exists N : nat,
      forall (T : finType) (E : {set {set T}}),
        N <= #|T| ->
        x104_uniform E 3 ->
        x104_brown_erdos_sos_free E e ->
        eps_den * #|E| <= eps_num * (#|T| ^ 2).
