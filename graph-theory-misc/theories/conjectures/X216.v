(** * GTMisc.conjectures.X216 -- Bondy-Murty complexity rows (wave X216, 2026-09-23) *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local x216 vocabulary ***********************************************)

(** *** Instances of the "second Hamilton cycle" search problem *)

(** An instance: a graph together with a cyclic vertex sequence. *)
Definition x216_cycle_instance : Type := {G : sgraph & seq G}.

(** The (unordered) edge set traversed by a cyclic vertex sequence: the pairs of
    consecutive vertices, including the closing pair.  Two Hamilton cycles are THE SAME
    cycle exactly when they traverse the same edges, so "a SECOND Hamilton cycle" is a
    Hamilton cycle with a different edge set (not merely a different vertex sequence:
    rotations and the reversal of a cycle are different sequences). *)
Definition x216_cycle_edges (G : sgraph) (c : seq G) : {set {set G}} :=
  [set e : {set G} | e \in [seq [set p.1; p.2] | p <- zip c (rot 1 c)]].

(** The vertices of a sequence, read as indices of the vertex enumeration. *)
Definition x216_enc_seq (G : sgraph) (c : seq G) : data :=
  enc_list [seq enc_nat (enum_rank v) | v <- c].

(** The encoded instance: adjacency matrix of the graph, paired with the given cycle. *)
Definition x216_enc_cycle_instance (x : x216_cycle_instance) : data :=
  Dpair (enc_graph (projT1 x)) (x216_enc_seq (projT2 x)).

(** Admissible instances: a cubic graph with a distinguished Hamilton cycle. *)
Definition x216_cubic_hamiltonian_instance (x : x216_cycle_instance) : Prop :=
  regular (projT1 x) 3 /\ hamiltonian_cycle (projT1 x) (projT2 x).

(** A correct output: the encoding of a Hamilton cycle other than the given one. *)
Definition x216_second_hamilton_output (x : x216_cycle_instance) (out : data) : Prop :=
  exists c' : seq (projT1 x),
    [/\ hamiltonian_cycle (projT1 x) c',
        x216_cycle_edges c' != x216_cycle_edges (projT2 x) &
        out = x216_enc_seq c'].

(** *** Internally disjoint odd paths, and a co-NP layer *)

(** An instance of the decision problem: a graph and two distinguished vertex sets. *)
Definition x216_paths_instance : Type := {G : sgraph & ({set G} * {set G})%type}.

Definition x216_enc_set (G : sgraph) (S : {set G}) : data :=
  enc_list [seq enc_bool (v \in S) | v <- enum G].

Definition x216_enc_paths_instance (x : x216_paths_instance) : data :=
  Dpair (enc_graph (projT1 x))
        (Dpair (x216_enc_set (projT2 x).1) (x216_enc_set (projT2 x).2)).

(** An (X,Y)-path of ODD length: a nonempty sequence of distinct vertices, consecutive
    ones adjacent, starting in X, ending in Y, with an odd number of edges. *)
Definition x216_odd_xy_path (G : sgraph) (X Y : {set G}) (p : seq G) : bool :=
  match p with
  | [::] => false
  | x :: q => [&& path (--) x q, uniq (x :: q), x \in X, last x q \in Y & odd (size q)]
  end.

(** The INTERNAL vertices of a path: all but its two endpoints. *)
Definition x216_internal (G : sgraph) (p : seq G) : {set G} :=
  match p with
  | [::] => set0
  | x :: q => [set v : G | v \in behead (belast x q)]
  end.

(** [k] internally disjoint (X,Y)-paths of odd length. *)
Definition x216_odd_disjoint_paths (G : sgraph) (X Y : {set G}) (k : nat) : Prop :=
  exists f : 'I_k -> seq G,
    (forall i : 'I_k, x216_odd_xy_path X Y (f i)) /\
    (forall i j : 'I_k, i != j ->
       [disjoint x216_internal (f i) & x216_internal (f j)]).

(** The decision predicate of the row, read off an encoded instance (k = |X|). *)
Definition x216_odd_paths_predicate (x : x216_paths_instance) : Prop :=
  x216_odd_disjoint_paths (projT2 x).1 (projT2 x).2 #|(projT2 x).1|.

(** Membership in co-NP in the cost-coupled model of [GTBase.complexity]: one program
    [p] with polynomially bounded step count, and one polynomial certificate-size bound,
    such that an instance is a NO-instance exactly when some short certificate makes [p]
    accept the pair (instance, certificate). *)
Definition x216_in_coNP (T : Type) (enc : T -> data) (P : T -> Prop) : Prop :=
  exists (p : prog) (c k : nat),
    poly_cost_on (fun xw : T * data => Dpair (enc xw.1) xw.2) p /\
    forall x : T,
      ~ P x <->
      exists w : data,
        dsize w <= c * (dsize (enc x)) ^ k + c /\ prun p (Dpair (enc x) w) = Dnat 1.

(** ** X216 statements *****************************************************)

(** Corpus row: bm:bm-021
    Site: https://graph-theory-ai.github.io/graph-conjectures/bm/bm-021/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/bondy_murty_reviews/bm-021.json
    English statement: (Bondy and Murty, Graph Theory, Appendix A, unsolved problem 21;
      the algorithmic form of Smith's theorem, after Thomason)
      There is a program whose step count is bounded by a polynomial in the size of its
      input and which, on the encoding of every pair consisting of a cubic graph and a
      Hamilton cycle of it, outputs the encoding of a Hamilton cycle of the same graph
      whose edge set differs from that of the given one.
    Definitions: [x216_cycle_instance] - a graph together with a cyclic vertex sequence
      (this file); [x216_cycle_edges c] - the unordered pairs of consecutive vertices of
      the sequence, its closing pair included (this file); [x216_enc_seq] /
      [x216_enc_cycle_instance] - the instance encoding, adjacency matrix of the graph
      paired with the list of vertex indices of the cycle (this file);
      [x216_cubic_hamiltonian_instance] - the graph is 3-regular and the sequence is one
      of its Hamilton cycles (this file); [x216_second_hamilton_output x out] - the output
      encodes a Hamilton cycle of the instance graph with a different edge set (this
      file); [polytime_outputs_on_class enc Class Spec] - some [prog] with polynomially
      bounded step count meets Spec on every encoded instance of Class (GTBase
      complexity.v); [poly_cost_on], [prun], [pcost], [enc_graph], [enc_list], [enc_nat]
      (same file); [regular G 3] - 3-regular, i.e. cubic (GTBase base.v);
      [hamiltonian_cycle] (GTBase common.v).
    Notes: BLOCKED.  The row asks "Is this problem in P?", i.e. it asks for a VERDICT
      about a SEARCH problem, and the body above is only the positive answer to it, in
      one particular cost-coupled model.  Two blockers, both recorded by the plan and by
      the 2026-07-17 blocked-retargeting audit, which rejected the finite-witness
      encodings of this family:
      (1) COMPUTATION MODEL.  [GTBase.complexity] fixes ONE interpreter and ONE program
      class; "the problem is in P" is a statement about a model of computation, and a
      positive answer in this particular [prog] class is neither known to be equivalent
      to, nor a faithful rendering of, membership in P.  The cost is measured in steps of
      that interpreter over the [data] encoding chosen here, and the polynomial is in
      [dsize] of that encoding rather than in the number of vertices.
      (2) SEARCH VS DECISION.  The row is a search problem (output a second cycle); the
      quantifier structure above ("some program, for every instance of the class, the
      output satisfies the spec") is the natural reading, but the source's question also
      admits the functional-problem-in-FP and the promise-problem readings, which differ.
      By Smith's theorem a second Hamilton cycle always exists, so the specification is
      never vacuous on the class, but the statement as written is at best the "in FP"
      reading of an open question about complexity classes, and the corpus leg therefore
      stays blocked. *)
Definition second_hamilton_cycle_cubic_polytime_statement : Prop :=
  polytime_outputs_on_class x216_enc_cycle_instance
    x216_cubic_hamiltonian_instance x216_second_hamilton_output.

(** Corpus row: bm:bm-022
    Site: https://graph-theory-ai.github.io/graph-conjectures/bm/bm-022/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/bondy_murty_reviews/bm-022.json
    English statement: (Bondy and Murty, Graph Theory, Appendix A, unsolved problem 22;
      after Thomassen 1980)
      There is a program whose step count is bounded by a polynomial in the size of its
      input, together with a polynomial bound on certificate sizes, such that for every
      graph G and every pair of vertex sets X and Y of G the following are equivalent:
      G has NO family of |X| internally disjoint paths of odd length, each running from a
      vertex of X to a vertex of Y; and there is a certificate of size within the bound on
      which the program accepts the pair formed by the encoded instance and that
      certificate.
    Definitions: [x216_paths_instance] - a graph with two distinguished vertex sets (this
      file); [x216_enc_set], [x216_enc_paths_instance] - the instance encoding (this
      file); [x216_odd_xy_path X Y p] - p is a sequence of distinct vertices, consecutive
      ones adjacent, first in X, last in Y, with an odd number of edges (this file);
      [x216_internal p] - the vertices of p other than its two endpoints (this file);
      [x216_odd_disjoint_paths X Y k] - a family of k such paths with pairwise disjoint
      internal vertex sets (this file); [x216_odd_paths_predicate] - that property with
      k = |X| (this file); [x216_in_coNP enc P] - the complement of P has polynomially
      bounded certificates checked by one polynomially bounded program of the cost-coupled
      model (this file); [prog], [prun], [pcost], [poly_cost_on], [dsize], [enc_graph],
      [enc_bool], [enc_list] (GTBase complexity.v).
    Notes: BLOCKED.  The row asks "Is this problem in co-NP?", and the body above is only
      the positive answer, in one particular model.  Blockers:
      (1) CERTIFICATE / COMPLEXITY-CLASS LAYER.  [GTBase.complexity] has no certificate
      layer; [x216_in_coNP] is a local, ad hoc rendering of "the complement is in NP" in
      the fixed [prog] model, and the 2026-07-17 audit machine-confirmed that the earlier
      GTMisc [in_NP]/[NP_hard] layer was DECOUPLED (satisfiable by a cost function
      [fun _ => 0]).  The local definition here couples cost and correctness to the same
      program, but it is still a statement about a bespoke model, not about co-NP.
      (2) THE INSTANCE PARAMETER k.  The source takes k to be part of the input, with X
      and Y k-subsets; the encoding above recovers k as |X| and does not record the
      promise |X| = |Y|, so instances with |X| <> |Y| are inside the quantifier.
      (3) INTERNAL DISJOINTNESS.  "Internally disjoint" is rendered as pairwise disjoint
      INTERNAL vertex sets, which permits two paths to share an endpoint and permits two
      paths with the same pair of endpoints; the source's linkage reading (distinct
      endpoints, one per vertex of X and of Y) is a different, stronger family.
      (4) Second reader, 2026-09-23: a fourth mismatch, not in the list above --
      [x216_odd_xy_path] requires only that the FIRST vertex lie in X and the LAST in
      Y; it does not require the path to meet X only in its first vertex and Y only in
      its last, which is part of the standard reading of "(X,Y)-path".  Internal
      vertices may therefore lie in X or in Y.  Any of these four points can change the
      truth value of the statement, so the corpus leg stays blocked. *)
Definition internally_disjoint_odd_paths_conp_statement : Prop :=
  x216_in_coNP x216_enc_paths_instance x216_odd_paths_predicate.
