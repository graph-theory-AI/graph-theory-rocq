(** * Hypergraph.conjectures.X209 -- v2 hypergraph cut excess row *)

From GTBase Require Export base.
From GTBase Require Import hypergraph_uniformity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X209 vocabulary ***********************************************)

Definition x209_uniform (T : finType) (E : {set {set T}}) (k : nat) : Prop :=
  uniform_family E k.

Definition x209_cut_edge
    (T : finType) (r : nat) (col : T -> 'I_r) (e : {set T}) : bool :=
  ~~ monochromatic_on col e.

Definition x209_cut_size
    (T : finType) (E : {set {set T}}) (r : nat) (col : T -> 'I_r) : nat :=
  non_monochromatic_count E col.

Definition x209_is_max_r_cut
    (T : finType) (E : {set {set T}}) (r c : nat) : Prop :=
  exists col : T -> 'I_r,
    x209_cut_size E col = c /\
    forall col' : T -> 'I_r, x209_cut_size E col' <= c.

(** Scale the excess by [r^(k-1)] to avoid rationals:
    [den * maxcut - (den - 1) * m], where [den = r^(k-1)]. *)
Definition x209_expected_den (r k : nat) : nat := r ^ k.-1.

Definition x209_scaled_excess
    (T : finType) (E : {set {set T}}) (r k x : nat) : Prop :=
  exists c : nat,
    x209_is_max_r_cut E r c /\
    x = x209_expected_den r k * c - (x209_expected_den r k).-1 * #|E|.

Definition x209_is_min_scaled_excess (r k m x : nat) : Prop :=
  exists (T : finType) (E : {set {set T}}),
    [/\ x209_uniform E k, #|E| = m, x209_scaled_excess E r k x &
        forall (T' : finType) (E' : {set {set T}}) (y : nat),
          x209_uniform E' k ->
          #|E'| = m ->
          x209_scaled_excess E' r k y ->
          x <= y].

(** The source's r-cut (re-encoding of 2026-10-26).  The helpers above (non-monochromatic
    edges, the baseline 1 - r^(1-k), a minimum over one vertex type) stay for the frozen
    migration chains; the statement uses the ones below. *)

(** An edge is multicoloured when it meets every one of the [r] colour classes. *)
Definition x209_multicoloured
    (T : finType) (r : nat) (col : T -> 'I_r) (e : {set T}) : bool :=
  [forall i : 'I_r, [exists v in e, col v == i]].

Definition x209_mc_cut_size
    (T : finType) (E : {set {set T}}) (r : nat) (col : T -> 'I_r) : nat :=
  #|[set e in E | x209_multicoloured col e]|.

Definition x209_is_max_mc_cut
    (T : finType) (E : {set {set T}}) (r c : nat) : Prop :=
  exists col : T -> 'I_r,
    x209_mc_cut_size E col = c /\
    forall col' : T -> 'I_r, x209_mc_cut_size E col' <= c.

(** Stirling numbers of the second kind: the partitions of a k-set into r nonempty blocks. *)
Fixpoint x209_stirling2 (k r : nat) : nat :=
  match k, r with
  | 0, 0 => 1
  | 0, _.+1 => 0
  | _.+1, 0 => 0
  | k'.+1, r'.+1 => r'.+1 * x209_stirling2 k' r'.+1 + x209_stirling2 k' r'
  end.

(** Sanity: S(k, r) r! counts the maps from a k-set onto an r-set. *)
Lemma x209_stirling2_3_2 : x209_stirling2 3 2 * 2`! = 6.
Proof. by []. Qed.

Lemma x209_stirling2_3_3 : x209_stirling2 3 3 * 3`! = 6.
Proof. by []. Qed.

Lemma x209_stirling2_2_3 : x209_stirling2 2 3 = 0.
Proof. by []. Qed.

Lemma x209_stirling2_k_1 (k : nat) : 0 < k -> x209_stirling2 k 1 = 1.
Proof.
case: k => // k _; elim: k => // k IH.
by rewrite /=; rewrite /= in IH; rewrite IH.
Qed.

(** The source's remark S(k,2) 2!/2^k = 1 - 2^(1-k). *)
Lemma x209_stirling2_k_2 (k : nat) : 0 < k -> x209_stirling2 k 2 * 2`! + 2 = 2 ^ k.
Proof.
case: k => // k _; elim: k => // k IH.
have e : x209_stirling2 k.+2 2 = 2 * x209_stirling2 k.+1 2 + x209_stirling2 k.+1 1 by [].
rewrite e (x209_stirling2_k_1 (ltn0Sn k)) expnS -IH (_ : 2`! = 2) //.
set s := x209_stirling2 _ _.
by rewrite mulnDl mulnDr mul1n -mulnA (mulnC s 2) -addnA.
Qed.

(** The excess of a maximum r-cut over the expected size S(k,r) r!/r^k m of a uniformly
    random r-cut, scaled by [r^k] to stay in the naturals. *)
Definition x209_mc_scaled_excess
    (T : finType) (E : {set {set T}}) (r k x : nat) : Prop :=
  exists c : nat,
    x209_is_max_mc_cut E r c /\
    x = r ^ k * c - x209_stirling2 k r * r`! * #|E|.

(** The least scaled excess over every k-uniform hypergraph with m edges, on any vertex type. *)
Definition x209_is_min_mc_scaled_excess (r k m x : nat) : Prop :=
  exists (T : finType) (E : {set {set T}}),
    [/\ x209_uniform E k, #|E| = m, x209_mc_scaled_excess E r k x &
        forall (T' : finType) (E' : {set {set T'}}) (y : nat),
          x209_uniform E' k ->
          #|E'| = m ->
          x209_mc_scaled_excess E' r k y ->
          x <= y].

(** ** X209 statements *****************************************************)

(** Corpus row: arxiv:1803.08462#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1803.08462__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1803.08462__00.json
    English statement: (Conlon, Fox, Kwan and Sudakov 2019, second plausible conjecture of
      "Hypergraph cuts above the average"; disproved in the same paper)
      For all fixed r and k with 2 <= r <= k, the smallest maximum r-cut over all k-uniform
      hypergraphs with m hyperedges has excess of order exactly the square root of m, where an
      r-cut colours the vertices with r colours, its size is the number of hyperedges meeting
      every colour, and its excess is that size minus S(k,r) r!/r^k times m, the expected size
      of a uniformly random r-cut.
    Definitions: [x209_uniform E k] - every hyperedge has exactly k vertices (this file);
      [x209_multicoloured col e] - the hyperedge e meets every one of the r colour classes
      (this file); [x209_mc_cut_size E col] - the number of multicoloured hyperedges (this
      file); [x209_is_max_mc_cut E r c] - c is the largest such size over all colourings with
      r colours (this file); [x209_stirling2 k r] - the Stirling number of the second kind
      S(k, r), by its recursion (this file); [x209_mc_scaled_excess E r k x] - x is r^k times
      the maximum r-cut minus S(k,r) r! times the number of hyperedges, the excess over the
      random r-cut scaled to stay in the naturals (this file); [x209_is_min_mc_scaled_excess r
      k m x] - x is the least such scaled excess over every k-uniform hypergraph with m
      hyperedges, on any vertex type (this file); [big_Theta_nat f g] - f is bounded above and
      below by constant multiples of g (base/theories/asymptotics.v).
    Notes: the excess is scaled by the fixed factor r^k, which does not change the Theta order
      for fixed r and k, and the square-root envelope is expressed as excess(m)^2 = Theta(m).
      RE-ENCODED 2026-10-26 (coordination/PROGRAMME.md A2 with the A4 direction re-encode;
      record meta/STATEMENT_IMPROVEMENTS.md; the row is frozen by the A9 cut_size and D1
      uniform_hypergraph families).  Two defects of the earlier encoding: (1) its minimum
      [x209_is_min_scaled_excess] typed E' over the outer witness type T (T' unused), so it
      ranged over the hypergraphs on one vertex type (faithfulness audit 2026-07-17,
      meta/BLOCKED_RETARGETING_AUDIT.md); (2) its cut counted the non-monochromatic hyperedges
      with the baseline 1 - r^(1-k), while the source (arXiv:1803.08462, e-print sha256
      572e09cb, hypergraph-max-cut.tex lines 188-190 and 291-305) counts the hyperedges with a
      vertex from every part, with the baseline S(k,r) r!/r^k; the two agree only for r = 2.
      The earlier helpers stay unchanged for the frozen migration chains.  The source's own
      Theorem 1.2 (label thm:nontrivial: for 2 <= r <= k with r >= 3 or k >= 4, every m-edge
      k-graph has an r-cut with excess Omega(m^(5/9))) refutes the conjecture, as the corpus
      status records. *)
Definition hypergraph_cut_excess_theta_sqrt_statement : Prop :=
  forall r k : nat,
    2 <= r ->
    r <= k ->
    exists excess : nat -> nat,
      (forall m : nat, x209_is_min_mc_scaled_excess r k m (excess m)) /\
      big_Theta_nat (fun m => (excess m) ^ 2) (fun m => m).
