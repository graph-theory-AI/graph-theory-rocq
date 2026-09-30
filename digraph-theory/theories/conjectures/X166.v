(** * Digraph.conjectures.X166 -- v2 disjoint paths NP-completeness row *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph.
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X166 vocabulary ***********************************************)

Definition x166_stable_set (D : diGraphType) (S : {set D}) : Prop :=
  forall x y : D,
    x \in S -> y \in S -> x != y -> ~~ (x --> y) /\ ~~ (y --> x).

Definition x166_stability_number_two (D : diGraphType) : Prop :=
  (exists S : {set D}, x166_stable_set S /\ #|S| = 2) /\
  forall S : {set D}, x166_stable_set S -> #|S| <= 2.

Definition x166_instance (k : nat) := {D : diGraphType & 'I_k -> (D * D)%type}.

Definition x166_enc_digraph (D : diGraphType) : data :=
  enc_list [seq enc_list [seq enc_bool (i --> j) | j <- enum D] | i <- enum D].

Definition x166_enc_instance (k : nat) (I : x166_instance k) : data :=
  x166_enc_digraph (projT1 I).

Definition x166_directed_path (D : diGraphType) (s t : D) (p : seq D) : Prop :=
  path (fun x y => x --> y) s p /\ last s p = t /\ uniq (s :: p).

Definition x166_internals (D : diGraphType) (s t : D) (p : seq D) : {set D} :=
  [set x : D | (x \in p) && (x != t)].

Definition x166_vertex_disjoint_directed_paths (k : nat) (I : x166_instance k) : Prop :=
  let D := projT1 I in
  let pairs := projT2 I in
  exists paths : forall i : 'I_k, seq D,
    (forall i : 'I_k, x166_directed_path (pairs i).1 (pairs i).2 (paths i)) /\
    forall i j : 'I_k, i != j ->
      x166_internals (pairs i).1 (pairs i).2 (paths i) :&:
      x166_internals (pairs j).1 (pairs j).2 (paths j) = set0.

Definition x166_in_np (k : nat) (P : x166_instance k -> Prop) : Prop :=
  exists cert_enc : x166_instance k -> data -> Prop,
    polytime_decides_on_class (@x166_enc_instance k)
      (fun _ => True) (fun I => exists c : data, cert_enc I c /\ P I).

Definition x166_np_hard (k : nat) (P : x166_instance k -> Prop) : Prop :=
  forall Q : x166_instance k -> Prop,
    @x166_in_np k Q ->
    exists red : prog,
      poly_cost_on (@x166_enc_instance k) red /\
      forall I : x166_instance k,
        prun red (@x166_enc_instance k I) = @x166_enc_instance k I /\ (Q I -> P I).

Definition x166_k_disjoint_paths_NP_complete_on_stability_two (k : nat) : Prop :=
  2 <= k /\
  @x166_in_np k (@x166_vertex_disjoint_directed_paths k) /\
  @x166_np_hard k (@x166_vertex_disjoint_directed_paths k) /\
  (forall I : x166_instance k,
    x166_stability_number_two (projT1 I) ->
    @x166_vertex_disjoint_directed_paths k I \/ ~ @x166_vertex_disjoint_directed_paths k I).

(** ** X166 statements *****************************************************)

(** Corpus row: arxiv:1604.02317#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1604.02317__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1604.02317__00.json
    English statement: (Chudnovsky, Scott, Seymour 2016, Disjoint paths in unions of tournaments, arXiv:1604.02317, informal conjecture)
      There is a k >= 2 for which the k vertex-disjoint directed paths problem, restricted to
      digraphs with stability number two, is NP-complete: the problem (given a digraph and k
      ordered terminal pairs, are there k directed paths joining them whose interiors are
      pairwise disjoint) lies in NP, is NP-hard, and is decided on every instance whose digraph
      has stability number exactly two.
    Definitions: [x166_instance k] - a digraph together with k ordered terminal pairs (this
      file); [x166_vertex_disjoint_directed_paths] - the k paths exist with pairwise disjoint
      interiors (this file); [x166_stable_set] / [x166_stability_number_two] - a set with no arc
      between distinct members, and the property that the largest such set has size two (this
      file); [x166_in_np] / [x166_np_hard] - membership and hardness in the shared cost-coupled
      computation model (this file, over [polytime_decides_on_class], [poly_cost_on], [prun] of
      GTBase complexity.v); [x166_enc_digraph] - the adjacency-matrix encoding (this file).
    Notes: The corpus is an informal suspicion (we suspect the problem might be NP-complete);
      the body encodes the affirmative form. Complexity notions come from the GTBase computation
      model, so the statement is only as faithful as that model; the hardness clause
      [x166_np_hard] uses identity-output reductions, which is weaker than a general many-one
      reduction. *)
Definition vertex_disjoint_paths_stability_two_np_complete_statement : Prop :=
  exists k : nat, x166_k_disjoint_paths_NP_complete_on_stability_two k.
