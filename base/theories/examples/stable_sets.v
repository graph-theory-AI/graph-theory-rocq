(** Downstream use of the upstream stable-set predicate through the GTBase views, without corpus imports: the empty
    set and the empty graph, a singleton, all vertices of an edgeless graph, the two adjacent vertices of [K_2],
    hereditary restriction, induced-subgraph transport, the raw Prop views and the bounded Boolean form. *)
From GTBase Require Import base stable_sets.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The empty set is stable in every graph, and so is the whole vertex set of the empty graph. *)
Example stable_empty (G : sgraph) : stable (set0 : {set G}) /\ stable [set: 'K_0].
Proof. by split; [exact: stable0 | apply/stable_noedgeP => -[]]. Qed.

(** A singleton is stable. *)
Example stable_singleton (G : sgraph) (x : G) : stable [set x].
Proof. exact: stable1. Qed.

(** An edgeless graph: every vertex set is stable, the whole carrier included. *)
Definition edgeless (n : nat) : sgraph :=
  @SGraph 'I_n (fun _ _ => false) (fun _ _ => erefl) (fun _ => erefl).

Example edgeless_stable (n : nat) : stable [set: edgeless n].
Proof. by apply/stable_noedgeP. Qed.

(** The two vertices of [K_2] are adjacent, so they are rejected together, while each alone is stable. *)
Example K2_pair :
  ~~ stable [set: 'K_2] /\ ~~ stable [set (ord0 : 'K_2); ord_max] /\ stable [set (ord0 : 'K_2)].
Proof.
split; first by apply/stablePn; exists ord0, ord_max; rewrite !inE.
by rewrite stable_pair stable1.
Qed.

(** Stability is hereditary: the pair of [K_2] cannot be extended to a stable set of [K_2]. *)
Example stable_hereditary (G : sgraph) (A B : {set G}) :
  A \subset B -> stable B -> stable A.
Proof. exact: sub_stable. Qed.

Example K2_no_stable_superset (B : {set 'K_2}) : [set: 'K_2] \subset B -> ~~ stable B.
Proof.
move=> sub; apply/negP => /(sub_stable sub) st.
by case: K2_pair => /negP nst _; apply: nst.
Qed.

(** Induced-subgraph transport: a set of the induced subgraph is stable exactly when its image is. *)
Example stable_induced_transport (G : sgraph) (H : {set G}) (K : {set induced H}) :
  stable K = stable (val @: K).
Proof. exact: stable_induced. Qed.

(** The raw presentations of the corpus, for every graph and supplied set: the [edge -> False] and distinct-vertex
    Prop views, and the bounded Boolean form with its equality disjunct. *)
Example raw_views (G : sgraph) (S : {set G}) :
  [/\ stable S <-> (forall x y : G, x \in S -> y \in S -> x -- y -> False),
      stable S <-> (forall x y : G, x \in S -> y \in S -> x != y -> ~~ (x -- y)) &
      stable S = [forall x in S, [forall y in S, (x == y) || ~~ (x -- y)]]].
Proof.
split; [exact: iff_sym (rwP (stable_noedgeP S)) | exact: iff_sym (rwP (stable_distinctP S)) | exact: stable_eqbE].
Qed.

Print Assumptions stable_empty.
Print Assumptions edgeless_stable.
Print Assumptions K2_pair.
Print Assumptions K2_no_stable_superset.
Print Assumptions raw_views.
