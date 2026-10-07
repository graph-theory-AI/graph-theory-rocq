(** Public-only client of [Hypergraph.foundations.hedgehog], the finite hedgehog [H_t]: its spikes are
    the ordered pairs [i < j] of ['I_t], its vertices the sum ['I_t + hedgehog_spike t], each edge the
    tagged triple [[set inl i; inl j; inr s]], and the family their image.  No conjecture module is
    imported.  Covered: the empty body [t = 0] and the singleton body [t = 1] (no spike, no edge), the
    concrete [t = 2] (three vertices, one edge), every edge of cardinal three with its identifying spike,
    and 3-uniformity for every [t] with the D1 canonical [uniform_family], vacuous when [t < 2]. *)
From GTBase Require Import base hypergraph_uniformity.
From Hypergraph.foundations Require Import hedgehog.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Empty and singleton bodies: no spike, so no edge *)

Lemma no_spike0 (s : hedgehog_spike 0) : False.
Proof. by case: s => -[[m Hm] _] _; rewrite ltn0 in Hm. Qed.

Lemma no_spike1 (s : hedgehog_spike 1) : False.
Proof. by case: s => -[i j] /=; rewrite (ord1 i) (ord1 j) ltnn. Qed.

Example hedgehog0_vertices : #|{: hedgehog_vertex 0}| = 0.
Proof. by rewrite card_hedgehog_vertex add0n; apply: eq_card0 => s; case: (no_spike0 s). Qed.

Example hedgehog0_edges : hedgehog_edges 0 = set0.
Proof. by apply: cards0_eq; rewrite card_hedgehog_edges; apply: eq_card0 => s; case: (no_spike0 s). Qed.

Example hedgehog1_vertices : #|{: hedgehog_vertex 1}| = 1.
Proof. by rewrite card_hedgehog_vertex (@eq_card0 _ {: hedgehog_spike 1}) // => s; case: (no_spike1 s). Qed.

Example hedgehog1_edges : hedgehog_edges 1 = set0.
Proof. by apply: cards0_eq; rewrite card_hedgehog_edges; apply: eq_card0 => s; case: (no_spike1 s). Qed.

(** ** The concrete hedgehog [H_2]: one spike, three vertices, one edge *)

Definition spike01 : hedgehog_spike 2 := exist _ (ord0, ord_max) isT.

Lemma spike2_unique (s : hedgehog_spike 2) : s = spike01.
Proof.
case: s => -[i j] /= ij; apply: val_inj => /=.
have j1 : (j : nat) = 1.
  by apply/eqP; rewrite eqn_leq -ltnS ltn_ord; exact: leq_ltn_trans (leq0n i) ij.
have i0 : (i : nat) = 0 by move: ij; rewrite j1 ltnS leqn0 => /eqP.
by congr pair; apply: val_inj.
Qed.

Example hedgehog2_edge : hedgehog_edge spike01 = [set inl ord0; inl ord_max; inr spike01].
Proof. by []. Qed.

Example hedgehog2_edges : hedgehog_edges 2 = [set hedgehog_edge spike01].
Proof.
apply/setP => e; rewrite inE; apply/hedgehog_edgesP/eqP => [[s ->]|->]; last by exists spike01.
by rewrite (spike2_unique s).
Qed.

Example hedgehog2_vertices : #|{: hedgehog_vertex 2}| = 3.
Proof. by rewrite card_hedgehog_vertex -card_hedgehog_edges hedgehog2_edges cards1. Qed.

(** ** Every edge: three vertices, identified by its spike *)

Example hedgehog_rank3 (t : nat) (e : {set hedgehog_vertex t}) : e \in hedgehog_edges t -> #|e| = 3.
Proof. exact: hedgehog_edges_card. Qed.

Example hedgehog_identifying_spike (t : nat) (s s' : hedgehog_spike t) :
  (inr s \in hedgehog_edge s') = (s == s').
Proof. exact: hedgehog_edge_spike. Qed.

Example hedgehog_one_edge_per_spike (t : nat) : #|hedgehog_edges t| = #|{: hedgehog_spike t}|.
Proof. exact: card_hedgehog_edges. Qed.

(** ** Uniformity with the D1 canonical, vacuous for the empty families *)

Example hedgehog_uniform (t : nat) : uniform_family (hedgehog_edges t) 3.
Proof. exact: hedgehog_edges_card. Qed.

Example hedgehog_uniform_empty : uniform_family (hedgehog_edges 1) 3 /\ hedgehog_edges 1 = set0.
Proof. by split; [exact: hedgehog_uniform | exact: hedgehog1_edges]. Qed.

Print Assumptions spike2_unique.
Print Assumptions hedgehog2_vertices.
Print Assumptions hedgehog_uniform_empty.
