(** * Hypergraph.foundations.hedgehog -- the finite hedgehog hypergraph H_t

    Library migration D7 (registry entry [hedgehog]; report meta/migration_reports/hedgehog.md; record
    meta/LIBRARY_MIGRATION_D7.md; public client theories/examples/hedgehog_hypergraphs.v).

    The hedgehog [H_t] as a concrete finite 3-uniform hypergraph, with exactly the carriers of the X117
    vocabulary it replaces:
    - [hedgehog_spike t]: the subtype of ordered pairs [(i, j)] of ['I_t] with [i < j] (one spike per
      unordered pair of body vertices, with a Boolean strict-order witness, so a finite subtype);
    - [hedgehog_vertex t]: the sum carrier ['I_t + hedgehog_spike t] (body vertices [inl i], spike
      vertices [inr s]);
    - [hedgehog_edge s]: the tagged triple [[set inl i; inl j; inr s]] of the spike [s = (i, j)];
    - [hedgehog_edges t]: the image family [[set hedgehog_edge s | s : hedgehog_spike t]].
    No positivity or rank guard: for [t = 0] the carrier and the family are empty, and for [t = 1]
    there is one body vertex and no edge.  Every edge has exactly three vertices and its spike vertex
    identifies it, so the family is 3-uniform (vacuously when [t < 2]) with one edge per spike.  The
    finite structures are MathComp's subtype, sum, set and image instances.

    Axiom-free: no Axiom/Parameter/Admitted. *)
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition hedgehog_spike (t : nat) : Type := {p : 'I_t * 'I_t | p.1 < p.2}.

Definition hedgehog_vertex (t : nat) : Type := ('I_t + hedgehog_spike t)%type.

Definition hedgehog_edge (t : nat) (s : hedgehog_spike t) : {set hedgehog_vertex t} :=
  [set inl (sval s).1; inl (sval s).2; inr s].

Definition hedgehog_edges (t : nat) : {set {set hedgehog_vertex t}} :=
  [set hedgehog_edge s | s : hedgehog_spike t].

Section Hedgehog.
Variable t : nat.
Implicit Types (s : hedgehog_spike t) (e : {set hedgehog_vertex t}).

(** The two body vertices of a spike are distinct (strict order). *)
Lemma hedgehog_spike_neq s : (sval s).1 != (sval s).2.
Proof. by case: s => -[i j] /= ij; rewrite neq_ltn ij. Qed.

(** The spike vertex [inr s] lies in [hedgehog_edge s'] exactly when [s = s']: it identifies the edge. *)
Lemma hedgehog_edge_spike s s' : (inr s \in hedgehog_edge s') = (s == s').
Proof. by rewrite !inE. Qed.

Lemma hedgehog_edge_inj : injective (@hedgehog_edge t).
Proof.
move=> s s' ss'; apply/eqP.
by rewrite -hedgehog_edge_spike -ss' hedgehog_edge_spike.
Qed.

(** Every edge has exactly three vertices: two distinct body vertices and its spike vertex. *)
Lemma card_hedgehog_edge s : #|hedgehog_edge s| = 3.
Proof.
rewrite /hedgehog_edge setUC cardsU1 cards2 !inE /=.
by rewrite (hedgehog_spike_neq s).
Qed.

Lemma hedgehog_edgesP e : reflect (exists s, e = hedgehog_edge s) (e \in hedgehog_edges t).
Proof. by apply: (iffP imsetP) => [[s _ ->]|[s ->]]; exists s. Qed.

(** Rank three, unconditionally (vacuous when there is no spike). *)
Lemma hedgehog_edges_card e : e \in hedgehog_edges t -> #|e| = 3.
Proof. by case/hedgehog_edgesP=> s ->; exact: card_hedgehog_edge. Qed.

(** One edge per spike, and [t] body vertices besides the spikes. *)
Lemma card_hedgehog_edges : #|hedgehog_edges t| = #|{: hedgehog_spike t}|.
Proof. by rewrite card_imset //; exact: hedgehog_edge_inj. Qed.

Lemma card_hedgehog_vertex : #|{: hedgehog_vertex t}| = t + #|{: hedgehog_spike t}|.
Proof. by rewrite card_sum card_ord. Qed.

End Hedgehog.
