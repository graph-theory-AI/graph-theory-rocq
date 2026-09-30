(** * Chromatic.conjectures.X203 -- v2 separation choosability min-degree row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X203 vocabulary ***********************************************)

Definition x203_separated_k_list_assignment
    (G : sgraph) (C : finType) (L : G -> {set C}) (k : nat) : Prop :=
  (forall v : G, #|L v| = k) /\
  forall u v : G, u -- v -> #|L u :&: L v| <= 1.

Definition x203_separation_choosable (G : sgraph) (k : nat) : Prop :=
  forall (C : finType) (L : G -> {set C}),
    x203_separated_k_list_assignment L k -> @list_colourable G C L.

Definition x203_separation_choosability_at_least (G : sgraph) (k : nat) : Prop :=
  forall j : nat, j < k -> ~ x203_separation_choosable G j.

Definition x203_min_degree_at_least (G : sgraph) (d : nat) : Prop :=
  forall v : G, d <= #|N(v)|.

(** ** X203 statements *****************************************************)

(** Corpus row: arxiv:1802.03727#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1802.03727__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1802.03727__00.json
    English statement: (Esperet, Kang and Thomasse 2018, Conjecture 1.3, arXiv:1802.03727)
      There is a function x from naturals to naturals that is unbounded, i.e. takes values above
      every bound, such that every finite simple graph of minimum degree at least d has separation
      choosability at least x(d), where separation choosability at least k means that for every j <
      k some list assignment with all lists of size j and with adjacent lists meeting in at most one
      colour admits no proper colouring from the lists.
    Definitions: [x203_separated_k_list_assignment L k] - all lists have size exactly k and
      adjacent vertices share at most one colour (this file); [x203_separation_choosable G k] -
      every such assignment admits a proper list colouring (this file);
      [x203_separation_choosability_at_least G k] - separation k'-choosability fails for every k' <
      k (this file); [x203_min_degree_at_least G d] (this file); [list_colourable] (GTBase
      base/theories/base.v).
    Notes: KNOWN UNFAITHFUL ENCODING, corpus leg blocked. The faithfulness audit of 2026-07-17,
      meta/BLOCKED_RETARGETING_AUDIT.md and the row's verification_note, found the statement
      trivially FALSE: the universal quantifier over graphs includes the EMPTY graph, which
      vacuously has minimum degree d for every d while being separation j-choosable for every j, so
      the required lower bound on its separation choosability fails as soon as x(d) > 0. The
      source's growth condition x_1(d) tends to infinity is also weakened to plain unboundedness.
      The body is left untouched here, WP4 changes comments only. *)
Definition separation_choosability_min_degree_unbounded_statement : Prop :=
  exists x : nat -> nat,
    (forall B : nat, exists d : nat, B <= x d) /\
    forall (d : nat) (G : sgraph),
      x203_min_degree_at_least G d ->
      x203_separation_choosability_at_least G (x d).
