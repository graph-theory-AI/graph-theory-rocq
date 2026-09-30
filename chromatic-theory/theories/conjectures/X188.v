(** * Chromatic.conjectures.X188 -- v2 interactive sum-choice row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X188 vocabulary ***********************************************)

Definition x188_size_choosable (G : sgraph) (f : G -> nat) : Prop :=
  forall (C : finType) (L : G -> {set C}),
    (forall v : G, #|L v| = f v) -> @list_colourable G C L.

Definition x188_sum_choice_at_most (G : sgraph) (k : nat) : Prop :=
  exists f : G -> nat,
    (\sum_(v : G) f v) <= k /\ x188_size_choosable f.

Definition x188_sum_choice_number (G : sgraph) (k : nat) : Prop :=
  x188_sum_choice_at_most G k /\
  forall j : nat, x188_sum_choice_at_most G j -> k <= j.

Definition x188_add_colour (G : sgraph) (k : nat)
    (L : G -> {set 'I_k}) (v : G) (c : 'I_k) : G -> {set 'I_k} :=
  fun u : G => if u == v then L u :|: [set c] else L u.

Fixpoint x188_requester_wins
    (G : sgraph) (k fuel : nat) (L : G -> {set 'I_k}) : Prop :=
  @list_colourable G 'I_k L \/
  if fuel is fuel'.+1 then
    exists v : G,
      forall c : 'I_k,
        @x188_requester_wins G k fuel'
          (@x188_add_colour G k L v c)
  else False.

Definition x188_interactive_sum_choice_at_most (G : sgraph) (k : nat) : Prop :=
  @x188_requester_wins G k k (fun _ : G => set0).

Definition x188_interactive_sum_choice_number (G : sgraph) (k : nat) : Prop :=
  x188_interactive_sum_choice_at_most G k /\
  forall j : nat, x188_interactive_sum_choice_at_most G j -> k <= j.

Definition x188_component_not_complete (G : sgraph) : Prop :=
  exists (root : G) (S : {set G}),
    S = [set y : G | connect (--) root y] /\ ~ clique S.

(** ** X188 statements *****************************************************)

(** Corpus row: arxiv:1703.05380#00
    Site: https://graph-theory-ai.github.io/graph-conjectures/arxiv/1703.05380__00/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/arxiv_reviews/1703.05380__00.json
    English statement: (Bonamy and Meeks 2021, Conjecture 1.1, arXiv:1703.05380)
      For every finite simple graph G having a connected component that is not a complete graph, the
      interactive sum choice number of G is strictly smaller than its sum choice number.
    Definitions: [x188_size_choosable G f] - every list assignment with #|L v| = f v admits a
      proper colouring from the lists (this file); [x188_sum_choice_at_most G k] and
      [x188_sum_choice_number G k] - the least total list size that guarantees colourability (this
      file); [x188_add_colour L v c] - add colour c to the list of v (this file);
      [x188_requester_wins G k fuel L] - the Requester wins the interactive game with the given
      fuel, either because the current lists already permit a colouring or because some vertex can
      be requested for which every adversary answer keeps the Requester winning (this file);
      [x188_interactive_sum_choice_number] (this file); [x188_component_not_complete G] - some
      connected component is not a clique (this file).
    Notes: KNOWN UNFAITHFUL ENCODING, corpus leg blocked. The faithfulness audit of 2026-07-17,
      meta/BLOCKED_RETARGETING_AUDIT.md and the row's verification_note, found that the game does
      not model the interactive sum choice number: [x188_add_colour] unions a colour into the list,
      so the adversary may re-supply a colour already present and the list does not grow, whereas in
      the Bonamy and Meeks game each request increases the size of the chosen vertex's list by one.
      The fuel is also tied to k rather than to the number of requests. The body is left untouched
      here, WP4 changes comments only. *)
Definition interactive_sum_choice_strict_statement : Prop :=
  forall (G : sgraph) (isc sc : nat),
    x188_component_not_complete G ->
    x188_interactive_sum_choice_number G isc ->
    x188_sum_choice_number G sc ->
    isc < sc.
