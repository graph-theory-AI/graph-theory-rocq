(** * Reconstruction.conjectures.X21 -- v2 deck-reconstruction continuation rows *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X21 vocabulary ************************************************)

Definition x21_l_deck_index (G : sgraph) (ell : nat) : Type :=
  {S : {set G} | #|S| == ell}.

Definition x21_same_l_deck (G H : sgraph) (ell : nat) : Prop :=
  exists f : x21_l_deck_index G ell -> x21_l_deck_index H ell,
    bijective f /\
    forall S : x21_l_deck_index G ell,
      inhabited (induced (val S) ≃ induced (val (f S))).

Definition x21_l_reconstructible (G : sgraph) (ell : nat) : Prop :=
  forall H : sgraph,
    #|H| = #|G| ->
    x21_same_l_deck G H ell ->
    inhabited (G ≃ H).

(** ** X21 statements ******************************************************)

(** Corpus row: studies:std_kelly_manvel_conjecture_reconstruction_from_the
    Site: none
    Review: none
    English statement: (Kelly and Manvel, "Kelly-Manvel Conjecture (reconstruction from the
      (n-r)-deck)")
      For every natural number r there is a threshold N, itself at least r, such that every
      simple graph G on n vertices with N <= n is reconstructible from its (n-r)-deck: for
      every simple graph H with the same number of vertices as G, if some bijection matches
      the (n-r)-element vertex subsets of G with those of H in such a way that the
      corresponding induced subgraphs are isomorphic, then G and H are isomorphic.
    Definitions: [x21_l_deck_index G ell] — the index type of the ell-deck of G, namely the
      vertex subsets of G of cardinality ell (X21.v); [x21_same_l_deck G H ell] — some
      bijection between the two index types matches the induced subgraphs on corresponding
      subsets up to isomorphism (X21.v); [x21_l_reconstructible G ell] — every H with the
      same number of vertices as G and the same ell-deck is isomorphic to G (X21.v);
      [induced], [diso] written [≃] are coq-graph-theory, re-exported by GTBase
      (base/theories/base.v).
    Notes: the deck is modelled as the family of induced subgraphs indexed by the vertex
      subsets of the given size, so having the same deck is again a bijection of index sets
      matching cards up to isomorphism. Two guards are added to the informal row:
      [r <= N] (harmless, since the conclusion is monotone in N, and it makes the nat
      subtraction [#|G| - r] the genuine n - r rather than a truncation at 0) and, inside
      [x21_l_reconstructible], the hypothesis [#|H| = #|G|] (in the informal statement the
      size of the deck already pins n down). *)
Definition kelly_manvel_n_minus_r_deck_reconstruction_statement : Prop :=
  forall r : nat, exists N : nat,
    r <= N /\
    forall G : sgraph,
      N <= #|G| ->
      x21_l_reconstructible G (#|G| - r).

(** Corpus row: studies:std_n_dl_s_conjecture_deck_reconstruction_of_trees
    Site: none
    Review: none
    English statement: (Nydl, "Nydl's Conjecture (ell-deck reconstruction of trees)")
      For all natural numbers n and ell with 4 <= n and floor(n/2) + 1 <= ell, any two trees
      on n vertices that have the same ell-deck are isomorphic; two graphs have the same
      ell-deck when some bijection between their ell-element vertex subsets matches the
      corresponding induced subgraphs up to isomorphism.
    Definitions: [x21_same_l_deck T1 T2 ell] — equality of ell-decks, as above (X21.v);
      [x21_l_deck_index] — the ell-element vertex subsets (X21.v); [is_tree [set: T]] — T is
      a connected forest (coq-graph-theory); [n./2] is MathComp integer halving, that is
      floor(n/2).
    Notes: both vertex-count hypotheses are written out ([#|T1| = n] and [#|T2| = n]) rather
      than left implicit in the phrase "two trees on n vertices". Nothing here forces the
      ell-deck to be non-empty; for ell above n the index type is empty, but the threshold
      hypothesis floor(n/2) + 1 <= ell does not exclude ell > n, so for such ell the
      hypothesis [x21_same_l_deck] is satisfied by the empty bijection and the statement
      then asserts that any two trees on n vertices are isomorphic — see the improvement
      ledger. *)
Definition nydl_tree_l_deck_reconstruction_statement : Prop :=
  forall (n ell : nat) (T1 T2 : sgraph),
    4 <= n ->
    n./2 + 1 <= ell ->
    #|T1| = n ->
    #|T2| = n ->
    is_tree [set: T1] ->
    is_tree [set: T2] ->
    x21_same_l_deck T1 T2 ell ->
    inhabited (T1 ≃ T2).

(** Corpus row: studies:std_spinoza_west_connectedness_threshold_conjecture
    Site: none
    Review: none
    English statement: (Spinoza and West, "Spinoza-West Connectedness Threshold Conjecture")
      For all natural numbers n and ell with 6 <= n and floor(n/2) + 1 <= ell, and for any
      two graphs G and H on n vertices having the same ell-deck: G is connected if and only
      if H is connected.
    Definitions: [x21_same_l_deck G H ell] — equality of ell-decks, as above (X21.v);
      [connected [set: G]] — the whole vertex set of G is connected in G (coq-graph-theory);
      [n./2] is MathComp integer halving, that is floor(n/2).
    Notes: the corpus wording is that "the connectedness of an n-vertex graph G is
      determined by its ell-deck"; being determined by the deck is encoded in the usual way,
      as: two n-vertex graphs with the same ell-deck agree on connectedness. The corpus
      classifies this row as Informal. The same ell > n remark as for the Nydl row applies:
      the threshold hypothesis does not bound ell by n, so for ell > n the deck-equality
      hypothesis is vacuously satisfiable — see the improvement ledger. *)
Definition spinoza_west_l_deck_connectedness_statement : Prop :=
  forall (n ell : nat) (G H : sgraph),
    6 <= n ->
    n./2 + 1 <= ell ->
    #|G| = n ->
    #|H| = n ->
    x21_same_l_deck G H ell ->
    (connected [set: G] <-> connected [set: H]).
