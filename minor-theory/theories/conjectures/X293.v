(** * Minor.conjectures.X293 -- v2 row: Hadwiger's conjecture as the chromatic characterisation of minor-closed
      classes (the studies row of Hadwiger's conjecture, record arXiv:1710.02727) *)

From GTBase Require Import base minor_classes.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X293 statement ******************************************************)

(** Reused vocabulary: GTBase.minor_classes [minor_closed] and library vocabulary, as X214 states Hadwiger's
    conjecture ([minor] and ['K_n] from coq-graph-theory, [χ(A)] coq-graph-theory's [chi_mem]).  X293 declares no
    helper of its own. *)

(** Corpus row: studies:std_hadwiger_s_conjecture
    Site: none
    Review: none
    English statement: (Hadwiger; studies slice of the corpus, record arXiv:1710.02727)
      Let t >= 1 be an integer, and let G be a minor-closed class of graphs.  Then chi(G) <= t if and only if
      K_(t+1) is not in G.
    Definitions: a class of graphs is a predicate [C : sgraph -> Prop]; it is minor-closed when every minor of a
      member is a member ([minor_closed C], GTBase.minor_classes; since isomorphic graphs are minors of each other,
      the class is then closed under isomorphism); "chi(G) <= t" for the class is "every member G has
      [χ([set: G]) <= t]" ([χ] coq-graph-theory's chromatic number); "K_(t+1) is not in G" is [~ C 'K_(t + 1)]
      (['K_n] the complete graph on n vertices; [minor] coq-graph-theory's minor relation).
    Notes: encoded as stated (arXiv:1710.02727v1, IslandsI4.tex l.61-63, its Conjecture 1).  The source calls a
      class minor-closed only if it is proper (l.57: it does not contain all graphs); C ranges here over every
      minor-closed class, which is equivalent: a class holding K_(t+1) fails both sides, and grounding_X293.v
      proves the statement equal to its form over proper classes ([g293_proper_equiv]).  The direction from
      "chi(G) <= t" to "K_(t+1) not in G" is immediate (K_(t+1) has chromatic number t+1); the converse is
      Hadwiger's conjecture.  The statement is equivalent to X214's [hadwiger_chromatic_clique_minor_statement]
      (bm:bm-041, chi(G) = k -> K_k is a minor of G): grounding_X293.v proves the equivalence ([g293_equiv_X214];
      forward through the class of K_(t+1)-minor-free graphs, backward through minor-closure).  The empty class
      satisfies both sides.  Pinned status open; open at the pin: arXiv:2512.20392v1 (main.tex l.171-176) states
      Hadwiger's conjecture with K_t (chi(G) >= t gives a K_t minor) and says it holds for t <= 6, so this row is
      known for t <= 5. *)
Definition hadwiger_minor_closed_class_statement : Prop :=
  forall t : nat, 1 <= t ->
  forall C : sgraph -> Prop,
    minor_closed C ->
    ((forall G : sgraph, C G -> χ([set: G]) <= t) <-> ~ C 'K_(t + 1)).
