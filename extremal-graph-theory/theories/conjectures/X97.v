(** * Extremal.conjectures.X97 -- v2 maximum-independent-set hitting row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X97 vocabulary ************************************************)

Definition x97_stable_set (G : sgraph) (S : {set G}) : Prop :=
  forall x y : G, x \in S -> y \in S -> x != y -> ~~ (x -- y).

Definition x97_maximum_independent_set (G : sgraph) (S : {set G}) : Prop :=
  x97_stable_set S /\
  forall T : {set G}, x97_stable_set T -> #|T| <= #|S|.

Definition x97_hits_all_maximum_independent_sets
    (G : sgraph) (X : {set G}) : Prop :=
  forall S : {set G},
    x97_maximum_independent_set S ->
    ~~ [disjoint X & S].

Definition x97_hitting_number_at_most (G : sgraph) (k : nat) : Prop :=
  exists X : {set G},
    #|X| <= k /\ x97_hits_all_maximum_independent_sets X.

(** Corpus row: studies:std_bollob_s_erd_s_tuza_conjecture_105
    Site: none
    Review: none
    English statement: (Bollobas, Erdos and Tuza, "Bollobas-Erdos-Tuza Conjecture")
      For all positive rationals delta = delta_num/delta_den and eps = eps_num/eps_den there is
      a threshold N such that every graph G on n >= N vertices whose independence number is at
      least delta * n has a vertex set of size at most eps * n meeting every MAXIMUM independent
      set; that is, eta(G) = o(|V(G)|) for such graphs.
    Definitions: [x97_stable_set S] - no two distinct vertices of S are adjacent (X97.v);
      [x97_maximum_independent_set S] - a stable set of maximum size (X97.v);
      [x97_hits_all_maximum_independent_sets G X] - X meets every maximum independent set
      (X97.v); [x97_hitting_number_at_most G k] - some such X has at most k vertices (X97.v);
      [alpha] - independence number (GTBase).
    Notes: this row comes from the studies slice of the corpus, which has no site or review page.
      o(|V(G)|) is rendered in eventual epsilon-N form, the threshold N depending on both delta
      and eps. The hitting number eta is introduced as an existential upper bound rather than as
      an exact minimum, which is equivalent for an upper-bound conclusion. *)
Definition bollobas_erdos_tuza_independent_set_hitting_statement : Prop :=
  forall delta_num delta_den eps_num eps_den : nat,
    0 < delta_num ->
    0 < delta_den ->
    0 < eps_num ->
    0 < eps_den ->
    exists N : nat,
      forall (n : nat) (G : sgraph),
        N <= n ->
        #|G| = n ->
        delta_den * α([set: G]) >= delta_num * n ->
        exists eta : nat,
          x97_hitting_number_at_most G eta /\
          eps_den * eta <= eps_num * n.
