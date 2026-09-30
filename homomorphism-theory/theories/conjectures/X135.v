(** * Hom.conjectures.X135 -- v2 Engbers homomorphism-count row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X135 vocabulary ***********************************************)

(** Graph homomorphism count, matching the D2tur local idiom: functions
    [G -> H] preserving adjacency, counted over the finite-function space. *)
Definition x135_hom_count (G H : sgraph) : nat :=
  #|[set f : {ffun G -> H} |
      [forall x : G, [forall y : G, (x -- y) ==> (f x -- f y)]]]|.

Definition x135_min_degree_at_least (G : sgraph) (delta : nat) : Prop :=
  forall v : G, delta <= #|N(v)|.

Definition x135_power_denominator (delta : nat) : nat :=
  2 * delta * delta.+1.

Definition x135_engbers_bound (delta n : nat) (H : sgraph) : nat :=
  maxn
    ((x135_hom_count 'K_(delta.+1) H) ^ (n * (2 * delta)))
    (maxn
       ((x135_hom_count (KB delta delta) H) ^ (n * delta.+1))
       ((x135_hom_count (KB delta (n - delta)) H) ^
          x135_power_denominator delta)).

(** ** X135 statements *****************************************************)

(** Corpus row: studies:std_engbers_homomorphism_count_maximisation_conjectu
    Site: none
    Review: none
    English statement: (Engbers, as Conjecture 1.4 of Guggiari and Scott,
      arXiv:1611.02911, "Engbers' Homomorphism-Count Maximisation Conjecture")
      For every minimum degree delta >= 1 and every graph H there is a threshold
      N = c(delta,H) such that every graph G with n >= N vertices all of whose
      vertices have at least delta neighbours satisfies
        hom(G,H) <= max { hom(K_(delta+1),H)^(n/(delta+1)),
                          hom(K_(delta,delta),H)^(n/(2*delta)),
                          hom(K_(delta,n-delta),H) },
      where hom(A,B) is the number of graph homomorphisms from A to B.  In the
      Rocq body both sides are raised to D = 2*delta*(delta+1) to clear the
      fractional exponents, giving hom(G,H)^D on the left and the three integral
      powers n*(2*delta), n*(delta+1) and D on the right.
    Definitions: [x135_hom_count G H] - the number of finite functions G -> H
      sending adjacent vertices to adjacent vertices, i.e. hom(G,H) (this file,
      X135.v); [x135_min_degree_at_least G delta] - every vertex has at least
      delta neighbours (X135.v); [x135_power_denominator delta] - the clearing
      exponent D = 2*delta*(delta+1) (X135.v); [x135_engbers_bound delta n H] -
      the maximum of the three cleared model terms (X135.v); ['K_n] and
      [KB n m] - the complete and complete bipartite graphs (coq-graph-theory
      sgraph.v).
    Notes: the corpus records this row as PARTIAL (proxy) purely because of the
      exponent clearing; the independent audit (wf_bdaea8ab, 2026-07-18) checked
      the quantifier order, the three model graphs and the cleared exponents and
      found the rendering exact.  Raising both sides to the positive power D is
      an equivalence over the naturals, so no strength is lost or gained.
      [x135_hom_count] is a local boolean re-encoding of base's [is_hom]
      (compare [hom_ffun]/[endo_count] in homomorphism-theory/U3.v). *)
Definition engbers_homomorphism_count_maximisation_statement : Prop :=
  forall (delta : nat) (H : sgraph),
    1 <= delta ->
    exists N : nat,
      forall (n : nat) (G : sgraph),
        N <= n ->
        #|G| = n ->
        x135_min_degree_at_least G delta ->
        (x135_hom_count G H) ^ x135_power_denominator delta
          <= x135_engbers_bound delta n H.

