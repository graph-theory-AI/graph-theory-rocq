(** * Extremal.conjectures.X125 -- v2 random-lift Hajos number row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X125 vocabulary ***********************************************)

Definition x125_lift (n ell : nat) (G : sgraph) : Prop :=
  exists pi : G -> 'I_n,
    (forall i : 'I_n, #|[set v : G | pi v == i]| = ell) /\
    (forall x y : G, x -- y -> pi x != pi y) /\
    (forall i j : 'I_n, i != j ->
      forall x : G, pi x = i ->
        exists y : G, pi y = j /\ x -- y /\
          forall z : G, pi z = j -> x -- z -> z = y).

Definition x125_topological_minor_K (G : sgraph) (k : nat) : Prop :=
  exists branch : 'K_k -> G,
    injective branch /\
    forall (x y : 'K_k),
      x -- y ->
      exists p : seq G,
        [/\ path (--) (branch x) p,
            last (branch x) p = branch y,
            uniq (branch x :: p) &
            forall z : G,
              z \in p -> z != branch y -> forall (u : 'K_k), z != branch u].

Definition x125_hajos_at_least (G : sgraph) (k : nat) : Prop :=
  x125_topological_minor_K G k.

Definition x125_random_lift_space
    (n ell : nat) (L : finType) (obs : L -> sgraph) : Prop :=
  forall x : L, x125_lift n ell (obs x).

Definition x125_isomorphic (G H : sgraph) : Prop :=
  exists f : G -> H,
    bijective f /\
    forall x y : G, (x -- y) = (f x -- f y).

Record x125_lift_model (ell : nat -> nat) := X125LiftModel {
  x125_sample : nat -> finType;
  x125_weight : forall n : nat, x125_sample n -> nat;
  x125_observe : forall n : nat, x125_sample n -> sgraph;
  x125_sample_nonempty :
    forall n : nat, exists x : x125_sample n, True;
  x125_positive_weight :
    forall (n : nat) (x : x125_sample n), 0 < @x125_weight n x;
  x125_sample_lift :
    forall (n : nat) (x : x125_sample n),
      x125_lift n (ell n) (@x125_observe n x);
  x125_sample_complete :
    forall (n : nat) (G : sgraph),
      x125_lift n (ell n) G ->
      exists x : x125_sample n, x125_isomorphic (@x125_observe n x) G;
  x125_uniform_weight :
    forall (n : nat) (x y : x125_sample n),
      @x125_weight n x = @x125_weight n y
}.

Definition x125_linear_lower_bound (ell : nat -> nat) : Prop :=
  exists c : nat, 0 < c /\ eventually (fun n => c * n <= ell n).

Definition x125_almost_all
    (ell : nat -> nat) (P : forall n : nat, sgraph -> Prop) : Prop :=
  exists (M : x125_lift_model ell)
         (good : forall n : nat, pred (x125_sample M n)),
    @fg_whp (@x125_sample ell M) (@x125_weight ell M)
      good /\
    forall (n : nat) (x : x125_sample M n),
      good n x -> P n (@x125_observe ell M n x).

(** Corpus row: studies:std_drier_linial_conjecture_haj_s_number_of_random_l
    Site: none
    Review: none
    English statement: (Drier and Linial, "Drier-Linial conjecture (Hajos number of random lifts of complete graphs)")
      For every fibre-size function ell that is eventually at least linear (c * n <= ell n for
      some c > 0 and all large n) there are a, b > 0 such that almost all ell(n)-lifts of K_n
      have Hajos number between a * n and b * n, i.e. a topological K_{a*n} minor and no
      topological K_k minor for k > b * n.
    Definitions: [x125_lift n ell G] - G is an ell-lift of K_n: a fibre map to 'I_n with all fibres of
      size ell, no edge inside a fibre, and a perfect matching between any two distinct fibres
      (X125.v); [x125_topological_minor_K G k] - injective branch vertices for K_k joined by
      internally disjoint paths avoiding the other branch vertices (X125.v);
      [x125_hajos_at_least G k] - the same (X125.v); [x125_isomorphic] - a bijection preserving
      and reflecting adjacency (X125.v); [x125_lift_model ell] - a record packaging, for each n,
      a non-empty finite sample type with positive uniform weights whose observations are
      exactly the ell(n)-lifts of K_n up to isomorphism (X125.v); [x125_almost_all ell P] -
      existence of such a model and of a good predicate holding with high probability under
      [fg_whp] and implying P (X125.v); [x125_linear_lower_bound] (X125.v); [eventually],
      [fg_whp] - GTBase asymptotics.
    Notes: this row is recorded as BLOCKED. The adversarial repair verification of 2026-07-18 found
      that the [exists M : x125_lift_model ell] quantifier admits a multiplicity-skewed
      observation model (extra sample points all observing the trivial disjoint-copies lift)
      that satisfies every record field yet concentrates the high-probability ratio on a single
      lift, making the statement provable with a = b = 1 independently of Drier-Linial (the
      engine is machine-checked in probe_x125_skew.v). The structural fix would be to pin the
      canonical uniform LABELLED lift model (matching-tuple sample space) or add a
      measure-faithfulness side condition. As it stands the body is VACUOUS-LOOKING / too weak
      (ledger). This row also comes from the studies slice, which has no site or review page. *)
Definition drier_linial_random_lift_hajos_number_statement : Prop :=
  forall ell : nat -> nat,
    x125_linear_lower_bound ell ->
    exists a b : nat,
      0 < a /\ 0 < b /\
      x125_almost_all ell
        (fun n (G : sgraph) =>
           x125_lift n (ell n) G ->
           x125_hajos_at_least G (a * n) /\
           forall k : nat, x125_hajos_at_least G k -> k <= b * n).
