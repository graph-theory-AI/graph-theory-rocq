(** * Hypergraph.conjectures.X148 -- v2 two-families/AK-bound row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X148 vocabulary ***********************************************)

Definition x148_two_families_hypotheses
    (I T : finType) (A B : I -> {set T}) : Prop :=
  (forall i : I, [disjoint A i & B i]) /\
  (forall i j : I, i != j -> ~~ [disjoint A i & B j]).

Definition x148_t_intersecting_first_family
    (I T : finType) (A : I -> {set T}) (t : nat) : Prop :=
  forall i j : I, i != j -> t <= #|A i :&: A j|.

Definition x148_AK_family_size (n t r : nat) : nat :=
  #|[set S : {set 'I_n} |
      t + r <= #|S :&: [set j : 'I_n | j < t + 2 * r]|]|.

Definition x148_AK_bound (n t : nat) : nat :=
  \max_(r < n.+1) x148_AK_family_size n t r.

(** ** X148 statements *****************************************************)

(** Corpus row: studies:std_gerbner_keszegh_methuku_abhishek_nagy_patk_s_tom
    Site: none
    Review: none
    English statement: (Gerbner, Keszegh, Methuku, Abhishek, Nagy, Patkos, Tompkins and Xiao,
      conjecture on two families and the Ahlswede-Khachatrian bound)
      For all t and n, if a family of pairs (A_i, B_i) of subsets of an n-element ground set
      satisfies the Bollobas two-families conditions - A_i is disjoint from B_i for every i, and
      A_i meets B_j whenever i and j differ - and the first family is t-intersecting, meaning
      that A_i and A_j share at least t elements whenever i and j differ, then the number of
      pairs is at most the Ahlswede-Khachatrian bound.
    Definitions: [x148_two_families_hypotheses A B] - the two Bollobas conditions above
      (hypergraph-theory/theories/conjectures/X148.v);
      [x148_t_intersecting_first_family A t] - any two distinct members of the first family
      share at least t elements (same file); [x148_AK_family_size n t r] - the number of subsets
      S of an n-element set with at least t+r elements among the first t+2r elements, i.e. the
      size of the r-th Frankl family (same file); [x148_AK_bound n t] - the largest of those
      sizes over r below n+1 (same file).
    Notes: BLOCKED - WRONG EXTREMAL OBJECT (faithfulness audit 2026-07-17,
      meta/BLOCKED_RETARGETING_AUDIT.md).  The source (Scott and Wilmer, verifying Gerbner et
      al. Conjecture 2.5) fixes a UNIFORM profile |A_i| = a and |B_i| = b with t <= a <= b and
      bounds the number of pairs by AK(a+b, a, t), the maximum size of an a-UNIFORM
      t-intersecting family of subsets of an (a+b)-element set.  The statement here drops
      uniformity entirely - there is no a, and no constraint on the sizes of A_i and B_i - and
      replaces the bound by the NON-UNIFORM maximum of Frankl families over the whole ground
      set, so it is a different claim and is believed false as written.  Recorded in
      meta/STATEMENT_IMPROVEMENTS.md. *)
Definition gerbner_two_families_ahlswede_khachatrian_bound_statement : Prop :=
  forall (t n : nat) (I T : finType) (A B : I -> {set T}),
    #|T| = n ->
    x148_two_families_hypotheses A B ->
    x148_t_intersecting_first_family A t ->
    #|I| <= x148_AK_bound n t.
