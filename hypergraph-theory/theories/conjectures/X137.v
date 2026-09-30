(** * Hypergraph.conjectures.X137 -- v2 Erdos-Rado sunflower row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X137 vocabulary ***********************************************)

Definition x137_uniform (T : finType) (F : {set {set T}}) (r : nat) : Prop :=
  forall A : {set T}, A \in F -> #|A| = r.

Definition x137_sunflower (T : finType) (petals : seq {set T}) : Prop :=
  exists core : {set T},
    forall A B : {set T},
      A \in petals -> B \in petals -> A != B -> A :&: B = core.

(** ** X137 statements *****************************************************)

(** Corpus row: studies:std_erd_s_rado_sunflower_conjecture
    Site: none
    Review: none
    English statement: (Erdos and Rado, sunflower conjecture)
      For every petal count k at least 2 there is a constant C depending only on k such that
      every family of sets, all of the same size r, with more than C to the power r members
      contains k distinct members forming a sunflower, i.e. any two of them meet in the same
      common core.
    Definitions: [x137_uniform F r] - every member of F has exactly r elements
      (hypergraph-theory/theories/conjectures/X137.v); [x137_sunflower petals] - there is a core
      set such that any two distinct entries of the list meet exactly in that core (same file).
    Notes: the k petals are presented as a duplicate-free list of members of F, so they are
      pairwise distinct.  BINDER ASSIGNMENT: the corpus statement_text reads "there is a
      constant C = C(r) depending only on r such that f_r(k) <= C^k"; the body here puts the
      constant on the PETAL COUNT and the SET SIZE in the exponent.  That is deliberate (audit
      fix 2026-07-18, meta/BLOCKED_RETARGETING_AUDIT.md, fresh-rows section): the opposite
      assignment follows from the 1960 Erdos-Rado sunflower LEMMA and carries none of the open
      content.  Recorded in meta/STATEMENT_IMPROVEMENTS.md. *)
Definition erdos_rado_sunflower_statement : Prop :=
  forall k : nat,
    2 <= k ->
    exists C : nat,
      forall (r : nat) (T : finType) (F : {set {set T}}),
        x137_uniform F r ->
        C ^ r < #|F| ->
        exists petals : seq {set T},
          [/\ size petals = k,
              uniq petals,
              (forall A : {set T}, A \in petals -> A \in F) &
              x137_sunflower petals].

