(** * Infinite.conjectures.grounding_X228 — grounding lemmas for wave X228.

    Qed-closed, axiom-free sanity results for
    [infinite_tournament_induced_saturation_statement] and for the four notions
    it introduces ([x228_ctournament], [x228_transitive], [x228_induced_copy],
    [x228_lf_perturbation]).

    Contents:
      - NON-VACUITY of the HYPOTHESIS: the cyclic triangle [C3_di]
        (base/theories/common.v) is a finite tournament that is NOT transitive,
        so the statement really quantifies over something.
      - GUARD HAS TEETH: the [~ x228_transitive] guard removes genuine cases
        (the linear order on three points is a transitive tournament), and it
        must: for a transitive T no T-free infinite tournament exists.
      - NON-VACUITY of [x228_ctournament] and [x228_induced_copy]: the strict
        order on [nat] is a countable tournament, and the transitive triangle
        embeds in it as an induced copy.
      - The T-FREE clause is satisfiable: the cyclic triangle has NO induced copy
        in the strict order on [nat].
      - The universally quantified [forall R'] is NOT vacuous: flipping the arc
        between two distinct vertices of a countable tournament produces a
        genuine locally finite perturbation ([x228_flip_perturbation]).  Without
        the nonemptiness clause of [x228_lf_perturbation] the statement would be
        self-contradictory, and [x228_flip_not_lf_self] records that [R] is not
        a perturbation of itself. *)

From GTBase Require Import base.
From Infinite Require Import conjectures.X228.
From mathcomp Require Import all_boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The strict order on [nat] as a countable tournament *)

Definition x228_lt : rel nat := fun x y => x < y.

Lemma x228_nat_trichotomy (x y : nat) : (x != y) = (x < y) (+) (y < x).
Proof.
by rewrite neq_ltn; case: ltngtP.
Qed.

Lemma x228_lt_ctournament : x228_ctournament x228_lt.
Proof. by split=> [x|x y]; rewrite /x228_lt ?ltnn //; exact: x228_nat_trichotomy. Qed.

(** ** The transitive tournament on three points *)

Definition x228_lt3_rel : rel 'I_3 := fun i j => (val i < val j)%N.
Definition x228_lt3 : diGraph := DiGraph x228_lt3_rel.

Lemma x228_lt3_tournament : tournament x228_lt3.
Proof.
split=> [i|i j]; rewrite /edge_rel /= /x228_lt3_rel ?ltnn //.
by rewrite -val_eqE; exact: x228_nat_trichotomy.
Qed.

(** TEETH — the [~ x228_transitive] guard removes genuine cases: the linear
    order on three points IS a transitive tournament, and the source excludes
    exactly such T (every infinite tournament contains large transitive
    subtournaments, so no T-free countable tournament exists for them). *)
Lemma x228_lt3_transitive : x228_transitive x228_lt3.
Proof.
by move=> i j k; rewrite /edge_rel /= /x228_lt3_rel; exact: ltn_trans.
Qed.

(** ** Non-vacuity of the hypothesis *)

(** [C3_di] (base/theories/common.v) is a finite tournament ... *)
Lemma x228_C3_tournament : tournament C3_di.
Proof. exact: tournament_C3_di. Qed.

(** ... which is NOT transitive, so the statement's hypothesis is satisfiable. *)
Lemma x228_C3_not_transitive : ~ x228_transitive C3_di.
Proof.
move=> tr.
by have := tr (@Ordinal 3 0 isT) (@Ordinal 3 1 isT) (@Ordinal 3 2 isT) isT isT.
Qed.

(** ** Non-vacuity and teeth of [x228_induced_copy] *)

(** The transitive triangle has an induced copy in the strict order on nat. *)
Lemma x228_lt3_in_lt : x228_induced_copy x228_lt3 x228_lt.
Proof. by exists (fun i : x228_lt3 => val i); split=> //; exact: val_inj. Qed.

(** ... but the CYCLIC triangle has none: "T-free countable tournament" is a
    satisfiable requirement, so the middle conjunct of the conclusion is not
    vacuous. *)
Lemma x228_C3_not_in_lt : ~ x228_induced_copy C3_di x228_lt.
Proof.
case=> f [_ Hf].
have a01 : x228_lt (f (@Ordinal 3 0 isT)) (f (@Ordinal 3 1 isT)).
  by rewrite -Hf.
have a12 : x228_lt (f (@Ordinal 3 1 isT)) (f (@Ordinal 3 2 isT)).
  by rewrite -Hf.
have a20 : x228_lt (f (@Ordinal 3 2 isT)) (f (@Ordinal 3 0 isT)).
  by rewrite -Hf.
by move: (ltn_trans (ltn_trans a01 a12) a20); rewrite ltnn.
Qed.

(** ** Locally finite perturbations exist *)

(** Flip the arc between [a] and [b], leaving every other pair alone. *)
Definition x228_flip (R : rel nat) (a b : nat) : rel nat :=
  fun x y => if ((x == a) && (y == b)) || ((x == b) && (y == a))
             then ~~ R x y else R x y.

Lemma x228_flip_cond_sym (a b x y : nat) :
  ((x == a) && (y == b)) || ((x == b) && (y == a))
  = ((y == a) && (x == b)) || ((y == b) && (x == a)).
Proof. by case: (x == a); case: (x == b); case: (y == a); case: (y == b). Qed.

Lemma x228_flip_ctournament (R : rel nat) (a b : nat) :
  a != b -> x228_ctournament R -> x228_ctournament (x228_flip R a b).
Proof.
move=> ab [irr tot]; split=> [x|x y]; rewrite /x228_flip.
  case: ifP => [|_]; last exact: irr.
  by case/orP => /andP[/eqP ea /eqP eb]; move: ab; rewrite -ea -eb eqxx.
rewrite -(x228_flip_cond_sym a b x y); case: ifP => _; last exact: tot.
by rewrite addNb addbN negbK; exact: tot.
Qed.

Lemma x228_flip_perturbation (R : rel nat) (a b : nat) :
  a != b -> x228_ctournament R -> x228_lf_perturbation R (x228_flip R a b).
Proof.
move=> ab cR; split; first exact: x228_flip_ctournament.
  exists a, b; split=> //; rewrite /x228_flip !eqxx /=.
  by case: (R a b).
move=> v; exists (maxn a b).+1 => u Hu.
have au : a < u by apply: leq_ltn_trans Hu; exact: leq_maxl.
have bu : b < u by apply: leq_ltn_trans Hu; exact: leq_maxr.
by rewrite /x228_flip (gtn_eqF au) (gtn_eqF bu) !andbF.
Qed.

(** TEETH — the NONEMPTINESS clause is load-bearing: a countable tournament is
    NOT a locally finite perturbation of itself.  Without that clause the
    statement would assert both "R is T-free" and "R contains T". *)
Lemma x228_flip_not_lf_self (R : rel nat) : ~ x228_lf_perturbation R R.
Proof. by case=> _ [x [y [_]]]; rewrite eqxx. Qed.

Print Assumptions infinite_tournament_induced_saturation_statement.
Print Assumptions x228_C3_not_transitive.
Print Assumptions x228_C3_not_in_lt.
Print Assumptions x228_flip_perturbation.
Print Assumptions x228_lt3_transitive.
