(** * Minor.conjectures.grounding_X214 — grounding lemmas for wave X214.

    Qed-closed, axiom-free sanity results for the three X214 statements and for the
    subdivision vocabulary they introduce ([has_subdivision], in
    Minor.foundations.containment).

    Per statement: a NON-VACUITY witness (a concrete graph satisfying the hypotheses)
    and a GUARD-HAS-TEETH lemma (the obvious degenerate witness — a small complete
    graph — fails the guard, resp. fails the conclusion, so the body is not trivially
    true).  The source-recorded settled cases (Hadwiger for k <= 6, Hajos for k <= 4)
    are deep theorems; the trivial instance k = 1 of Hadwiger is proved instead. *)

From GTBase Require Import base.
From GraphTheory Require Import minor.
From Minor.foundations Require Import containment.
From Minor.conjectures Require Import X214.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Complete-graph toolkit ***********************************************)

(** Every vertex set of a complete graph is connected (any two distinct vertices
    are adjacent, so one restricted step suffices). *)
Lemma connected_Kn (n : nat) (A : {set 'K_n}) : connected A.
Proof.
move=> x y xA yA; case: (eqVneq x y) => [->|xy]; first exact: connect0.
by apply: connect1; rewrite /= xA yA /=; exact: xy.
Qed.

(** ['K_n] is k-connected in the Whitney sense as soon as [k < n]. *)
Lemma k_connected_Kn (n k : nat) : k < n -> k_connected 'K_n k.
Proof.
move=> lt; split; first by rewrite card_ord.
by move=> S _; exact: connected_Kn.
Qed.

(** ['K_n] has every ['K_m] with [m <= n] as a minor (the whole vertex set is a clique). *)
Lemma Kn_minor_Km (n m : nat) : m <= n -> minor 'K_n 'K_m.
Proof.
move=> le; apply: (@minor_of_clique _ [set: 'K_n]); last exact: Kn_clique.
by rewrite cardsT card_ord.
Qed.

(** The chromatic number of ['K_n] is [n]. *)
Lemma chi_Kn (n : nat) : χ([set: 'K_n]) = n.
Proof. by rewrite (chi_clique (@Kn_clique n)) cardsT card_ord. Qed.

(** ** bm-029 (Kelmans–Seymour) ********************************************)

(** NON-VACUITY: ['K_6] satisfies both hypotheses of
    [kelmans_seymour_k5_subdivision_statement] — it is 5-connected and it is not
    Wagner-planar (it already contains ['K_5] as a minor).  So the statement is not
    vacuously true. *)
Lemma X214_kelmans_seymour_nonvacuous :
  k_connected 'K_6 5 /\ ~ wagner_planar 'K_6.
Proof.
split; first exact: k_connected_Kn.
by case=> no5 _; apply: no5; exact: Kn_minor_Km.
Qed.

(** GUARD HAS TEETH (1): the 5-connectivity guard excludes the obvious degenerate
    witness ['K_3], which has too few vertices. *)
Lemma X214_kelmans_seymour_guard_K3 : ~ k_connected 'K_3 5.
Proof. by case; rewrite card_ord. Qed.

(** GUARD HAS TEETH (2): the non-planarity guard excludes ['K_4], which IS
    Wagner-planar; a K5 minor would need five vertices and a K3,3 minor six. *)
Lemma X214_kelmans_seymour_guard_K4 : wagner_planar 'K_4.
Proof.
split=> m; first by move: (minor_card m); rewrite !card_ord.
by move: (minor_card m); rewrite card_ord card_sum !card_ord.
Qed.

(** ** bm-041 (Hadwiger) ***************************************************)

(** NON-VACUITY: the hypothesis of [hadwiger_chromatic_clique_minor_statement] is
    satisfiable — ['K_3] has chromatic number exactly 3 — and the conclusion holds
    there. *)
Lemma X214_hadwiger_nonvacuous : χ([set: 'K_3]) = 3 /\ minor 'K_3 'K_3.
Proof. by split; [exact: chi_Kn | exact: Kn_minor_Km]. Qed.

(** GUARD HAS TEETH: the chromatic hypothesis is load-bearing — dropping it would
    make the body claim a ['K_4] minor for ['K_3], which is false. *)
Lemma X214_hadwiger_guard_teeth : ~ minor 'K_3 'K_4.
Proof. by apply: (@small_K_free 3 'K_3); rewrite card_ord. Qed.

(** SETTLED CASE (the trivial instance k = 1 of Hadwiger): a graph of chromatic
    number 1 has a vertex, hence a ['K_1] minor. *)
Lemma X214_hadwiger_k1 (G : sgraph) : χ([set: G]) = 1 -> minor G 'K_1.
Proof.
move=> chi1; case: (set_0Vmem [set: G]) => [E0|[x _]].
  by move: chi1; rewrite E0 chi0.
apply: (@minor_of_clique _ [set x]); first by rewrite cards1.
exact: clique1.
Qed.

(** ** bm-042 (Hajos for k = 5, 6) *****************************************)

(** NON-VACUITY: the hypotheses of [hajos_k5_k6_subdivision_statement] are
    satisfiable at k = 5 — ['K_5] has chromatic number exactly 5 — and the
    conclusion holds there (every graph contains a subdivision of itself). *)
Lemma X214_hajos_nonvacuous :
  χ([set: 'K_5]) = 5 /\ has_subdivision 'K_5 'K_5.
Proof. by split; [exact: chi_Kn | exact: has_subdivision_refl]. Qed.

(** GUARD HAS TEETH: the chromatic hypothesis is load-bearing — ['K_3] contains NO
    subdivision of ['K_5], since a subdivision model embeds the five branch vertices
    injectively. *)
Lemma X214_hajos_guard_teeth : ~ has_subdivision 'K_3 'K_5.
Proof. by move/has_subdivision_card; rewrite !card_ord. Qed.

(** The [k = 5 \/ k = 6] guard has teeth too: at k = 7 the body would be FALSE,
    since Catlin's refutation applies; here we only record that the guard does
    exclude k = 7 syntactically, by exhibiting that 7 is neither 5 nor 6. *)
Lemma X214_hajos_guard_excludes_7 : ~ ((7 = 5) \/ (7 = 6)).
Proof. by case. Qed.

Print Assumptions kelmans_seymour_k5_subdivision_statement.
Print Assumptions hadwiger_chromatic_clique_minor_statement.
Print Assumptions hajos_k5_k6_subdivision_statement.
Print Assumptions X214_kelmans_seymour_nonvacuous.
Print Assumptions X214_kelmans_seymour_guard_K3.
Print Assumptions X214_kelmans_seymour_guard_K4.
Print Assumptions X214_hadwiger_nonvacuous.
Print Assumptions X214_hadwiger_guard_teeth.
Print Assumptions X214_hadwiger_k1.
Print Assumptions X214_hajos_nonvacuous.
Print Assumptions X214_hajos_guard_teeth.
