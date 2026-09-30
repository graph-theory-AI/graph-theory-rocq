(** * GTMisc.conjectures.grounding_X227 -- grounding lemmas for wave X227

    Qed-closed sanity results for the hat-guessing and random-subset vocabulary of
    [GTMisc.conjectures.X227].

    - NON-VACUITY: the players always win the ONE-colour hat game on a nonempty graph
      ([x227_hat_win_1]), so the hat guessing number is at least 1; ['K_1] is
      0-degenerate and ['K_3] has minimum degree exactly 2, so the antecedents of the two
      hat rows are satisfiable; ['K_3] has independence number 1 and order 3, so it
      satisfies the hypothesis of the binomial-gap row with alpha = 1/3, which lies in
      the range (0,1/2).
    - THE GUARDS HAVE TEETH: the two-colour game on ['K_1] is LOST, so
      [x227_hat_guessing_le 'K_1 1] holds and the bound cannot be lowered to 0; the
      binomial-gap inequality FAILS for eps = 1 on every instance of the class, so the
      size of eps is real content and the conclusion is not an empty inequality.
    - THE BLOCKED LEVINE PLACEHOLDERS: the hypothesis class of the two placeholder
      bodies is inhabited by the constant sequence 1/2, which does NOT tend to 0 --
      the machine-checked form of the "refutable as written" note of those two rows
      (recorded as two separate lemmas; no refutation of a statement is committed). *)

From GTBase Require Import base.
From GTMisc.conjectures Require Import X227.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Degrees and independence numbers of complete graphs *)

Lemma x227_neigh_Kn (n : nat) (x : 'K_n.+1) : N(x) = [set~ x].
Proof. by apply/setP => y; rewrite !inE /edge_rel /= eq_sym. Qed.

Lemma x227_deg_Kn (n : nat) (x : 'K_n.+1) : #|N(x)| = n.
Proof. by rewrite x227_neigh_Kn cardsC1 card_ord. Qed.

Lemma x227_alpha_gt0 (G : sgraph) (x : G) : 0 < α([set: G]).
Proof. by rewrite -(cards1 x); apply: stabset_bound; rewrite in_stabsets subsetT stable1. Qed.

Lemma x227_alpha_Kn (n : nat) : α([set: 'K_n.+1]) = 1.
Proof.
apply/eqP; rewrite eqn_leq (x227_alpha_gt0 (ord0 : 'K_n.+1)) andbT.
case: (alphaP [set: 'K_n.+1]) => S HS.
have Hst : {in S &, forall u v, ~~ u -- v}.
  by apply/stableP; exact: maxstabset_stable HS.
apply/card_le1_eqP => x y xS yS; apply/eqP.
by move: (Hst x y xS yS); rewrite /edge_rel /= negbK eq_sym.
Qed.

(** ** The hat guessing game is inhabited, and its bounds have teeth *)

(** One colour is always guessed correctly: [HG(G) >= 1] on every nonempty graph. *)
Lemma x227_hat_win_1 (G : sgraph) (x : G) : x227_hat_guessing_win G 1.
Proof.
exists (fun _ _ => ord0); split; first by [].
by move=> c; exists x; rewrite (ord1 (c x)).
Qed.

(** Hence no graph with a vertex has hat guessing number 0. *)
Lemma x227_not_hat_le_0 (G : sgraph) (x : G) : ~ x227_hat_guessing_le G 0.
Proof. by move=> H; move: (H 1 (x227_hat_win_1 x)). Qed.

(** On the one-vertex graph the players LOSE with two or more colours: the vertex sees
    nothing, so its guess is the same for all colourings and the adversary avoids it. *)
Lemma x227_hat_le_K1 : x227_hat_guessing_le 'K_1 1.
Proof.
move=> [|[|q']] // [s [Hloc Hwin]].
pose v0 : 'K_1 := ord0.
pose z0 : 'I_q'.+2 := ord0.
pose z1 : 'I_q'.+2 := @Ordinal q'.+2 1 isT.
have Hz : z1 != z0 by apply/eqP; case.
have Hconst : forall c c' : {ffun 'K_1 -> 'I_q'.+2}, s v0 c = s v0 c'.
  move=> c c'; apply: Hloc => u Hu.
  by move: Hu; rewrite (ord1 u) /v0 /edge_rel /=.
pose a := s v0 [ffun _ => z0].
pose b := if a == z0 then z1 else z0.
have Hba : b != a.
  rewrite /b; case: ifP => [/eqP ->|/negbT H]; first exact: Hz.
  by rewrite eq_sym.
have [v Hv] := Hwin [ffun _ => b].
move: Hv; rewrite (ord1 v) ffunE (Hconst [ffun _ => b] [ffun _ => z0]) -/a => Hab.
by move: Hba; rewrite Hab eqxx.
Qed.

(** ['K_1] is 0-degenerate: the antecedent of the degeneracy rows is satisfiable. *)
Lemma x227_degenerate_K1 : k_degenerate 'K_1 0.
Proof.
move=> S _ /set0Pn[x xS]; exists x; split=> //.
have H0 : #|N(x)| = 0 := @x227_deg_Kn 0 x.
have Hsub : #|N(x) :&: S| <= #|N(x)| by apply: subset_leq_card; exact: subsetIl.
by rewrite H0 in Hsub.
Qed.

(** ['K_3] has minimum degree exactly 2: the antecedent of part (iii) is satisfiable. *)
Lemma x227_min_degree_K3 : x227_min_degree 'K_3 2.
Proof.
split=> [v|]; first by rewrite (@x227_deg_Kn 2 v).
by exists (ord0 : 'K_3); rewrite (@x227_deg_Kn 2).
Qed.

(** ** The binomial-gap row *)

Lemma x227_stable_sum_gt0 (G : sgraph) (x : G) : 0 < x227_stable_sum G.
Proof.
rewrite /x227_stable_sum (bigD1 [set: G]) //=.
by rewrite addn_gt0 (x227_alpha_gt0 x).
Qed.

(** ['K_3] satisfies the hypothesis with alpha = 1/3, which lies in (0,1/2). *)
Lemma x227_binomial_hypothesis_K3 :
  [/\ 0 < 1, 2 * 1 < 3, 0 < #|'K_3| & 3 * α([set: 'K_3]) = 1 * #|'K_3|].
Proof.
split=> //; first by rewrite card_ord.
by rewrite (@x227_alpha_Kn 2) card_ord.
Qed.

(** The conclusion is NOT an empty inequality: eps = 1 fails on every instance. *)
Lemma x227_binomial_gap_eps1_fails (a b : nat) (G : sgraph) :
  0 < a -> 2 * a < b -> 0 < #|G| ->
  ~ (x227_stable_sum G * (b * 1) + 1 * (b * (2 ^ #|G| * #|G|))
       <= a * 1 * (2 ^ #|G| * #|G|)).
Proof.
move=> Ha Hab Hn.
have Hab' : a < b by apply: leq_ltn_trans Hab; exact: leq_pmull.
have HP : 0 < 2 ^ #|G| * #|G| by rewrite muln_gt0 expn_gt0 Hn andbT.
apply/negP; rewrite -ltnNge mul1n muln1.
have H1 : a * (2 ^ #|G| * #|G|) < b * (2 ^ #|G| * #|G|).
  by rewrite ltn_mul2r HP Hab'.
by rewrite (leq_trans H1) // leq_addl.
Qed.

(** ** The blocked Levine placeholders are decoupled from their intended meaning *)

Definition x227_half : x227_rat_seq := fun _ => (1, 2).

Lemma x227_half_levine (cls : x227_family_class) : x227_levine_success cls x227_half.
Proof. by split=> [t|t t' _]. Qed.

Lemma x227_half_not_to_zero : ~ x227_rat_seq_to_zero x227_half.
Proof.
move=> /(_ 1 3 isT isT) [N HN].
by move: (HN N (leqnn N)).
Qed.

Print Assumptions x227_alpha_Kn.
Print Assumptions x227_hat_win_1.
Print Assumptions x227_hat_le_K1.
Print Assumptions x227_not_hat_le_0.
Print Assumptions x227_degenerate_K1.
Print Assumptions x227_min_degree_K3.
Print Assumptions x227_stable_sum_gt0.
Print Assumptions x227_binomial_hypothesis_K3.
Print Assumptions x227_binomial_gap_eps1_fails.
Print Assumptions x227_half_levine.
Print Assumptions x227_half_not_to_zero.
