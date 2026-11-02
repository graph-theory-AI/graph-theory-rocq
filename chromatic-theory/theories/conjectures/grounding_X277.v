(** * Chromatic.conjectures.grounding_X277 -- grounding certificates for wave X277 (2026-11-02)

    - arxiv:2307.15048#00: hyp_inhabited at p = 1/2 (a = 1, b = 2), where G(n, 1/2) has positive mass for every n, and
      the statement gives its fg_whp clause there.  not_trivially_true drops the hypothesis 0 < p: the variant with
      the p = 0 endpoint added (G(n, 1) is K_n with probability 1, written as the p = 1 clause is) is false, since
      K_n needs n colours and the event's upper half then fails for every constant at arbitrarily large n, and it
      implies the statement.  The p = 1 clause itself is false ([g277_p_one_clause_false]: the edgeless graph is
      correspondence colourable with one colour, and n > c trunc_log 2 n for arbitrarily large n), the source's p = 1
      endpoint, informally "false as printed"; the gate keeps an unregistered refutation of the open row (a theorem
      of type ~ statement) out, and registering one is for Marc's decision.
    - erdos:1156: hyp_inhabited (an unbounded window exists, G(n, 1/2) has positive mass, and the statement gives
      its window); not_trivially_true: without "sufficiently slowly" the claim is false (the window n + 1 around 0
      contains chi(G) <= n always), and that variant implies the statement.
    - helper_sanity for [x277_correspondence_colourable]: at k = 3 it is X159's [x159_correspondence_3_colourable]
      (the Boolean and the Prop forms of the same notion), the edgeless graph is 1-colourable, and K_2 is not.
    - teeth for arxiv:2307.15048#00's event (Marcol's A3, O1): K_n needs n colours ([g277_Kn_needs_n], identity
      matchings), so the upper half of the event fails on K_n at n = 2 ^ c2.+1 for every constant c2
      ([g277_Kn_upper_fails]) and beyond any N ([g277_Kn_upper_fails_beyond]), which refutes the p = 0 clause. *)

From GTBase Require Import base common finite_graph.
From Chromatic.conjectures Require Import X159 X277.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** arxiv:2307.15048#00 *************************************************** *)

(* c * log2 n < n for arbitrarily large n (n = 2 ^ 2 ^ j) *)
Lemma g277_log_gap (c N : nat) : exists n : nat, N <= n /\ c * trunc_log 2 n < n.
Proof.
set j := (c + N).+1.
have hcj : c < j by rewrite /j ltnS leq_addr.
have hNj : N < j by rewrite /j ltnS leq_addl.
have hj : j < 2 ^ j := ltn_expl j (isT : 1 < 2).
have h2j : j.*2 <= 2 ^ j.
  have := ltn_expl j.-1 (isT : 1 < 2).
  rewrite /j /= => h.
  by rewrite expnS -mul2n leq_pmul2l.
exists (2 ^ (2 ^ j)); split.
  apply: (leq_trans (ltnW hNj)); apply: (leq_trans (ltnW hj)).
  exact: ltnW (ltn_expl (2 ^ j) (isT : 1 < 2)).
rewrite trunc_expnK //.
apply: (@leq_trans (2 ^ c * 2 ^ j)).
  by rewrite ltn_pmul2r ?expn_gt0 //; exact: ltn_expl.
rewrite -expnD leq_pexp2l //.
apply: (leq_trans _ h2j).
by rewrite -addnn leq_add2r ltnW.
Qed.


(* the edgeless graph on 'I_n is correspondence colourable with one colour: no edge is ever checked *)
Lemma g277_edgeless_colourable1 (n : nat) :
  x277_correspondence_colourable (fg_labelled_sgraph (set0 : {set {set 'I_n}})) 1.
Proof.
apply/forallP=> C; apply/implyP=> _; apply/existsP; exists [ffun _ => ord0].
apply/forallP=> u; apply/forallP=> v; apply/implyP.
by rewrite /edge_rel /= /fg_srel /fg_edge_set_rel !in_set0 !orbF andbF.
Qed.


(* the p = 1 clause of the statement (G(n, 0) is the edgeless graph) is false *)
Lemma g277_p_one_clause_false :
  ~ (exists c1 c2 : nat, [/\ 0 < c1, 0 < c2 &
     eventually (fun n => let G := fg_labelled_sgraph (set0 : {set {set 'I_n}}) in
       [forall k : 'I_n.+1, x277_correspondence_colourable G k ==> (n <= c1 * k * trunc_log 2 n)] &&
       [exists k : 'I_(c2 * n).+1, x277_correspondence_colourable G k && (k * trunc_log 2 n <= c2 * n)])]).
Proof.
case=> c1 [c2 [_ _ [N hN]]].
have [n [Nn gap]] := g277_log_gap c1 N.+1.
have n1 : 1 < n.+1 by rewrite ltnS (leq_trans _ Nn).
case/andP: (hN n (ltnW Nn)) => low _.
have := forallP low (Ordinal n1).
rewrite /= g277_edgeless_colourable1 /= muln1 => h.
by move: gap; rewrite ltnNge h.
Qed.


(** hyp_inhabited: 0 < a < b at a = 1, b = 2; G(n, 1/2) has positive total weight; the statement gives its fg_whp
    clause there. *)
Definition g277_dp_hyp_claim : Prop :=
  [/\ 0 < 1, 1 < 2, (forall n : nat, 0 < fg_total_weight (@fg_gnp_weight (2 - 1) 2 n)) &
   (correspondence_chromatic_random_graph_theta_n_over_log_n_statement ->
     exists c1 c2 : nat, [/\ 0 < c1, 0 < c2 &
       @fg_whp (fun n : nat => {set {set 'I_n}}) (fun n => @fg_gnp_weight (2 - 1) 2 n)
         (fun n E => let G := fg_labelled_sgraph E in
            [forall k : 'I_n.+1, x277_correspondence_colourable G k ==> (n <= c1 * k * trunc_log 2 n)] &&
            [exists k : 'I_(c2 * n).+1, x277_correspondence_colourable G k && (k * trunc_log 2 n <= c2 * n)])])].

Theorem g277_dp_hyp_inhabited : g277_dp_hyp_claim.
Proof.
split=> //; last by case=> h _; exact: h 1 2 isT isT.
move=> n; rewrite /fg_total_weight (bigD1 set0) //=.
apply: (leq_trans _ (leq_addr _ _)).
by rewrite /fg_gnp_weight /fg_valid_labelled_edges sub0set cards0 /= !exp1n.
Qed.


(** ** helper_sanity: x277_correspondence_colourable ****************************** *)

(* at k = 3 the Boolean helper is X159's Prop notion: an assignment as a set or as a function, the same three clauses *)
Lemma g277_cc_x159 (G : sgraph) :
  x277_correspondence_colourable G 3 <-> x159_correspondence_3_colourable G.
Proof.
split.
- move=> h C [hs [hf hi]].
  pose S := [set p : (G * 'I_3) * (G * 'I_3) | C p.1.1 p.2.1 p.1.2 p.2.2].
  have hS : [&& [forall u : G, [forall v : G, (u -- v) ==> [forall a : 'I_3, [forall b : 'I_3,
           (((u, a), (v, b)) \in S) == (((v, b), (u, a)) \in S)]]]],
        [forall u : G, [forall v : G, (u -- v) ==> [forall a : 'I_3, [forall b1 : 'I_3, [forall b2 : 'I_3,
           ((((u, a), (v, b1)) \in S) && (((u, a), (v, b2)) \in S)) ==> (b1 == b2)]]]]] &
        [forall u : G, [forall v : G, (u -- v) ==> [forall a1 : 'I_3, [forall a2 : 'I_3, [forall b : 'I_3,
           ((((u, a1), (v, b)) \in S) && (((u, a2), (v, b)) \in S)) ==> (a1 == a2)]]]]]].
    apply/and3P; split.
    + apply/forallP=> u; apply/forallP=> v; apply/implyP=> uv.
      apply/forallP=> a; apply/forallP=> b; rewrite !inE /=.
      by rewrite (hs u v uv a b).
    + apply/forallP=> u; apply/forallP=> v; apply/implyP=> uv.
      apply/forallP=> a; apply/forallP=> b1; apply/forallP=> b2; apply/implyP.
      rewrite !inE /= => /andP [h1 h2]; apply/eqP; exact: hf u v a b1 b2 uv h1 h2.
    + apply/forallP=> u; apply/forallP=> v; apply/implyP=> uv.
      apply/forallP=> a1; apply/forallP=> a2; apply/forallP=> b; apply/implyP.
      rewrite !inE /= => /andP [h1 h2]; apply/eqP; exact: hi u v a1 a2 b uv h1 h2.
  have /existsP [col hcol] := implyP (forallP h S) hS.
  exists col => u v uv.
  by have := implyP (forallP (forallP hcol u) v) uv; rewrite inE.
- move=> h; apply/forallP=> S; apply/implyP => /and3P [hs hf hi].
  pose C := fun (u v : G) (a b : 'I_3) => ((u, a), (v, b)) \in S.
  have [|col hcol] := h C.
    split; [|split].
    + move=> u v uv a b.
      by apply/eqP; move: hs; move/forallP/(_ u)/forallP/(_ v)/implyP/(_ uv)/forallP/(_ a)/forallP/(_ b).
    + move=> u v a b1 b2 uv h1 h2; apply/eqP.
      move: hf; move/forallP/(_ u)/forallP/(_ v)/implyP/(_ uv)/forallP/(_ a)/forallP/(_ b1)/forallP/(_ b2)/implyP.
      by apply; rewrite /C in h1 h2; rewrite h1 h2.
    + move=> u v a1 a2 b uv h1 h2; apply/eqP.
      move: hi; move/forallP/(_ u)/forallP/(_ v)/implyP/(_ uv)/forallP/(_ a1)/forallP/(_ a2)/forallP/(_ b)/implyP.
      by apply; rewrite /C in h1 h2; rewrite h1 h2.
  apply/existsP; exists [ffun u => col u].
  apply/forallP=> u; apply/forallP=> v; apply/implyP=> uv.
  by rewrite !ffunE; exact: hcol u v uv.
Qed.


(* K_2 is not 1-colourable: match the single colours of its two ends *)
Lemma g277_K2_not_1 : ~~ x277_correspondence_colourable 'K_2 1.
Proof.
pose v0 : 'K_2 := ord0.
pose v1 : 'K_2 := Ordinal (isT : 1 < 2).
pose c : 'I_1 := ord0.
pose S := [set ((v0, c), (v1, c)); ((v1, c), (v0, c))].
apply/negP => /forallP /(_ S) /implyP h.
have : [exists col : {ffun ('K_2) -> 'I_1}, [forall u : ('K_2), [forall v : ('K_2),
          (u -- v) ==> (((u, col u), (v, col v)) \notin S)]]].
  apply: h; apply/and3P; split.
  - apply/forallP=> u; apply/forallP=> v; apply/implyP=> uv.
    apply/forallP=> a; apply/forallP=> b.
    rewrite (ord1 a) (ord1 b) !inE !xpair_eqE !eqxx !andbT /=.
    by rewrite orbC andbC [(v == v1) && _]andbC.
  - apply/forallP=> u; apply/forallP=> v; apply/implyP=> uv.
    apply/forallP=> a; apply/forallP=> b1; apply/forallP=> b2; apply/implyP=> _.
    by rewrite (ord1 b1) (ord1 b2).
  - apply/forallP=> u; apply/forallP=> v; apply/implyP=> uv.
    apply/forallP=> a1; apply/forallP=> a2; apply/forallP=> b; apply/implyP=> _.
    by rewrite (ord1 a1) (ord1 a2).
case/existsP=> col /forallP /(_ v0) /forallP /(_ v1) /implyP hc.
have e01 : v0 -- v1 by [].
move: (hc e01); rewrite (ord1 (col v0)) (ord1 (col v1)).
by rewrite !inE eqxx.
Qed.


Definition g277_cc_helper_claim : Prop :=
  [/\ forall G : sgraph, x277_correspondence_colourable G 3 <-> x159_correspondence_3_colourable G,
      forall n : nat, x277_correspondence_colourable (fg_labelled_sgraph (set0 : {set {set 'I_n}})) 1 &
      ~~ x277_correspondence_colourable ('K_2) 1].

Theorem g277_cc_helper_sanity : g277_cc_helper_claim.
Proof. split; [exact: g277_cc_x159 | exact: g277_edgeless_colourable1 | exact: g277_K2_not_1]. Qed.

(** ** arxiv:2307.15048#00: teeth (Marcol's A3, O1) and not_trivially_true ************************** *)

(* K_n is not correspondence colourable with fewer than n colours: the identity matching on every edge *)
Lemma g277_Kn_needs_n (n k : nat) : x277_correspondence_colourable ('K_n) k -> n <= k.
Proof.
move=> h.
pose S := [set p : ('K_n * 'I_k) * ('K_n * 'I_k) | (p.1.1 != p.2.1) && (p.1.2 == p.2.2)].
have hS : [&& [forall u : ('K_n), [forall v : ('K_n), (u -- v) ==> [forall a : 'I_k, [forall b : 'I_k,
           (((u, a), (v, b)) \in S) == (((v, b), (u, a)) \in S)]]]],
        [forall u : ('K_n), [forall v : ('K_n), (u -- v) ==> [forall a : 'I_k, [forall b1 : 'I_k, [forall b2 : 'I_k,
           ((((u, a), (v, b1)) \in S) && (((u, a), (v, b2)) \in S)) ==> (b1 == b2)]]]]] &
        [forall u : ('K_n), [forall v : ('K_n), (u -- v) ==> [forall a1 : 'I_k, [forall a2 : 'I_k, [forall b : 'I_k,
           ((((u, a1), (v, b)) \in S) && (((u, a2), (v, b)) \in S)) ==> (a1 == a2)]]]]]].
  apply/and3P; split.
  - apply/forallP=> u; apply/forallP=> v; apply/implyP=> _; apply/forallP=> a; apply/forallP=> b.
    by rewrite !inE /= [v == u]eq_sym [b == a]eq_sym.
  - apply/forallP=> u; apply/forallP=> v; apply/implyP=> _; apply/forallP=> a; apply/forallP=> b1; apply/forallP=> b2.
    by apply/implyP; rewrite !inE /= => /andP [/andP [_ /eqP <-] /andP [_ /eqP <-]].
  - apply/forallP=> u; apply/forallP=> v; apply/implyP=> _; apply/forallP=> a1; apply/forallP=> a2; apply/forallP=> b.
    by apply/implyP; rewrite !inE /= => /andP [/andP [_ /eqP ->] /andP [_ /eqP ->]].
have /existsP [col hcol] := implyP (forallP h S) hS.
have inj : injective col.
  move=> u v e; apply/eqP; apply: contraTT isT => uv; apply/negP => _.
  have := implyP (forallP (forallP hcol u) v); rewrite /edge_rel /= uv => /(_ isT).
  by rewrite !inE /= uv e eqxx.
by have := leq_card col inj; rewrite !card_ord.
Qed.

(* the upper half of the event fails on K_n at n = 2 ^ c2.+1, for every constant c2 (Marcol's probe at one order) *)
Lemma g277_Kn_upper_fails (c2 : nat) :
  exists n : nat, ~~ [exists k : 'I_(c2 * n).+1,
    x277_correspondence_colourable ('K_n) k && (k * trunc_log 2 n <= c2 * n)].
Proof.
exists (2 ^ c2.+1); apply/existsP => -[k /andP [ck le]].
have nk := g277_Kn_needs_n ck.
move: le; rewrite trunc_expnK // => le.
have := leq_trans (leq_mul nk (leqnn c2.+1)) le.
by rewrite [c2 * _]mulnC leq_pmul2l ?expn_gt0 // ltnn.
Qed.

(* ... and beyond any N: at n = 2 ^ (c2.+1 + N) *)
Lemma g277_Kn_upper_fails_beyond (c2 N : nat) :
  exists n : nat, N <= n /\ ~~ [exists k : 'I_(c2 * n).+1,
    x277_correspondence_colourable ('K_n) k && (k * trunc_log 2 n <= c2 * n)].
Proof.
exists (2 ^ (c2.+1 + N)); split.
  apply: ltnW; apply: (leq_ltn_trans (leq_addl c2.+1 N)); exact: ltn_expl.
apply/existsP => -[k /andP [ck le]].
have nk := g277_Kn_needs_n ck.
move: le; rewrite trunc_expnK // => le.
have := leq_trans (leq_mul nk (leqnn (c2.+1 + N))) le.
rewrite [c2 * _]mulnC leq_pmul2l ?expn_gt0 //.
by rewrite leqNgt addSn ltnS leq_addr.
Qed.

(* the p = 0 endpoint: G(n, 1) is the complete graph K_n with probability 1, written as the p = 1 clause is *)
Definition g277_dp_p_zero_clause : Prop :=
  exists c1 c2 : nat, [/\ 0 < c1, 0 < c2 &
     eventually (fun n => let G := ('K_n) in
       [forall k : 'I_n.+1, x277_correspondence_colourable G k ==> (n <= c1 * k * trunc_log 2 n)] &&
       [exists k : 'I_(c2 * n).+1, x277_correspondence_colourable G k && (k * trunc_log 2 n <= c2 * n)])].

Lemma g277_p_zero_clause_false : ~ g277_dp_p_zero_clause.
Proof.
case=> c1 [c2 [_ _ [N hN]]].
have [n [Nn hn]] := g277_Kn_upper_fails_beyond c2 N.
case/andP: (hN n Nn) => _ up.
by move: hn; rewrite up.
Qed.

(** not_trivially_true for arxiv:2307.15048#00: drop the hypothesis 0 < p.  The variant with the p = 0 endpoint
    added is false (K_n), and it implies the statement. *)
Definition g277_dp_ntt_claim : Prop :=
  ~ (correspondence_chromatic_random_graph_theta_n_over_log_n_statement /\ g277_dp_p_zero_clause) /\
  (correspondence_chromatic_random_graph_theta_n_over_log_n_statement /\ g277_dp_p_zero_clause ->
     correspondence_chromatic_random_graph_theta_n_over_log_n_statement).

Theorem g277_dp_not_trivially_true : g277_dp_ntt_claim.
Proof.
split; last by case.
by case=> _; exact: g277_p_zero_clause_false.
Qed.

(** ** erdos:1156 ****************************************************************** *)

(* chi(G) <= |G| (coq-graph-theory's leq_chi) *)
Lemma g277_chi_le_card (G : sgraph) : χ([set: G]) <= #|G|.
Proof.
by rewrite -cardsT; exact: leq_chi.
Qed.

(* G(n, 1/2) has positive total weight: the empty edge set has weight 1 *)
Lemma g277_gnp_half_total_pos (n : nat) : 0 < fg_total_weight (@fg_gnp_weight 1 2 n).
Proof.
rewrite /fg_total_weight (bigD1 set0) //=.
apply: (leq_trans _ (leq_addr _ _)).
by rewrite /fg_gnp_weight /fg_valid_labelled_edges sub0set cards0 /= !exp1n.
Qed.

(** hyp_inhabited: an unbounded window exists, the mass is positive, and the statement gives its window. *)
Definition g277_win_hyp_claim : Prop :=
  [/\ (forall M : nat, eventually (fun n => M <= n)),
      (forall n : nat, 0 < fg_total_weight (@fg_gnp_weight 1 2 n)) &
      (random_graph_chromatic_number_not_concentrated_in_slowly_growing_windows_statement ->
         exists w : nat -> nat, forall M : nat, eventually (fun n => M <= w n))].

Theorem g277_win_hyp_inhabited : g277_win_hyp_claim.
Proof.
split; [by move=> M; exists M | exact: g277_gnp_half_total_pos |].
by case=> w [hw _]; exists w.
Qed.

(** not_trivially_true: the claim for EVERY unbounded window (dropping "sufficiently slowly") is false, at w n = n + 1
    and f = 0, and it implies the statement (take w = id). *)
Definition g277_win_every_unbounded_window : Prop :=
  forall w : nat -> nat, (forall M : nat, eventually (fun n => M <= w n)) ->
    forall f : nat -> nat, eventually (fun n =>
      0 < fg_total_weight (@fg_gnp_weight 1 2 n) /\
      2 * fg_event_weight (@fg_gnp_weight 1 2 n)
            (fun E => let G := fg_labelled_sgraph E in
               (f n < χ([set: G]) + w n) && (χ([set: G]) < f n + w n))
        < fg_total_weight (@fg_gnp_weight 1 2 n)).

Definition g277_win_ntt_claim : Prop :=
  ~ g277_win_every_unbounded_window /\
  (g277_win_every_unbounded_window ->
     random_graph_chromatic_number_not_concentrated_in_slowly_growing_windows_statement).

Theorem g277_win_not_trivially_true : g277_win_ntt_claim.
Proof.
split; last first.
  by move=> V; exists id; split; [move=> M; exists M | apply: V => M; exists M].
move=> V.
have [N hN] := V (fun n => n.+1) (fun M => ex_intro _ M (fun n hn => leqW hn)) (fun _ => 0).
have [_] := hN N (leqnn N).
have -> : fg_event_weight (@fg_gnp_weight 1 2 N)
            (fun E => let G := fg_labelled_sgraph E in
               (0 < χ([set: G]) + N.+1) && (χ([set: G]) < 0 + N.+1))
          = fg_total_weight (@fg_gnp_weight 1 2 N).
  rewrite /fg_event_weight /fg_total_weight; apply: eq_bigl => E /=.
  rewrite addnS ltn0Sn add0n ltnS /=.
  by have := g277_chi_le_card (fg_labelled_sgraph E); rewrite card_ord.
by rewrite ltnNge leq_pmull.
Qed.


Print Assumptions g277_dp_hyp_inhabited.
Print Assumptions g277_p_one_clause_false.
Print Assumptions g277_dp_not_trivially_true.
Print Assumptions g277_cc_helper_sanity.
Print Assumptions g277_win_hyp_inhabited.
Print Assumptions g277_win_not_trivially_true.
Print Assumptions g277_Kn_needs_n.
Print Assumptions g277_Kn_upper_fails.
Print Assumptions g277_Kn_upper_fails_beyond.
Print Assumptions g277_p_zero_clause_false.
