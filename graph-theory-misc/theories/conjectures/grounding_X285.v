(** * GTMisc.conjectures.grounding_X285 -- grounding certificates for wave X285 (2026-11-04)

    For each of the five rows: hyp_inhabited (the body's conditions hold at an instance, and the statement gives
    its consequence there) and not_trivially_true (a variant that drops one hypothesis is false and implies the
    statement).  X285.v has no local helper, so there is no helper_sanity certificate.
    - Weak Meyniel: K_1 is nonempty and connected.  Without "connected" the row is false: fewer than n cops lose
      on the edgeless graph on n vertices (the robber sits on a free vertex and never moves), and n = C + 1
      beats every bound C * n^(q-1) on c(G)^q.  This is the printed Conjecture 2 read literally.
    - Hat guessing and the Hadwiger number: K_1 has Hadwiger number 1.  Without the Hadwiger hypothesis the row
      asks one bound f(0) for every graph, false on K_(f(0)+1), where the players win with f(0) + 1 colours (each
      vertex guesses the colour that makes the colour sum congruent to its own index).
    - Universal vertex: HG(K_1) <= 1.  Without the bound on HG(G) the row asks one bound f(0) for every G', false
      on K_(f(0)) plus a universal vertex, a complete graph on f(0) + 1 vertices.
    - Locke: F_14^(1) of the record (its figure file F_14_1-new.graphml) is 3-connected, triangle-free and cubic
      with alpha = 5 < 42/8, so the class is not empty; the checks are by computation on its edge table.  Without
      3-connectivity the row is false: m disjoint copies of F_14^(1) are triangle-free and cubic, with alpha <= 5m
      on 14m vertices.
    - Meyniel synonym: as X217's Meyniel row (grounding_X217), at K_3 and on the edgeless graph on (C+1)^2
      vertices, where ceil(sqrt n) = C + 1. *)

From GTBase Require Import base asymptotics.
From GraphTheory Require Import coloring.
From GTMisc.foundations Require Import cops.
From GTMisc.conjectures Require Import X99 X227 X217 grounding_X217 X285.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Weak Meyniel *)

(* The edgeless graph on n vertices. *)
Definition g285_edgeless (n : nat) : sgraph :=
  @SGraph 'I_n (fun _ _ => false) (fun _ _ => erefl) (fun _ => erefl).

(* In the edgeless graph a cop move keeps every cop in place. *)
Lemma g285_edgeless_move (n j : nat) (C C' : cop_position (g285_edgeless n) j) :
  cop_move C C' -> C' = C.
Proof.
move=> /forallP h; apply/ffunP => i; move: (h i).
by rewrite /edge_rel /= orbF => /eqP ->.
Qed.

(* A robber on a vertex free of cops is never caught: he stays put. *)
Lemma g285_edgeless_escape (n j t : nat) (C : cop_position (g285_edgeless n) j) (r : g285_edgeless n) :
  ~~ captured C r -> cops_capture t C r = false.
Proof.
elim: t C => [|t IH] C nc /=; first by rewrite (negbTE nc).
rewrite (negbTE nc) /=; apply/negbTE/existsPn => C'; rewrite negb_and.
case mv: (cop_move C C') => //=; move: (g285_edgeless_move mv) => ->.
rewrite (negbTE nc) /=; apply/forallPn; exists r.
by rewrite /robber_move eqxx /= IH.
Qed.

(* Fewer than n cops lose on the edgeless graph on n vertices. *)
Lemma g285_edgeless_cops (n j : nat) : j < n -> ~ cops_win (g285_edgeless n) j.
Proof.
move=> jn [t /existsP [C0 /forallP win]].
have [r rC] : exists r : g285_edgeless n, r \notin codom C0.
  apply/existsP; rewrite -negb_forall; apply/negP => /forallP all.
  have sub : [set: g285_edgeless n] \subset [set x in codom C0].
    by apply/subsetP => x _; rewrite inE all.
  move: (subset_leq_card sub); rewrite cardsT card_ord => h.
  have h2 : #|[set x in codom C0]| <= size (codom C0) by rewrite cardsE card_size.
  have := leq_trans h h2; rewrite size_codom card_ord => nj.
  by move: (leq_ltn_trans nj jn); rewrite ltnn.
have nc : ~~ captured C0 r.
  by apply/existsPn => i; apply/eqP => e; move: rC; rewrite -e codom_f.
by move: (win r); rewrite g285_edgeless_escape.
Qed.

Definition g285_wm_hyp_claim : Prop :=
  [/\ 0 < #|'K_1|, connected [set: 'K_1], cop_number_le ('K_1) 1 &
      (weak_meyniel_cop_number_statement ->
         exists q C k : nat, 1 <= q /\ k ^ q <= C * #|'K_1| ^ (q - 1) /\ cop_number_le ('K_1) k)].

Theorem g285_wm_hyp_inhabited : g285_wm_hyp_claim.
Proof.
split; [by rewrite card_ord | exact: (@connected_Kn 1) | by exists 1; split; last exact: (@cops_win_Kn 0) |].
move=> [q [C [q1 h]]]; have [k [kq w]] := h ('K_1) (ltac:(by rewrite card_ord)) (@connected_Kn 1).
by exists q, C, k.
Qed.

(* The printed reading: every graph, without "connected". *)
Definition g285_wm_any_graph : Prop :=
  exists q C : nat, 1 <= q /\
    forall G : sgraph, 0 < #|G| ->
      exists k : nat, k ^ q <= C * #|G| ^ (q - 1) /\ cop_number_le G k.

Definition g285_wm_ntt_claim : Prop :=
  ~ g285_wm_any_graph /\ (g285_wm_any_graph -> weak_meyniel_cop_number_statement).

Theorem g285_wm_not_trivially_true : g285_wm_ntt_claim.
Proof.
split; last first.
  by move=> [q [C [q1 h]]]; exists q, C; split=> // G G0 _; exact: h.
move=> [q [C [q1 h]]].
have [k [kq [j [jk wj]]]] := h (g285_edgeless C.+1) (ltac:(by rewrite card_ord)).
have nj : C.+1 <= j by rewrite leqNgt; apply/negP => lt; exact: (g285_edgeless_cops lt wj).
move: kq; rewrite card_ord; case: q q1 {h} => // q' _; rewrite subn1 /= => kq.
have : C.+1 ^ q'.+1 <= C * C.+1 ^ q'.
  by apply: leq_trans kq; rewrite leq_exp2r //; exact: leq_trans nj jk.
by rewrite expnS leq_pmul2r ?expn_gt0 // ltnn.
Qed.

(** ** Hat guessing: shared lemmas *)

(* The modular identity behind the sum strategy. *)
Lemma g285_mod_cancel (m a x : nat) : x < m -> ((x + a) %% m + m - a %% m) %% m = x.
Proof.
move=> xm; have m0 : 0 < m by exact: leq_ltn_trans (leq0n x) xm.
have am : a %% m <= m by exact: ltnW (ltn_pmod a m0).
rewrite -addnBA // modnDml {1}(divn_eq a m).
by rewrite -addnA -addnA subnKC // addnA modnDr -modnDmr modnMl addn0 modn_small.
Qed.

(* On K_(n+1) the players win with n + 1 colours: vertex v guesses the colour that makes the total colour sum
   congruent to v. *)
Lemma g285_hat_win_Kn (n : nat) : x227_hat_guessing_win 'K_n.+1 n.+1.
Proof.
pose g (v : 'K_n.+1) (c : {ffun ('K_n.+1) -> 'I_n.+1}) : 'I_n.+1 :=
  inord ((v + n.+1 - (\sum_(u | u != v) c u) %% n.+1) %% n.+1).
exists g; split.
  move=> v c c' agree; rewrite /g.
  have -> : \sum_(u | u != v) c u = \sum_(u | u != v) c' u.
    by apply: eq_bigr => u uv; rewrite (agree u) // /edge_rel /= eq_sym.
  by [].
move=> c; set w : 'K_n.+1 := inord ((\sum_u c u) %% n.+1).
exists w; apply: val_inj; rewrite /g /= inordK ?ltn_pmod //.
have wv : (w : nat) = (c w + \sum_(u < n.+1 | u != w) c u) %% n.+1.
  by rewrite -(bigD1 (P := xpredT) w) // /w inordK // ltn_pmod.
by rewrite {1}wv g285_mod_cancel.
Qed.

(* The sum strategy on any nonempty complete graph, with #|G| colours, vertices indexed by enum_rank. *)
Lemma g285_hat_win_complete (G : sgraph) :
  0 < #|G| -> (forall x y : G, x != y -> x -- y) -> x227_hat_guessing_win G #|G|.
Proof.
move=> m0 cpl.
pose g (v : G) (c : {ffun G -> 'I_#|G|}) : 'I_#|G| :=
  Ordinal (ltn_pmod (enum_rank v + #|G| - (\sum_(u | u != v) c u) %% #|G|) m0).
exists g; split.
  move=> v c c' agree; apply: val_inj => /=.
  have -> : \sum_(u | u != v) c u = \sum_(u | u != v) c' u.
    by apply: eq_bigr => u uv; rewrite (agree u) // cpl.
  by [].
move=> c; set w : G := enum_val (Ordinal (ltn_pmod (\sum_u c u) m0)).
exists w; apply: val_inj => /=.
have wv : (enum_rank w : nat) = (c w + \sum_(u | u != w) c u) %% #|G|.
  by rewrite enum_valK /= -(bigD1 (P := xpredT) w).
by rewrite {1}wv g285_mod_cancel.
Qed.

(* X227's win gives X99's winning strategy (the same game, functions for finite functions). *)
Lemma g285_win_227_99 (G : sgraph) (q : nat) : x227_hat_guessing_win G q -> x99_winning_hat_strategy G q.
Proof.
move=> [s [loc win]]; exists (fun v hats => s v [ffun x => hats x]); split.
  by move=> v a b ab; apply: loc => u uv; rewrite !ffunE ab.
by move=> hats; have [v e] := win [ffun x => hats x]; apply/existsP; exists v; rewrite e ffunE.
Qed.

(* K_1 has hat guessing number at most 1: the constant guess is beaten. *)
Lemma g285_K1_hat_le1 : x99_hat_guessing_number_at_most ('K_1) 1.
Proof.
move=> q q1 [g [loc win]].
pose c0 : 'I_q := Ordinal (ltnW q1).
pose c1 : 'I_q := Ordinal q1.
pose a : ('K_1) -> 'I_q := fun _ => if g ord0 (fun _ => c0) == c0 then c1 else c0.
have ga : g ord0 a = g ord0 (fun _ => c0) by apply: loc => u; rewrite (ord1 u) /edge_rel.
have := win a; case/existsP => v; rewrite (ord1 v) ga /a.
case: (g ord0 (fun=> c0) =P c0) => [e|ne]; last by move/eqP.
by rewrite e => /eqP /(congr1 val).
Qed.

(** ** Hat guessing bounded by a function of the Hadwiger number *)

Lemma g285_K1_hadwiger : x99_hadwiger_number ('K_1) 1.
Proof.
split; first by apply: (@minor.minor_of_clique _ [set: 'K_1] 1);
  [rewrite cardsT card_ord | move=> x y _ _; rewrite (ord1 x) (ord1 y) eqxx].
by move=> t /minor_card; rewrite !card_ord.
Qed.

Definition g285_hh_hyp_claim : Prop :=
  x99_hadwiger_number ('K_1) 1 /\
  (hat_guessing_hadwiger_function_bound_statement -> exists k : nat, x99_hat_guessing_number_at_most ('K_1) k).

Theorem g285_hh_hyp_inhabited : g285_hh_hyp_claim.
Proof.
split; first exact: g285_K1_hadwiger.
by move=> [f h]; exists (f 1); exact: h g285_K1_hadwiger.
Qed.

(* The variant without the Hadwiger hypothesis. *)
Definition g285_hh_no_minor : Prop :=
  exists f : nat -> nat, forall (G : sgraph) (h : nat), x99_hat_guessing_number_at_most G (f h).

Definition g285_hh_ntt_claim : Prop :=
  ~ g285_hh_no_minor /\ (g285_hh_no_minor -> hat_guessing_hadwiger_function_bound_statement).

Theorem g285_hh_not_trivially_true : g285_hh_ntt_claim.
Proof.
split; last by move=> [f h]; exists f => G k _; exact: h.
move=> [f h]; apply: (h ('K_(f 0).+1) 0 (f 0).+1 (ltnSn _)).
exact: g285_win_227_99 (g285_hat_win_Kn (f 0)).
Qed.

(** ** Hat guessing after adding a universal vertex *)

Lemma g285_K1_hat_le1_227 : x227_hat_guessing_le ('K_1) 1.
Proof.
move=> q w; rewrite leqNgt; apply/negP => q1.
exact: (g285_K1_hat_le1 q1 (g285_win_227_99 w)).
Qed.

Definition g285_au_hyp_claim : Prop :=
  x227_hat_guessing_le ('K_1) 1 /\
  (hat_guessing_add_universal_vertex_statement ->
     exists k : nat, x227_hat_guessing_le (add_node ('K_1) [set: 'K_1]) k).

Theorem g285_au_hyp_inhabited : g285_au_hyp_claim.
Proof.
split; first exact: g285_K1_hat_le1_227.
by move=> [f h]; exists (f 1); exact: h g285_K1_hat_le1_227.
Qed.

(* Adding a universal vertex to a complete graph gives a complete graph. *)
Lemma g285_add_node_Kn_complete (n : nat) (x y : add_node 'K_n [set: 'K_n]) : x != y -> x -- y.
Proof.
by case: x => [x|]; case: y => [y|] //= xy; rewrite /edge_rel /= ?inE.
Qed.

(* The variant without the bound on HG(G). *)
Definition g285_au_no_base : Prop :=
  exists f : nat -> nat, forall (G : sgraph) (m : nat), x227_hat_guessing_le (add_node G [set: G]) (f m).

Definition g285_au_ntt_claim : Prop :=
  ~ g285_au_no_base /\ (g285_au_no_base -> hat_guessing_add_universal_vertex_statement).

Theorem g285_au_not_trivially_true : g285_au_ntt_claim.
Proof.
split; last by move=> [f h]; exists f => G m _; exact: h.
move=> [f h]; have := h ('K_(f 0)) 0.
have c1 : #|add_node 'K_(f 0) [set: 'K_(f 0)]| = (f 0).+1 by rewrite card_option card_ord.
have win := @g285_hat_win_complete (add_node ('K_(f 0)) [set: 'K_(f 0)]) (ltac:(by rewrite c1))
  (@g285_add_node_Kn_complete (f 0)).
move=> /(_ _ win); by rewrite c1 ltnn.
Qed.

(** ** Locke: F_14^(1) and its disjoint copies *)

(* F_14^(1) of arXiv:1911.12471v2 (figures/F_14_1-new.graphml, drawn in its Figure 1): 14 vertices, 21 edges. *)
Definition g285_f14_table : seq (nat * nat) :=
  [:: (0, 1); (2, 1); (0, 3); (4, 5); (6, 7); (7, 0); (6, 2); (3, 4); (5, 1); (10, 11); (11, 8);
      (10, 9); (9, 12); (12, 8); (2, 10); (11, 3); (12, 13); (6, 13); (7, 8); (4, 13); (5, 9)].

Definition g285_f14_conn (a b : nat) : bool := ((a, b) \in g285_f14_table) || ((b, a) \in g285_f14_table).

Definition g285_f14_adj (x y : 'I_14) : bool := (x != y) && g285_f14_conn (val x) (val y).

Lemma g285_f14_sym : symmetric g285_f14_adj.
Proof. by move=> x y; rewrite /g285_f14_adj /g285_f14_conn eq_sym orbC. Qed.

Lemma g285_f14_irrefl : irreflexive g285_f14_adj.
Proof. by move=> x; rewrite /g285_f14_adj eqxx. Qed.

Definition g285_f14 : sgraph := SGraph g285_f14_sym g285_f14_irrefl.

Local Notation F := g285_f14.
Local Notation O14 i := (@Ordinal 14 i isT).

Definition g285_fv : seq F :=
  [:: O14 0; O14 1; O14 2; O14 3; O14 4; O14 5; O14 6; O14 7; O14 8; O14 9; O14 10; O14 11; O14 12; O14 13].

Lemma g285_fv_all (x : F) : x \in g285_fv.
Proof. by case: x => -[|[|[|[|[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]]]]] Hx //=; apply/eqP. Qed.

Lemma g285_fv_uniq : uniq g285_fv.
Proof. by vm_compute. Qed.

Arguments g285_fv : simpl never.

Lemma g285_f14_card : #|F| = 14.
Proof. exact: card_ord. Qed.

Lemma g285_f14_triangle_free : triangle_free F.
Proof.
have h : all (fun x => all (fun y => all (fun z => ~~ [&& x -- y, y -- z & z -- x]) g285_fv) g285_fv) g285_fv.
  by vm_compute.
move=> x y z xy yz zx.
move/allP: h => /(_ x (g285_fv_all x)) /allP /(_ y (g285_fv_all y)) /allP /(_ z (g285_fv_all z)).
by rewrite xy yz zx.
Qed.

Lemma g285_f14_cubic : regular F 3.
Proof.
have h : all (fun v => size [seq u <- g285_fv | v -- u] == 3) g285_fv by vm_compute.
move=> v; have e : N(v) =i [seq u <- g285_fv | v -- u].
  by move=> u; rewrite mem_filter g285_fv_all andbT inE.
rewrite (eq_card e) (card_uniqP (filter_uniq _ g285_fv_uniq)).
by apply/eqP; move/allP: h => /(_ v (g285_fv_all v)).
Qed.

(* Breadth-first reachability avoiding the vertices of [rem] (as grounding_X268's g268_reach). *)
Fixpoint g285_reach (rem : seq F) (n : nat) (R : seq F) : seq F :=
  if n is n'.+1 then
    g285_reach rem n'
      (R ++ [seq y <- g285_fv | (y \notin rem) && (y \notin R) && has (fun x => @edge_rel F x y) R])
  else R.

Lemma g285_reachP (S : {set F}) (rem : seq F) (r : F) :
  (forall y, (y \in S) = (y \in rem)) ->
  forall n R, (forall x, x \in R ->
      x \notin rem /\ connect (preliminaries.restrict_mem (mem ([set: F] :\: S)) (--)) r x) ->
  forall y, y \in g285_reach rem n R ->
    y \notin rem /\ connect (preliminaries.restrict_mem (mem ([set: F] :\: S)) (--)) r y.
Proof.
move=> hS; elim=> [|n IH] R hR y; first exact: hR.
move=> hy; apply: (IH (R ++ [seq y <- g285_fv | (y \notin rem) && (y \notin R) && has (fun x => @edge_rel F x y) R])
  _ y hy) => x.
rewrite mem_cat => /orP[/hR // |].
rewrite mem_filter => /andP[/andP[/andP[hx _] /hasP[z hz hzx]] _]; split=> //.
have [hzr hcz] := hR z hz; apply: connect_trans hcz (connect1 _).
by rewrite /preliminaries.restrict_mem /= !inE !hS hzr hx hzx.
Qed.

Definition g285_conn_ok (rem : seq F) : bool :=
  let r := head (O14 0) [seq y <- g285_fv | y \notin rem] in
  let L := g285_reach rem 14 [:: r] in
  all (fun y => (y \in rem) || (y \in L)) g285_fv.

Lemma g285_connected_of (S : {set F}) (rem : seq F) :
  (forall y, (y \in S) = (y \in rem)) -> g285_conn_ok rem -> connected ([set: F] :\: S).
Proof.
move=> hS; rewrite /g285_conn_ok; cbv zeta.
case hf: [seq y <- g285_fv | y \notin rem] => [|r f] hall.
  move=> x y hx _; exfalso; move: hx; rewrite !inE hS andbT => hx.
  by have := mem_filter (fun y => y \notin rem) x g285_fv; rewrite hf hx g285_fv_all in_nil.
have hr : r \notin rem by have := mem_head r f; rewrite -hf mem_filter => /andP[].
apply: (@connected_center _ r) => [y|]; last by rewrite !inE hS hr.
rewrite !inE hS andbT => hy.
have hreach : y \in g285_reach rem 14 [:: r].
  by move/allP: hall => /(_ y (g285_fv_all y)); rewrite (negbTE hy) orFb.
have [] // := @g285_reachP S rem r hS 14 [:: r] _ y hreach.
by move=> x; rewrite inE => /eqP ->; split=> //; exact: connect0.
Qed.

Lemma g285_conn_ok2 :
  all (fun a => all (fun b => g285_conn_ok [:: a; b]) g285_fv) g285_fv && g285_conn_ok [::].
Proof. by vm_compute. Qed.

Lemma g285_f14_three_connected : k_connected F 3.
Proof.
split; first by rewrite card_ord.
move=> S hS; have [h2 h0] := andP g285_conn_ok2.
have ok2 a b : g285_conn_ok [:: a; b].
  by move/allP: h2 => /(_ a (g285_fv_all a)) /allP /(_ b (g285_fv_all b)).
have : #|S| = 0 \/ #|S| = 1 \/ #|S| = 2 by move: hS; case: #|S| => [|[|[|n]]]; auto.
case=> [/cards0_eq -> | [/eqP/cards1P [a ->] | /eqP/cards2P [a [b [_ ->]]]]].
- by apply: (@g285_connected_of _ [::] _ h0) => y; rewrite !inE.
- by apply: (@g285_connected_of _ [:: a; a] _ (ok2 a a)) => y; rewrite !inE orbb.
- by apply: (@g285_connected_of _ [:: a; b] _ (ok2 a b)) => y; rewrite !inE.
Qed.

(* The neighbours of [v], listed. *)
Definition g285_nbrs (v : F) : seq F := [seq u <- g285_fv | v -- u].

Lemma g285_nbrsE (v x : F) : (x \in g285_nbrs v) = v -- x.
Proof. by rewrite /g285_nbrs mem_filter g285_fv_all andbT. Qed.

Arguments g285_nbrs : simpl never.

(* Largest stable subsequence of [vs] avoiding [X], by branching on the first vertex. *)
Fixpoint g285_mis (vs X : seq F) : nat :=
  if vs is v :: r then
    if v \in X then g285_mis r X
    else maxn (g285_mis r X) (g285_mis r (g285_nbrs v ++ X)).+1
  else 0.

Lemma g285_mis_cons (v : F) (r X : seq F) :
  g285_mis (v :: r) X =
    if v \in X then g285_mis r X else maxn (g285_mis r X) (g285_mis r (g285_nbrs v ++ X)).+1.
Proof. by []. Qed.

Lemma g285_misP (vs X T : seq F) :
  uniq T -> {subset T <= vs} -> (forall x y, x \in T -> y \in T -> ~~ x -- y) ->
  (forall x, x \in T -> x \notin X) -> size T <= g285_mis vs X.
Proof.
elim: vs X T => [|v r IH] X T uT sT stT dT.
  by case: T uT sT {stT dT} => [//|t T'] _ /(_ t (mem_head _ _)).
rewrite g285_mis_cons; case vX: (v \in X).
  apply: IH => // x xT; have := sT x xT; rewrite inE => /orP[/eqP xv|//].
  by move: (dT x xT); rewrite xv vX.
rewrite leq_max; case vT: (v \in T); last first.
  apply/orP; left; apply: IH => // x xT; have := sT x xT; rewrite inE => /orP[/eqP xv|//].
  by move: xT; rewrite xv vT.
have sz : size T = (size (rem v T)).+1.
  rewrite size_rem // prednK // lt0n size_eq0; apply/eqP => T0.
  by rewrite T0 in vT.
apply/orP; right; rewrite sz ltnS; apply: IH.
- exact: rem_uniq.
- move=> x; rewrite (mem_rem_uniq _ uT) inE => /andP[xv xT].
  by have := sT x xT; rewrite inE (negbTE xv).
- by move=> x y; rewrite !(mem_rem_uniq _ uT) !inE => /andP[_ xT] /andP[_ yT]; exact: stT.
- move=> x; rewrite (mem_rem_uniq _ uT) inE => /andP[xv xT]; rewrite mem_cat negb_or (dT x xT) andbT.
  by rewrite g285_nbrsE (stT v x vT xT).
Qed.

Lemma g285_mis_f14 : g285_mis g285_fv [::] = 5.
Proof. by vm_compute. Qed.

Lemma g285_f14_alpha : α([set: F]) <= 5.
Proof.
rewrite /alpha_mem; apply/bigmax_leqP => S /stabsetsP [_ /stableP st].
rewrite cardE -g285_mis_f14; apply: g285_misP.
- exact: enum_uniq.
- by move=> x _; exact: g285_fv_all.
- by move=> x y; rewrite !mem_enum; exact: st.
- by move=> x _; rewrite in_nil.
Qed.

Definition g285_locke_hyp_claim : Prop :=
  [/\ k_connected g285_f14 3, triangle_free g285_f14, regular g285_f14 3,
      8 * α([set: g285_f14]) < 3 * #|g285_f14| &
      (locke_finitely_many_statement -> exists N : nat, #|g285_f14| <= N)].

Theorem g285_locke_hyp_inhabited : g285_locke_hyp_claim.
Proof.
split; [exact: g285_f14_three_connected | exact: g285_f14_triangle_free | exact: g285_f14_cubic | |].
  rewrite g285_f14_card; apply: (@leq_ltn_trans (8 * 5)); last by [].
  by rewrite leq_mul2l g285_f14_alpha orbT.
move=> [N h]; exists N; apply: h.
- exact: g285_f14_three_connected.
- exact: g285_f14_triangle_free.
- exact: g285_f14_cubic.
- rewrite g285_f14_card; apply: (@leq_ltn_trans (8 * 5)); last by [].
  by rewrite leq_mul2l g285_f14_alpha orbT.
Qed.

(* m disjoint copies of F_14^(1). *)
Definition g285_fcopies_rel (m : nat) : rel ('I_m * F) := fun x y => (x.1 == y.1) && (x.2 -- y.2).

Lemma g285_fcopies_sym (m : nat) : symmetric (@g285_fcopies_rel m).
Proof. by move=> x y; rewrite /g285_fcopies_rel eq_sym sg_sym. Qed.

Lemma g285_fcopies_irrefl (m : nat) : irreflexive (@g285_fcopies_rel m).
Proof. by move=> x; rewrite /g285_fcopies_rel sg_irrefl andbF. Qed.

Definition g285_fcopies (m : nat) : sgraph := SGraph (@g285_fcopies_sym m) (@g285_fcopies_irrefl m).

Lemma g285_fcopies_card (m : nat) : #|g285_fcopies m| = m * 14.
Proof. by rewrite card_prod card_ord g285_f14_card. Qed.

Lemma g285_fcopies_cubic (m : nat) : regular (g285_fcopies m) 3.
Proof.
move=> [i a].
have -> : N((i, a) : g285_fcopies m) = [set (i, b) | b in N(a)].
  apply/setP => [[j b]]; rewrite !inE /edge_rel /= /g285_fcopies_rel /=; apply/andP/imsetP.
  - by move=> [/eqP <- ab]; exists b; rewrite ?inE.
  - by move=> [c cN [-> ->]]; rewrite eqxx; move: cN; rewrite inE.
rewrite card_imset; last exact: (g285_f14_cubic a).
by move=> b c [].
Qed.

Lemma g285_fcopies_triangle_free (m : nat) : triangle_free (g285_fcopies m).
Proof.
move=> [i a] [j b] [k c]; rewrite /edge_rel /= /g285_fcopies_rel /=.
by move=> /andP[_ ab] /andP[_ bc] /andP[_ ca]; exact: g285_f14_triangle_free ab bc ca.
Qed.

Lemma g285_fcopies_alpha (m : nat) : α([set: g285_fcopies m]) <= 5 * m.
Proof.
rewrite /alpha_mem; apply/bigmax_leqP => S /stabsetsP [_ /stableP st].
rewrite -sum1_card (partition_big (fun x : g285_fcopies m => x.1) xpredT) //=.
apply: (@leq_trans (\sum_(j < m) 5)); last by rewrite big_const_ord iter_addn_0.
apply: leq_sum => j _; rewrite sum1_card.
have inj : {in [pred x : g285_fcopies m | (x \in S) && (x.1 == j)] &, injective (fun x : g285_fcopies m => x.2)}.
  by move=> [i a] [k b]; rewrite !inE /= => /andP[_ /eqP ->] /andP[_ /eqP ->] /= ->.
rewrite -(card_in_imset inj).
apply: (@leq_trans #|[set a : F | ((j, a) : g285_fcopies m) \in S]|).
  apply: subset_leq_card; apply/subsetP => a /imsetP [[i b]].
  by rewrite !inE /= => /andP[bS /eqP ij] ->; rewrite -ij.
apply: leq_trans g285_f14_alpha; apply: stabset_bound; apply/stabsetsP; split; first exact: subsetT.
apply/stableP => a b; rewrite !inE => aS bS.
by have := st _ _ aS bS; rewrite /edge_rel /= /g285_fcopies_rel eqxx.
Qed.

(* The variant without 3-connectivity. *)
Definition g285_locke_no_conn : Prop :=
  exists N : nat, forall G : sgraph,
    triangle_free G -> regular G 3 -> 8 * α([set: G]) < 3 * #|G| -> #|G| <= N.

Definition g285_locke_ntt_claim : Prop :=
  ~ g285_locke_no_conn /\ (g285_locke_no_conn -> locke_finitely_many_statement).

Theorem g285_locke_not_trivially_true : g285_locke_ntt_claim.
Proof.
split; last by move=> [N h]; exists N => G _; exact: h.
move=> [N h]; have := h (g285_fcopies N.+1) (@g285_fcopies_triangle_free N.+1) (@g285_fcopies_cubic N.+1).
have -> : 8 * α([set: g285_fcopies N.+1]) < 3 * #|g285_fcopies N.+1|.
  apply: (@leq_ltn_trans (8 * (5 * N.+1))); first by rewrite leq_mul2l g285_fcopies_alpha orbT.
  by rewrite g285_fcopies_card mulnA (mulnC N.+1 14) mulnA ltn_pmul2r.
move=> /(_ isT); rewrite g285_fcopies_card => h'.
by move: (leq_trans (leq_pmulr N.+1 (isT : 0 < 14)) h'); rewrite ltnn.
Qed.

(** ** Meyniel synonym *)

(* sqrt_ceil is the least s with n <= s ^ 2. *)
Lemma g285_sqrt_ceil_sq (s : nat) : sqrt_ceil (s ^ 2) <= s.
Proof. by rewrite /sqrt_ceil; case: (ex_minnP (sqrt_ceil_ex (s ^ 2))) => m _ /(_ s (leqnn _)). Qed.

Definition g285_mey_hyp_claim : Prop :=
  [/\ 0 < #|'K_3|, connected [set: 'K_3] &
      (meyniel_cop_number_sqrt_duplicate_statement ->
         exists C : nat, cop_number_le ('K_3) (C * sqrt_ceil #|'K_3|))].

Theorem g285_mey_hyp_inhabited : g285_mey_hyp_claim.
Proof.
split; [by rewrite card_ord | exact: (@connected_Kn 3) |].
by move=> [C h]; exists C; apply: h; [rewrite card_ord | exact: (@connected_Kn 3)].
Qed.

(* The variant without "connected". *)
Definition g285_mey_any_graph : Prop :=
  exists C : nat, forall G : sgraph, 0 < #|G| -> cop_number_le G (C * sqrt_ceil #|G|).

Definition g285_mey_ntt_claim : Prop :=
  ~ g285_mey_any_graph /\ (g285_mey_any_graph -> meyniel_cop_number_sqrt_duplicate_statement).

Theorem g285_mey_not_trivially_true : g285_mey_ntt_claim.
Proof.
split; last by move=> [C h]; exists C => G G0 _; exact: h.
move=> [C h].
have [j [jk wj]] := h (g285_edgeless (C.+1 ^ 2)) (ltac:(by rewrite card_ord expn_gt0)).
apply: (g285_edgeless_cops _ wj); apply: (leq_ltn_trans jk); rewrite card_ord.
apply: (@leq_ltn_trans (C * C.+1)); first by rewrite leq_mul2l g285_sqrt_ceil_sq orbT.
by rewrite -mulnn ltn_pmul2r.
Qed.
