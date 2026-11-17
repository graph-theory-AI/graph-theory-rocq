(** * Atlas.conjectures.implications_A2 -- cross-package edges with a [Digraph] endpoint

    Same role as [implications_A1.v] for the relations whose one endpoint
    lives in [digraph-theory].  That package's prelude imports
    [mathcomp-classical] ([boolp]); the statements themselves are axiom-free
    but NO [boolp] / [classical_sets] lemma may be used in a proof here
    (every theorem must print "Closed under the global context"). *)

From GTBase Require Import base.
From Chromatic.conjectures Require Import U8 X218.
From Cycle.conjectures Require Import X9.
From Digraph Require Import digraph dipath oriented.
From Digraph.conjectures Require Import chi_bounded classic_core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Recorded dispositions (wave A2; re-read in wave A1, 2026-09-24: no edge provable within budget) *)

(*@EDGE from=conj2_1605_statement to=graphs_with_a_forbidden_induced_tree_are_chi_bounded_statement kind=equiv status=candidate proved=false cite="gc:e010" note="BLOCKED (re-read 2026-09-24): conj2_1605 is encoded on ORIENTED graphs (ind_free H G for an oriented H, chi/omega of the underlying graph), while the corpus argument reads the paper's Conjecture 2 as a statement on undirected H. (=>) conj2 -> Gyarfas-Sumner is elementary (orient a T-free graph by enum_rank; it then has no induced copy of any orientation H of T, so the if half of conj2 applies; needs only the sgraph -> diGraphType orientation bridge of interop_graph_theory.v), but (<=) fails to follow: the if half of conj2 for an oriented forest H does not follow from Gyarfas-Sumner (an oriented G avoiding H may contain U(H) induced with another orientation; this oriented version is open and stronger), and the only-if half (underlying H with a cycle => not chi-bounded) needs Erdos' high-girth high-chromatic graphs, not in the repo. Possible encoding issue in digraph-theory chi_bounded.v to be checked against arXiv:1605.07411 Conjecture 2." *)
(*@EDGE from=every_forest_is_good_statement to=conj2_1605_statement kind=implies status=candidate proved=false cite="gc:e170" note="BLOCKED (re-read 2026-09-24): the target is a biconditional on ORIENTED graphs. Its if half (oriented H with forest underlying graph => oriented-H-free class chi-bounded) does not follow from polynomial chi-boundedness of U(H)-free undirected graphs, because an oriented G avoiding H may contain U(H) induced with another orientation; its only-if half needs Erdos' high-girth high-chromatic graphs (not in the repo)." *)

(** ** e099: proper edge-coloured short cycles (X9.v, arxiv:1806.00825#00)
    ==> Caccetta-Haggkvist (classic_core.v, opg:caccetta_haggkvist_conjecture).

    For a loopless digraph [D] with [n] vertices and minimum out-degree
    [r >= 1]: a digon [u --> v --> u] is a dicycle with two vertices, and
    [2 <= (n + r - 1) %/ r] because [r <= outdeg u <= n - 1].  Without a
    digon, the underlying simple graph [e099_und D] ([u -- v] when [u != v]
    and [u --> v] or [v --> u]) colours its edge [[set u; w]], [u --> w], by
    [enum_rank u], its tail ([e099_col]); colour class [i] holds the edges
    from [enum_val i] to its at least [r] out-neighbours.  The source gives a
    cycle with at most [ceil_div n r] vertices whose incident edges have
    distinct colours, so no vertex is the tail of both of its cycle edges:
    a backward arc propagates along the cycle ([e099_step]), and the cycle
    or its reversal is a dicycle of [D] of the same size ([e099_orient]). *)

Section E099.
Variable D : diGraphType.

Definition e099_rel : rel D := fun u v => (u != v) && ((u --> v) || (v --> u)).

Lemma e099_sym : symmetric e099_rel.
Proof. by move=> u v; rewrite /e099_rel eq_sym orbC. Qed.

Lemma e099_irrefl : irreflexive e099_rel.
Proof. by move=> u; rewrite /e099_rel eqxx. Qed.

Definition e099_und : sgraph := SGraph e099_sym e099_irrefl.

Definition e099_tail (v0 : D) (e : {set e099_und}) : D :=
  if [pick u in e | [exists w in e, (u : D) --> (w : D)]] is Some u then u else v0.

Lemma e099_tailE (v0 u w : D) :
  (forall v : D, ~~ (v --> v)) -> (forall a b : D, a --> b -> ~~ (b --> a)) ->
  u --> w -> e099_tail v0 ([set u; w] : {set e099_und}) = u.
Proof.
move=> nl nd uw; rewrite /e099_tail.
case: pickP => [x /andP [xe /existsP [y /andP [ye xy]]]|].
  move: xe ye xy; rewrite !inE => /orP [/eqP -> //|/eqP ->] /orP [/eqP ->|/eqP ->] wy.
    by move: (nd _ _ uw); rewrite wy.
  by move: (nl w); rewrite wy.
move/(_ u) => /=; rewrite !inE eqxx /= => /negbT /existsPn /(_ w).
by rewrite !inE eqxx orbT uw.
Qed.

Definition e099_col (v0 : D) (e : {set e099_und}) : 'I_#|e099_und| :=
  enum_rank (e099_tail v0 e : e099_und).

Lemma e099_classes (v0 : D) (r : nat) :
  (forall v : D, ~~ (v --> v)) -> (forall a b : D, a --> b -> ~~ (b --> a)) ->
  (forall v : D, r <= outdeg v) ->
  @x9_colour_classes_large e099_und #|e099_und| r (e099_col v0).
Proof.
move=> nl nd hdeg i; set v := enum_val i.
apply: leq_trans (hdeg v) _; rewrite /outdeg.
have inj : {in [set w | v --> w] &, injective (fun w : D => [set v; w] : {set e099_und})}.
  move=> w1 w2; rewrite !inE => h1 h2 /setP /(_ w1).
  rewrite !inE eqxx orbT => /esym /orP [/eqP e|/eqP //].
  by move: (nl v); rewrite -{2}e h1.
rewrite -(card_in_imset inj); apply: subset_leq_card.
apply/subsetP => e /imsetP [w]; rewrite inE => vw ->.
rewrite inE /x9_edge_set in_edges; apply/andP; split.
  by rewrite /edge_rel /= /e099_rel vw andbT; apply: contraNneq (nl v) => {2}->.
by rewrite /e099_col (e099_tailE v0 nl nd vw) enum_valK.
Qed.

Lemma e099_step (v0 : D) (c : seq e099_und) :
  (forall v : D, ~~ (v --> v)) -> (forall a b : D, a --> b -> ~~ (b --> a)) ->
  @x9_genuine_cycle e099_und c ->
  @x9_cycle_incident_edges_properly_coloured e099_und #|e099_und| (e099_col v0) c ->
  {in c, forall x : e099_und, (next c x : D) --> (x : D) ->
     (next c (next c x) : D) --> (next c x : D)}.
Proof.
move=> nl nd [/andP [cc uc] sz] pc x xc bx.
have mem y : y \in c -> [set y; next c y] \in x9_cycle_edges c.
  move=> yc; rewrite /x9_cycle_edges -in_seq_cycle_edge_set -(seq_next_edge_set_uniq uc).
  by apply/seq_next_edge_setP; exists y.
have xz : x != next c (next c x).
  have E := rot_index xc; have nr := next_rot (index x c) uc.
  have ur : uniq (rot (index x c) c) by rewrite rot_uniq.
  have sr : size (rot (index x c) c) = size c := size_rot _ _.
  rewrite -!nr; rewrite E in ur sr *; move: ur sr.
  case: (drop _ _ ++ _) => [|y [|z s]] /= ur sr; try by rewrite -sr in sz.
  rewrite eqxx; move: ur; rewrite !inE negb_or => /andP [/andP [xy xz'] _].
  rewrite [y == x]eq_sym (negbTE xy) eqxx.
  by move: xz'; rewrite negb_or => /andP [].
have yc : next c x \in c by rewrite mem_next.
move: xz yc bx; set y := next c x; set z := next c y; move=> xz yc bx.
have : e099_rel y z := next_cycle cc yc.
rewrite /e099_rel => /andP [_ /orP [yz|//]].
have xy : x != y by apply/eqP => e; move: bx; rewrite -e (negbTE (nl x)).
have := pc _ _ (mem x xc) (mem y yc).
rewrite /e099_col [[set x; next c x]]setUC (e099_tailE v0 nl nd bx) (e099_tailE v0 nl nd yz) eqxx.
move=> h; suff : ~~ true by []; apply: h.
  by apply/eqP => /setP /(_ x); rewrite !inE eqxx orbT -/y -/z (negbTE xy) (negbTE xz).
by rewrite -setI_eq0; apply/set0Pn; exists y; rewrite !inE -/y eqxx.
Qed.

Lemma e099_orient (v0 : D) (c : seq e099_und) :
  (forall v : D, ~~ (v --> v)) -> (forall a b : D, a --> b -> ~~ (b --> a)) ->
  @x9_genuine_cycle e099_und c ->
  @x9_cycle_incident_edges_properly_coloured e099_und #|e099_und| (e099_col v0) c ->
  cycle (fun x y : D => x --> y) c \/ cycle (fun x y : D => y --> x) c.
Proof.
move=> nl nd gc pc; have step := @e099_step v0 c nl nd gc pc.
case: gc => /andP [cc uc] sz.
case: (boolP [exists x in c, (next c x : D) --> (x : D)]).
- case/existsP => x0 /andP [x0c b0]; right; apply: (cycle_from_next uc) => x xc.
  have E := rot_index x0c; have nr := next_rot (index x0 c) uc.
  have ur : uniq (rot (index x0 c) c) by rewrite rot_uniq.
  have all_i i : i < size c ->
      (next c (nth x0 (rot (index x0 c) c) i) : D) --> (nth x0 (rot (index x0 c) c) i : D).
    elim: i => [|i IH] lt; first by rewrite E.
    have lti : i < size c by apply: ltnW.
    have -> : nth x0 (rot (index x0 c) c) i.+1 = next c (nth x0 (rot (index x0 c) c) i).
      rewrite -nr; move: ur lti; rewrite -(size_rot (index x0 c)) E => ur lti.
      by rewrite next_nth mem_nth // index_uniq.
    by apply: step (IH lti); rewrite -(mem_rot (index x0 c)) mem_nth ?size_rot.
  have := all_i (index x (rot (index x0 c) c)); rewrite nth_index ?mem_rot //; apply.
  by rewrite -(size_rot (index x0 c)) index_mem mem_rot.
- move/existsPn => nb; left; apply: (cycle_from_next uc) => x xc.
  have : e099_rel x (next c x) := next_cycle cc xc.
  rewrite /e099_rel => /andP [_ /orP [//|bx]].
  by move: (nb x); rewrite xc bx.
Qed.

End E099.

(*@EDGE from=proper_edge_coloured_short_cycle_statement to=caccetta_haggkvist_statement kind=implies status=verified proof=e099_proper_edge_coloured_short_cycle_implies_caccetta_haggkvist cite="gc:e099" note="Underlying graph: u -- v when u != v and u --> v or v --> u. A digon u --> v --> u is a dicycle with 2 <= (n + r - 1) %/ r vertices, as r <= outdeg u <= n - 1 by looplessness. Without a digon, the edge [set u; w] with u --> w gets the colour enum_rank u (its tail), so colour class i holds the edges from enum_val i to its at least r out-neighbours; the source cycle, with at most ceil_div n r = (n + r - 1) %/ r vertices, gives incident edges distinct colours, so no vertex is the tail of both of its cycle edges, a backward arc propagates along the cycle, and the cycle or its reversal is a dicycle of D of the same size." *)

Theorem e099_proper_edge_coloured_short_cycle_implies_caccetta_haggkvist :
  proper_edge_coloured_short_cycle_statement -> caccetta_haggkvist_statement.
Proof.
move=> hX D r n0 nl r0 hdeg.
case: (boolP [exists u : D, exists v : D, (u --> v) && (v --> u)]).
- case/existsP => u /existsP [v /andP [uv vu]]; exists [:: u; v]; split.
    rewrite /dicycle /= uv vu /= !inE andbT.
    by apply/eqP => e; move: uv; rewrite e (negbTE (nl v)).
  have ltr : r < #|D|.
    apply: leq_ltn_trans (hdeg u) _; rewrite /outdeg -cardsT; apply: proper_card.
    apply/properP; split; first exact: subsetT.
    by exists u; rewrite !inE // (negbTE (nl u)).
  by rewrite leq_divRL // mul2n -addnn -addnBAC // leq_add2r subn1 -ltnS prednK.
- move/existsPn => nd0.
  have nd : forall a b : D, a --> b -> ~~ (b --> a).
    by move=> a b ab; apply/negP => ba; move: (nd0 a) => /existsPn /(_ b); rewrite ab ba.
  have /card_gt0P [v0 _] := n0.
  have [c [gc [szc pc]]] := hX #|e099_und D| r (e099_und D) (@e099_col D v0) n0 r0 erefl
    (@e099_classes D v0 r nl nd hdeg).
  have [sz3 uc] : 2 < size c /\ uniq c by case: gc => /andP [_ ?] ?.
  have nn : ~~ nilp c by rewrite /nilp -lt0n (ltnW (ltnW sz3)).
  case: (@e099_orient D v0 c nl nd gc pc) => [fw|bw]; [exists c | exists (rev c)].
    by split; [rewrite /dicycle nn fw uc | exact: szc].
  split; last by rewrite size_rev; exact: szc.
  by rewrite /dicycle rev_cycle rev_uniq /nilp size_rev -/(nilp c) nn bw uc.
Qed.

Print Assumptions e099_proper_edge_coloured_short_cycle_implies_caccetta_haggkvist.
Print Assumptions e099_orient.
