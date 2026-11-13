(** * Minor.conjectures.implications_X42 — corpus-relation edges landing in X42

    Edges of [meta/corpus_relations.json] whose TARGET is the X42 row
    [even_hole_k4_diamond_free_bounded_treewidth_statement].  Axiom-free: only
    [Qed]-closed results live here; a candidate edge that does not close is
    documented, never stated.

    ** The bridge F1 between the two treewidth encodings.

    X220 / X228 measure treewidth with [tw_le] (a [sdecomp] over a [forest]
    index, [width D <= k.+1]); X27 / X42 measure it with
    [x27_treewidth_at_most] (an arbitrary [sgraph] index that [is_tree], plus the
    three tree-decomposition clauses spelled out by hand).  The two are
    EQUIVALENT ([tw_le_iff_x27]).  The easy direction turns a tree index into a
    [forest] record; the other direction needs the index forest to be made
    connected, which is [Minor.foundations.width_params.tw_le_tree].  In both
    directions the only real friction is that [sbag_conn] states its
    connectedness with the PREDICATE [[pred t | x \in B t]] while
    [x27_tree_decomposition] states it with the SET [[set t | x \in bag t]];
    [restrict_bag] + [eq_connect] mediate.

    ** e050 (PROVED).  [even_hole_diamond_free_bounded_tree_alpha_statement] ⟹
    [even_hole_k4_diamond_free_bounded_treewidth_statement]: an (even hole, K_4,
    diamond)-free graph is in particular (even hole, diamond)-free, so the source
    gives a tree decomposition whose bags have independence number at most [k];
    K_4-freeness forbids a clique of size 4 inside a bag; finite Ramsey
    ([Minor.foundations.ramsey_small.ramsey_bound] at [s = 4], [a = k]) then
    bounds every bag, hence the width, and F1 delivers the X27-shaped
    conclusion. *)

From GTBase Require Import base.
From GraphTheory Require Import preliminaries.
From Minor.foundations Require Import containment width_params ramsey_small hole_containments.
From Minor.conjectures Require Import X27 X42 X220.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The bridge F1 : [tw_le] ⟺ [x27_treewidth_at_most] *******************)

(** The two spellings of "the index nodes whose bag contains [v]". *)
Lemma restrict_bag (G T : sgraph) (D : T -> {set G}) (v : G) :
  restrict [pred t : T | v \in D t] (@sedge T)
    =2 restrict [set t : T | v \in D t] (@sedge T).
Proof. exact: GTBase.bag_decompositions.restrict_bag. Qed.

Lemma tw_le_x27 (G : sgraph) (k : nat) : tw_le G k -> x27_treewidth_at_most G k.
Proof.
case/tw_le_tree => T [D [dec w conn]].
exists (sgraph_of_forest T), D; split; first by split; [exact: forest_is_forest|exact: conn].
split.
- split=> [v|].
  + by have [t vt] := sbag_cover dec v; apply/existsP; exists t.
  + split=> [x y xy|v t1 t2 h1 h2].
    * by have [t /andP[xt yt]] := sbag_edge dec xy; apply/existsP; exists t; rewrite xt yt.
    * rewrite inE in h1; rewrite inE in h2.
      rewrite -(eq_connect (@restrict_bag G T D v)).
      exact: (sbag_conn dec h1 h2).
- by move=> t; apply: leq_trans w; rewrite /width; exact: leq_bigmax.
Qed.

Lemma x27_tw_le (G : sgraph) (k : nat) : x27_treewidth_at_most G k -> tw_le G k.
Proof.
case=> T [bag [[tf tc] [[cov [edg cn]] bnd]]].
exists (@Forest T tf), bag; split; last first.
  by rewrite /width; apply/bigmax_leqP => t _; exact: bnd.
split.
- by move=> x; have /existsP[t ht] := cov x; exists t.
- by move=> x y xy; have /existsP[t ht] := edg x y xy; exists t.
- move=> x t1 t2 h1 h2; rewrite (eq_connect (@restrict_bag G T bag x)).
  by apply: (cn x); rewrite inE.
Qed.

Lemma tw_le_iff_x27 (G : sgraph) (k : nat) :
  tw_le G k <-> x27_treewidth_at_most G k.
Proof. by split; [exact: tw_le_x27|exact: x27_tw_le]. Qed.

(** ** Dictionary between the two "induced-H-free" spellings ***************)

(** [x42_induced_free] (no vertex set induces a copy of [H]) implies the
    negation of [has_induced_copy] (no injective edge-reflecting map [H -> G]):
    the image of such a map is a vertex set that induces a copy of [H]
    ([isubgraph_induced]). *)
Lemma induced_free_no_copy (G H : sgraph) :
  x42_induced_free G H -> ~ has_induced_copy G H.
Proof.
move=> hf [i]; apply: (hf [set x in codom i]).
exact: diso_sym (isubgraph_induced i).
Qed.

(** A clique on exactly four vertices induces a copy of ['K_4]. *)
Lemma clique4_K4 (G : sgraph) (S : {set G}) :
  clique S -> #|S| = 4 -> inhabited (induced S ≃ 'K_4).
Proof.
move=> cS c4; split.
have e : #|induced S| = 4 by rewrite card_induced.
rewrite -e; apply: diso_Kn => x y xy.
by apply: (cS _ _ (valP x) (valP y)); rewrite val_eqE.
Qed.

(** ** e050 (PROVED) *******************************************************)

Theorem even_hole_diamond_free_bounded_tree_alpha_implies_even_hole_k4_diamond_free_bounded_treewidth :
  even_hole_diamond_free_bounded_tree_alpha_statement ->
  even_hole_k4_diamond_free_bounded_treewidth_statement.
Proof.
case=> k src.
have [N HN] := ramsey_bound 4 k.
exists N => G eh k4 dia.
have [T [D [dec ab]]] := src G eh (induced_free_no_copy dia).
have cl4 : forall (t : T) (S : {set G}), S \subset D t -> clique S -> #|S| != 4.
  move=> t S _ cS; apply/negP => /eqP c4.
  exact: (induced_free_inhabited G 'K_4).1 k4 S (clique4_K4 cS c4).
apply: tw_le_x27; exists T, D; split; first exact: dec.
rewrite /width; apply/bigmax_leqP => t _.
by apply: leq_trans (HN G (D t) (ab t) (cl4 t)) (leqnSn N).
Qed.

(*@EDGE from=even_hole_diamond_free_bounded_tree_alpha_statement to=even_hole_k4_diamond_free_bounded_treewidth_statement kind=implies status=verified proved=true proof=even_hole_diamond_free_bounded_tree_alpha_implies_even_hole_k4_diamond_free_bounded_treewidth cite="gc:e050" note="Hypothesis-class containment plus Ramsey: (even hole, K_4, diamond)-free graphs are (even hole, diamond)-free, so the source bounds the independence number of every bag of some tree decomposition by k; no induced K_4 forbids a clique of size 4 inside a bag, so finite Ramsey (foundations/ramsey_small.v, ramsey_bound at s=4, a=k) bounds every bag by N(4,k), hence the width; the bridge F1 (tw_le_x27, built on foundations/width_params.v tw_le_tree) converts the forest-indexed sdecomp into the tree-indexed x27_treewidth_at_most. Constant c := N(4,k)." *)

(** ** e051 — the four even-hole containments, and the one hypothesis left ***

    [theta_prism_even_wheel_free_bounded_treewidth_statement] ⟹
    [even_hole_k4_diamond_free_bounded_treewidth_statement] (gc:e051).

    Re-derivation.  Instantiate the source at [t = 4] (the source's [exists c] is then
    available with no choice principle, since [t] is FIXED — contrast e053).  Five of
    the six hypotheses the source needs on an (even hole, K_4, diamond)-free [G] are
    now discharged below, and the conclusion is converted by the bridge F1
    ([tw_le_x27]):

    - [~ has_induced_copy G (cycle_graph 4)] : [even_hole_free_no_C4] — a [C_4] IS an
      even hole ([Minor.foundations.hole_containments.C4_even_hole]);
    - [~ has_induced_copy G x42_diamond] : [induced_free_no_copy];
    - [forall H, x220_theta H -> ~ has_induced_copy G H] : [even_hole_free_no_theta] —
      a theta, i.e. a graph that IS a subdivision of ['K_2,3], contains an even hole
      ([subdiv_KB23_even_hole]): of the three internally disjoint paths joining the two
      branch vertices two have the same parity, and since the encoded theta is EXACT
      ([subdiv_rep] forces every edge of [H] to be an edge of a subdivision path) their
      union is an INDUCED cycle;
    - [forall H, x220_prism H -> ~ has_induced_copy G H] : [even_hole_free_no_prism] —
      the same parity argument on the three matching paths of a prism
      ([prism_even_hole]);
    - [x220_clique_free G 4] : [K4_free_clique_free] — a clique with at least four
      vertices has a four-element subset ([sub_card_exact]), which is again a clique
      ([clique_sub]) and induces a copy of ['K_4] ([clique4_K4]).

    The sixth is the even-wheel containment [x220_even_wheel_free G]: a hole [c] of an
    even-hole-free graph has ODD length, so if a vertex [v] outside [c] had an EVEN
    number [k >= 4] of neighbours on [c], the [k] arcs of [c] cut out by those
    neighbours would have lengths summing to the odd [#|c|], hence one arc would have
    EVEN length, and that arc together with [v] is an even hole.  [e051_modulo_even_wheel]
    below states the edge modulo that one containment.  The last section of this file
    proves it ([even_hole_free_even_wheel_free], without diamond-freeness, through the
    arc parity lemmas [odd_block] / [even_arc] and [arc_hole]), and the edge theorem
    at its end applies [e051_modulo_even_wheel] to it. *)

(** *** The three even-hole containments *)

Lemma even_hole_free_no_C4 (G : sgraph) :
  x27_even_hole_free G -> ~ has_induced_copy G (cycle_graph 4).
Proof. by move=> eh [i]; case: (C4_even_hole i) => c [hc pc]; exact: (eh c hc pc). Qed.

Lemma even_hole_free_no_theta (G H : sgraph) :
  x27_even_hole_free G -> x220_theta H -> ~ has_induced_copy G H.
Proof.
move=> eh th [i]; case: (subdiv_KB23_even_hole th) => c [hc pc].
apply: (eh [seq i x | x <- c]); first exact: isubgraph_hole.
by rewrite size_map.
Qed.

Lemma even_hole_free_no_prism (G H : sgraph) :
  x27_even_hole_free G -> x220_prism H -> ~ has_induced_copy G H.
Proof.
move=> eh pr [i]; case: (prism_even_hole pr) => c [hc pc].
apply: (eh [seq i x | x <- c]); first exact: isubgraph_hole.
by rewrite size_map.
Qed.

(** *** No induced ['K_4] bounds the clique number by 4 *)

Lemma K4_free_clique_free (G : sgraph) :
  x42_induced_free G 'K_4 -> x220_clique_free G 4.
Proof.
move=> k4 S cS; rewrite ltnNge; apply/negP => h4.
have [B sub cardB] := sub_card_exact h4.
exact: (induced_free_inhabited G 'K_4).1 k4 B (clique4_K4 (clique_sub cS sub) cardB).
Qed.

(** *** The edge, modulo the one missing containment *)

Theorem e051_modulo_even_wheel :
  (forall G : sgraph,
     x27_even_hole_free G -> x42_induced_free G x42_diamond ->
     x220_even_wheel_free G) ->
  theta_prism_even_wheel_free_bounded_treewidth_statement ->
  even_hole_k4_diamond_free_bounded_treewidth_statement.
Proof.
move=> wheel src; case: (src 4) => c Hc.
exists c => G eh k4 dia; apply: tw_le_x27; apply: Hc.
- exact: even_hole_free_no_C4.
- exact: induced_free_no_copy dia.
- by move=> H th; exact: even_hole_free_no_theta eh th.
- by move=> H pr; exact: even_hole_free_no_prism eh pr.
- exact: wheel G eh dia.
- exact: K4_free_clique_free k4.
Qed.

(*@EDGE from=theta_prism_even_wheel_free_bounded_treewidth_statement to=even_hole_k4_diamond_free_bounded_treewidth_statement kind=implies status=verified proof=theta_prism_even_wheel_free_bounded_treewidth_implies_even_hole_k4_diamond_free_bounded_treewidth cite="gc:e051" note="Corpus argument: each of C_4, theta, prism and even wheel contains an even hole, so (even hole, K_4, diamond)-free graphs lie in the class C*_4 and the t = 4 instance of the source bounds their treewidth. All six source hypotheses are proved here and in foundations/hole_containments.v: ~has_induced_copy G (cycle_graph 4) (even_hole_free_no_C4, from four_cycle_hole), ~has_induced_copy G x42_diamond (induced_free_no_copy), theta-freeness (even_hole_free_no_theta, from subdiv_KB23_even_hole), prism-freeness (even_hole_free_no_prism, from prism_even_hole), x220_clique_free G 4 (K4_free_clique_free), and x220_even_wheel_free G (even_hole_free_even_wheel_free, without diamond-freeness: a hole of an even-hole-free graph is odd, so an even number k >= 4 of spokes leaves an arc of even length >= 2 between two consecutive spokes (even_arc, from the run parity lemma odd_block), and that arc plus the centre is an even hole (arc_hole)); the bridge F1 (tw_le_x27) converts the treewidth encoding. The theorem applies e051_modulo_even_wheel to the even-wheel containment." *)

Print Assumptions tw_le_x27.
Print Assumptions even_hole_free_no_C4.
Print Assumptions even_hole_free_no_theta.
Print Assumptions even_hole_free_no_prism.
Print Assumptions K4_free_clique_free.
Print Assumptions e051_modulo_even_wheel.
Print Assumptions x27_tw_le.
Print Assumptions even_hole_diamond_free_bounded_tree_alpha_implies_even_hole_k4_diamond_free_bounded_treewidth.

(** ** e051 closed — no even wheel in an even-hole-free graph ****************

    [x220_even_wheel_free G] holds for EVERY even-hole-free [G]; diamond-freeness is
    not needed.  Let [c] be a hole, so [size c] is odd, and [v] a vertex off [c] whose
    number of spokes (neighbours on [c]) is even and at least 4.  Read the spokes as
    the predicate [(. -- v)] on the cyclic sequence [c]: [even_arc] (from the parity
    lemma [odd_block] on a rotation of [c] that starts at a spoke) finds two spokes [x]
    and [y] whose run [q] of non-spokes in between has ODD size, with another spoke in
    the rest of [c].  The arc [x :: q ++ [y]] plus [v] is a hole ([arc_hole]: a chord
    among the arc's vertices would be a chord of [c], the rest of [c] keeps [x] and
    [y] apart, and [v] sees only [x] and [y]) on [size q + 3] vertices: an even hole. *)

Section Blocks.
Variables (T : eqType) (S : pred T).

(** A list ending in an [S] element whose length and number of [S] elements differ in parity has a block
    -- a run [q] of non-[S] elements followed by an [S] element [y], starting the list or right after an
    [S] element -- of odd length. *)
Lemma odd_block (p : seq T) (z : T) :
  S z -> odd (size (rcons p z)) != odd (count S (rcons p z)) ->
  exists u q y w, [/\ rcons p z = u ++ q ++ y :: w, u = [::] \/ S (last z u), ~~ has S q, S y
                    & odd (size q)].
Proof.
move: {2}(size p) (leqnn (size p)) => m; elim: m p => [|m IH] p.
  by rewrite leqn0 size_eq0 => /eqP-> Sz /=; rewrite Sz.
move=> lep Sz neq.
case hp: (has S p); last first.
  exists [::], p, z, [::]; split => //; [by rewrite cats1 | by left | by rewrite hp |].
  move: neq; rewrite size_rcons -cats1 count_cat /= Sz addn0.
  by move: hp; rewrite has_count lt0n => /negbFE/eqP->; case: (odd (size p)).
case: (split_find hp) lep neq => y q w Sy qS lep neq.
case oq: (odd (size q)).
  by exists [::], q, y, (rcons w z); split => //; [rewrite -cats1 cat_rcons -catA /= cats1 | left].
have lew : size w <= m.
  by move: lep; rewrite size_cat size_rcons addSn ltnS => /(leq_trans (leq_addl _ _)).
have qS0 : count S q = 0 by apply/eqP; rewrite -leqn0 leqNgt -has_count (negbTE qS).
have neqw : odd (size (rcons w z)) != odd (count S (rcons w z)).
  move: neq; rewrite rcons_cat size_cat count_cat size_rcons -[rcons q y]cats1 count_cat qS0 /= Sy.
  by rewrite !oddD /= oq /=; case: (odd (size (rcons w z))); case: (odd (count S (rcons w z))).
have [u' [q' [y' [w' [E u'S q'S Sy' oq']]]]] := IH w lew Sz neqw.
exists (rcons q y ++ u'), q', y', w'; split => //.
  by rewrite rcons_cat E catA.
right; rewrite last_cat last_rcons.
by case: u' E u'S => [|a u'] //= _ [//|].
Qed.

(** A cyclic sequence of odd length with an even number, at least three, of [S] elements has, up to
    rotation, the form [x :: q ++ y :: rest] with [x] and [y] in [S], no [S] element in [q], [q] of odd
    length and an [S] element in [rest].  [P] is any rotation-invariant property of the sequence. *)
Lemma even_arc (P : seq T -> Prop) (c : seq T) :
  (forall n s, P (rot n s) <-> P s) -> P c -> odd (size c) -> ~~ odd (count S c) -> 3 <= count S c ->
  exists x q y rest, [/\ P (x :: q ++ y :: rest), S x && S y, ~~ has S q, odd (size q) & has S rest].
Proof.
move=> Prot Pc oc ec c3.
have hc : has S c by rewrite has_count (leq_trans _ c3).
have rest_has x q y rest : perm_eq (x :: q ++ y :: rest) c -> S x -> S y -> ~~ has S q -> has S rest.
  move/permP/(_ S) => cnt Sx Sy qS; move: c3; rewrite -cnt /= count_cat /= Sx Sy.
  move: qS; rewrite !has_count -leqNgt leqn0 => /eqP->.
  by rewrite add0n !add1n !ltnS.
have [x0 [p [Pp pp Sx0]]] : exists x0 p, [/\ P (x0 :: p), perm_eq (x0 :: p) c & S x0].
  case: (split_find hc) Pc => x0 s1 s2 Sx0 _ Pc; exists x0, (s2 ++ s1).
  have -> : x0 :: s2 ++ s1 = rot (size s1) (rcons s1 x0 ++ s2) by rewrite -cats1 -catA rot_size_cat.
  by split => //; [apply/Prot | rewrite perm_rot].
have Ps : P (rcons p x0) by rewrite -rot1_cons; apply/Prot.
have ps : perm_eq (rcons p x0) c by rewrite -rot1_cons perm_rot.
have neq : odd (size (rcons p x0)) != odd (count S (rcons p x0)).
  by move/permP: (ps) => ->; rewrite (perm_size ps) oc; move: ec; case: (odd (count S c)).
have [u [q [y [w [E uS qS Sy oq]]]]] := odd_block Sx0 neq.
case/lastP: u E uS => [|u0 x] E uS.
  case/lastP: w E => [|w0 z] E.
    move: E; rewrite /= cats1 => /rcons_inj [pq _]; move/permP/(_ S): pp c3.
    rewrite pq /= Sx0 => <-; move: qS; rewrite has_count -leqNgt leqn0 => /eqP->.
    by [].
  move: E; rewrite /= -rcons_cons -rcons_cat => /rcons_inj [pE _].
  exists x0, q, y, w0; rewrite -pE Sx0 Sy; split => //.
  by apply: rest_has Sx0 Sy qS; rewrite -pE.
have Sx : S x by case: uS => [/eqP|]; [rewrite -size_eq0 size_rcons | rewrite last_rcons].
have tE : rot (size u0) (rcons p x0) = x :: q ++ y :: (w ++ u0).
  by rewrite E cat_rcons rot_size_cat /= -catA.
exists x, q, y, (w ++ u0); rewrite Sx Sy; split => //.
  by rewrite -tE; apply/Prot.
by apply: rest_has Sx Sy qS; rewrite -tE perm_rot.
Qed.

End Blocks.

(** A consecutive pair of [y :: r ++ [:: x]] with [r] nonempty has an end in [r]. *)
Lemma spairs_inner (T : eqType) (y x : T) (r : seq T) (a b : T) :
  r != [::] -> (a, b) \in spairs (y :: r ++ [:: x]) -> (a \in r) || (b \in r).
Proof.
elim: r y => [//|r1 r IH] y _.
rewrite cat_cons spairs_cons in_cons xpair_eqE => /orP[/andP[_ /eqP->]|h].
  by rewrite mem_head orbT.
case: r IH h => [|r2 r] IH h.
  by move: h; rewrite /= inE xpair_eqE => /andP[/eqP-> _]; rewrite mem_head.
by case/orP: (IH r1 isT h) => h'; apply/orP; [left | right]; rewrite in_cons h' orbT.
Qed.

(** A hole [x :: q ++ y :: rest] and a vertex [v] off it adjacent to [x] and [y] but to no vertex of
    a nonempty [q], with [rest] nonempty: [v], [x], [q], [y] form a hole. *)
Lemma arc_hole (G : sgraph) (v x y : G) (q rest : seq G) :
  induced_cycles.hole (x :: q ++ y :: rest) -> v \notin x :: q ++ y :: rest -> x -- v -> y -- v ->
  ~~ has (fun u => u -- v) q -> q != [::] -> rest != [::] -> induced_cycles.hole (v :: x :: rcons q y).
Proof.
have AE : x :: q ++ y :: rest = (x :: rcons q y) ++ rest by rewrite cat_cons cat_rcons.
case=> /andP[cyc un] [_ chl] vN xv yv qv q0 r0.
set A := x :: rcons q y.
have unA : uniq (A ++ rest) by rewrite -AE.
have vA : v \notin A by apply: contra vN; rewrite AE mem_cat => ->.
have pA : path (--) x (rcons q y).
  by move: cyc; rewrite /= rcons_cat cat_path /= !rcons_path => /and4P[-> -> _ _].
split; [apply/andP; split|split].
- by rewrite /= rcons_path pA last_rcons sgP xv yv.
- by rewrite cons_uniq vA; move: unA; rewrite cat_uniq => /andP[].
- by rewrite /= size_rcons; case: (q) q0.
have SpE : spairs (v :: A ++ [:: v]) = (v, x) :: spairs A ++ [:: (y, v)].
  by rewrite /A cat_cons spairs_cons cats1 -!rcons_cons spairs_rcons2.
have SpC : spairs (x :: (q ++ y :: rest) ++ [:: x]) = spairs A ++ spairs (y :: rest ++ [:: x]).
  by rewrite -catA -cat_cons spairs_cat_mid.
have disj z : z \in A -> z \in rest -> False.
  move=> zA zr; move: unA; rewrite cat_uniq => /and3P[_ /negP nh _]; apply: nh.
  by apply/hasP; exists z.
have oldC a b : a \in A -> b \in A -> a -- b -> ((a, b) \in spairs A) || ((b, a) \in spairs A).
  move=> aA bA ab; have inC z : z \in A -> z \in x :: q ++ y :: rest by rewrite AE mem_cat => ->.
  move: (chl a b (inC a aA) (inC b bA) ab); rewrite consec_spairs SpC !mem_cat.
  rewrite -!orbA => /or4P[h|h|h|h].
  - by rewrite h.
  - by case/orP: (spairs_inner r0 h) => hr; [case: (disj a aA hr) | case: (disj b bA hr)].
  - by rewrite h orbT.
  - by case/orP: (spairs_inner r0 h) => hr; [case: (disj b bA hr) | case: (disj a aA hr)].
have vcase b : b \in A -> v -- b ->
    ((v, b) \in spairs (v :: A ++ [:: v])) || ((b, v) \in spairs (v :: A ++ [:: v])).
  rewrite SpE => bA vb; move: bA; rewrite /A in_cons => /predU1P[->|]; first by rewrite mem_head.
  rewrite mem_rcons in_cons => /predU1P[->|bq]; first by rewrite !(in_cons, mem_cat, mem_seq1) eqxx !orbT.
  by move/negP: qv; case; apply/hasP; exists b => //; rewrite sgP.
move=> a b; rewrite [a \in _]in_cons [b \in _]in_cons => /predU1P[->|aA] /predU1P[->|bA] ab.
- by rewrite sg_irrefl in ab.
- by rewrite consec_spairs; apply: vcase.
- by rewrite consec_spairs orbC; apply: vcase => //; rewrite sgP.
- rewrite consec_spairs SpE.
  by case/orP: (oldC a b aA bA ab) => h; rewrite !in_cons !mem_cat h !orbT.
Qed.

(** *** Even-hole-free graphs have no even wheel *)

Lemma even_hole_free_even_wheel_free (G : sgraph) :
  x27_even_hole_free G -> x220_even_wheel_free G.
Proof.
move=> eh v c hc vc; have uc : uniq c by case: hc => /andP[].
have cardE : #|x220_spokes c v| = count (fun u => u -- v) c.
  rewrite -size_filter; move/card_uniqP: (filter_uniq (fun u => u -- v) uc) => <-.
  by apply: eq_card => u; rewrite !inE mem_filter andbC.
rewrite cardE => s3; apply/negPn/negP => ev.
case oc: (odd (size c)); last by apply: (eh c hc); rewrite oc.
have Prot n s :
    (induced_cycles.hole (rot n s) /\ v \notin rot n s) <-> (induced_cycles.hole s /\ v \notin s).
  rewrite mem_rot; split=> -[h1 h2]; split=> //.
    exact: (induced_cycles.hole_rot n s).1 h1.
  exact: (induced_cycles.hole_rot n s).2 h1.
have [x [q [y [rest [[hq vq] /andP[xv yv] qv oq rh]]]]] :=
  even_arc (S := fun u => u -- v) (P := fun s => induced_cycles.hole s /\ v \notin s)
    Prot (conj hc vc) oc ev s3.
apply: (eh (v :: x :: rcons q y)).
  by apply: arc_hole hq vq xv yv qv _ _; [case: (q) oq | case: (rest) rh].
by rewrite /= size_rcons /= !negbK oq.
Qed.

(** *** The edge *)

Theorem theta_prism_even_wheel_free_bounded_treewidth_implies_even_hole_k4_diamond_free_bounded_treewidth :
  theta_prism_even_wheel_free_bounded_treewidth_statement ->
  even_hole_k4_diamond_free_bounded_treewidth_statement.
Proof.
apply: e051_modulo_even_wheel => G eh _.
exact: even_hole_free_even_wheel_free.
Qed.

Print Assumptions even_hole_free_even_wheel_free.
Print Assumptions theta_prism_even_wheel_free_bounded_treewidth_implies_even_hole_k4_diamond_free_bounded_treewidth.
