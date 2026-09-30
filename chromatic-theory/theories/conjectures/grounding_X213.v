(** * Chromatic.conjectures.grounding_X213 -- grounding lemmas for wave X213.

    Qed-closed, axiom-free sanity results for the primitives introduced in
    [X213.v] and for the hypothesis blocks of its six statements: a SATISFIABLE
    witness for every guard, and a GUARD-HAS-TEETH lemma showing that the obvious
    degenerate reading fails.  These validate the statements; they do not prove
    them. *)

From mathcomp Require Import fingroup perm.
From GraphTheory Require Import bij.
From GTBase Require Import base.
From Chromatic.conjectures Require Import U8 X3 X213.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Arithmetic / cardinality helpers ***********************************)

(** Three pairwise distinct vertices do not fit in a two-vertex graph. *)
Lemma x213_no_three_distinct_I2 (u v w : 'I_2) :
  u != v -> u != w -> v != w -> False.
Proof.
rewrite -!val_eqE /=; move: (ltn_ord u) (ltn_ord v) (ltn_ord w).
by case: (val u) => [|[|nu]]; case: (val v) => [|[|nv]]; case: (val w) => [|[|nw]].
Qed.

(** ** [x213_proper_edge_colouring] / [x213_edge_colourable] **************)

(** Non-vacuity, and the [bm-057] hypothesis block at its smallest instance:
    [K_2] has two vertices (an even, positive number), is 1-regular, satisfies
    2 <= 2*1, and IS 1-edge-colourable.  So the conjecture's guard is
    satisfiable and its conclusion is not empty there. *)
Lemma x213_regular_K2 : regular 'K_2 1.
Proof.
move=> v; have -> : N(v) = [set~ v].
  by apply/setP => u; rewrite !inE /= eq_sym.
by rewrite cardsC1 card_ord.
Qed.

Lemma x213_edge_colourable_K2 : x213_edge_colourable 'K_2 1.
Proof.
exists (fun _ _ => ord0); split => // u v w uv uw vw.
by case: (x213_no_three_distinct_I2 uv uw vw).
Qed.

Lemma x213_one_factorization_hypotheses_K2 :
  [/\ 0 < #|'K_2|, ~~ odd #|'K_2|, regular 'K_2 1, #|'K_2| <= 2 * 1
    & x213_edge_colourable 'K_2 1].
Proof.
rewrite card_ord; split => //.
- exact: x213_regular_K2.
- exact: x213_edge_colourable_K2.
Qed.

(** Guard has teeth: one colour is NOT enough for [K_3] -- the number of colours
    really constrains [x213_edge_colourable]. *)
Lemma x213_not_edge_colourable_K3_1 : ~ x213_edge_colourable 'K_3 1.
Proof.
case=> col [_ prop].
pose a : 'K_3 := @Ordinal 3 0 isT.
pose b : 'K_3 := @Ordinal 3 1 isT.
pose c : 'K_3 := @Ordinal 3 2 isT.
have ab : a -- b by [].
have ac : a -- c by [].
have bc : b != c by [].
by move: (prop a b c ab ac bc); rewrite (ord1 (col a b)) (ord1 (col a c)) eqxx.
Qed.

(** ** [x213_used_colours] ************************************************)

(** Non-vacuity: the colour of an edge is used. *)
Lemma x213_used_colours_edge (G : sgraph) (k : nat) (col : G -> G -> 'I_k)
    (u v : G) : u -- v -> col u v \in x213_used_colours col.
Proof.
move=> uv; rewrite inE; apply/existsP; exists u; apply/existsP; exists v.
by rewrite uv eqxx.
Qed.

(** Guard has teeth: an edgeless graph uses NO colour, so the bound
    [#|used colours| <= m] is not vacuously informative. *)
Lemma x213_used_colours_K1 (k : nat) (col : 'K_1 -> 'K_1 -> 'I_k) :
  x213_used_colours col = set0.
Proof.
apply/setP => c; rewrite !inE; apply/existsP => -[u /existsP[v]].
by rewrite /edge_rel /= (ord1 u) (ord1 v) eqxx.
Qed.

(** ** [x213_kempe_step] / [x213_kempe_reach] *****************************)

(** Non-vacuity: interchanging two colours on the EMPTY set changes nothing, so
    every colouring of a nonempty graph makes a (trivial) Kempe step to itself
    and reaches itself. *)
Lemma x213_kempe_step_refl (G : sgraph) (k : nat) (x : G)
    (col : G -> G -> 'I_k) : x213_kempe_step col col.
Proof.
exists (col x x), (col x x), set0; split.
- by move=> u v; rewrite !inE.
- by move=> u v; rewrite inE.
- by move=> u v w; rewrite inE.
- by move=> u v; rewrite inE.
Qed.

Lemma x213_kempe_reach_refl (G : sgraph) (k n : nat) (col : G -> G -> 'I_k) :
  x213_kempe_reach n col col.
Proof. by case: n => [|n] //=; left. Qed.

(** Structural law: a Kempe change only moves colours between the two chosen
    ones -- off the interchanged set the colouring is unchanged. *)
Lemma x213_kempe_step_fixed (G : sgraph) (k : nat) (col col' : G -> G -> 'I_k) :
  x213_kempe_step col col' ->
  exists a b : 'I_k,
    forall u v : G, (col' u v = col u v) \/ (col' u v = a) \/ (col' u v = b).
Proof.
case=> a [b] [K] [_ _ _ Hcol']; exists a, b => u v.
by rewrite Hcol'; case: ifP => _; [case: ifP => _; [right; right | right; left] | left].
Qed.

(** ** [bm-045] hypothesis block ******************************************)

(** Guard has teeth: [K_3] is 3-chromatic but DOES contain a 3-clique, so the
    "no k-clique" guard of the Erdos-Lovasz Tihany statement excludes it (a
    complete graph obviously has no splitting of the required kind). *)
Lemma x213_chi_K3 : χ([set: 'K_3]) = 3.
Proof.
have cl : clique [set: 'K_3] by move=> x y _ _ xy.
by rewrite (chi_clique cl) cardsT card_ord.
Qed.

Lemma x213_erdos_lovasz_tihany_guard_excludes_K3 :
  ~ (forall S : {set 'K_3}, clique S -> #|S| < 3).
Proof.
move=> H; have cl : clique [set: 'K_3] by move=> x y _ _ xy.
by move: (H [set: 'K_3] cl); rewrite cardsT card_ord.
Qed.

(** ** [bm-046] hypothesis block ******************************************)

(** Non-vacuity: two empty vertex sets are anticomplete and both have
    chromatic number 0, so the second alternative of the El-Zahar-Erdos
    conclusion is satisfiable (at k = 0). *)
Lemma x213_anticomplete_set0 (G : sgraph) :
  x3_anticomplete (@set0 G) (@set0 G) /\ χ(@set0 G) = 0 /\ χ(@set0 G) = 0.
Proof.
split; last by split; exact: chi0.
by split; [rewrite -setI_eq0 set0I eqxx | move=> a b; rewrite inE].
Qed.

(** Guard has teeth: the clique alternative is not free -- [K_1] has no
    2-clique, so at r = 2 the first disjunct genuinely fails on it. *)
Lemma x213_no_two_clique_K1 : ~ (exists S : {set 'K_1}, clique S /\ #|S| = 2).
Proof.
case=> S [_ cS]; have : #|S| <= #|'K_1| by apply: max_card.
by rewrite cS card_ord.
Qed.

(** ** [bm-050] hypothesis block ******************************************)

(** Non-vacuity: [K_2] is triangle-free and has no induced [K_3], so both
    guards of the triangle-free induced-tree statement hold together. *)
Lemma x213_triangle_free_K2 : triangle_free 'K_2.
Proof.
move=> x y z xy yz zx.
by apply: (x213_no_three_distinct_I2 (u := x) (v := y) (w := z)); rewrite // eq_sym.
Qed.

Lemma x213_no_induced_K3_in_K2 : ~ has_induced 'K_3 'K_2.
Proof.
case=> S [d]; have Hc := card_bij (diso_v d).
have le : #|[pred x : 'K_2 | x \in S]| <= #|'K_2| by apply: max_card.
by move: le; rewrite -card_sig -Hc !card_ord.
Qed.

(** ** [bm-053] hypothesis block ******************************************)

(** Non-vacuity of the toroidal guard.  A graph with NO dart -- an edgeless
    graph -- carries the identity rotation system, and GTBase's Euler count
    evaluates it to at most one, so such a graph passes [surface_embeddable 1].
    Recall the convention checked in base/theories/surface.v: [surface_euler_genus]
    halves (2 + E - V - F), so its value is the ORIENTABLE genus and the TORUS is
    the index 1, not 2 (this is the defect the 2026-09-23 readback blocked bm-053
    and the three X219 toroidal rows on).
    VERTEX-COUNT UPDATE (base fix 2026-09-23): V now counts EVERY vertex, isolated
    ones included, so a dartless graph with at least one vertex has computed genus
    0, not 1 -- the bound proved here is the weaker [<= 1], which stays true and is
    all the toroidal guard needs.  The sharp statements now live in base:
    [surface_embeddable_edgeless] (every nonempty edgeless graph is PLANAR) and the
    canary [surface_embeddable_K1]; the two lemmas below are kept as the local
    re-derivation this grounding file quotes. *)
Lemma x213_surface_embeddable_no_dart (G : sgraph) :
  (forall d : surface_dart G, False) -> surface_embeddable 1 G.
Proof.
move=> nodart.
pose e : {perm surface_dart G} := 1%g.
have Hsrc : forall d : surface_dart G, (sval (e d)).1 = (sval d).1.
  by move=> d; case: (nodart d).
have Hvtx : forall d : surface_dart G,
    porbit e d = [set d' | (sval d').1 == (sval d).1].
  by move=> d; case: (nodart d).
have c0 : #|{: surface_dart G}| = 0.
  by apply: eq_card0 => d; case: (nodart d).
exists (@SurfaceEmbedding G e Hsrc Hvtx).
rewrite /surface_euler_genus /surface_embedding_edges c0 div0n addn0.
set V := surface_embedding_vertices _; set F := surface_embedding_faces _.
have h : 2 - V - F <= 2 by apply: leq_trans (leq_subr F (2 - V)) (leq_subr V 2).
by apply: (leq_trans (leq_div2r 2 h)).
Qed.

Lemma x213_no_dart_K1 (d : surface_dart 'K_1) : False.
Proof. by case: d => [[x y]] /=; rewrite /edge_rel /= (ord1 x) (ord1 y) eqxx. Qed.

Lemma x213_surface_embeddable_K1 : surface_embeddable 1 'K_1.
Proof. exact: x213_surface_embeddable_no_dart x213_no_dart_K1. Qed.

(** The [bm-053] hypothesis block is SATISFIABLE in its repaired form: the
    one-vertex graph embeds in the torus AND is connected. *)
Lemma x213_toroidal_guard_K1 :
  surface_embeddable 1 'K_1 /\ connected [set: 'K_1].
Proof.
split; first exact: x213_surface_embeddable_K1.
have -> : [set: 'K_1] = [set (ord0 : 'K_1)].
  by apply/setP => x; rewrite !inE (ord1 x) eqxx.
exact: connected1.
Qed.

(** GUARD HAS TEETH (the connectivity half, added 2026-09-23; comment refreshed
    for the base vertex-count fix of the same day).  The two-vertex edgeless graph
    is accepted as "toroidal" although it is disconnected: [surface_euler_genus]
    applies one Euler-characteristic formula to the whole graph, and here that
    formula returns genus 0 (V = 2, E = F = 0, and the nat subtraction truncates),
    which is exactly what let the padding refutation of the X219 row
    arxiv:2407.18800#01 through.  The [connected [set: G]] guard excludes this
    graph, so it is not decorative.  (Before the base fix the same graph was
    accepted through the isolated-vertex blind spot instead, at computed genus 1;
    the witness and the lemma below are unchanged, only the arithmetic behind them
    is.) *)
Definition x213_two_isolated : sgraph := sjoin 'K_1 'K_1.

Lemma x213_no_dart_two_isolated (d : surface_dart x213_two_isolated) : False.
Proof.
by case: d => [[[x|x] [y|y]] p]; move: p;
   rewrite /edge_rel /= ?(ord1 x) ?(ord1 y) ?sg_irrefl.
Qed.

Lemma x213_two_isolated_embeddable : surface_embeddable 1 x213_two_isolated.
Proof. exact: x213_surface_embeddable_no_dart x213_no_dart_two_isolated. Qed.

Lemma x213_two_isolated_disconnected : ~ connected [set: x213_two_isolated].
Proof.
move=> /connectedTE /(_ (inl ord0) (inr ord0)).
by rewrite (@join_disc 'K_1 'K_1).
Qed.

Lemma x213_connected_guard_has_teeth :
  exists G : sgraph, surface_embeddable 1 G /\ ~ connected [set: G].
Proof.
exists x213_two_isolated; split; first exact: x213_two_isolated_embeddable.
exact: x213_two_isolated_disconnected.
Qed.

Print Assumptions erdos_lovasz_tihany_statement.
Print Assumptions el_zahar_erdos_statement.
Print Assumptions triangle_free_induced_tree_chi_bounded_statement.
Print Assumptions albertson_toroidal_delete_three_statement.
Print Assumptions one_factorization_conjecture_statement.
Print Assumptions vizing_kempe_interchange_statement.
Print Assumptions x213_edge_colourable_K2.
Print Assumptions x213_not_edge_colourable_K3_1.
Print Assumptions x213_kempe_step_refl.
Print Assumptions x213_surface_embeddable_K1.
Print Assumptions x213_toroidal_guard_K1.
Print Assumptions x213_connected_guard_has_teeth.
