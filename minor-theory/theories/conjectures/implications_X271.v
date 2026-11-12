(** * Minor.conjectures.implications_X271 -- two Rocq-only edges from X214's rows into X271's.

    Wave X271 encodes, among its rows, Hajos' conjecture at five (studies:std_haj_s_conjecture_k_5,
    [hajos_k5_subdivision_statement]) and Seymour's H-Hadwiger conjecture (studies:std_h_hadwiger_conjecture,
    [h_hadwiger_minor_free_colourable_statement]).  Wave X214 encodes the Bondy-Murty rows bm:bm-042 (Hajos for
    k = 5 and k = 6, [hajos_k5_k6_subdivision_statement]) and bm:bm-041 (Hadwiger,
    [hadwiger_chromatic_clique_minor_statement]).  The theorems below record two Rocq-only implication edges
    (meta/corpus_relations.json joins neither pair):
    - Hajos at k = 5 and 6 => Hajos at k = 5: the instance k = 5, with the same exact chromatic number and the same
      subdivision containment (X271's Notes name it a candidate edge);
    - Hadwiger => H-Hadwiger, which Fischer and Steiner note (arXiv:2304.04246v1, text l.73): if G has no H minor
      and #|H| <= chi(G), Hadwiger at chi(G) gives a minor of the complete graph on chi(G) vertices, which has H as
      a subgraph, so G would have an H minor; hence chi(G) <= #|H| - 1.
    Neither converse is claimed (over all H, the converse of the second needs minor to be decidable).
    A third Rocq-only edge, inside X271, follows them: the two phrasings of the odd Hadwiger conjecture
    (studies:std_odd_hadwiger_conjecture, [odd_hadwiger_chromatic_odd_minor_statement], and
    studies:std_odd_hadwiger_conjecture_411, [odd_hadwiger_odd_minor_free_colourable_statement]) are equivalent, as
    X271's Notes say; its converse direction uses the decidability of X271's odd-minor tree model on finite graphs.
    Axiom-free: only [Qed]-closed results, and no helper of its own. *)

From GTBase Require Import base.
From GraphTheory Require Import minor.
From Minor.conjectures Require Import X214 X271.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Hajos at k = 5 and 6 (X214, bm:bm-042) ==> Hajos at k = 5 (X271) *)

(*@EDGE from=hajos_k5_k6_subdivision_statement to=hajos_k5_subdivision_statement kind=implies status=verified proof=hajos_k5_k6_subdivision_implies_hajos_k5_subdivision note="Rocq-only edge (no corpus relation), routed after wave X271 (Lancelot's (685), (686)): bm:bm-042 states Hajos' conjecture for k = 5 and k = 6; its instance k = 5 is studies:std_haj_s_conjecture_k_5, with the same exact chromatic number and the same subdivision containment (has_subdivision); X271's Notes name it a candidate edge." *)
Theorem hajos_k5_k6_subdivision_implies_hajos_k5_subdivision :
  hajos_k5_k6_subdivision_statement -> hajos_k5_subdivision_statement.
Proof.
move=> hajos G chiG.
exact: (hajos 5 G (or_introl erefl) chiG).
Qed.

(** ** Hadwiger (X214, bm:bm-041) ==> H-Hadwiger (X271) *)

(*@EDGE from=hadwiger_chromatic_clique_minor_statement to=h_hadwiger_minor_free_colourable_statement kind=implies status=verified proof=hadwiger_chromatic_clique_minor_implies_h_hadwiger_minor_free_colourable note="Rocq-only edge (no corpus relation), routed after wave X271 (Lancelot's (685), (686)): Hadwiger's conjecture implies Seymour's H-Hadwiger conjecture for every H (Fischer and Steiner, arXiv:2304.04246v1, text l.73). If G has no H minor and #|H| <= chi(G), Hadwiger at chi(G) gives a minor of the complete graph on chi(G) vertices; H is a subgraph of it (widen_ord after enum_rank, injective, and distinct vertices are adjacent there), so sub_minor and minor_trans give an H minor, a contradiction; otherwise chi(G) <= #|H| - 1. The H with no vertex falls in the first case." *)
Theorem hadwiger_chromatic_clique_minor_implies_h_hadwiger_minor_free_colourable :
  hadwiger_chromatic_clique_minor_statement -> h_hadwiger_minor_free_colourable_statement.
Proof.
move=> had H G nHG.
case: (leqP #|H| χ([set: G])) => [le|lt]; last by move: lt; case: #|H|.
exfalso; apply: nHG; apply: (minor_trans (had _ G erefl)); apply: sub_minor.
exists (fun x : H => widen_ord le (enum_rank x)).
  by move=> x y /(congr1 val) /= /val_inj /enum_rank_inj.
by move=> x y _ ne.
Qed.

(** ** The two phrasings of the odd Hadwiger conjecture (X271) are equivalent *)

(** studies:std_odd_hadwiger_conjecture ([odd_hadwiger_chromatic_odd_minor_statement]: t <= chi(G) gives an odd K_t
    minor) and studies:std_odd_hadwiger_conjecture_411 ([odd_hadwiger_odd_minor_free_colourable_statement]: for
    t >= 2, no odd K_t minor gives chi(G) <= t - 1), both in X271's tree model [x271_odd_minor_tree_model].  X271's
    Notes say that they are one conjecture: for t >= 2 each instance is the contrapositive of the other's, and the
    first row's instances t <= 1 hold.
    - Forward: the contrapositive, on nat.
    - Backward: the tree model is decidable on finite graphs, through a Boolean form over [{ffun 'K_t -> {set G}}]
      and [{ffun G -> bool}] (as Minor.foundations.minor_dec does for [minor]).  Without a model, t = 0 has the
      empty model, t = 1 a one-vertex model (chi(G) >= 1 gives a vertex, leq_chi), and t >= 2 contradicts the
      second phrasing.
    Both rows are disproved at the pin (Kuhn, Sauermann, Steiner and Wigderson, arXiv:2512.20392v1, Theorem 1.3);
    the equivalence records that the two phrasings fall together. *)

(*@EDGE from=odd_hadwiger_chromatic_odd_minor_statement to=odd_hadwiger_odd_minor_free_colourable_statement kind=equiv status=verified proof=odd_hadwiger_chromatic_odd_minor_equiv_odd_hadwiger_odd_minor_free_colourable note="Rocq-only edge (no corpus relation), routed after X305 (Lancelot's (712), (714)): the two phrasings of the odd Hadwiger conjecture, studies:std_odd_hadwiger_conjecture (t <= chi(G) gives an odd K_t minor) and studies:std_odd_hadwiger_conjecture_411 (for t >= 2, no odd K_t minor gives chi(G) <= t - 1), over X271's tree model; X271's Notes say that they are one conjecture. Forward: the contrapositive, on nat. Backward: the tree model is decidable on finite graphs (a Boolean form over finite functions); without a model, the empty model at t = 0, a one-vertex model at t = 1, and the second phrasing at t >= 2. Both rows are disproved at the pin." *)
Theorem odd_hadwiger_chromatic_odd_minor_equiv_odd_hadwiger_odd_minor_free_colourable :
  odd_hadwiger_chromatic_odd_minor_statement <-> odd_hadwiger_odd_minor_free_colourable_statement.
Proof.
split.
- move=> odd t G t2 nm; case: t t2 nm => [|[|t]] // _ nm.
  rewrite leqNgt; apply/negP => lt; exact: nm (odd _ G lt).
- move=> odd2 t G tchi.
  pose b := [exists B : {ffun 'K_t -> {set G}}, exists sigma : {ffun G -> bool},
    [&& [forall x, B x != set0],
        [forall x, forall u, forall v, (u \in B x) ==> (v \in B x) ==>
           connect (fun a c : G => [&& a \in B x, c \in B x, a -- c & sigma a != sigma c]) u v],
        [forall x, forall y, (x != y) ==> [disjoint B x & B y]] &
        [forall x, forall y, (x -- y) ==>
           [exists u, exists v, [&& u \in B x, v \in B y, u -- v & sigma u == sigma v]]]]].
  have bP : b -> x271_odd_minor_tree_model G 'K_t.
    case/existsP => B /existsP [sigma] /and4P [/forallP p1 /forallP p2 /forallP p3 /forallP p4].
    exists (fun x => B x), (fun v => sigma v); split.
    + exact: p1.
    + by move=> x u v uB vB; move: (p2 x) => /forallP/(_ u)/forallP/(_ v); rewrite uB vB.
    + by move=> x y xy; move: (p3 x) => /forallP/(_ y); rewrite xy.
    + move=> x y xy; move: (p4 x) => /forallP/(_ y); rewrite xy.
      by case/existsP => u /existsP [v /and4P [uB vB uv su]]; exists u, v.
  have Pb : x271_odd_minor_tree_model G 'K_t -> b.
    case=> B [sigma [q1 q2 q3 q4]]; apply/existsP; exists (finfun B); apply/existsP; exists (finfun sigma).
    apply/and4P; split.
    + by apply/forallP => x; rewrite ffunE.
    + apply/forallP => x; apply/forallP => u; apply/forallP => v; apply/implyP => uB; apply/implyP => vB.
      rewrite !ffunE in uB vB.
      apply: (@connect_sub _ (fun a c : G => [&& a \in B x, c \in B x, a -- c & sigma a != sigma c]));
        last exact: q2 x u v uB vB.
      by move=> a c e; apply: connect1; rewrite !ffunE.
    + by apply/forallP => x; apply/forallP => y; apply/implyP => xy; rewrite !ffunE; exact: q3.
    + apply/forallP => x; apply/forallP => y; apply/implyP => xy; case: (q4 x y xy) => u [v [uB vB uv su]].
      by apply/existsP; exists u; apply/existsP; exists v; rewrite !ffunE uB vB uv su.
  case: (boolP b) => [/bP //|/negP nb]; exfalso.
  have nm : ~ x271_odd_minor_tree_model G 'K_t by move/Pb.
  clear bP Pb nb b; case: t tchi nm => [|[|t]] tchi nm.
  + by apply: nm; exists (fun _ => set0), (fun _ => true); split; case.
  + have : 0 < #|G| by apply: leq_trans tchi _; rewrite -cardsT; exact: leq_chi.
    case/card_gt0P => v _; apply: nm; exists (fun _ => [set v]), (fun _ => true); split.
    * by move=> x; apply/set0Pn; exists v; rewrite inE.
    * by move=> x u w; rewrite !inE => /eqP-> /eqP->; exact: connect0.
    * by move=> x y; rewrite [x]ord1 [y]ord1 eqxx.
    * by move=> x y; rewrite [x]ord1 [y]ord1 sg_irrefl.
  + by move: (odd2 t.+2 G isT nm) => /(leq_trans tchi); rewrite ltnn.
Qed.
