(** * Digraph.conjectures.implications_X221 — wave X221 implication edges

    The three confirmed [implies] relations of meta/corpus_relations.json whose
    BOTH endpoints now own a Rocq statement:

      - e105 : arxiv:2306.04710#02 ==> arxiv:2202.13306#00
               (hero status of Delta(1,2,2) in {K_1 + P⃗_2}-free digraphs implies
               the same in oriented complete multipartite graphs).
               VERIFIED here by the Qed theorem
               [delta122_hero_k1_plus_dipath2_free_implies_delta122_hero_oriented_complete_multipartite]: an oriented complete
               multipartite digraph has no induced copy of an arc plus an
               isolated vertex, so its class is contained in the source class
               and the single dicolouring bound transfers.
      - e106 : arxiv:2410.23566#03 ==> arxiv:2410.23566#05
               ([conj_9] of conjectures/unvd.v implies
               [kextension_linear_unavoidability_statement]).
               VERIFIED here by the Qed theorem
               [conj_9_implies_kextension_linear_unavoidability] (below): every
               acyclic digraph HAS a pinned unavoidability value (unavoidability
               is decidable, and 2 ^ |V| vertices suffice), acyclicity passes to
               induced subdigraphs, and the k deletions form an isomorphism
               chain, so conj_9's constant C gives the bound
               max(C,1)^k * max(c,1) * |V(E)| for the k-extension E.
      - e158 : arxiv:2403.02298#00 ==> arxiv:2403.02298#01
               (the acyclic-number Theta conjecture implies the dichromatic
               Theta conjecture).
               CANDIDATE: the source's argument goes through the inequality
               t-vec(n) >= n / a-vec(n) and the paper's already-proved upper
               bound t-vec(n) <= (sqrt 2 + o(1)) sqrt(n / log n). Both are
               external inputs (the first is the standard
               chi-vec >= |V| / alpha-vec bound, the second a theorem of the
               paper); neither is formalized, so the edge is recorded, not
               proved. Asserting it with the missing halves as hypotheses would
               smuggle in the conclusion.

    No X216 implication file exists: the only corpus relation touching
    bm:bm-070 is e233 to opg:caccetta_haggkvist_conjecture, whose verdict is
    [related_only] ("neither implies the other"), so no edge is scheduled. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup all_algebra.
From Digraph Require Import prelude interop_graph_theory digraph oriented tournament.
From Digraph Require Import dipath order strong classic_core dichromatic omegabar.
From Digraph Require Import heroes heroes_dichotomy unvd twinwidth twinwidth_ordered.
From GTBase Require Import asymptotics.
From Digraph Require Import X221.
From Digraph.foundations Require Import tournament_unavoidability.
From Digraph.foundations Require subdivision.
From Digraph.conjectures Require implications_X123 grounding_dichromatic_cycle.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The class bridge for e105

    In an oriented complete multipartite digraph, non-adjacency is transitive,
    so no vertex can be non-adjacent to both ends of an arc: there is no
    induced copy of an arc together with an isolated vertex. *)
Lemma x221_ocm_no_arrow (D : diGraphType) :
  x221_oriented_complete_multipartite D -> no_induced_arrowK2_K1 D.
Proof.
move=> [_ tr] [a [b [c [_ [_ [_ [ab [_ [nacx [ncax [nbcx ncbx]]]]]]]]]]].
have h1 : x221_nonadj a c by rewrite /x221_nonadj nacx ncax.
have h2 : x221_nonadj c b by rewrite /x221_nonadj ncbx nbcx.
by have := tr _ _ _ h1 h2; rewrite /x221_nonadj ab.
Qed.

(*@EDGE from=delta122_hero_k1_plus_dipath2_free_statement to=delta122_hero_oriented_complete_multipartite_statement kind=implies status=verified proof=delta122_hero_k1_plus_dipath2_free_implies_delta122_hero_oriented_complete_multipartite cite="gc:e105" note="Class containment: an oriented complete multipartite digraph has transitive non-adjacency, hence no induced arc-plus-isolated-vertex (K_1 + P_2-directed); so the guarded class of the source is a superclass of the target's and the single dicolouring bound transfers verbatim." *)

Theorem delta122_hero_k1_plus_dipath2_free_implies_delta122_hero_oriented_complete_multipartite :
  delta122_hero_k1_plus_dipath2_free_statement ->
  delta122_hero_oriented_complete_multipartite_statement.
Proof.
move=> [B hB]; exists B => D [ocm df]; apply: hB; split.
- by case: ocm.
- exact: x221_ocm_no_arrow ocm.
- exact: df.
Qed.

(** ** The converse class bridge (the reverse of e105)

    Within ORIENTED digraphs the two class descriptions coincide: if
    non-adjacency were not transitive there would be vertices [u], [v], [w] with
    [u], [v] non-adjacent, [v], [w] non-adjacent and [u], [w] adjacent, which is
    an induced arc plus a vertex non-adjacent to both its ends.  (The degenerate
    equalities are discharged by the adjacency of [u] and [w].) *)
Lemma x221_no_arrow_ocm (D : diGraphType) :
  oriented_dg D -> no_induced_arrowK2_K1 D ->
  x221_oriented_complete_multipartite D.
Proof.
move=> Dor naf.
have arc_neq : forall x y : D, x --> y -> x != y.
  move=> x y xy; apply/eqP => e; rewrite -e in xy.
  by apply: (negP (Dor _ _ xy)).
have key : forall a b c : D, a --> b ->
    ~~ (a --> c) -> ~~ (c --> a) -> ~~ (b --> c) -> ~~ (c --> b) -> False.
  move=> a b c ab nac nca nbc ncb; apply: naf; exists a, b, c.
  have hab : a != b := arc_neq _ _ ab.
  have hac : a != c.
    by apply/eqP => e; rewrite -e in ncb; apply: (negP ncb).
  have hbc : b != c.
    by apply/eqP => e; rewrite -e in nac; apply: (negP nac).
  exact: (conj hab (conj hac (conj hbc (conj ab
            (conj (Dor _ _ ab) (conj nac (conj nca (conj nbc ncb)))))))).
split; first exact: Dor.
move=> u v w; rewrite /x221_nonadj => /andP[nuv nvu] /andP[nvw nwv].
apply/andP; split; apply/negP => harc.
- exact: (key u w v harc nuv nvu nwv nvw).
- exact: (key w u v harc nwv nvw nuv nvu).
Qed.

(*@EDGE from=delta122_hero_oriented_complete_multipartite_statement to=delta122_hero_k1_plus_dipath2_free_statement kind=implies status=verified proof=delta122_hero_oriented_complete_multipartite_implies_delta122_hero_k1_plus_dipath2_free cite="audit: meta/X211-X229_faithfulness_audit.md:178 (corpus e105 is the other direction)" note="Converse class bridge: within oriented digraphs 'no induced arc-plus-isolated-vertex' IMPLIES that non-adjacency is transitive (a non-transitivity witness u,v,w is exactly such an induced pattern), so the two guarded classes are equal and the single dicolouring bound transfers back. Together with the e105 direction the two Props are equivalent; the corpus nevertheless lists the source row disproved and the target row open." *)

Theorem delta122_hero_oriented_complete_multipartite_implies_delta122_hero_k1_plus_dipath2_free :
  delta122_hero_oriented_complete_multipartite_statement ->
  delta122_hero_k1_plus_dipath2_free_statement.
Proof.
move=> [B hB]; exists B => D [Dor naf df]; apply: hB; split=> //.
exact: x221_no_arrow_ocm.
Qed.

(*@EDGE from=conj_9 to=kextension_linear_unavoidability_statement kind=implies status=verified proof=conj_9_implies_kextension_linear_unavoidability cite="gc:e106" note="Proved: every acyclic digraph has a pinned unavoidability value (tournament unavoidability is decidable over relations on 'I_M through the foundation's tournament_unavoidable_unbundledE, and 2^|V| vertices suffice by a transitive subtournament, implications_X123's ramsey_transitive, along a topological order, subdivision's acyclic_topo_embed); acyclicity passes to induced subdigraphs; deleting the k added vertices one at a time is an isomorphism chain, so conj_9's C at each step gives unvd(E) <= max(C,1)^k * max(c,1) * |V(E)|, and a digraph with at most one vertex has value at most its order." *)

(** ** e106: Conjecture 9 implies the linear unavoidability of k-extensions

    The literature argument deletes the k added vertices one at a time and applies
    unvd(E) <= C * unvd(E - v) at each step. Over the RELATIONAL [unvd] it needs two
    facts that the two statements do not give; both are proved here.
    - Existence (F1, F2): [tournament_unavoidable D M] is decidable ([e106_unavbP]: a
      finite search over tournaments on ['I_M], read back through the foundation's
      [tournament_unavoidable_unbundledE] and the arc-only carrier [e106_rel_carrier]),
      and an acyclic [D] is [2 ^ #|D|]-unavoidable ([e106_acyclic_unavoidable]: a
      transitive set of [#|D|.+1] vertices, implications_X123's [ramsey_transitive],
      ordered by out-rank, receives [D] along a topological order, subdivision's
      [acyclic_topo_embed]); so [ex_minn] gives the value ([e106_unvd_exists]).
    - The chain (F3): the value is invariant under [dgiso]; acyclicity passes to
      induced subdigraphs (grounding_dichromatic_cycle's [acyclicb_potential]); in
      [del_vertex s] the complement of the rest of [S] is isomorphic to the complement
      of [S] ([e106_del_induced]).
    [e106_kext_bound] inducts on k: k = 0 transfers c along the isomorphism; a step with
    more than one vertex applies conj_9 to the deletion of a vertex of [S]; a digraph
    with at most one vertex has value at most its order ([e106_unvd_small]). The bound
    is max(C,1)^k * max(c,1). The three modules above are only Required, so their
    generic names stay qualified. *)

(** ** F1: tournament unavoidability is decidable, so every unavoidable digraph has a least value *)

(** A relation on ['I_M] read as a digraph (only the arc relation; no tournament is built). *)
Definition e106_rel_carrier (M : nat) (r : rel 'I_M) : Type := 'I_M.
HB.instance Definition _ (M : nat) (r : rel 'I_M) := Finite.on (e106_rel_carrier r).
HB.instance Definition _ (M : nat) (r : rel 'I_M) := HasArc.Build (e106_rel_carrier r) r.

(** [r] is a tournament on ['I_M]: no loop, and exactly one arc between two distinct vertices. *)
Definition e106_tourb (M : nat) (r : {ffun 'I_M * 'I_M -> bool}) : bool :=
  [forall i, [forall j, if i == j then ~~ r (i, j) else r (i, j) (+) r (j, i)]].

(** Every tournament on ['I_M] receives [D] injectively and arc-preservingly. *)
Definition e106_unavb (D : diGraphType) (M : nat) : bool :=
  [forall r : {ffun 'I_M * 'I_M -> bool}, e106_tourb r ==>
    [exists f : {ffun D -> 'I_M},
      injectiveb f && [forall u, [forall v, (u --> v) ==> r (f u, f v)]]]].

Lemma e106_unavbP (D : diGraphType) (M : nat) :
  reflect (tournament_unavoidable D M) (e106_unavb D M).
Proof.
apply: (iffP forallP) => [H | H r].
- apply/tournament_unavoidable_unbundledE => T irr semi asym cardT.
  pose e (i : 'I_M) : T := enum_val (cast_ord (esym cardT) i).
  have e_inj : injective e by move=> i j /enum_val_inj /cast_ord_inj.
  pose r := [ffun p : 'I_M * 'I_M => e p.1 --> e p.2].
  have tr : e106_tourb r.
    apply/forallP => i; apply/forallP => j; rewrite !ffunE /=.
    have [<-|ij] := eqVneq i j; first by rewrite irr.
    have eij : e i != e j by rewrite (inj_eq e_inj).
    by case/orP: (semi _ _ eij) => a; rewrite a (negbTE (asym _ _ a)).
  have /implyP /(_ tr) /existsP [f /andP [/injectiveP finj /forallP fhom]] := H r.
  exists (e \o f); split; first exact: inj_comp e_inj finj.
  by move=> u v uv; have := implyP (forallP (fhom u) v) uv; rewrite ffunE.
- apply/implyP => tr; pose rr (i j : 'I_M) := r (i, j).
  have irr : irreflexive (@arc (e106_rel_carrier rr)).
    by move=> i; have := forallP (forallP tr i) i; rewrite eqxx => /negbTE.
  have xo (i j : 'I_M) : i != j -> r (i, j) (+) r (j, i).
    by move=> ij; have := forallP (forallP tr i) j; rewrite (negbTE ij).
  have semi (u v : e106_rel_carrier rr) : u != v -> (u --> v) || (v --> u).
    move=> uv; have := xo u v uv.
    change ((u --> v) || (v --> u)) with (r (u, v) || r (v, u)).
    by case: (r (u, v)); case: (r (v, u)).
  have asym (u v : e106_rel_carrier rr) : u --> v -> ~~ (v --> u).
    move=> uv; have [e|ne] := eqVneq u v; first by move: uv; rewrite e irr.
    move: (xo u v ne) uv; change ((u --> v) -> ~~ (v --> u)) with (r (u, v) -> ~~ r (v, u)).
    by case: (r (u, v)); case: (r (v, u)).
  have [f [finj fhom]] :=
    (tournament_unavoidable_unbundledE D M).1 H (e106_rel_carrier rr) irr semi asym (card_ord M).
  apply/existsP; exists [ffun x => (f x : 'I_M)]; apply/andP; split.
    by apply/injectiveP => x y; rewrite !ffunE; exact: finj.
  by apply/forallP => u; apply/forallP => v; apply/implyP => uv; rewrite !ffunE; exact: fhom.
Qed.

(** ** F2: an acyclic digraph is unavoidable (2 ^ #|D| vertices suffice) *)
Lemma e106_acyclic_unavoidable (D : diGraphType) :
  acyclicb D -> tournament_unavoidable D (2 ^ #|D|).
Proof.
move=> ac.
have noback (u v : D) : u --> v -> ~~ connect (@arc D) v u.
  by move=> uv; exact: implyP (forallP (forallP ac u) v) uv.
have [g [ginj gmono]] := subdivision.acyclic_topo_embed noback.
apply/tournament_unavoidable_unbundledE => T irr semi asym cardT.
have tS : implications_X123.tourn_on (@arc T) [set: T] by move=> u v _ _ uv; exact: semi.
have big : 2 ^ #|D| <= #|[set: T]| by rewrite cardsT cardT.
have [U [_ cU trU]] := implications_X123.ramsey_transitive asym tS big.
have tU : implications_X123.tourn_on (@arc T) U by move=> u v _ _ uv; exact: semi.
have [t0 _] : {t0 : T | t0 \in U} by apply/sigW/card_gt0P; rewrite cU.
pose rk := implications_X123.out_rank (@arc T) U.
pose f (x : D) : T := odflt t0 [pick u in U | rk u == #|D| - g x].
have fP x : f x \in U /\ rk (f x) = #|D| - g x.
  have lt : #|D| - g x < #|U| by rewrite cU ltnS leq_subr.
  have [u uU ru] := implications_X123.out_rank_onto asym tU trU lt.
  rewrite /f; case: pickP => [w /andP [wU /eqP ->] | none] //=.
  by move: (none u); rewrite /= uU /rk ru eqxx.
exists f; split.
  move=> x y e; apply: ginj; apply/val_inj.
  have := (fP x).2; rewrite e (fP y).2 => exy.
  by apply/eqP; rewrite -(eqn_sub2lE (ltnW (ltn_ord (g x))) (ltnW (ltn_ord (g y)))) exy.
move=> x y xy.
have [fxU rx] := fP x; have [fyU ry] := fP y.
rewrite (implications_X123.out_rank_ltE asym tU trU fxU fyU) -/rk rx ry.
by rewrite ltn_sub2l // (leq_trans (gmono x y xy)) // ltnW.
Qed.

(** Every acyclic digraph has an unavoidability value: the least unavoidable order, by [ex_minn]. *)
Lemma e106_unvd_exists (D : diGraphType) : acyclicb D -> exists N, unavoidability_number D N.
Proof.
move=> ac; have ex : exists N, e106_unavb D N.
  by exists (2 ^ #|D|); apply/e106_unavbP; exact: e106_acyclic_unavoidable.
case: (ex_minnP ex) => N /e106_unavbP uN minN; exists N; split=> // M lt /e106_unavbP uM.
by move: (minN M uM); rewrite leqNgt lt.
Qed.

(** ** F3: isomorphism, induced subdigraphs and the deletion chain *)
Lemma e106_unavoidable_dgiso (D1 D2 : diGraphType) (N : nat) :
  dgiso D1 D2 -> tournament_unavoidable D2 N -> tournament_unavoidable D1 N.
Proof.
case=> h [hbij harc] un; apply/tournament_unavoidable_unbundledE => T irr semi asym cardT.
have [f [finj fhom]] := (tournament_unavoidable_unbundledE D2 N).1 un T irr semi asym cardT.
exists (f \o h); split; first exact: inj_comp finj (bij_inj hbij).
by move=> u v uv; apply: fhom; rewrite harc.
Qed.

Lemma e106_unvd_dgiso (D1 D2 : diGraphType) (N : nat) :
  dgiso D1 D2 -> unavoidability_number D2 N -> unavoidability_number D1 N.
Proof.
move=> iso [u2 m2]; split; first exact: e106_unavoidable_dgiso iso u2.
by move=> M lt u1; apply: (m2 M lt); exact: e106_unavoidable_dgiso (dgiso_sym iso) u1.
Qed.

Lemma e106_acyclicb_induced (D : diGraphType) (P : {set D}) :
  acyclicb D -> acyclicb (induced_digraph P).
Proof.
move=> ac.
have noback (u v : D) : u --> v -> ~~ connect (@arc D) v u.
  by move=> uv; exact: implyP (forallP (forallP ac u) v) uv.
have [g [_ gmono]] := subdivision.acyclic_topo_embed noback.
apply: (@grounding_dichromatic_cycle.acyclicb_potential (induced_digraph P) (fun y => g (val y))).
by move=> x y xy; exact: gmono.
Qed.

Lemma e106_induced_setT (D : diGraphType) : dgiso (induced_digraph [set: D]) D.
Proof.
exists val; split=> //.
exists (fun x : D => exist _ x (in_setT x) : induced_digraph [set: D]) => [[x xP]|x] //=.
by apply: val_inj.
Qed.

(** Deleting [s] of [S]: the complement of [S] in [D] is the complement of the rest of [S]
    in [D - s]. *)
Section Deletion.
Variables (D : diGraphType) (S : {set D}) (s : D).

Definition e106_rest : {set del_vertex s} := [set x | val x \in S].

Lemma e106_rest_card : s \in S -> #|e106_rest| = #|S|.-1.
Proof.
move=> sS; rewrite (cardsD1 s S) sS add1n /= -(card_imset _ val_inj).
suff -> : [set \val x | x in e106_rest] = S :\ s by [].
apply/setP => z; rewrite !inE.
apply/imsetP/andP => [[x] | [zs zS]].
  by rewrite inE => xS ->; split=> //; have := valP x; rewrite !inE.
have zP : z \in [set~ s] by rewrite !inE.
by exists (exist _ z zP) => //; rewrite inE.
Qed.

Lemma e106_del_induced :
  s \in S -> dgiso (induced_digraph (~: e106_rest)) (induced_digraph (~: S)).
Proof.
move=> sS.
have fwd (y : induced_digraph (~: e106_rest)) : val (val y) \in ~: S.
  by have := valP y; rewrite !inE.
have bwd1 (x : induced_digraph (~: S)) : val x \in [set~ s].
  have := valP x; rewrite !inE; apply: contraNneq => ->; exact: sS.
have bwd2 (x : induced_digraph (~: S)) :
    (exist _ (val x) (bwd1 x) : del_vertex s) \in ~: e106_rest.
  by have := valP x; rewrite !inE.
exists (fun y => exist _ (val (val y)) (fwd y) : induced_digraph (~: S)); split=> //.
exists (fun x => exist _ (exist _ (val x) (bwd1 x)) (bwd2 x) : induced_digraph (~: e106_rest)).
  by move=> y; do 2 apply: val_inj.
by move=> x; apply: val_inj.
Qed.

End Deletion.

(** An acyclic digraph on at most one vertex is [#|D|]-unavoidable, so its value is at most
    [#|D|]. *)
Lemma e106_unvd_small (D : diGraphType) (N : nat) :
  acyclicb D -> (#|D| <= 1)%N -> unavoidability_number D N -> (N <= #|D|)%N.
Proof.
move=> ac D1 [_ mN]; rewrite leqNgt; apply/negP => lt; apply: (mN _ lt).
case: (posnP #|D|) => [D0|Dpos]; first exact: tournament_unavoidable_empty.
apply/tournament_unavoidable_unbundledE => T irr semi asym cardT.
have [t0 _] : {t0 : T | t0 \in T} by apply/sigW/card_gt0P; rewrite cardT.
have one (x y : D) : x = y by apply: (card_le1_eqP D1).
exists (fun _ => t0); split; first by move=> x y _; exact: one.
move=> u v; rewrite (one v u) => uu.
by move: (loop_not_acyclicb uu); rewrite ac.
Qed.

(** ** The induction over k *)
Lemma e106_kext_bound (C c : nat) (F : diGraphType -> Prop) :
  (forall (D : diGraphType) (v : D), acyclicb D -> (1 < #|D|)%N ->
     forall nD nDv : nat, unvd D nD -> unvd (del_vertex v) nDv -> (nD <= C * nDv)%N) ->
  (forall (A : diGraphType) (N : nat), F A -> unavoidability_number A N -> (N <= c * #|A|)%N) ->
  forall (k : nat) (D : diGraphType) (S : {set D}),
    acyclicb D -> #|S| = k -> (exists A : diGraphType, F A /\ dgiso (induced_digraph (~: S)) A) ->
    forall N : nat, unavoidability_number D N -> (N <= maxn C 1 ^ k * maxn c 1 * #|D|)%N.
Proof.
move=> h9 hF; elim=> [|k IH] D S ac cS [A [FA iso]] N uN.
- move/cards0_eq: cS => S0; subst S; move: iso; rewrite setC0 => iso.
  have isoDA : dgiso D A := dgiso_trans (dgiso_sym (e106_induced_setT D)) iso.
  have := hF A N FA (e106_unvd_dgiso (dgiso_sym isoDA) uN).
  rewrite expn0 mul1n -(dgiso_card isoDA) => /leq_trans; apply.
  by rewrite leq_mul2r leq_maxl orbT.
- have [s sS] : {s | s \in S} by apply/sigW/set0Pn; rewrite -card_gt0 cS.
  have [small|big] := leqP #|D| 1.
    apply: leq_trans (e106_unvd_small ac small uN) _.
    by rewrite -[X in (X <= _)%N]mul1n leq_mul2r muln_gt0 expn_gt0 !leq_maxr orbT.
  have acD' : acyclicb (del_vertex s) by exact: e106_acyclicb_induced.
  have [n' un'] := e106_unvd_exists acD'.
  have le1 := h9 D s ac big N n' uN un'.
  have cS' : #|e106_rest S s| = k by rewrite (e106_rest_card sS) cS.
  have iso' : exists A, F A /\ dgiso (induced_digraph (~: e106_rest S s)) A.
    by exists A; split=> //; exact: dgiso_trans (e106_del_induced sS) iso.
  have le2 := IH _ _ acD' cS' iso' n' un'.
  have cD' : (#|del_vertex s| <= #|D|)%N by rewrite card_sig cardsC1 leq_pred.
  apply: (leq_trans le1); rewrite expnS -!mulnA leq_mul //; first by rewrite leq_maxl.
  by apply: (leq_trans le2); rewrite mulnA leq_mul2l cD' orbT.
Qed.

Theorem conj_9_implies_kextension_linear_unavoidability :
  conj_9 -> kextension_linear_unavoidability_statement.
Proof.
move=> [C h9] F k [c hF]; exists (maxn C 1 ^ k * maxn c 1) => D N [ac [S [cS hA]]] uN.
exact: (e106_kext_bound h9 hF ac cS hA uN).
Qed.

(*@EDGE from=oriented_triangle_free_acyclic_number_theta_statement to=oriented_triangle_free_dichromatic_theta_statement kind=implies status=candidate proved=false cite="gc:e158" note="Source argument: t-vec(n) >= n / a-vec(n) turns the a-vec upper bound into the missing t-vec lower bound, and the matching t-vec upper bound (sqrt 2 + o(1)) sqrt(n/log n) is already proved in arXiv:2403.02298. Both inputs are external to the two statements (the first is the chi-vec >= |V|/alpha-vec bound, the second a theorem of the paper); adding them as hypotheses would smuggle in the conclusion, so the edge stays a candidate." *)

(** ** Print Assumptions audit *)

Print Assumptions x221_ocm_no_arrow.
Print Assumptions delta122_hero_k1_plus_dipath2_free_implies_delta122_hero_oriented_complete_multipartite.
Print Assumptions x221_no_arrow_ocm.
Print Assumptions delta122_hero_oriented_complete_multipartite_implies_delta122_hero_k1_plus_dipath2_free.
Print Assumptions conj_9_implies_kextension_linear_unavoidability.
Print Assumptions e106_kext_bound.
Print Assumptions e106_unvd_exists.
Print Assumptions e106_acyclic_unavoidable.
Print Assumptions e106_unavbP.
