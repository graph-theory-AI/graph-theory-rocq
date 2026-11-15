(** * Extremal.conjectures.implications_X309 -- a dependency-graph EDGE with an X309 endpoint.

    Same role as [implications_X287.v] (atlas): a machine-checked implication between two statements, here both of
    extremal-graph-theory.  The edge is a RELATIVE theorem: a [Qed]-closed [Theorem A -> B] proved WITHOUT resolving
    either endpoint.  Axiom-free: no [Axiom] / [Parameter] / [Admitted] / [Conjecture].

    The edge below is a Rocq-only edge (no corpus relation): the Fraughnaugh-Locke conjecture (X309: a triangle-free
    subcubic G containing none of the six graphs [x287_bb_graph i] as a subgraph has 3 #|G| <= 8 alpha(G)) implies
    the Bajnok-Brinkmann statement (X287), as its record says (Cames van Batenburg, Goedgebeur and Joret,
    arXiv:1911.12471v2, Revision_IndependenceRatio8over3.tex l.229-230).
    - Clause 1 (every 2-connected triangle-free subcubic G with 8 alpha(G) < 3 #|G| is isomorphic to one of the six):
      X309 gives some [x287_bb_graph i] as a subgraph of G ([has_subgraph] is decided by [e309_subgraphbP]), and a
      2-connected subcubic G containing a copy of a graph in which every vertex but at most one has three neighbours
      is isomorphic to that graph ([e309_iso_of_copy]: the l.230 argument; the vertex of degree 2 of F_11,
      F_19^(1), F_19^(2) would be a cut vertex).
    - Clause 2 (each of the six is 2-connected, triangle-free and subcubic with 8 alpha < 3n) and clause 3 (no two are
      isomorphic) are closed facts about the tables, proved here outright: clause 2 by [vm_compute] on explicit vertex
      lists (grounding_X287's F_11 lemmas made generic), clause 3 by the order and, for the two pairs of equal order,
      the number of closed 5-walks (F_14^(1) / F_14^(2)) and of closed 7-walks (F_19^(1) / F_19^(2)), which an
      isomorphism preserves ([e309_cw_iso]).
    Both statements are true before the pin (Theorem 7 and Corollary 8 of arXiv:1911.12471v2, recorded solved
    through ERRATA by lit35 and lit23); the edge relates them as encoded. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries digraph sgraph.
From GTBase Require Import base common finite_graph.
From Extremal.conjectures Require Import X287 grounding_X287 X309.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Generic list machinery: grounding_X287's F_11 lemmas, generic in the graph and a complete vertex list *)

Lemma e309_cardN (F : sgraph) (l : seq F) (v : F) :
  (forall x, x \in l) -> uniq l -> #|N(v)| = size [seq u <- l | v -- u].
Proof.
move=> hl ul; have e : N(v) =i [seq u <- l | v -- u].
  by move=> u; rewrite mem_filter hl andbT inE.
by rewrite (eq_card e) (card_uniqP (filter_uniq _ ul)).
Qed.

Definition e309_tf_check (F : sgraph) (l : seq F) : bool :=
  all (fun x => all (fun y => all (fun z => ~~ [&& x -- y, y -- z & z -- x]) l) l) l.

Lemma e309_tf (F : sgraph) (l : seq F) : (forall x, x \in l) -> e309_tf_check l -> triangle_free F.
Proof.
move=> hl h x y z xy yz zx.
move/allP: h => /(_ x (hl x)) /allP /(_ y (hl y)) /allP /(_ z (hl z)).
by rewrite xy yz zx.
Qed.

Lemma e309_sc (F : sgraph) (l : seq F) : (forall x, x \in l) -> uniq l ->
  all (fun v => size [seq u <- l | v -- u] <= 3) l -> subcubic F.
Proof.
move=> hl ul h v; rewrite (@e309_cardN F l v hl ul).
by move/allP: h => /(_ v (hl v)).
Qed.

Lemma e309_deg3 (F : sgraph) (l : seq F) (u : F) : (forall x, x \in l) -> uniq l ->
  all (fun v => (v == u) || (size [seq w <- l | v -- w] == 3)) l -> forall x, x != u -> #|N(x)| = 3.
Proof.
move=> hl ul h x xu; rewrite (@e309_cardN F l x hl ul); apply/eqP.
by move/allP: h => /(_ x (hl x)); rewrite (negbTE xu).
Qed.

(* Breadth-first reachability avoiding the vertices of [rem] (grounding_X287's g287_reach, generic). *)
Fixpoint e309_reach (F : sgraph) (l rem : seq F) (n : nat) (R : seq F) : seq F :=
  if n is n'.+1 then
    e309_reach l rem n' (R ++ [seq y <- l | (y \notin rem) && (y \notin R) && has (fun x => x -- y) R])
  else R.

Lemma e309_reachP (F : sgraph) (l rem : seq F) (S : {set F}) (r : F) :
  (forall y, (y \in S) = (y \in rem)) ->
  forall n R, (forall x, x \in R ->
      x \notin rem /\ connect (preliminaries.restrict_mem (mem ([set: F] :\: S)) (--)) r x) ->
  forall y, y \in @e309_reach F l rem n R ->
    y \notin rem /\ connect (preliminaries.restrict_mem (mem ([set: F] :\: S)) (--)) r y.
Proof.
move=> hS; elim=> [|n IH] R hR y; first exact: hR.
move=> hy; apply: (IH (R ++ [seq y <- l | (y \notin rem) && (y \notin R) && has (fun x => x -- y) R])
  _ y hy) => x.
rewrite mem_cat => /orP[/hR // |].
rewrite mem_filter => /andP[/andP[/andP[hx _] /hasP[z hz hzx]] _]; split=> //.
have [hzr hcz] := hR z hz; apply: connect_trans hcz (connect1 _).
by rewrite /preliminaries.restrict_mem /= !inE !hS hzr hx hzx.
Qed.

Definition e309_conn_ok (F : sgraph) (l : seq F) (r0 : F) (rem : seq F) : bool :=
  let r := head r0 [seq y <- l | y \notin rem] in
  let L := @e309_reach F l rem (size l) [:: r] in
  all (fun y => (y \in rem) || (y \in L)) l.

Lemma e309_connected_of (F : sgraph) (l : seq F) (r0 : F) (S : {set F}) (rem : seq F) :
  (forall x, x \in l) -> (forall y, (y \in S) = (y \in rem)) -> e309_conn_ok l r0 rem ->
  connected ([set: F] :\: S).
Proof.
move=> hl hS; rewrite /e309_conn_ok; cbv zeta.
case hf: [seq y <- l | y \notin rem] => [|r f] hall.
  move=> x y hx _; exfalso; move: hx; rewrite !inE hS andbT => hx.
  by have := mem_filter (fun y => y \notin rem) x l; rewrite hf hx hl in_nil.
have hr : r \notin rem by have := mem_head r f; rewrite -hf mem_filter => /andP[].
apply: (@connected_center _ r) => [y|]; last by rewrite !inE hS hr.
rewrite !inE hS andbT => hy.
have hreach : y \in @e309_reach F l rem (size l) [:: r].
  by move/allP: hall => /(_ y (hl y)); rewrite (negbTE hy) orFb.
have [] // := @e309_reachP F l rem S r hS (size l) [:: r] _ y hreach.
by move=> x; rewrite inE => /eqP ->; split=> //; exact: connect0.
Qed.

Lemma e309_k2 (F : sgraph) (l : seq F) (r0 : F) : (forall x, x \in l) -> 2 < #|F| ->
  all (fun a => e309_conn_ok l r0 [:: a]) l -> e309_conn_ok l r0 [::] -> k_connected F 2.
Proof.
move=> hl n2 h1 h0; split=> // S hS.
have : #|S| = 0 \/ #|S| = 1 by move: hS; case: #|S| => [|[|n]]; auto.
case=> [/cards0_eq -> | /eqP/cards1P [a ->]].
- by apply: (@e309_connected_of F l r0 _ [::] hl _ h0) => y; rewrite !inE.
- by apply: (@e309_connected_of F l r0 _ [:: a] hl _ (allP h1 a (hl a))) => y; rewrite !inE.
Qed.

Definition e309_nbrs (F : sgraph) (l : seq F) (v : F) : seq F := [seq u <- l | v -- u].

Lemma e309_nbrsE (F : sgraph) (l : seq F) (v x : F) : (forall y, y \in l) -> (x \in e309_nbrs l v) = v -- x.
Proof. by move=> hl; rewrite /e309_nbrs mem_filter hl andbT. Qed.

(* Largest stable subsequence of [vs] avoiding [X] (grounding_X287's g287_mis, generic). *)
Fixpoint e309_mis (F : sgraph) (l vs X : seq F) : nat :=
  if vs is v :: r then
    if v \in X then e309_mis l r X
    else maxn (e309_mis l r X) (e309_mis l r (e309_nbrs l v ++ X)).+1
  else 0.

Lemma e309_mis_cons (F : sgraph) (l : seq F) (v : F) (r X : seq F) :
  @e309_mis F l (v :: r) X =
    if v \in X then @e309_mis F l r X else maxn (@e309_mis F l r X) (@e309_mis F l r (e309_nbrs l v ++ X)).+1.
Proof. by []. Qed.

Lemma e309_misP (F : sgraph) (l : seq F) : (forall y, y \in l) ->
  forall vs X T : seq F, uniq T -> {subset T <= vs} -> (forall x y, x \in T -> y \in T -> ~~ x -- y) ->
  (forall x, x \in T -> x \notin X) -> size T <= @e309_mis F l vs X.
Proof.
move=> hl; elim=> [|v r IH] X T uT sT stT dT.
  by case: T uT sT {stT dT} => [//|t T'] _ /(_ t (mem_head _ _)).
rewrite e309_mis_cons; case vX: (v \in X).
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
  by rewrite (@e309_nbrsE F l v x hl) (stT v x vT xT).
Qed.

Lemma e309_alpha (F : sgraph) (l : seq F) (m : nat) : (forall y, y \in l) -> @e309_mis F l l [::] = m ->
  α([set: F]) <= m.
Proof.
move=> hl hm; rewrite /alpha_mem; apply/bigmax_leqP => S /stabsetsP [_ /stableP st].
rewrite cardE -hm; apply: (@e309_misP F l hl).
- exact: enum_uniq.
- by move=> x _; exact: hl.
- by move=> x y; rewrite !mem_enum; exact: st.
- by move=> x _; rewrite in_nil.
Qed.

(** ** Closed walks, their list form, and their invariance under isomorphism *)

(** [e309_w k x y]: the number of walks of length [k] from [x] to [y]. *)
Fixpoint e309_w (G : sgraph) (k : nat) (x y : G) : nat :=
  if k is k'.+1 then \sum_(z | x -- z) e309_w k' z y else (x == y).

(** [e309_cw G k]: the number of closed walks of length [k] (the trace of the k-th power of the adjacency matrix). *)
Definition e309_cw (G : sgraph) (k : nat) : nat := \sum_(x : G) e309_w k x x.

(** The same count over an explicit vertex list, with [sumn] (a plain fold that [vm_compute] evaluates). *)
Fixpoint e309_wl (G : sgraph) (l : seq G) (k : nat) (x y : G) : nat :=
  if k is k'.+1 then sumn [seq e309_wl l k' z y | z <- l & x -- z] else (x == y).

Lemma e309_sum_list (G : sgraph) (l : seq G) (P : pred G) (f : G -> nat) :
  (forall x, x \in l) -> uniq l -> \sum_(z | P z) f z = sumn [seq f z | z <- l & P z].
Proof.
move=> hl ul; rewrite sumnE big_map big_filter; apply: perm_big.
apply: uniq_perm; [exact: index_enum_uniq | exact: ul | by move=> x; rewrite mem_index_enum hl].
Qed.

Lemma e309_w_list (G : sgraph) (l : seq G) : (forall x, x \in l) -> uniq l ->
  forall k (x y : G), e309_w k x y = @e309_wl G l k x y.
Proof.
move=> hl ul; elim=> [|k IH] x y //=.
rewrite (@e309_sum_list G l (fun z => x -- z) (fun z => e309_w k z y) hl ul).
by congr sumn; apply: eq_map => z; exact: IH.
Qed.

Lemma e309_cw_list (G : sgraph) (l : seq G) (k : nat) : (forall x, x \in l) -> uniq l ->
  e309_cw G k = sumn [seq @e309_wl G l k x x | x <- l].
Proof.
move=> hl ul; rewrite /e309_cw (@e309_sum_list G l predT (fun x => e309_w k x x) hl ul) filter_predT.
by congr sumn; apply: eq_map => x; exact: (@e309_w_list G l hl ul k x x).
Qed.

Section E309Iso.
Import bij.

Lemma e309_w_iso (G H : sgraph) (i : G ≃ H) (k : nat) (x y : G) : e309_w k (i x) (i y) = e309_w k x y.
Proof.
elim: k x y => [|k IH] x y /=; first by rewrite (inj_eq (@bij_injective _ _ i)).
rewrite (reindex_onto i i^-1) /=; try by move=> z _; exact: bijK'.
by apply: eq_big => [z | z _]; [rewrite bijK eqxx andbT; exact: edge_diso | exact: IH].
Qed.

Lemma e309_cw_iso (G H : sgraph) (i : G ≃ H) (k : nat) : e309_cw G k = e309_cw H k.
Proof.
rewrite /e309_cw (reindex_onto i i^-1) /=; try by move=> y _; exact: bijK'.
by apply: eq_big => [x | x _]; [rewrite bijK eqxx | rewrite e309_w_iso].
Qed.

End E309Iso.

(** ** has_subgraph is decidable *)

Definition e309_subgraphb (G H : sgraph) : bool :=
  [exists f : {ffun H -> G}, injectiveb f && [forall x : H, [forall y : H, (x -- y) ==> (f x -- f y)]]].

Lemma e309_subgraphbP (G H : sgraph) : reflect (has_subgraph G H) (e309_subgraphb G H).
Proof.
apply: (iffP existsP) => [[f /andP[/injectiveP inj_f /forallP hf]] | ].
  apply/has_subgraphP; exists f; split=> // x y xy.
  by move/forallP: (hf x) => /(_ y); rewrite xy.
case/has_subgraphP => f [inj_f hf]; exists (finfun f); apply/andP; split.
  by apply/injectiveP => x y; rewrite !ffunE; exact: inj_f.
by apply/forallP => x; apply/forallP => y; apply/implyP => xy; rewrite !ffunE; exact: hf.
Qed.

(** ** The l.230 argument: a copy of a nearly cubic F in a subcubic 2-connected G is all of G *)

(** A property kept by every step of a path holds at its end. *)
Lemma e309_path_keep (T : Type) (e : rel T) (P : pred T) : (forall a b, e a b -> P a -> P b) ->
  forall (p : seq T) (a : T), path e a p -> P a -> P (last a p).
Proof.
move=> step; elim=> [|b p IH] a //= /andP [ab pb] Pa.
exact: IH _ pb (step _ _ ab Pa).
Qed.

Lemma e309_iso_of_copy (F G : sgraph) (u : F) (h : F -> G) :
  subcubic G -> k_connected G 2 -> 1 < #|F| ->
  (forall x : F, x != u -> #|N(x)| = 3) ->
  injective h -> (forall x y : F, x -- y -> h x -- h y) ->
  inhabited (G ≃ F).
Proof.
move=> scG [_ kG] F2 deg3 hinj hhom.
have sub (x : F) : h @: N(x) \subset N(h x).
  by apply/subsetP => _ /imsetP [y yN ->]; rewrite in_opn; apply: hhom; rewrite -in_opn.
(* 1. a vertex other than u: the neighbours of its image are exactly the images of its neighbours *)
have nb3 (x : F) : x != u -> N(h x) = h @: N(x).
  move=> xu; apply/eqP; rewrite eq_sym eqEcard sub card_imset // deg3 //; exact: scG.
have [x0 x0u] : exists x0 : F, x0 != u.
  case/card_gt1P: F2 => a [b [_ _ ab]].
  by case: (eqVneq a u) => [au | au]; [exists b; rewrite -au eq_sym | exists a].
(* an image vertex other than h u has all its neighbours in the image *)
have one (a b : G) : a != h u -> a -- b -> a \in h @: [set: F] -> b \in h @: [set: F].
  move=> au ab /imsetP [z _ az].
  have zu : z != u by apply: contraNneq au => zu; rewrite az zu eqxx.
  have : b \in N(h z) by rewrite in_opn -az.
  by rewrite nb3 // => /imsetP [y _ ->]; apply: imset_f; rewrite inE.
(* 2. u: an extra neighbour w of h u is impossible inside the image; outside it, h u is a cut vertex *)
have nbu : N(h u) = h @: N(u).
  apply/setP => w; apply/idP/idP; last exact: (subsetP (sub u)).
  rewrite in_opn => uw.
  case: (boolP (w \in h @: [set: F])) => [/imsetP [z _ wz] | wout].
    have zu : z != u by apply: contraTneq uw => zu; rewrite wz zu sg_irrefl.
    have : h u \in N(h z) by rewrite in_opn -wz sg_sym.
    rewrite nb3 // => /imsetP [y yN /hinj e].
    by rewrite wz; apply: imset_f; rewrite in_opn sg_sym -in_opn e.
  exfalso.
  have cS : #|[set h u]| < 2 by rewrite cards1.
  have wS : w \in [set: G] :\: [set h u] by rewrite !inE eq_sym (sg_edgeNeq uw).
  have xS : h x0 \in [set: G] :\: [set h u] by rewrite !inE (inj_eq hinj) x0u.
  case/connectP: (kG _ cS w (h x0) wS xS) => p pp lp.
  have stepo (a b : G) : preliminaries.restrict_mem (mem ([set: G] :\: [set h u])) (--) a b ->
      a \notin h @: [set: F] -> b \notin h @: [set: F].
    rewrite /preliminaries.restrict_mem /= !inE ?andbT => /andP [/andP [_ bu] ab] aout.
    apply/negP => bin; move/negP: aout; apply.
    by apply: (one b a bu _ bin); rewrite sg_sym.
  have := e309_path_keep stepo pp wout.
  by rewrite -lp (imset_f h (in_setT x0)).
have nbz (z : F) : N(h z) = h @: N(z).
  by case: (eqVneq z u) => [-> | zu]; [exact: nbu | exact: nb3].
(* 3. the image is all of G, so h is a bijection, and it reflects adjacency *)
have cG : connected [set: G] by move: (kG set0); rewrite cards0 setD0; apply.
have onto (b : G) : b \in h @: [set: F].
  case/connectP: (cG (h x0) b (in_setT _) (in_setT _)) => p pp lp.
  have stepi (a c : G) : preliminaries.restrict_mem (mem [set: G]) (--) a c ->
      a \in h @: [set: F] -> c \in h @: [set: F].
    rewrite /preliminaries.restrict_mem /= => /andP [_ ac] /imsetP [z _ az].
    have : c \in N(h z) by rewrite in_opn -az.
    by rewrite nbz => /imsetP [y _ ->]; apply: imset_f; rewrite inE.
  rewrite lp; apply: (e309_path_keep stepi pp).
  by apply: imset_f; rewrite inE.
have e : h @: [set: F] = [set: G] by apply/setP => b; rewrite inE onto.
have hbij : bijective h.
  apply: (inj_card_bij hinj).
  by rewrite -cardsT -e card_imset // cardsT leqnn.
case: hbij => g hK gK.
have hedge (a b : F) : (h a -- h b) = (a -- b).
  apply/idP/idP => [ab | ]; last exact: hhom.
  have : h b \in N(h a) by rewrite in_opn.
  by rewrite nbz => /imsetP [c cN /hinj ->]; rewrite -in_opn.
(* 4. the isomorphism, from the inverse of h *)
constructor; apply: (@Diso' G F g h gK hK) => a b.
by rewrite -hedge !gK.
Qed.

(** ** The six tables: clause 2 and the degree pattern, by vm_compute *)

(** ** x287_bb_graph 0: order 11, alpha 4 *)
Local Notation F0 := (x287_bb_graph (@Ordinal 6 0 isT)).

Definition e309_l0 : seq F0 :=
  [:: @Ordinal 11 0 isT; @Ordinal 11 1 isT; @Ordinal 11 2 isT; @Ordinal 11 3 isT; @Ordinal 11 4 isT;
    @Ordinal 11 5 isT; @Ordinal 11 6 isT; @Ordinal 11 7 isT; @Ordinal 11 8 isT; @Ordinal 11 9 isT;
    @Ordinal 11 10 isT].

Lemma e309_l0_enum : enum 'I_11 = e309_l0.
Proof. by apply: (inj_map val_inj); rewrite val_enum_ord. Qed.

Lemma e309_l0_all (x : F0) : x \in e309_l0.
Proof. by rewrite -e309_l0_enum mem_enum. Qed.

Lemma e309_l0_uniq : uniq e309_l0.
Proof. by rewrite -e309_l0_enum enum_uniq. Qed.

Lemma e309_c2_0 : [/\ k_connected F0 2, triangle_free F0, subcubic F0 & 8 * α([set: F0]) < 3 * #|F0|].
Proof.
have hl := e309_l0_all; have ul := e309_l0_uniq.
have hc : #|F0| = 11 by exact: card_ord.
split.
- by apply: (@e309_k2 F0 e309_l0 (@Ordinal 11 0 isT) hl); [rewrite hc | vm_compute | vm_compute].
- by apply: (@e309_tf F0 e309_l0 hl); vm_compute.
- by apply: (@e309_sc F0 e309_l0 hl ul); vm_compute.
- have ha : α([set: F0]) <= 4 by apply: (@e309_alpha F0 e309_l0 4 hl); vm_compute.
  by rewrite hc; apply: leq_ltn_trans (leq_mul (leqnn 8) ha) _.
Qed.

Lemma e309_deg_0 : exists u : F0, forall x : F0, x != u -> #|N(x)| = 3.
Proof.
exists (@Ordinal 11 10 isT); apply: (@e309_deg3 F0 e309_l0 _ e309_l0_all e309_l0_uniq).
by vm_compute.
Qed.

(** ** x287_bb_graph 1: order 14, alpha 5 *)
Local Notation F1 := (x287_bb_graph (@Ordinal 6 1 isT)).

Definition e309_l1 : seq F1 :=
  [:: @Ordinal 14 0 isT; @Ordinal 14 1 isT; @Ordinal 14 2 isT; @Ordinal 14 3 isT; @Ordinal 14 4 isT;
    @Ordinal 14 5 isT; @Ordinal 14 6 isT; @Ordinal 14 7 isT; @Ordinal 14 8 isT; @Ordinal 14 9 isT;
    @Ordinal 14 10 isT; @Ordinal 14 11 isT; @Ordinal 14 12 isT; @Ordinal 14 13 isT].

Lemma e309_l1_enum : enum 'I_14 = e309_l1.
Proof. by apply: (inj_map val_inj); rewrite val_enum_ord. Qed.

Lemma e309_l1_all (x : F1) : x \in e309_l1.
Proof. by rewrite -e309_l1_enum mem_enum. Qed.

Lemma e309_l1_uniq : uniq e309_l1.
Proof. by rewrite -e309_l1_enum enum_uniq. Qed.

Lemma e309_c2_1 : [/\ k_connected F1 2, triangle_free F1, subcubic F1 & 8 * α([set: F1]) < 3 * #|F1|].
Proof.
have hl := e309_l1_all; have ul := e309_l1_uniq.
have hc : #|F1| = 14 by exact: card_ord.
split.
- by apply: (@e309_k2 F1 e309_l1 (@Ordinal 14 0 isT) hl); [rewrite hc | vm_compute | vm_compute].
- by apply: (@e309_tf F1 e309_l1 hl); vm_compute.
- by apply: (@e309_sc F1 e309_l1 hl ul); vm_compute.
- have ha : α([set: F1]) <= 5 by apply: (@e309_alpha F1 e309_l1 5 hl); vm_compute.
  by rewrite hc; apply: leq_ltn_trans (leq_mul (leqnn 8) ha) _.
Qed.

Lemma e309_deg_1 : exists u : F1, forall x : F1, x != u -> #|N(x)| = 3.
Proof.
exists (@Ordinal 14 0 isT); apply: (@e309_deg3 F1 e309_l1 _ e309_l1_all e309_l1_uniq).
by vm_compute.
Qed.

(** ** x287_bb_graph 2: order 14, alpha 5 *)
Local Notation F2 := (x287_bb_graph (@Ordinal 6 2 isT)).

Definition e309_l2 : seq F2 :=
  [:: @Ordinal 14 0 isT; @Ordinal 14 1 isT; @Ordinal 14 2 isT; @Ordinal 14 3 isT; @Ordinal 14 4 isT;
    @Ordinal 14 5 isT; @Ordinal 14 6 isT; @Ordinal 14 7 isT; @Ordinal 14 8 isT; @Ordinal 14 9 isT;
    @Ordinal 14 10 isT; @Ordinal 14 11 isT; @Ordinal 14 12 isT; @Ordinal 14 13 isT].

Lemma e309_l2_enum : enum 'I_14 = e309_l2.
Proof. by apply: (inj_map val_inj); rewrite val_enum_ord. Qed.

Lemma e309_l2_all (x : F2) : x \in e309_l2.
Proof. by rewrite -e309_l2_enum mem_enum. Qed.

Lemma e309_l2_uniq : uniq e309_l2.
Proof. by rewrite -e309_l2_enum enum_uniq. Qed.

Lemma e309_c2_2 : [/\ k_connected F2 2, triangle_free F2, subcubic F2 & 8 * α([set: F2]) < 3 * #|F2|].
Proof.
have hl := e309_l2_all; have ul := e309_l2_uniq.
have hc : #|F2| = 14 by exact: card_ord.
split.
- by apply: (@e309_k2 F2 e309_l2 (@Ordinal 14 0 isT) hl); [rewrite hc | vm_compute | vm_compute].
- by apply: (@e309_tf F2 e309_l2 hl); vm_compute.
- by apply: (@e309_sc F2 e309_l2 hl ul); vm_compute.
- have ha : α([set: F2]) <= 5 by apply: (@e309_alpha F2 e309_l2 5 hl); vm_compute.
  by rewrite hc; apply: leq_ltn_trans (leq_mul (leqnn 8) ha) _.
Qed.

Lemma e309_deg_2 : exists u : F2, forall x : F2, x != u -> #|N(x)| = 3.
Proof.
exists (@Ordinal 14 0 isT); apply: (@e309_deg3 F2 e309_l2 _ e309_l2_all e309_l2_uniq).
by vm_compute.
Qed.

(** ** x287_bb_graph 3: order 19, alpha 7 *)
Local Notation F3 := (x287_bb_graph (@Ordinal 6 3 isT)).

Definition e309_l3 : seq F3 :=
  [:: @Ordinal 19 0 isT; @Ordinal 19 1 isT; @Ordinal 19 2 isT; @Ordinal 19 3 isT; @Ordinal 19 4 isT;
    @Ordinal 19 5 isT; @Ordinal 19 6 isT; @Ordinal 19 7 isT; @Ordinal 19 8 isT; @Ordinal 19 9 isT;
    @Ordinal 19 10 isT; @Ordinal 19 11 isT; @Ordinal 19 12 isT; @Ordinal 19 13 isT; @Ordinal 19 14 isT;
    @Ordinal 19 15 isT; @Ordinal 19 16 isT; @Ordinal 19 17 isT; @Ordinal 19 18 isT].

Lemma e309_l3_enum : enum 'I_19 = e309_l3.
Proof. by apply: (inj_map val_inj); rewrite val_enum_ord. Qed.

Lemma e309_l3_all (x : F3) : x \in e309_l3.
Proof. by rewrite -e309_l3_enum mem_enum. Qed.

Lemma e309_l3_uniq : uniq e309_l3.
Proof. by rewrite -e309_l3_enum enum_uniq. Qed.

Lemma e309_c2_3 : [/\ k_connected F3 2, triangle_free F3, subcubic F3 & 8 * α([set: F3]) < 3 * #|F3|].
Proof.
have hl := e309_l3_all; have ul := e309_l3_uniq.
have hc : #|F3| = 19 by exact: card_ord.
split.
- by apply: (@e309_k2 F3 e309_l3 (@Ordinal 19 0 isT) hl); [rewrite hc | vm_compute | vm_compute].
- by apply: (@e309_tf F3 e309_l3 hl); vm_compute.
- by apply: (@e309_sc F3 e309_l3 hl ul); vm_compute.
- have ha : α([set: F3]) <= 7 by apply: (@e309_alpha F3 e309_l3 7 hl); vm_compute.
  by rewrite hc; apply: leq_ltn_trans (leq_mul (leqnn 8) ha) _.
Qed.

Lemma e309_deg_3 : exists u : F3, forall x : F3, x != u -> #|N(x)| = 3.
Proof.
exists (@Ordinal 19 18 isT); apply: (@e309_deg3 F3 e309_l3 _ e309_l3_all e309_l3_uniq).
by vm_compute.
Qed.

(** ** x287_bb_graph 4: order 19, alpha 7 *)
Local Notation F4 := (x287_bb_graph (@Ordinal 6 4 isT)).

Definition e309_l4 : seq F4 :=
  [:: @Ordinal 19 0 isT; @Ordinal 19 1 isT; @Ordinal 19 2 isT; @Ordinal 19 3 isT; @Ordinal 19 4 isT;
    @Ordinal 19 5 isT; @Ordinal 19 6 isT; @Ordinal 19 7 isT; @Ordinal 19 8 isT; @Ordinal 19 9 isT;
    @Ordinal 19 10 isT; @Ordinal 19 11 isT; @Ordinal 19 12 isT; @Ordinal 19 13 isT; @Ordinal 19 14 isT;
    @Ordinal 19 15 isT; @Ordinal 19 16 isT; @Ordinal 19 17 isT; @Ordinal 19 18 isT].

Lemma e309_l4_enum : enum 'I_19 = e309_l4.
Proof. by apply: (inj_map val_inj); rewrite val_enum_ord. Qed.

Lemma e309_l4_all (x : F4) : x \in e309_l4.
Proof. by rewrite -e309_l4_enum mem_enum. Qed.

Lemma e309_l4_uniq : uniq e309_l4.
Proof. by rewrite -e309_l4_enum enum_uniq. Qed.

Lemma e309_c2_4 : [/\ k_connected F4 2, triangle_free F4, subcubic F4 & 8 * α([set: F4]) < 3 * #|F4|].
Proof.
have hl := e309_l4_all; have ul := e309_l4_uniq.
have hc : #|F4| = 19 by exact: card_ord.
split.
- by apply: (@e309_k2 F4 e309_l4 (@Ordinal 19 0 isT) hl); [rewrite hc | vm_compute | vm_compute].
- by apply: (@e309_tf F4 e309_l4 hl); vm_compute.
- by apply: (@e309_sc F4 e309_l4 hl ul); vm_compute.
- have ha : α([set: F4]) <= 7 by apply: (@e309_alpha F4 e309_l4 7 hl); vm_compute.
  by rewrite hc; apply: leq_ltn_trans (leq_mul (leqnn 8) ha) _.
Qed.

Lemma e309_deg_4 : exists u : F4, forall x : F4, x != u -> #|N(x)| = 3.
Proof.
exists (@Ordinal 19 18 isT); apply: (@e309_deg3 F4 e309_l4 _ e309_l4_all e309_l4_uniq).
by vm_compute.
Qed.

(** ** x287_bb_graph 5: order 22, alpha 8 *)
Local Notation F5 := (x287_bb_graph (@Ordinal 6 5 isT)).

Definition e309_l5 : seq F5 :=
  [:: @Ordinal 22 0 isT; @Ordinal 22 1 isT; @Ordinal 22 2 isT; @Ordinal 22 3 isT; @Ordinal 22 4 isT;
    @Ordinal 22 5 isT; @Ordinal 22 6 isT; @Ordinal 22 7 isT; @Ordinal 22 8 isT; @Ordinal 22 9 isT;
    @Ordinal 22 10 isT; @Ordinal 22 11 isT; @Ordinal 22 12 isT; @Ordinal 22 13 isT; @Ordinal 22 14 isT;
    @Ordinal 22 15 isT; @Ordinal 22 16 isT; @Ordinal 22 17 isT; @Ordinal 22 18 isT; @Ordinal 22 19 isT;
    @Ordinal 22 20 isT; @Ordinal 22 21 isT].

Lemma e309_l5_enum : enum 'I_22 = e309_l5.
Proof. by apply: (inj_map val_inj); rewrite val_enum_ord. Qed.

Lemma e309_l5_all (x : F5) : x \in e309_l5.
Proof. by rewrite -e309_l5_enum mem_enum. Qed.

Lemma e309_l5_uniq : uniq e309_l5.
Proof. by rewrite -e309_l5_enum enum_uniq. Qed.

Lemma e309_c2_5 : [/\ k_connected F5 2, triangle_free F5, subcubic F5 & 8 * α([set: F5]) < 3 * #|F5|].
Proof.
have hl := e309_l5_all; have ul := e309_l5_uniq.
have hc : #|F5| = 22 by exact: card_ord.
split.
- by apply: (@e309_k2 F5 e309_l5 (@Ordinal 22 0 isT) hl); [rewrite hc | vm_compute | vm_compute].
- by apply: (@e309_tf F5 e309_l5 hl); vm_compute.
- by apply: (@e309_sc F5 e309_l5 hl ul); vm_compute.
- have ha : α([set: F5]) <= 8 by apply: (@e309_alpha F5 e309_l5 8 hl); vm_compute.
  by rewrite hc; apply: leq_ltn_trans (leq_mul (leqnn 8) ha) _.
Qed.

Lemma e309_deg_5 : exists u : F5, forall x : F5, x != u -> #|N(x)| = 3.
Proof.
exists (@Ordinal 22 0 isT); apply: (@e309_deg3 F5 e309_l5 _ e309_l5_all e309_l5_uniq).
by vm_compute.
Qed.

(** ** The six together *)

Lemma e309_ord2 (i : 'I_6) : 1 < #|x287_bb_graph i|.
Proof. have [_ _ ->] := g287_helper_sanity; by case: i => -[|[|[|[|[|[|m]]]]]]. Qed.

Lemma e309_deg (i : 'I_6) : exists u : x287_bb_graph i, forall x : x287_bb_graph i, x != u -> #|N(x)| = 3.
Proof.
case: i => -[|[|[|[|[|[|m]]]]]] Hi //;
  [exact: e309_deg_0 | exact: e309_deg_1 | exact: e309_deg_2 | exact: e309_deg_3 | exact: e309_deg_4
  | exact: e309_deg_5].
Qed.

Lemma e309_clause2 : forall i : 'I_6,
  [/\ k_connected (x287_bb_graph i) 2, triangle_free (x287_bb_graph i), subcubic (x287_bb_graph i) &
      8 * α([set: x287_bb_graph i]) < 3 * #|x287_bb_graph i|].
Proof.
case=> -[|[|[|[|[|[|m]]]]]] Hi //;
  [exact: e309_c2_0 | exact: e309_c2_1 | exact: e309_c2_2 | exact: e309_c2_3 | exact: e309_c2_4
  | exact: e309_c2_5].
Qed.

(** ** Clause 3: the order, then closed 5-walks and closed 7-walks *)

Lemma e309_card_0 : #|F0| = 11.
Proof. exact: card_ord. Qed.

Lemma e309_card_1 : #|F1| = 14.
Proof. exact: card_ord. Qed.

Lemma e309_card_2 : #|F2| = 14.
Proof. exact: card_ord. Qed.

Lemma e309_card_3 : #|F3| = 19.
Proof. exact: card_ord. Qed.

Lemma e309_card_4 : #|F4| = 19.
Proof. exact: card_ord. Qed.

Lemma e309_card_5 : #|F5| = 22.
Proof. exact: card_ord. Qed.

Definition e309_v1_5 : nat := sumn [seq @e309_wl F1 e309_l1 5 x x | x <- e309_l1].

Lemma e309_cw5_1 : e309_cw F1 5 = e309_v1_5.
Proof. by rewrite /e309_v1_5; exact: (@e309_cw_list F1 e309_l1 5 e309_l1_all e309_l1_uniq). Qed.

Definition e309_v2_5 : nat := sumn [seq @e309_wl F2 e309_l2 5 x x | x <- e309_l2].

Lemma e309_cw5_2 : e309_cw F2 5 = e309_v2_5.
Proof. by rewrite /e309_v2_5; exact: (@e309_cw_list F2 e309_l2 5 e309_l2_all e309_l2_uniq). Qed.

Definition e309_v3_7 : nat := sumn [seq @e309_wl F3 e309_l3 7 x x | x <- e309_l3].

Lemma e309_cw7_3 : e309_cw F3 7 = e309_v3_7.
Proof. by rewrite /e309_v3_7; exact: (@e309_cw_list F3 e309_l3 7 e309_l3_all e309_l3_uniq). Qed.

Definition e309_v4_7 : nat := sumn [seq @e309_wl F4 e309_l4 7 x x | x <- e309_l4].

Lemma e309_cw7_4 : e309_cw F4 7 = e309_v4_7.
Proof. by rewrite /e309_v4_7; exact: (@e309_cw_list F4 e309_l4 7 e309_l4_all e309_l4_uniq). Qed.

Lemma e309_ne_14 : e309_v1_5 != e309_v2_5.
Proof. by vm_compute. Qed.

Lemma e309_ne_19 : e309_v3_7 != e309_v4_7.
Proof. by vm_compute. Qed.

Section E309Order.
Import bij.

Lemma e309_clause3 : forall i j : 'I_6, i != j -> ~ inhabited (x287_bb_graph i ≃ x287_bb_graph j).
Proof.
case=> -[|[|[|[|[|[|m]]]]]] Hi; case=> -[|[|[|[|[|[|n]]]]]] Hj //; move=> _ [iso].
- by move: (card_bij (diso_v iso)); rewrite e309_card_0 e309_card_1.
- by move: (card_bij (diso_v iso)); rewrite e309_card_0 e309_card_2.
- by move: (card_bij (diso_v iso)); rewrite e309_card_0 e309_card_3.
- by move: (card_bij (diso_v iso)); rewrite e309_card_0 e309_card_4.
- by move: (card_bij (diso_v iso)); rewrite e309_card_0 e309_card_5.
- by move: (card_bij (diso_v iso)); rewrite e309_card_1 e309_card_0.
- by move: (e309_cw_iso iso 5); rewrite e309_cw5_1 e309_cw5_2 => e; move: e309_ne_14; rewrite e eqxx.
- by move: (card_bij (diso_v iso)); rewrite e309_card_1 e309_card_3.
- by move: (card_bij (diso_v iso)); rewrite e309_card_1 e309_card_4.
- by move: (card_bij (diso_v iso)); rewrite e309_card_1 e309_card_5.
- by move: (card_bij (diso_v iso)); rewrite e309_card_2 e309_card_0.
- by move: (e309_cw_iso iso 5); rewrite e309_cw5_2 e309_cw5_1 => e; move: e309_ne_14; rewrite e eqxx.
- by move: (card_bij (diso_v iso)); rewrite e309_card_2 e309_card_3.
- by move: (card_bij (diso_v iso)); rewrite e309_card_2 e309_card_4.
- by move: (card_bij (diso_v iso)); rewrite e309_card_2 e309_card_5.
- by move: (card_bij (diso_v iso)); rewrite e309_card_3 e309_card_0.
- by move: (card_bij (diso_v iso)); rewrite e309_card_3 e309_card_1.
- by move: (card_bij (diso_v iso)); rewrite e309_card_3 e309_card_2.
- by move: (e309_cw_iso iso 7); rewrite e309_cw7_3 e309_cw7_4 => e; move: e309_ne_19; rewrite e eqxx.
- by move: (card_bij (diso_v iso)); rewrite e309_card_3 e309_card_5.
- by move: (card_bij (diso_v iso)); rewrite e309_card_4 e309_card_0.
- by move: (card_bij (diso_v iso)); rewrite e309_card_4 e309_card_1.
- by move: (card_bij (diso_v iso)); rewrite e309_card_4 e309_card_2.
- by move: (e309_cw_iso iso 7); rewrite e309_cw7_4 e309_cw7_3 => e; move: e309_ne_19; rewrite e eqxx.
- by move: (card_bij (diso_v iso)); rewrite e309_card_4 e309_card_5.
- by move: (card_bij (diso_v iso)); rewrite e309_card_5 e309_card_0.
- by move: (card_bij (diso_v iso)); rewrite e309_card_5 e309_card_1.
- by move: (card_bij (diso_v iso)); rewrite e309_card_5 e309_card_2.
- by move: (card_bij (diso_v iso)); rewrite e309_card_5 e309_card_3.
- by move: (card_bij (diso_v iso)); rewrite e309_card_5 e309_card_4.
Qed.

End E309Order.

(** ** Fraughnaugh-Locke (X309) ==> Bajnok-Brinkmann (X287) *)

(*@EDGE from=fraughnaugh_locke_forbidden_subgraph_independence_statement to=bajnok_brinkmann_six_exceptional_graphs_statement kind=implies status=verified proof=fraughnaugh_locke_forbidden_subgraph_independence_implies_bajnok_brinkmann_six_exceptional_graphs note="Rocq-only edge (no corpus relation), routed by Lancelot's NOTE 2026-11-15T05:12:42Z and (786): Fraughnaugh and Locke's conjecture (X309) implies the Bajnok-Brinkmann statement (X287), as arXiv:1911.12471v2 l.229-230 says. Clause 1: for a 2-connected triangle-free subcubic G with 8 alpha(G) < 3n, X309 gives some x287_bb_graph i as a subgraph (has_subgraph decided by a boolean reflection), and e309_iso_of_copy makes G isomorphic to it: every vertex of the copy but one has three neighbours, so their images have no other neighbour, an extra neighbour of the remaining image is impossible inside the copy and makes it a cut vertex outside it, and the copy, closed under adjacency in a connected G, is all of G. Clauses 2 and 3 are closed facts about the tables, proved outright: clause 2 by vm_compute on explicit vertex lists, clause 3 by the order and, for the two pairs of equal order, the closed 5-walks and closed 7-walks an isomorphism preserves. Both statements are true before the pin (Theorem 7 and Corollary 8 of arXiv:1911.12471v2)." *)
Theorem fraughnaugh_locke_forbidden_subgraph_independence_implies_bajnok_brinkmann_six_exceptional_graphs :
  fraughnaugh_locke_forbidden_subgraph_independence_statement -> bajnok_brinkmann_six_exceptional_graphs_statement.
Proof.
move=> hFL; split; [| exact: e309_clause2 | exact: e309_clause3].
move=> G k2 tf sc ha.
have [i hi] : exists i : 'I_6, has_subgraph G (x287_bb_graph i).
  case: (boolP [exists i : 'I_6, e309_subgraphb G (x287_bb_graph i)]) => [/existsP [i /e309_subgraphbP hi] | nex].
    by exists i.
  exfalso; have none : forall i : 'I_6, ~ has_subgraph G (x287_bb_graph i).
    move=> i /e309_subgraphbP hb; move: nex; rewrite negb_exists => /forallP /(_ i).
    by rewrite hb.
  by move: (hFL G tf sc none); rewrite leqNgt ha.
case/has_subgraphP: hi => h [hinj hhom].
have [u hu] := e309_deg i.
by exists i; exact: (e309_iso_of_copy sc k2 (e309_ord2 i) hu hinj hhom).
Qed.
