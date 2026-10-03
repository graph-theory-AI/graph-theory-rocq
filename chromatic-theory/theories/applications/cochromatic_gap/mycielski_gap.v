(** * Mycielski construction and exact parameter certificates.

    The cochromatic reduction selects a shadow precisely when the old
    copy has the root's color. The selected vertices induce the original
    graph and avoid one palette color. Extension uses a new independent
    shadow class and an existing independent class for the root.

    These lemmas use arbitrary finite palettes, then connect them to
    GraphTheory's chromatic number and XE2's cochromatic number. *)
From mathcomp Require Import all_boot.
From GraphTheory Require Import coloring partition dom.
From GTBase Require Import base stable_sets.
From Chromatic.conjectures Require Import X7 XE2 XE1.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition proper_map (G : sgraph) (C : finType) (f : G -> C) :=
  forall x y, x -- y -> f x != f y.
Definition homogeneous_map (G : sgraph) (C : finType) (f : G -> C) :=
  forall c, clique [set v | f v == c] \/
            xe1_stable_set [set v | f v == c].
Definition independent_color (G : sgraph) (C : finType) (f : G -> C) (c : C) :=
  xe1_stable_set [set v | f v == c].

Section Mycielski.
Variable G : sgraph.
Definition myc_rel : rel (option (bool * G)) :=
 fun x y => match x, y with
 | None, Some (b, _) => b
 | Some (b, _), None => b
 | Some (b, v), Some (c, w) => (~~ (b && c)) && (v -- w)
 | None, None => false
 end.
Lemma myc_sym : symmetric myc_rel.
Proof.
move=> [[b x]|] [[c y]|]; rewrite /myc_rel /= //.
by rewrite [b && c]andbC sgP.
Qed.
Lemma myc_irrefl : irreflexive myc_rel.
Proof. by move=> [[b x]|] //=; rewrite /myc_rel sg_irrefl andbF. Qed.
Definition mycielski : sgraph := SGraph myc_sym myc_irrefl.
Definition old (v : G) : mycielski := Some (false, v).
Definition shadow (v : G) : mycielski := Some (true, v).
Definition root : mycielski := None.
Lemma old_edge x y : old x -- old y = (x -- y).
Proof. by []. Qed.
Lemma old_shadow_edge x y : old x -- shadow y = (x -- y).
Proof. by []. Qed.
Lemma shadow_old_edge x y : shadow x -- old y = (x -- y).
Proof. by []. Qed.
Lemma shadow_edge x y : shadow x -- shadow y = false.
Proof. by []. Qed.
Lemma root_old_edge x : root -- old x = false.
Proof. by []. Qed.
Lemma root_shadow_edge x : root -- shadow x.
Proof. by []. Qed.
Lemma old_inj : injective old.
Proof. by move=> x y []. Qed.
Lemma shadow_inj : injective shadow.
Proof. by move=> x y []. Qed.
End Mycielski.
Arguments root {G}.

Lemma homogeneous_pullback (G H : sgraph) (C : finType)
    (i : G -> H) (f : H -> C) :
  injective i -> (forall x y, i x -- i y = (x -- y)) ->
  homogeneous_map f -> homogeneous_map (fun x => f (i x)).
Proof.
move=> inj_i edge_i hf c; case: (hf c)=> h; [left|right].
- move=> x y; rewrite !inE => hx hy hxy.
  rewrite -edge_i; apply: h; rewrite ?inE //.
  by rewrite (inj_eq inj_i).
- move/stable_noedgeP: h => h; apply/stable_noedgeP => x y; rewrite !inE=> hx hy hxy.
  apply: (h (i x) (i y)); rewrite ?inE ?edge_i //.
Qed.

Lemma homogeneous_injective_colors (G : sgraph) (C D : finType)
    (f : G -> C) (g : G -> D) (embed : D -> C) :
  (forall x, embed (g x) = f x) ->
  homogeneous_map f -> homogeneous_map g.
Proof.
move=> he hf c; case: (hf (embed c))=> h;
  [left|right; move/stable_noedgeP: h => h; apply/stable_noedgeP];
  move=> x y; rewrite !inE=> /eqP hx /eqP hy hxy;
  apply: (h x y); rewrite ?inE //; apply/eqP;
  by rewrite -he ?hx ?hy.
Qed.

Section MycielskiReduction.
Variables (G : sgraph) (C : finType) (f : mycielski G -> C).
Hypothesis hf : homogeneous_map f.
Definition selected (x : G) : mycielski G :=
  if f (old x) == f (@root G) then shadow x else old x.
Lemma selected_inj : injective selected.
Proof.
move=> x y; rewrite /selected.
by case: (f (old x) == f root); case: (f (old y) == f root)=> [][].
Qed.
Lemma selected_avoids x : f (selected x) != f (@root G).
Proof.
rewrite /selected; case hx: (f (old x) == f root); last by rewrite hx.
case: (hf (f root))=> hr.
- have h := hr root (old x).
  have er : root != old x by [].
  have rr : root \in [set v | f v == f root] by rewrite inE eqxx.
  have ox : old x \in [set v | f v == f root] by rewrite inE hx.
  by have := h rr ox er.
- move/stable_noedgeP: hr => hr; apply/negP=> hs.
  apply: (hr root (shadow x)); rewrite ?inE ?eqxx //.

Qed.
Lemma selected_edge x y : selected x -- selected y = (x -- y).
Proof.
rewrite /selected.
case hx: (f (old x) == f root); case hy: (f (old y) == f root)=> //=.
case: (hf (f root))=> hr.
- have er : root != old x by [].
  have rr : root \in [set v | f v == f root] by rewrite inE eqxx.
  have ox : old x \in [set v | f v == f root] by rewrite inE hx.
  by have := hr root (old x) rr ox er.
- move/stable_noedgeP: hr => hr; symmetry; apply/negP=> hxy.
  apply: (hr (old x) (old y)); rewrite ?inE ?hx ?hy //.
Qed.
Definition reduced_color (x : G) : {c : C | c != f (@root G)} :=
  Sub (f (selected x)) (selected_avoids x).
Lemma reduced_homogeneous : homogeneous_map reduced_color.
Proof.
apply: (@homogeneous_injective_colors G C _ (fun x => f (selected x))
        reduced_color val) => //.
exact: homogeneous_pullback selected_inj selected_edge hf.
Qed.
End MycielskiReduction.

Section MycielskiExtension.
Variables (G : sgraph) (C : finType) (f : G -> C) (c0 : C).
Definition extended_color (x : mycielski G) : option C :=
  match x with
  | Some (false, v) => Some (f v)
  | Some (true, _) => None
  | None => Some c0
  end.
Lemma extended_independent : independent_color extended_color None.
Proof.
apply/stable_noedgeP; move=> [[[] x]|] [[[] y]|]; rewrite /extended_color !inE /= //.
Qed.
Lemma extended_homogeneous :
  homogeneous_map f -> independent_color f c0 ->
  homogeneous_map extended_color.
Proof.
move=> hf /stable_noedgeP hi [c|]; last by right; exact: extended_independent.
case ec: (c0 == c).
- right; move/eqP: ec=> <-; apply/stable_noedgeP.
  move=> [[[] x]|] [[[] y]|]; rewrite /extended_color !inE /= //.
  move=> hx hy hxy; apply: (hi x y); rewrite ?inE //.
- case: (hf c)=> hc; [left|right; move/stable_noedgeP: hc => hc; apply/stable_noedgeP];
    move=> [[[] x]|] [[[] y]|]; rewrite /extended_color !inE /= ?(inj_eq Some_inj) ?ec //.
  + move=> hx hy hxy; apply: hc; rewrite ?inE //.
  + move=> hx hy hxy; apply: (hc x y); rewrite ?inE //.
Qed.
Lemma extended_proper : proper_map f -> proper_map extended_color.
Proof.
move=> hf [[[] x]|] [[[] y]|] //=.
exact: hf.
Qed.
End MycielskiExtension.

Lemma proper_homogeneous (G : sgraph) (C : finType) (f : G -> C) :
  proper_map f -> homogeneous_map f.
Proof.
move=> hf c; right; apply/stable_noedgeP => x y; rewrite !inE=> /eqP hx /eqP hy hxy.
by have := hf x y hxy; rewrite hx hy eqxx.
Qed.
Lemma proper_independent (G : sgraph) (C : finType) (f : G -> C) (c : C) :
  proper_map f -> independent_color f c.
Proof.
move=> hf; apply/stable_noedgeP => x y; rewrite !inE=> /eqP hx /eqP hy hxy.
by have := hf x y hxy; rewrite hx hy eqxx.
Qed.
Lemma reduced_proper (G : sgraph) (C : finType) (f : mycielski G -> C)
    (hf : proper_map f) :
  proper_map (reduced_color (proper_homogeneous hf)).
Proof.
move=> x y hxy; rewrite /reduced_color /= -val_eqE /=.
have he := selected_edge (proper_homogeneous hf) x y.
apply: hf; by rewrite he.
Qed.

Lemma ordinal_homogeneous (G : sgraph) (C : finType) (f : G -> C) :
  homogeneous_map f -> homogeneous_map (fun x => enum_rank (f x)).
Proof.
apply: (@homogeneous_injective_colors G C _ f _ enum_val).
by move=> x; rewrite enum_rankK.
Qed.
Lemma homogeneous_of_ord (G : sgraph) (C : finType) (f : G -> 'I_#|C|) :
  homogeneous_map f -> homogeneous_map (fun x => enum_val (f x)).
Proof.
apply: (@homogeneous_injective_colors G _ C f _ enum_rank).
by move=> x; rewrite enum_valK.
Qed.
Lemma palette_cochromatic (G : sgraph) (C : finType) (f : G -> C) :
  homogeneous_map f -> xe2_cochromatic_colouring G #|C|.
Proof. move=> hf; exists (fun x => enum_rank (f x)); exact: ordinal_homogeneous. Qed.
Lemma palette_cochromatic_lower (G : sgraph) (k : nat) :
  xe2_cochromatic_number G k ->
  forall (C : finType) (f : G -> C), homogeneous_map f -> k <= #|C|.
Proof. move=> [_ hk] C f hf; exact: hk (palette_cochromatic hf). Qed.

Lemma mycielski_cochromatic_lower (G : sgraph) (k q : nat) :
  xe2_cochromatic_number G k ->
  xe2_cochromatic_colouring (mycielski G) q -> k.+1 <= q.
Proof.
move=> hk [f hf].
have h := palette_cochromatic_lower hk (reduced_homogeneous hf).
rewrite card_sig cardC1 card_ord in h.
have hq : 0 < q := leq_ltn_trans (leq0n _) (ltn_ord (f root)).
by rewrite -(prednK hq) ltnS.
Qed.

Lemma proper_chi_bound (G : sgraph) (C : finType) (f : G -> C) :
  proper_map f -> χ([set: G]) <= #|C|.
Proof.
move=> hf.
pose P := preim_partition f [set: G].
have hp : coloring P [set: G].
  apply/andP; split; first exact: preim_partitionP.
  apply/forall_inP=> A /imsetP[x _ ->]; apply/stableP.
  move=> y z; rewrite !inE /= => /eqP hy /eqP hz.
  apply/negP=> hyz; by have := hf y z hyz; rewrite -hy -hz eqxx.
apply: leq_trans (color_bound hp) _.
pose fiber c := [set x : G | c == f x].
have hsub : P \subset [set fiber c | c in [set: C]].
  apply/subsetP=> A /imsetP[x _ ->]; apply/imsetP.
  exists (f x); first by rewrite inE.
  by apply/setP=> y; rewrite /fiber !inE.
apply: leq_trans (subset_leq_card hsub) _.
by have := leq_imset_card fiber [set: C]; rewrite cardsT.
Qed.

Lemma chi_lower_from_palettes (G : sgraph) (k : nat) :
  (forall (C : finType) (f : G -> C), proper_map f -> k <= #|C|) ->
  k <= χ([set: G]).
Proof.
move=> h; case: chiP=> P /andP[hp /forall_inP hs] _.
have hb x : pblock P x \in P.
  apply: pblock_mem; by rewrite (cover_partition hp) inE.
pose f (x : G) : {A : {set G} | A \in P} := Sub (pblock P x) (hb x).
have hf : proper_map f.
  move=> x y hxy; apply/negP=> /eqP he.
  have hsame : pblock P x = pblock P y := congr1 val he.
  have hx : x \in pblock P x by rewrite mem_pblock (cover_partition hp) inE.
  have hy : y \in pblock P x by rewrite hsame mem_pblock (cover_partition hp) inE.
  by have /stableP/(_ x y hx hy) := hs _ (hb x); rewrite hxy.
have := h _ f hf; by rewrite card_sig.
Qed.

Definition cochromatic_certificate (G : sgraph) (k : nat) : Prop :=
  exists (C : finType) (f : G -> C) (c : C),
    #|C| = k /\ homogeneous_map f /\ independent_color f c /\
    (forall (D : finType) (g : G -> D), homogeneous_map g -> k <= #|D|).
Definition chromatic_certificate (G : sgraph) (k : nat) : Prop :=
  exists (C : finType) (f : G -> C),
    #|C| = k /\ proper_map f /\
    (forall (D : finType) (g : G -> D), proper_map g -> k <= #|D|).

Lemma cochromatic_certificate_exact G k :
  cochromatic_certificate G k -> xe2_cochromatic_number G k.
Proof.
move=> [C [f [c [hC [hf [hi hl]]]]]]; split.
- rewrite -hC; exact: palette_cochromatic hf.
- move=> q [g hg]; have := hl _ g hg; by rewrite card_ord.
Qed.
Lemma chromatic_certificate_exact G k :
  chromatic_certificate G k -> χ([set: G]) = k.
Proof.
move=> [C [f [hC [hf hl]]]]; apply/eqP; rewrite eqn_leq.
apply/andP; split.
- rewrite -hC; exact: proper_chi_bound hf.
- exact: chi_lower_from_palettes hl.
Qed.
Lemma mycielski_cochromatic_certificate G k :
  cochromatic_certificate G k -> cochromatic_certificate (mycielski G) k.+1.
Proof.
move=> hcert; have hex := cochromatic_certificate_exact hcert.
case: hcert=> C [f [c [hC [hf [hi hl]]]]].
exists ([the finType of option C]), (extended_color f c), None; split.
- by rewrite card_option hC.
split; first exact: extended_homogeneous hf hi.
split; first exact: extended_independent.
move=> D g hg.
exact: mycielski_cochromatic_lower hex (palette_cochromatic hg).
Qed.
Lemma mycielski_chromatic_certificate G k :
  chromatic_certificate G k -> 0 < #|G| ->
  chromatic_certificate (mycielski G) k.+1.
Proof.
move=> [C [f [hC [hf hl]]]] /card_gt0P[x _].
exists ([the finType of option C]), (extended_color f (f x)); split.
- by rewrite card_option hC.
split; first exact: extended_proper hf.
move=> D g hg.
have h := hl _ _ (reduced_proper hg).
rewrite card_sig cardC1 in h.
have hd : 0 < #|D| by apply/card_gt0P; exists (g root); rewrite inE.
by rewrite -(prednK hd) ltnS.
Qed.

Lemma mycielski_root_neighbors_stable (G : sgraph) (x y : mycielski G) :
  root -- x -> root -- y -> ~~ (x -- y).
Proof. by case: x=> [[[] x]|]; case: y=> [[[] y]|]. Qed.

Lemma mycielski_cliques_bounded (G : sgraph) (n : nat) :
  2 <= n -> 0 < #|G| ->
  (forall K : {set G}, clique K -> #|K| <= n) ->
  forall K : {set mycielski G}, clique K -> #|K| <= n.
Proof.
move=> hn /card_gt0P[x0 _] hb K hK.
case hr: (root \in K).
- have hd : #|K :\ root| <= 1.
    apply/card_le1_eqP=> x y /setD1P[hxr hx] /setD1P[hyr hy].
    apply/eqP; apply/negPn/negP=> hxy.
    have hrx : root -- x by apply: hK=> //; rewrite eq_sym.
    have hry : root -- y by apply: hK=> //; rewrite eq_sym.
    have := mycielski_root_neighbors_stable hrx hry.
    by rewrite sgP (hK y x hy hx hxy).
  rewrite (cardsD1 root K) hr /= add1n.
  exact: leq_trans (leq_ltn_trans hd (ltnSn _)) hn.
- pose proj (x : mycielski G) : G :=
    if x is Some (_, v) then v else x0.
  have hpedge x y : x \in K -> y \in K -> x -- y -> proj x -- proj y.
    case: x=> [[[] x]|]; case: y=> [[[] y]|];
      rewrite /proj /= ?hr //.
  have hinj : {in K &, injective proj}.
    move=> x y hx hy hxy; apply/eqP; apply/negPn/negP=> hneq.
    have he := hpedge x y hx hy (hK x y hx hy hneq).
    by rewrite hxy sg_irrefl in he.
  have hc : clique (proj @: K).
    move=> _ _ /imsetP[x hx ->] /imsetP[y hy ->] hxy.
    have hneq : x != y by apply: contraNneq hxy=> ->.
    exact: hpedge x y hx hy (hK x y hx hy hneq).
  by rewrite -(card_in_imset hinj); exact: hb hc.
Qed.
Lemma omega_from_cliques (G : sgraph) n :
  (forall K : {set G}, clique K -> #|K| <= n) -> ω([set: G]) <= n.
Proof.
move=> h; case: omegaP=> K hK.
exact: h (maxclique_clique hK).
Qed.
