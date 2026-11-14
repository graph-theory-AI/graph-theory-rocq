(** * Topological.conjectures.grounding_X307 -- grounding lemmas for wave X307

    [Qed]-closed, axiom-free certificates for the row of [Topological.conjectures.X307]:
      - hyp_inhabited: the Petersen graph ([petersen_ord], GTBase) is 2-connected and cubic, embeds in the torus
        (an explicit rotation system with 30 darts and 5 faces, so its orientable genus count is
        (2 + 15 - 10 - 5) %/ 2 = 1) and is not 3-edge-colourable (a pruned search over colour lists of its 15
        edges, run on nat codes); the statement's conclusion is then claimed for it;
      - not_trivially_true: the Petersen graph has a K_5 minor (contract the five spokes), so it is not
        Wagner-planar and the variant "every such graph is planar" (no edge deleted) is false, while that
        variant implies the row (deleting edges keeps Wagner-planarity, and a cubic graph has two distinct edges);
      - the guard of the Notes: 2-connectivity gives connectivity ([g307_k2_connected]);
      - [surface_embeddable 1 G] is the package's [toroidal G] ([g307_surface_embeddable_genus],
        [g307_surface_embeddable_toroidal]): same darts, the rotation systems transported field by field.
    Every vm_compute below runs on nat lists and codes only; lemmas transfer the results to the vertices and darts. *)

From mathcomp Require Import perm.
From GraphTheory Require Import minor.
From GTBase Require Import base petersen surface edge_colourings.
From Topological.foundations Require Import embedding.
From Topological.conjectures Require Import X307.
Set SsrOldRewriteGoalsOrder.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Notation Pg := petersen_ord.
Local Notation O10 i := (@Ordinal 10 i isT).
Local Notation D := (surface_dart Pg).

(** ** Cubic and 2-connected (the reachability check of grounding_X268.v over an explicit vertex list) *)

Definition g307_pv : seq Pg :=
  [:: O10 0; O10 1; O10 2; O10 3; O10 4; O10 5; O10 6; O10 7; O10 8; O10 9].

Lemma g307_pv_all (x : Pg) : x \in g307_pv.
Proof. by case: x => -[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]] Hx //=; apply/eqP. Qed.

Arguments g307_pv : simpl never.

Lemma g307_nbrs_ok : all (fun v => size [seq y <- g307_pv | @edge_rel Pg v y] == 3) g307_pv.
Proof. by vm_compute. Qed.

Lemma g307_petersen_regular : regular Pg 3.
Proof.
move=> v; have hu : uniq g307_pv by vm_compute.
move/allP: g307_nbrs_ok => /(_ v (g307_pv_all v)) /eqP <-.
have /card_uniqP <- := filter_uniq (fun y => @edge_rel Pg v y) hu.
apply: eq_card => y.
by rewrite in_opn mem_filter g307_pv_all andbT.
Qed.

(* Breadth-first reachability avoiding the vertices of [rem]. *)
Fixpoint g307_reach (rem : seq Pg) (n : nat) (R : seq Pg) : seq Pg :=
  if n is n'.+1 then
    g307_reach rem n'
      (R ++ [seq y <- g307_pv | (y \notin rem) && (y \notin R) && has (fun x => @edge_rel Pg x y) R])
  else R.

Lemma g307_reachP (S : {set Pg}) (rem : seq Pg) (r : Pg) :
  (forall y, (y \in S) = (y \in rem)) ->
  forall n R, (forall x, x \in R ->
      x \notin rem /\ connect (preliminaries.restrict_mem (mem ([set: Pg] :\: S)) (--)) r x) ->
  forall y, y \in g307_reach rem n R ->
    y \notin rem /\ connect (preliminaries.restrict_mem (mem ([set: Pg] :\: S)) (--)) r y.
Proof.
move=> hS; elim=> [|n IH] R hR y; first exact: hR.
move=> hy; apply: (IH (R ++ [seq y <- g307_pv | (y \notin rem) && (y \notin R) && has (fun x => @edge_rel Pg x y) R])
  _ y hy) => x.
rewrite mem_cat => /orP[/hR // |].
rewrite mem_filter => /andP[/andP[/andP[hx _] /hasP[z hz hzx]] _]; split=> //.
have [hzr hcz] := hR z hz; apply: connect_trans hcz (connect1 _).
by rewrite /preliminaries.restrict_mem /= !inE !hS hzr hx hzx.
Qed.

Definition g307_conn_ok (rem : seq Pg) : bool :=
  let r := head (O10 0) [seq y <- g307_pv | y \notin rem] in
  let L := g307_reach rem 10 [:: r] in
  all (fun y => (y \in rem) || (y \in L)) g307_pv.

Lemma g307_connected_of (S : {set Pg}) (rem : seq Pg) :
  (forall y, (y \in S) = (y \in rem)) -> g307_conn_ok rem -> connected ([set: Pg] :\: S).
Proof.
move=> hS; rewrite /g307_conn_ok; cbv zeta.
case hf: [seq y <- g307_pv | y \notin rem] => [|r f] hall.
  move=> x y hx _; exfalso; move: hx; rewrite !inE hS andbT => hx.
  by have := mem_filter (fun y => y \notin rem) x g307_pv; rewrite hf hx g307_pv_all in_nil.
have hr : r \notin rem by have := mem_head r f; rewrite -hf mem_filter => /andP[].
apply: (@connected_center _ r) => [y|]; last by rewrite !inE hS hr.
rewrite !inE hS andbT => hy.
have hreach : y \in g307_reach rem 10 [:: r].
  by move/allP: hall => /(_ y (g307_pv_all y)); rewrite (negbTE hy) orFb.
have [] // := @g307_reachP S rem r hS 10 [:: r] _ y hreach.
by move=> x; rewrite inE => /eqP ->; split=> //; exact: connect0.
Qed.

Lemma g307_conn_ok1 : all (fun a => g307_conn_ok [:: a]) g307_pv && g307_conn_ok [::].
Proof. by vm_compute. Qed.

Lemma g307_petersen_2conn : k_connected Pg 2.
Proof.
split; first by rewrite card_ord.
move=> S hS; have [h1 h0] := andP g307_conn_ok1.
have : #|S| = 0 \/ #|S| = 1 by move: hS; case: #|S| => [|[|n]]; auto.
case=> [/cards0_eq -> | /eqP/cards1P [a ->]].
- by apply: (@g307_connected_of _ [::] _ h0) => y; rewrite !inE.
- apply: (@g307_connected_of _ [:: a] _ (allP h1 a (g307_pv_all a))) => y.
  by rewrite !inE.
Qed.

(** ** The torus: an explicit rotation system with five faces *)

(** ** Orbit counting by representatives (any permutation of any finite type) *)

Lemma g307_porbit_eq (T : finType) (s : {perm T}) (x y : T) : y \in porbit s x -> porbit s y = porbit s x.
Proof. by case/porbitP => i ->; rewrite porbit_perm. Qed.

Lemma g307_card_porbits (T : finType) (s : {perm T}) (rs : seq T) :
  uniq rs ->
  (forall x, exists2 r, r \in rs & x \in porbit s r) ->
  {in rs &, forall r r', r' \in porbit s r -> r = r'} ->
  #|porbits s| = size rs.
Proof.
move=> urs cover sep.
have -> : porbits s = [set porbit s r | r in rs].
  apply/setP => O; apply/imsetP/imsetP => [[x _ ->] | [r _ ->]]; last by exists r.
  by have [r rin xr] := cover x; exists r => //; exact: g307_porbit_eq.
have inj : {in rs &, injective (porbit s)}.
  by move=> r r' rin r'in e; apply: sep => //; rewrite e porbit_id.
have e : [set porbit s r | r in rs] =i map (porbit s) rs.
  by move=> O; apply/imsetP/mapP => [[r rin ->] | [r rin ->]]; exists r.
have u : uniq (map (porbit s) rs) by rewrite (map_inj_in_uniq inj).
(* the form of walks_paths.v: eq_card onto the seq, then card_uniqP *)
rewrite (eq_card e) -(size_map (porbit s) rs).
first [exact/card_uniqP/u | by apply/card_uniqP | exact: (elimT (card_uniqP _) u)].
Qed.

Lemma g307_porbit_traject (T : finType) (s : {perm T}) (x y : T) :
  (y \in porbit s x) = (y \in traject s x #|T|).
Proof.
apply/idP/idP => [yx | /trajectP [i _ ->]]; last by apply/porbitP; exists i; rewrite permX.
have hle : #|porbit s x| <= #|T| by exact: max_card.
rewrite -(subnKC hle) trajectD mem_cat.
by rewrite -porbit_traject yx.
Qed.

(** ** Nat codes of vertices and darts *)

Definition g307_adjn (a b : nat) : bool := (a != b) && petersen_conn a b.

Lemma g307_adjE (u v : Pg) : (u -- v) = g307_adjn (val u) (val v).
Proof. by rewrite petersen_ord_edgeE /g307_adjn val_eqE. Qed.

Lemma g307_val_iota (x : Pg) : val x \in iota 0 10.
Proof. first [by rewrite mem_iota /= add0n ltn_ord | rewrite mem_iota; exact: (ltn_ord x)]. Qed.

Definition g307_code (d : D) : nat * nat := (val (sval d).1, val (sval d).2).

(* Equal codes mean equal vertex pairs: by rewriting with val_eqE, as g307_adjE does. *)
Lemma g307_code_eq (d1 d2 : D) :
  (g307_code d1 == g307_code d2) = ((sval d1).1 == (sval d2).1) && ((sval d1).2 == (sval d2).2).
Proof. by rewrite /g307_code xpair_eqE !val_eqE. Qed.

Lemma g307_code_inj : injective g307_code.
Proof.
move=> d1 d2 e.
have /andP [/eqP e1 /eqP e2] : ((sval d1).1 == (sval d2).1) && ((sval d1).2 == (sval d2).2).
  by rewrite -g307_code_eq e eqxx.
clear e; move: e1 e2; case: d1 => [[a1 b1] h1]; case: d2 => [[a2 b2] h2] /= e1 e2.
by subst a2 b2; apply: val_inj.
Qed.

Definition g307_dn : seq (nat * nat) :=
  [seq p <- [seq (a, b) | a <- iota 0 10, b <- iota 0 10] | g307_adjn p.1 p.2].

Lemma g307_code_dn (d : D) : g307_code d \in g307_dn.
Proof.
have h : g307_adjn (val (sval d).1) (val (sval d).2) by rewrite -g307_adjE; exact: (svalP d).
rewrite /g307_dn mem_filter; apply/andP; split; first by first [exact: h | move: h].
apply/allpairsP; exists (val (sval d).1, val (sval d).2).
by split; [exact: g307_val_iota | exact: g307_val_iota | ].
Qed.

Lemma g307_dn_dart (c : nat * nat) : c \in g307_dn -> exists d : D, g307_code d = c.
Proof.
rewrite /g307_dn mem_filter => /andP [hadj /allpairsP [[a b] [ha hb e]]]; subst c.
have a10 : (a < 10)%N by move: ha; rewrite mem_iota.
have b10 : (b < 10)%N by move: hb; rewrite mem_iota.
have va : val (inord a : Pg) = a := inordK a10.
have vb : val (inord b : Pg) = b := inordK b10.
have hab : (inord a : Pg) -- inord b by rewrite g307_adjE va vb.
by exists (exist _ (inord a, inord b) hab);
  first [exact: (congr2 pair va vb) | by move: (congr2 pair va vb) | by rewrite /g307_code /= !inordK].
Qed.

Lemma g307_dn_uniq : uniq g307_dn.
Proof. by vm_compute. Qed.

Lemma g307_dn_size : size g307_dn = 30.
Proof. by vm_compute. Qed.

Lemma g307_card_dart : #|{: D}| = 30.
Proof.
have hu : uniq (map g307_code (enum {: D})) by rewrite (map_inj_uniq g307_code_inj) enum_uniq.
have e : map g307_code (enum {: D}) =i g307_dn.
  move=> c; apply/mapP/idP => [[d _ ->]|cin]; first exact: g307_code_dn.
  by have [d <-] := g307_dn_dart cin; exists d; rewrite ?mem_enum.
have := perm_size (uniq_perm hu g307_dn_uniq e).
rewrite size_map g307_dn_size => <-.
first [exact: cardE | by rewrite cardE].
Qed.

(** Any dart map with a nat shadow: trajectories transfer. *)
Lemma g307_traject_code (f : D -> D) (fn : nat * nat -> nat * nat) :
  (forall d, g307_code (f d) = fn (g307_code d)) ->
  forall n d, map g307_code (traject f d n) = traject fn (g307_code d) n.
Proof. by move=> h; elim=> [|n IH] d //=; rewrite IH h. Qed.

Lemma g307_mem_traject (f : D -> D) (fn : nat * nat -> nat * nat) :
  (forall d, g307_code (f d) = fn (g307_code d)) ->
  forall n d d', (d' \in traject f d n) = (g307_code d' \in traject fn (g307_code d) n).
Proof. by move=> h n d d'; rewrite -(g307_traject_code h) (mem_map g307_code_inj). Qed.

(** ** The rotation: cyclic neighbour orders (choice 52 of x307_rotsearch.v, 5 faces) *)

Definition g307_ordn (a : nat) : seq nat :=
  match a with
  | 0 => [:: 5; 4; 1] | 1 => [:: 6; 2; 0] | 2 => [:: 1; 3; 7] | 3 => [:: 8; 4; 2] | 4 => [:: 0; 3; 9]
  | 5 => [:: 0; 7; 8] | 6 => [:: 9; 8; 1] | 7 => [:: 9; 5; 2] | 8 => [:: 6; 5; 3] | _ => [:: 7; 6; 4]
  end%N.

Definition g307_nextn (a b : nat) : nat := (nth 0%N (g307_ordn a) ((index b (g307_ordn a)).+1 %% 3)) %% 10.

Definition g307_next (u v : Pg) : Pg := inord (g307_nextn (val u) (val v)).

Lemma g307_next_val (u v : Pg) : val (g307_next u v) = g307_nextn (val u) (val v).
Proof.
have h := ltn_pmod (nth 0%N (g307_ordn (val u)) ((index (val v) (g307_ordn (val u))).+1 %% 3)) (isT : 0 < 10).
first [exact: (inordK h) | by move: (inordK h) | by rewrite /g307_next /= inordK].
Qed.

Lemma g307_next_adjn :
  all (fun a => all (fun b => g307_adjn a b ==> g307_adjn a (g307_nextn a b)) (iota 0 10)) (iota 0 10).
Proof. by vm_compute. Qed.

Lemma g307_next_adj (u v : Pg) : u -- v -> u -- g307_next u v.
Proof.
rewrite !g307_adjE g307_next_val; apply/implyP.
by move/allP: g307_next_adjn => /(_ _ (g307_val_iota u)) /allP /(_ _ (g307_val_iota v)).
Qed.

Definition g307_rot (d : D) : D :=
  exist _ ((sval d).1, g307_next (sval d).1 (sval d).2) (g307_next_adj (svalP d)).

Definition g307_rotn (c : nat * nat) : nat * nat := (c.1, g307_nextn c.1 c.2).

Lemma g307_code_rot (d : D) : g307_code (g307_rot d) = g307_rotn (g307_code d).
Proof.
first [ exact: (congr1 (pair (val (sval d).1)) (g307_next_val (sval d).1 (sval d).2))
      | by move: (congr1 (pair (val (sval d).1)) (g307_next_val (sval d).1 (sval d).2)) ].
Qed.

Lemma g307_rotn_inj_ok :
  all (fun c1 => all (fun c2 => (g307_rotn c1 == g307_rotn c2) ==> (c1 == c2)) g307_dn) g307_dn.
Proof. by vm_compute. Qed.

Lemma g307_rot_inj : injective g307_rot.
Proof.
move=> d1 d2 e; apply: g307_code_inj; apply/eqP.
move/allP: g307_rotn_inj_ok => /(_ _ (g307_code_dn d1)) /allP /(_ _ (g307_code_dn d2)) /implyP; apply.
by rewrite -!g307_code_rot e eqxx.
Qed.

Definition g307_erot : {perm D} := perm g307_rot_inj.

Lemma g307_erot_src (d : D) : (sval (g307_erot d)).1 = (sval d).1.
Proof. by rewrite permE. Qed.

Lemma g307_vertex_okn :
  all (fun c => all (fun c' => (c'.1 == c.1) == (c' \in traject g307_rotn c 30)) g307_dn) g307_dn.
Proof. by vm_compute. Qed.

Lemma g307_erot_vertex (d : D) : porbit g307_erot d = [set d' | (sval d').1 == (sval d).1].
Proof.
have hr : forall e, g307_code (g307_erot e) = g307_rotn (g307_code e).
  by move=> e; rewrite permE g307_code_rot.
apply/setP => d'; rewrite inE g307_porbit_traject g307_card_dart (g307_mem_traject hr).
move/allP: g307_vertex_okn => /(_ _ (g307_code_dn d)) /allP /(_ _ (g307_code_dn d')) /eqP <-.
first [exact: val_eqE | by rewrite -val_eqE | by rewrite /g307_code /= val_eqE].
Qed.

Definition g307_embedding : surface_embedding Pg :=
  SurfaceEmbedding g307_erot_src g307_erot_vertex.

(** ** Five faces *)

Definition g307_face (d : D) : D := surface_rev_dart (g307_rot d).

Definition g307_facen (c : nat * nat) : nat * nat := (g307_nextn c.1 c.2, c.1).

Lemma g307_code_face (d : D) : g307_code (g307_face d) = g307_facen (g307_code d).
Proof.
first [ exact: (congr1 (fun x => (x, val (sval d).1)) (g307_next_val (sval d).1 (sval d).2))
      | by move: (congr1 (fun x => (x, val (sval d).1)) (g307_next_val (sval d).1 (sval d).2)) ].
Qed.

Lemma g307_face_permE (d : D) : surface_face_perm g307_embedding d = g307_face d.
Proof.
first [by rewrite /surface_face_perm permM !permE | by rewrite /surface_face_perm permM /= !permE].
Qed.

(* One representative per face, by a nat-level orbit walk over g307_dn. *)
Fixpoint g307_repsn (n : nat) (cs seen : seq (nat * nat)) : seq (nat * nat) :=
  if n is n'.+1 then
    match cs with
    | [::] => [::]
    | c :: cs' => if c \in seen then g307_repsn n' cs' seen
                  else c :: g307_repsn n' cs' (traject g307_facen c 30 ++ seen)
    end
  else [::].

Definition g307_frn : seq (nat * nat) := g307_repsn 30 g307_dn [::].

Lemma g307_faces_okn :
  [&& size g307_frn == 5, uniq g307_frn, all (fun r => r \in g307_dn) g307_frn,
      all (fun c => has (fun r => c \in traject g307_facen r 30) g307_frn) g307_dn &
      all (fun r => all (fun r' => (r' \in traject g307_facen r 30) ==> (r == r')) g307_frn) g307_frn].
Proof. by vm_compute. Qed.

Definition g307_d0 : D := exist _ (O10 0, O10 1) isT.

Definition g307_dart_of (c : nat * nat) : D := insubd g307_d0 (inord c.1, inord c.2).

Lemma g307_code_dart_of (c : nat * nat) : c \in g307_dn -> g307_code (g307_dart_of c) = c.
Proof.
move=> cin; have [d <-] := g307_dn_dart cin.
have hp : ((inord (g307_code d).1, inord (g307_code d).2) : Pg * Pg) = val d.
  first [by case: d => [[u v] h] /=; rewrite !inord_val | by case: d => [[u v] h]; congr pair; exact: inord_val].
by rewrite /g307_dart_of hp valKd.
Qed.

Lemma g307_faces : surface_embedding_faces g307_embedding = 5.
Proof.
have /and5P [/eqP hs hu hin hcov hsep] := g307_faces_okn.
pose rs := map g307_dart_of g307_frn.
have hmap : map g307_code rs = g307_frn.
  rewrite /rs -map_comp -{2}(map_id g307_frn); apply/eq_in_map => c cin.
  first [exact: g307_code_dart_of (allP hin c cin) | by move: (g307_code_dart_of (allP hin c cin))].
have hf : forall e, g307_code (surface_face_perm g307_embedding e) = g307_facen (g307_code e).
  by move=> e; rewrite g307_face_permE g307_code_face.
have tr r d : (d \in traject (surface_face_perm g307_embedding) r 30)
              = (g307_code d \in traject g307_facen (g307_code r) 30) := g307_mem_traject hf 30 r d.
have hu' : uniq rs by rewrite -(map_inj_uniq g307_code_inj) hmap.
have hcov' : forall x, exists2 r, r \in rs & x \in porbit (surface_face_perm g307_embedding) r.
  move=> d; move/allP: hcov => /(_ _ (g307_code_dn d)) /hasP [r rin rd].
  exists (g307_dart_of r); first exact: map_f.
  by rewrite g307_porbit_traject g307_card_dart tr (g307_code_dart_of (allP hin r rin)).
have hsep' : {in rs &, forall r r', r' \in porbit (surface_face_perm g307_embedding) r -> r = r'}.
  move=> r r' /mapP [c cin ->] /mapP [c' c'in ->].
  rewrite g307_porbit_traject g307_card_dart tr.
  rewrite (g307_code_dart_of (allP hin _ cin)) (g307_code_dart_of (allP hin _ c'in)) => h.
  by move/allP: hsep => /(_ _ cin) /allP /(_ _ c'in) /implyP /(_ h) /eqP ->.
by rewrite /surface_embedding_faces (g307_card_porbits hu' hcov' hsep') /rs size_map hs.
Qed.

Lemma g307_petersen_toroidal : surface_embeddable 1 Pg.
Proof.
exists g307_embedding.
by rewrite /surface_euler_genus /surface_embedding_edges /surface_embedding_vertices g307_card_dart g307_faces card_ord.
Qed.

(** ** Not 3-edge-colourable: a pruned search over colour lists of the 15 edges *)

(** The 15 edges, normalized (smaller end first). *)
Definition g307_tb : seq (nat * nat) := [seq (minn p.1 p.2, maxn p.1 p.2) | p <- petersen_edge_table].

Definition g307_idx (a b : nat) : nat := index (minn a b, maxn a b) g307_tb.

(** The properness constraints: a vertex x with two neighbours y < z, as ((x, y), z). *)
Definition g307_tri : seq (nat * nat * nat) :=
  [seq t <- [seq (xy, z) | xy <- [seq (x, y) | x <- iota 0 10, y <- iota 0 10], z <- iota 0 10]
   | g307_adjn t.1.1 t.1.2 && g307_adjn t.1.1 t.2 && (t.1.2 < t.2)].

Definition g307_okL (L : seq nat) : bool :=
  all (fun t => (maxn (g307_idx t.1.1 t.1.2) (g307_idx t.1.1 t.2) < size L) ==>
                (nth 0 L (g307_idx t.1.1 t.1.2) != nth 0 L (g307_idx t.1.1 t.2))) g307_tri.

(** The 30 constraints as a literal list of edge-index pairs, so that the search does not recompute the
    1000-triple table at every node; g307_cons_ok checks the list against the table.  The search step is an
    if, not &&: vm_compute evaluates every argument of a function, and && would not prune. *)
Definition g307_cons : seq (nat * nat) :=
  [:: (0, 4); (0, 5); (4, 5); (0, 1); (0, 6); (1, 6); (1, 2); (1, 7); (2, 7); (2, 3); (2, 8); (3, 8); (4, 3); (4, 9);
      (3, 9); (5, 10); (5, 14); (10, 14); (6, 13); (6, 12); (13, 12); (7, 10); (7, 11); (10, 11); (8, 14); (8, 13);
      (14, 13); (9, 12); (9, 11); (12, 11)].

Lemma g307_cons_ok : g307_cons = [seq (g307_idx t.1.1 t.1.2, g307_idx t.1.1 t.2) | t <- g307_tri].
Proof. by vm_compute. Qed.

Definition g307_okc (L : seq nat) : bool :=
  all (fun ij => (maxn ij.1 ij.2 < size L) ==> (nth 0 L ij.1 != nth 0 L ij.2)) g307_cons.

Lemma g307_okL_okc (L : seq nat) : g307_okL L = g307_okc L.
Proof.
(* unfold first and compare pointwise, so that no unification computes the 1000-triple table *)
by rewrite /g307_okL /g307_okc g307_cons_ok all_map; apply: eq_all => t.
Qed.

Fixpoint g307_search (n : nat) (p : seq nat) : bool :=
  if n is n'.+1 then has (fun x => if g307_okc (rcons p x) then g307_search n' (rcons p x) else false) [:: 0; 1; 2]
  else true.

Lemma g307_searchS (n : nat) (p : seq nat) :
  g307_search n.+1 p = has (fun x => g307_okc (rcons p x) && g307_search n (rcons p x)) [:: 0; 1; 2].
Proof. by []. Qed.

Lemma g307_search_false : g307_search 15 [::] = false.
Proof. by vm_compute. Qed.

(** One constraint survives taking a prefix. *)
Lemma g307_ok_take (L : seq nat) (k i j : nat) :
  (maxn i j < size L) ==> (nth 0 L i != nth 0 L j) ->
  (maxn i j < size (take k L)) ==> (nth 0 (take k L) i != nth 0 (take k L) j).
Proof.
move=> /implyP hL; apply/implyP; rewrite size_take => hk.
have hk' : maxn i j < size L.
  by apply: leq_trans hk _; case: ifP => [/ltnW // | _]; exact: leqnn.
have hmk : (if k < size L then k else size L) <= k.
  by case: ifP => [_ | /negbT]; [exact: leqnn | rewrite -leqNgt].
have hm : maxn i j < k := leq_trans hk hmk.
have hi : i < k := leq_ltn_trans (leq_maxl i j) hm.
have hj : j < k := leq_ltn_trans (leq_maxr i j) hm.
by rewrite !nth_take //; exact: hL hk'.
Qed.

Lemma g307_okc_take (L : seq nat) (k : nat) : g307_okc L -> g307_okc (take k L).
Proof. by move=> /allP h; apply/allP => ij ijin; exact: (@g307_ok_take L k _ _ (h ij ijin)). Qed.

Lemma g307_search_complete (L : seq nat) :
  size L = 15 -> all (fun x => x < 3) L -> g307_okc L ->
  forall m k, k + m = 15 -> g307_search m (take k L).
Proof.
move=> sL hL ok; elim=> [|m IH] k hkm; first by [].
have kL : k < size L by rewrite sL -hkm addnS ltnS leq_addr.
have h1 : g307_okc (take k.+1 L) := g307_okc_take k.+1 ok.
have h2 : g307_search m (take k.+1 L) by apply: IH; rewrite addSnnS.
rewrite (take_nth 0 kL) in h1 h2.
rewrite g307_searchS; apply/hasP; exists (nth 0 L k).
  by move/allP: hL => /(_ _ (mem_nth 0 kL)); case: (nth 0 L k) => [|[|[|n]]].
exact: (introT andP (conj h1 h2)).
Qed.

(** From a proper 3-edge-colouring of Pg to a nat colour list satisfying okL. *)
Section Colouring.
Variable col : {set Pg} -> 'I_3.

Definition g307_ecol (a b : nat) : nat := val (col [set (inord a : Pg); inord b]).

Lemma g307_ecolC (a b : nat) : g307_ecol a b = g307_ecol b a.
Proof. by rewrite /g307_ecol setUC. Qed.

Lemma g307_ecol_minmax (a b : nat) : g307_ecol (minn a b) (maxn a b) = g307_ecol a b.
Proof.
(* leqP of MathComp 2 is indexed by minn / maxn, so the case analysis may already rewrite them; the
   commutativity rule is applied once (under ? it would repeat forever). *)
first [ by case: (leqP a b) => h; [ | exact: g307_ecolC ]
      | by case: (leqP a b) => h;
          [ rewrite (minn_idPl h) (maxn_idPr h)
          | rewrite (minn_idPr (ltnW h)) (maxn_idPl (ltnW h)) g307_ecolC ] ].
Qed.

Definition g307_L : seq nat := [seq g307_ecol p.1 p.2 | p <- g307_tb].

End Colouring.

Lemma g307_tri_ok :
  all (fun t => [&& t.1.1 < 10, t.1.2 < 10, t.2 < 10,
                    (minn t.1.1 t.1.2, maxn t.1.1 t.1.2) \in g307_tb &
                    (minn t.1.1 t.2, maxn t.1.1 t.2) \in g307_tb]) g307_tri.
Proof. by vm_compute. Qed.

(** An entry of the colour list is the colour of its edge, proved on small goals. *)
Lemma g307_L_nth (col : {set Pg} -> 'I_3) (x y : nat) :
  (minn x y, maxn x y) \in g307_tb -> nth 0 (g307_L col) (g307_idx x y) = g307_ecol col x y.
Proof.
move=> hin.
rewrite /g307_L (nth_map (0, 0)); last by rewrite /g307_idx index_mem.
have -> : nth (0, 0) g307_tb (g307_idx x y) = (minn x y, maxn x y) by rewrite /g307_idx nth_index.
exact: (g307_ecol_minmax col x y).
Qed.

Lemma g307_petersen_snark : ~ exists col : {set Pg} -> 'I_3, proper_edge_colouring col.
Proof.
case=> col hcol.
have ok : g307_okL (g307_L col).
  apply/allP => t tin; apply/implyP => _.
  move/allP: g307_tri_ok => /(_ t tin) /and5P [x10 y10 z10 xy xz].
  rewrite (g307_L_nth col xy) (g307_L_nth col xz) /g307_ecol.
  move: tin; rewrite /g307_tri mem_filter => /andP [/andP [/andP [hxy hxz] hlt] _].
  have v1 : val (inord t.1.1 : Pg) = t.1.1 := inordK x10.
  have v2 : val (inord t.1.2 : Pg) = t.1.2 := inordK y10.
  have v3 : val (inord t.2 : Pg) = t.2 := inordK z10.
  have exy : (inord t.1.1 : Pg) -- inord t.1.2 by rewrite g307_adjE v1 v2.
  have exz : (inord t.1.1 : Pg) -- inord t.2 by rewrite g307_adjE v1 v3.
  have ne : (inord t.1.2 : Pg) != inord t.2.
    by apply/eqP => /(congr1 val); rewrite v2 v3 => e; rewrite e ltnn in hlt.
  by rewrite val_eqE; exact: hcol _ _ _ exy exz ne.
have sz : size (g307_L col) = 15 by rewrite /g307_L size_map.
have lt3 : all (fun x => x < 3) (g307_L col).
  apply/allP => x; rewrite /g307_L => /mapP [p _ ->].
  first [exact: ltn_ord | exact: (ltn_ord (col [set (inord p.1 : Pg); inord p.2]))].
have okc : g307_okc (g307_L col) by rewrite -g307_okL_okc.
have := @g307_search_complete (g307_L col) sz lt3 okc 15 0 (erefl _).
by rewrite take0 g307_search_false.
Qed.

(** ** A K_5 minor, planarity under edge deletion, two edges at a cubic vertex *)

(** The spoke contraction: bag i = {i, i + 5}. *)
Definition g307_bag (i : 'K_5) : {set Pg} := [set inord i; inord (i + 5)].

Lemma g307_bags_ok :
  all (fun i => all (fun j => (i == j) || has (fun a => has (fun b => g307_adjn a b) [:: j; j + 5]) [:: i; i + 5])
                    (iota 0 5)) (iota 0 5)
  && all (fun i => g307_adjn i (i + 5)) (iota 0 5).
Proof. by vm_compute. Qed.

Lemma g307_K5_iota (i : 'K_5) : (i : nat) \in iota 0 5.
Proof. by rewrite mem_iota /= add0n ltn_ord. Qed.

Lemma g307_lt10 (i : 'K_5) : ((i : nat) < 10)%N.
Proof. by apply: ltn_trans (ltn_ord i) _. Qed.

Lemma g307_lt10' (i : 'K_5) : ((i : nat) + 5 < 10)%N.
Proof. by case: i => [[|[|[|[|[|n]]]]] H]. Qed.

Lemma g307_v1 (i : 'K_5) : val (inord i : Pg) = i.
Proof. exact: (inordK (g307_lt10 i)). Qed.

Lemma g307_v2 (i : 'K_5) : val (inord (i + 5) : Pg) = i + 5.
Proof. exact: (inordK (g307_lt10' i)). Qed.

Lemma g307_petersen_K5_minor : minor Pg 'K_5.
Proof.
have [hn hs] := andP g307_bags_ok.
apply: (@minor_of_rmap _ _ g307_bag); split.
- by move=> i; apply/set0Pn; exists (inord i); rewrite /g307_bag !inE eqxx.
- move=> i; rewrite /g307_bag; apply: connected2.
  rewrite g307_adjE g307_v1 g307_v2.
  by move/allP: hs => /(_ _ (g307_K5_iota i)).
- move=> i j ij; rewrite /g307_bag disjoint_set2 -!val_eqE !g307_v1 !g307_v2.
  move: ij; rewrite -val_eqE.
  by case: i => [[|[|[|[|[|m]]]]] Hi]; case: j => [[|[|[|[|[|m']]]]] Hj].
- move=> i j ij; have {}ij : i != j by exact: ij.
  apply/neighborP.
  have := allP (allP hn _ (g307_K5_iota i)) _ (g307_K5_iota j).
  case/orP => [/eqP e | /hasP [a ain /hasP [b bin hab]]].
    by move: ij; rewrite (ord_inj e) eqxx.
  exists (inord a), (inord b); split.
  + move: ain; rewrite /g307_bag !in_cons in_nil orbF !inE.
    by case/orP => /eqP ->; rewrite eqxx ?orbT.
  + move: bin; rewrite /g307_bag !in_cons in_nil orbF !inE.
    by case/orP => /eqP ->; rewrite eqxx ?orbT.
  + have a10 : a < 10.
      by move: ain; rewrite !in_cons in_nil orbF; case/orP => /eqP ->; [exact: g307_lt10 | exact: g307_lt10'].
    have b10 : b < 10.
      by move: bin; rewrite !in_cons in_nil orbF; case/orP => /eqP ->; [exact: g307_lt10 | exact: g307_lt10'].
    have va : val (inord a : Pg) = a := inordK a10.
    have vb : val (inord b : Pg) = b := inordK b10.
    by rewrite g307_adjE va vb.
Qed.

Lemma g307_petersen_not_planar : ~ wagner_planar Pg.
Proof. by case=> n5 _; apply: n5; exact: g307_petersen_K5_minor. Qed.

(** Deleting edges keeps a graph Wagner-planar (crossing.v's wagner_planar_sub, specialised). *)
Lemma g307_planar_del (G : sgraph) (F : {set {set G}}) : wagner_planar G -> wagner_planar (del_edge_set G F).
Proof.
move=> [n5 n33].
have m : minor G (del_edge_set G F) by apply: sub_minor; exact: has_subgraph_del_edge_set.
by split=> h; [apply: n5 | apply: n33]; exact: minor_trans m h.
Qed.

(** A cubic graph with a vertex has two distinct edges at that vertex. *)
Lemma g307_two_edges (G : sgraph) (v : G) :
  #|N(v)| = 3 -> exists e1 e2 : {set G}, [/\ e1 \in E(G), e2 \in E(G) & e1 != e2].
Proof.
move=> h3; have /card_gt1P [a [b [ain bin ab]]] : 1 < #|N(v)| by rewrite h3.
have va : v -- a by rewrite -in_opn.
have vb : v -- b by rewrite -in_opn.
exists [set v; a], [set v; b]; split.
- by apply/edgesP; exists v, a.
- by apply/edgesP; exists v, b.
- apply/eqP => /setP /(_ a); rewrite !inE eqxx orbT => /esym /orP [] /eqP e.
  + by move: va; rewrite e sgP.
  + by move: ab; rewrite e eqxx.
Qed.

(** ** The guard of the Notes: 2-connectivity gives connectivity *)

Lemma g307_k2_connected (G : sgraph) : k_connected G 2 -> connected [set: G].
Proof. by case=> _ /(_ set0); rewrite cards0 setD0; apply. Qed.

(** ** [surface_embeddable 1 G] is the package's [toroidal G] (Topological.foundations.embedding) *)

Lemma g307_edge_perm_eq (G : sgraph) : surface_edge_perm G = edge_perm G.
Proof.
have h : forall d : surface_dart G, surface_edge_perm G d = edge_perm G d.
  by move=> d; rewrite permE edge_permE; apply: val_inj.
by apply/perm.permP.
Qed.

Lemma g307_surface_embeddable_genus (G : sgraph) (g : nat) :
  surface_embeddable g G <-> embeds_in_genus G g.
Proof.
have ep := g307_edge_perm_eq G; split.
- case=> E gE; exists (Emb (surface_erot_src E) (surface_erot_vertex E)).
  by move: gE; rewrite /surface_euler_genus /euler_genus /surface_embedding_faces /emF
    /surface_face_perm /face_perm /= -ep.
- case=> E gE; exists (SurfaceEmbedding (erot_src E) (erot_vertex E)).
  by move: gE; rewrite /surface_euler_genus /euler_genus /surface_embedding_faces /emF
    /surface_face_perm /face_perm /= -ep.
Qed.

Lemma g307_surface_embeddable_toroidal (G : sgraph) : surface_embeddable 1 G <-> toroidal G.
Proof. exact: g307_surface_embeddable_genus. Qed.

(** ** hyp_inhabited: the Petersen graph meets the four hypotheses *)

Definition g307_hyp_claim : Prop :=
  [/\ k_connected Pg 2, regular Pg 3, surface_embeddable 1 Pg
    & ~ (exists col : {set Pg} -> 'I_3, proper_edge_colouring col)] /\
  (grunbaum_torus_cubic_statement ->
     exists e1 e2 : {set Pg},
       [/\ e1 \in E(Pg), e2 \in E(Pg), e1 != e2 & wagner_planar (del_edge_set Pg [set e1; e2])]).

Theorem g307_hyp_inhabited : g307_hyp_claim.
Proof.
have h := And4 g307_petersen_2conn g307_petersen_regular g307_petersen_toroidal g307_petersen_snark.
split=> // S; case: h => k2 r3 tor nc; exact: S _ k2 r3 tor nc.
Qed.

(** ** not_trivially_true: without the two deleted edges the conclusion fails on the Petersen graph *)

Definition g307_planar_variant : Prop :=
  forall G : sgraph, k_connected G 2 -> regular G 3 -> surface_embeddable 1 G ->
    ~ (exists col : {set G} -> 'I_3, proper_edge_colouring col) -> wagner_planar G.

Definition g307_ntt_claim : Prop :=
  ~ g307_planar_variant /\ (g307_planar_variant -> grunbaum_torus_cubic_statement).

Theorem g307_not_trivially_true : g307_ntt_claim.
Proof.
split=> [V | V G k2 r3 tor nc].
  exact: g307_petersen_not_planar
    (V _ g307_petersen_2conn g307_petersen_regular g307_petersen_toroidal g307_petersen_snark).
have pl := V G k2 r3 tor nc.
have [v _] : exists v : G, true by case: k2 => /ltnW /ltnW /card_gt0P [v _] _; exists v.
have [e1 [e2 [h1 h2 h12]]] := g307_two_edges (r3 v).
by exists e1, e2; split=> //; exact: g307_planar_del.
Qed.
