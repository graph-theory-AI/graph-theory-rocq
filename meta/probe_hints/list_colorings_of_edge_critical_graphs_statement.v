(** Witness hint (lane item, 2026-10-25): an axiom-free REFUTATION of
    [Chromatic.conjectures.U4.list_colorings_of_edge_critical_graphs_statement] as encoded before
    the source's definition of Delta-edge-critical (corpus row
    opg:list_colorings_of_edge_critical_graphs).

    [Delta_edge_critical G] only asks that deleting any edge lowers the chromatic index; the
    source asks that G is not Delta-edge-colourable while every edge-deleted subgraph is. On
    loopless multigraphs the chromatic index can exceed Delta + 1, and the fat triangle below (two
    parallel edges on each side of a triangle) meets the old hypothesis: its six edges pairwise
    share an endpoint, so the line graph is K_6, chi' = 6, chi'(G - e) = 5 and Delta = 4. The
    lists {0,1,2,4} on one edge and {0,1,2,3} on the other five have four colours each, are not
    all equal and cover only five colours, so no list edge colouring exists. Under the source's
    definition the fat triangle is not Delta-edge-critical (chi'(G - e) = 5 > 4), and this file
    no longer compiles (hint-stale-FIX-OK). *)
From GraphTheory Require Import mgraph.
From GTBase Require Export base.
From Chromatic.conjectures Require Import U4.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* probe: the fat triangle, two parallel edges on each side of a triangle; edge e joins e %% 3 and (e %% 3).+1 %% 3 *)
Definition ft_end (b : bool) (e : 'I_6) : 'I_3 :=
  if b then @Ordinal 3 ((e %% 3).+1 %% 3) (@ltn_pmod (e %% 3).+1 3 isT)
  else @Ordinal 3 (e %% 3) (@ltn_pmod e 3 isT).

Definition fat_triangle : mgraph := @mgraph.Graph unit unit 'I_3 'I_6 ft_end (fun _ => tt) (fun _ => tt).

Definition ft_I6 : seq 'I_6 :=
  [:: @Ordinal 6 0 isT; @Ordinal 6 1 isT; @Ordinal 6 2 isT;
      @Ordinal 6 3 isT; @Ordinal 6 4 isT; @Ordinal 6 5 isT].
Definition ft_I3 : seq 'I_3 := [:: @Ordinal 3 0 isT; @Ordinal 3 1 isT; @Ordinal 3 2 isT].

Lemma ft_enum6 : enum 'I_6 = ft_I6.
Proof. by apply: (inj_map val_inj); rewrite val_enum_ord. Qed.
Lemma ft_enum3 : enum 'I_3 = ft_I3.
Proof. by apply: (inj_map val_inj); rewrite val_enum_ord. Qed.
Lemma ft_all6 (P : pred 'I_6) : all P ft_I6 -> forall x, P x.
Proof. by move=> /allP h x; apply: h; rewrite -ft_enum6 mem_enum. Qed.
Lemma ft_all3 (P : pred 'I_3) : all P ft_I3 -> forall x, P x.
Proof. by move=> /allP h x; apply: h; rewrite -ft_enum3 mem_enum. Qed.
Lemma ft_card6 (P : pred 'I_6) : #|P| = count P ft_I6.
Proof. by rewrite cardE /enum_mem -enumT ft_enum6 size_filter. Qed.

Lemma ft_loopless : loopless fat_triangle.
Proof.
move=> e; move: e; apply: (ft_all6 (P := fun e : 'I_6 => ft_end false e != ft_end true e)).
by vm_compute.
Qed.

(* the shared endpoint of two edges: a vertex both edges are incident to *)
(* the shared endpoint of two edges: a vertex both edges are incident to *)
Definition ft_common (e1 e2 : 'I_6) : 'I_3 :=
  if e1 %% 3 == e2 %% 3 then ft_end false e1
  else if (e1 %% 3).+1 %% 3 == e2 %% 3 then ft_end true e1 else ft_end false e1.

Lemma ft_incident (x : fat_triangle) (e : edge fat_triangle) :
  incident x e = (ft_end false e == x) || (ft_end true e == x).
Proof. by apply/existsP/orP => [[[] h]|[h|h]]; [right | left | exists false | exists true]. Qed.

Lemma ft_all66 (P : 'I_6 -> 'I_6 -> bool) : all (fun x => all (P x) ft_I6) ft_I6 -> forall x y, P x y.
Proof. move=> h x; apply: ft_all6; move: x; exact: (ft_all6 (P := fun x => all (P x) ft_I6)). Qed.

(** All six edges pairwise share an endpoint: the line graph is complete. *)
Lemma ft_line_complete (e1 e2 : line_graph fat_triangle) : (e1 -- e2) = (e1 != e2).
Proof.
rewrite /edge_rel /= /line_rel; case: (e1 =P e2) => //= _.
apply/existsP; exists (ft_common e1 e2); rewrite !ft_incident; move: e1 e2.
apply: (ft_all66 (P := fun e1 e2 : 'I_6 =>
  ((ft_end false e1 == ft_common e1 e2) || (ft_end true e1 == ft_common e1 e2)) &&
  ((ft_end false e2 == ft_common e1 e2) || (ft_end true e2 == ft_common e1 e2)))).
by vm_compute.
Qed.

Lemma ft_clique (A : {set line_graph fat_triangle}) : clique A.
Proof. by move=> x y _ _ xy; rewrite ft_line_complete. Qed.

Lemma ft_card_setD1 (T : finType) (x : T) : #|[set: T] :\ x| = #|T|.-1.
Proof. by have := cardsD1 x [set: T]; rewrite in_setT cardsT add1n => ->. Qed.

Lemma ft_cardL : #|line_graph fat_triangle| = 6.
Proof. exact: card_ord. Qed.

Lemma ft_chiT : χ([set: line_graph fat_triangle]) = 6.
Proof. by rewrite (chi_clique (@ft_clique [set: _])) cardsT ft_cardL. Qed.

Lemma ft_chiD (e : line_graph fat_triangle) : χ([set: line_graph fat_triangle] :\ e) = 5.
Proof.
by rewrite (chi_clique (@ft_clique _)) ft_card_setD1 ft_cardL.
Qed.

(** The old hypothesis holds: deleting any edge lowers the chromatic index from 6 to 5. *)
Lemma ft_critical_old : Delta_edge_critical fat_triangle.
Proof. by move=> e; rewrite ft_chiT ft_chiD. Qed.

Lemma ft_edges_at (v : fat_triangle) : #|edges_at v| = 4.
Proof.
rewrite cardsE (eq_card (B := fun e : 'I_6 => (ft_end false e == v) || (ft_end true e == v))); first by move=> e; exact: ft_incident.
rewrite ft_card6; apply/eqP; move: v.
apply: (ft_all3 (P := fun v : 'I_3 =>
  count (fun e : 'I_6 => (ft_end false e == v) || (ft_end true e == v)) ft_I6 == 4)).
by vm_compute.
Qed.

Lemma ft_mDelta : mDelta fat_triangle = 4.
Proof.
apply/eqP; rewrite eqn_leq; apply/andP; split.
- by apply/bigmax_leqP => v _; rewrite ft_edges_at.
- by rewrite -(ft_edges_at (@Ordinal 3 0 isT)); apply: leq_bigmax_cond.
Qed.

(** Lists of mDelta = 4 colours from 'I_5, not all equal; they cover only five colours. *)
Definition ft_L (e : line_graph fat_triangle) : {set 'I_5} :=
  if e == @Ordinal 6 0 isT then [set: 'I_5] :\ @Ordinal 5 3 isT else [set: 'I_5] :\ @Ordinal 5 4 isT.

Lemma ft_L_card (e : line_graph fat_triangle) : #|ft_L e| = mDelta fat_triangle.
Proof.
by rewrite ft_mDelta /ft_L; case: (_ == _); rewrite ft_card_setD1 card_ord.
Qed.

Lemma refuted : ~ list_colorings_of_edge_critical_graphs_statement.
Proof.
move=> /(_ fat_triangle ft_loopless ft_critical_old _ ft_L ft_L_card) [].
- move=> /(_ (@Ordinal 6 0 isT) (@Ordinal 6 1 isT)) /setP /(_ (@Ordinal 5 3 isT)).
  by rewrite /ft_L !inE.
- case=> f [fL fp].
  have finj : injective f.
    move=> x y fxy; apply/eqP; apply: contraT => xy.
    by move: (fp x y); rewrite ft_line_complete xy fxy eqxx => /(_ isT).
  by have := leq_card f finj; rewrite ft_cardL card_ord.
Qed.

Print Assumptions refuted.
