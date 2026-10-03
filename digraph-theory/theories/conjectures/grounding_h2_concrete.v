(** * Digraph.conjectures.grounding_h2_concrete — GROUNDING the CONCRETE H2 /
      2-extremal constructions (two_extremal, two_extremal_hajos,
      two_extremal_glue, generalised_wheel, glue_eul_subtype)

    FAITHFULNESS CHECK.  These files STATE Aboulker–Aubian–Charbit Conjecture 9.2
    (arXiv:2304.04690 §9) and build the CONCRETE H₂ constructions: the generalised
    wheel [gwheel], the directed Hajós join [dhajos], the symmetric odd cycle base,
    the vertex amalgams [vglue] / [ueglue], the rim [di_cycle], the plane-tree data
    and the concrete membership predicate [in_H2_concrete].  This file proves SMALL,
    KNOWN, decidable facts those constructions MUST satisfy if they are faithful, and
    runs falsification / non-vacuity probes.  It is COMPLEMENTARY to the committed
    [grounding_two_extremal.v] (no overlap: that file grounds the symmetric-triangle
    base, [canon_tree] legality, the [arc2]-Hajós added/deleted arc, and the W₃
    spoke/rim arcs; HERE we ground the gwheel n=3 STRUCTURAL side facts via the
    committed lemmas, the symmetric-3-cycle Eulerian+H₂ value, [wheel_tree]
    even-B-parity, the directed Hajós join's SECOND deletion, the [di_cycle 3] rim
    side facts, the [vglue] 2-vertex amalgam, and the [conj_9_2_*] non-vacuity).

    We import ONLY committed modules.  Every lemma is Qed; no Admitted/Axiom. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From mathcomp Require Import generic_quotient.
From GraphTheory Require Import preliminaries.
From Digraph Require Import prelude interop_graph_theory digraph oriented tournament.
From Digraph Require Import dipath strong dichromatic classic_core.
From Digraph Require Import two_extremal two_extremal_hajos two_extremal_glue.
From Digraph Require Import generalised_wheel glue_eul_subtype glue_tree.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope quotient_scope.

(** ** §A — the generalised wheel [gwheel 3] (= W₃): vertex count + STRUCTURAL side
       facts via the committed lemmas

    GROUNDS: [gwheel n] (generalised_wheel.v) is the classical wheel W_n on [n.+1]
    vertices.  The committed file proves looplessness, Eulerianness, the digon-graph
    forest and 2-connectivity for general [n ≥ 3]; here we instantiate the STRUCTURAL
    package at the SMALLEST case [n = 3] (W₃), which the assignment singles out.  This
    is a faithfulness datum: the smallest member of the H₂ tree-join family really has
    the advertised structure. *)

(** [#|gwheel 3| = 4] : 1 hub + 3 rim.  (Re-grounding [gwheel_card] at [n = 3].) *)
Lemma gwheel3_vcount : #|gwheel 3| = 4.
Proof. by rewrite gwheel_card. Qed.

(** [gwheel 3] is loopless (committed [gwheel_loopless], [n ≥ 2]). *)
Lemma gw3_loopless : loopless (gwheel 3).
Proof. by apply: gwheel_loopless. Qed.

(** [gwheel 3] is Eulerian (committed [gwheel_Eulerian]): in-degree = out-degree
    everywhere — hub has in = out = 3, each rim has in = out = 2. *)
Lemma gw3_Eulerian : Eulerian (gwheel 3).
Proof. by apply: gwheel_Eulerian. Qed.

(** The STRUCTURAL package of [gwheel 3] (W₃): Eulerian, digon graph a FOREST,
    underlying graph 2-CONNECTED, and membership in the concretely-generated H₂.
    This is exactly the committed [gwheel_is_wheel] instantiated at [n = 3] — proving
    the smallest generalised wheel inhabits every advertised property. *)
Lemma gw3_is_wheel (llD : loopless (gwheel 3)) :
  [/\ Eulerian (gwheel 3),
      is_forest [set: digonG llD],
      two_connected_sg (underlyingG llD)
    & in_H2_concrete realises_gw (gwheel 3)].
Proof. by apply: gwheel_is_wheel. Qed.

(** The digon graph of [gwheel 3] is a FOREST (committed [gwheel_digonG_forest]):
    its digon graph is the hub-rim STAR, acyclic.  RED-FLAG check: if a rim-rim
    digon existed the digon graph would carry a cycle and fail to be a forest. *)
Lemma gw3_digonG_forest (llD : loopless (gwheel 3)) :
  is_forest [set: digonG llD].
Proof. by apply: gwheel_digonG_forest. Qed.

(** The digon adjacency of W₃ is EXACTLY "exactly one endpoint is the hub" (committed
    [gwheel_digonADJ]).  We instantiate at the hub [ord0] and rim label 1: a DIGON. *)
Lemma gw3_digon_hub_rim :
  digonADJ (ord0 : gwheel 3) (Ordinal (n := 4) (m := 1) isT).
Proof. by rewrite gwheel_digonADJ. Qed.

(** Two rim vertices are NOT a digon (the rim is a directed single-arc cycle):
    rim 1 and rim 2 do not form a digon.  RED-FLAG check on [gwheel_digonADJ]. *)
Lemma gw3_no_rim_digon :
  ~~ digonADJ (Ordinal (n := 4) (m := 1) isT : gwheel 3)
              (Ordinal (n := 4) (m := 2) isT).
Proof. by rewrite gwheel_digonADJ. Qed.

(** [gwheel 3] is a generalised wheel under the concrete predicate
    [generalised_wheel_pred] (committed) — the abstract predicate of [two_extremal.v]
    is genuinely INHABITED by W₃. *)
Lemma gw3_generalised_wheel : generalised_wheel_pred (gwheel 3).
Proof. by apply: gwheel_is_generalised_wheel. Qed.

(** ** §B — the symmetric 3-cycle base: Eulerian and an H₂ value

    GROUNDS: the base members of H₂ are the symmetric ODD cycles (two_extremal.v §4).
    The committed [grounding_two_extremal.v] already grounds inhabitation, looplessness
    and strongness of [sym_cycle 3].  HERE we ground the missing values the rim/base
    must satisfy: it is EULERIAN (a bidirected cycle is balanced: in = out = 2 at every
    vertex) and it is a BASE member of [in_H2_concrete]. *)

(** Every vertex of [sym_cycle 3] has out-set = in-set (each neighbour is reciprocal),
    hence in-degree = out-degree: [sym_cycle 3] is EULERIAN. *)
Lemma symcyc3_Eulerian : Eulerian (sym_cycle 3).
Proof.
move=> v; rewrite /degree_balance.indeg /outdeg.
(* the out-set and in-set coincide because adjacency is SYMMETRIC *)
rewrite (_ : [set u : sym_cycle 3 | u --> v] = [set w : sym_cycle 3 | v --> w]) //.
apply/setP => w; rewrite !inE /arc/= /symcyc_rel.
by rewrite orbC.
Qed.

(** [sym_cycle 3] is a BASE member of the concretely-generated H₂ (for any realisation
    relation): the symmetric triangle inhabits [in_H2_concrete] via [inH2_base]. *)
Lemma symcyc3_in_H2 (realises : ptree -> diGraphType -> Prop) :
  in_H2_concrete realises (sym_cycle 3).
Proof.
apply: inH2_base.
by exists 3; split => //; exact: dgiso_refl.
Qed.

(** RED-FLAG / discriminating value: the out-degree of each [sym_cycle 3] vertex is
    exactly 2 (two reciprocal neighbours), NOT 1 — distinguishing the SYMMETRIC cycle
    from the directed rim [di_cycle] (out-degree 1).  We check vertex 0. *)
Lemma symcyc3_outdeg0 :
  outdeg (Ordinal (n := 3) (m := 0) isT : sym_cycle 3) = 2.
Proof.
rewrite /outdeg.
rewrite (_ : [set w : sym_cycle 3 | _ --> w]
           = [set (Ordinal (n := 3) (m := 1) isT : sym_cycle 3);
                  (Ordinal (n := 3) (m := 2) isT : sym_cycle 3)]).
  by rewrite cards2.
apply/setP => w; rewrite !inE /arc/= /symcyc_rel.
by case: w => [[|[|[|m]]] h] //=; rewrite -!val_eqE.
Qed.

(** ** §C — even-B-parity of the [wheel_tree] star datum (the empty-A generalised
       wheel data, n ≥ 2)

    GROUNDS: the hub tree of a generalised wheel is a STAR ([wheel_tree n]: a root
    with [n] B-leaves), a legal Def-9.1 datum (generalised_wheel.v §3).  The committed
    [grounding_two_extremal.v] grounds the 2-LEAF [canon_tree]; here we ground the
    [n]-leaf [wheel_tree] family: it has even-B-parity (one colour class of leaves),
    the right edge/leaf count, and is LEGAL.  This is a SECOND independent witness that
    the parity predicate is satisfiable on a non-trivial (star) tree. *)

(** [wheel_tree 3] has exactly 3 edges (committed [pt_edges_wheel]). *)
Lemma wheel_tree3_edges : pt_edges (wheel_tree 3) = 3.
Proof. by rewrite pt_edges_wheel. Qed.

(** [wheel_tree 3] has exactly 3 leaves. *)
Lemma wheel_tree3_nleaves : pt_nleaves (wheel_tree 3) = 3.
Proof. by rewrite pt_nleaves_wheel. Qed.

(** EVEN-B-PARITY of the star [wheel_tree n] for every [n] (committed
    [even_B_parity_wheel]): all leaves share one root-B-parity, so every leaf-to-leaf
    path crosses an even number of B-edges.  We instantiate at [n = 3] (the W₃ hub
    star) and also expose the general-[n] form. *)
Lemma wheel_tree3_even_B_parity : even_B_parity (wheel_tree 3).
Proof. exact: even_B_parity_wheel. Qed.

Lemma wheel_tree_even_B_parity_all n : even_B_parity (wheel_tree n).
Proof. exact: even_B_parity_wheel. Qed.

(** The verbatim Def-9.1 leaf-to-leaf form for the star [wheel_tree 3] (via the proved
    equivalence [even_B_parityP]): every leaf-to-leaf tree path has an EVEN number of
    B-edges. *)
Lemma wheel_tree3_even_B_parity_pairwise :
  even_B_parity_pairwise (wheel_tree 3).
Proof. by rewrite -even_B_parityP; exact: wheel_tree3_even_B_parity. Qed.

(** [wheel_tree 3] is a LEGAL Def-9.1 datum (committed [wheel_tree_legal], [n ≥ 2]):
    so the tree-join generator on the STAR is non-vacuous, not just on [canon_tree]. *)
Lemma wheel_tree3_legal (inH2 : diGraphType -> Prop) :
  is_two_hajos_data inH2 (wheel_tree 3).
Proof. by apply: wheel_tree_legal. Qed.

(** ** §D — the directed Hajós join [dhajos] deletes BOTH original arcs

    GROUNDS: Def 1.5 (two_extremal.v §4) deletes [u v₁] AND [v₂ w], identifies
    [v₁ = v₂], and adds [u w].  The committed [grounding_two_extremal.v] checks the
    added arc [u → w] and the deleted [u v₁].  HERE we ground the SECOND deletion —
    the original arc [v₂ w] of D₂ must be GONE between the merged vertex and [w] — and
    also re-confirm, on the SAME single-arc data, the added arc and a structural
    invariant of the join. *)

Section DhajosBothDeleted.

(** The single-arc digraph on ['I_2]: only [0 --> 1]. *)
Definition g_arc2_rel (x y : 'I_2) : bool := (val x == 0) && (val y == 1).
Definition g_arc2_car : Type := 'I_2.
HB.instance Definition _ := Finite.on g_arc2_car.
HB.instance Definition _ := HasArc.Build g_arc2_car g_arc2_rel.
Definition g_arc2 : diGraphType := g_arc2_car.

Definition a0 : g_arc2 := Ordinal (n := 2) (m := 0) isT.
Definition a1 : g_arc2 := Ordinal (n := 2) (m := 1) isT.

Lemma g_arc2_a0a1 : a0 --> a1. Proof. by []. Qed.

(** The Hajós join of two copies of [g_arc2] along [a0 a1] (in both factors).
    Data: D₁ = D₂ = g_arc2, [u = a0], [v1 = a1], [v2 = a0], [w = a1].  The identified
    vertex is [v1 = v2 = ...]: the carrier deletes [inr v2 = inr a0]; the merged vertex
    is [inl v1 = inl a1]; the added arc is [inl a0 → inr a1]. *)
Definition gJ : diGraphType := dhajos a0 a1 a0 a1.

Lemma gU_pf : (inl a0 : g_arc2 + g_arc2) != inr a0. Proof. by []. Qed.
Lemma gW_pf : (inr a1 : g_arc2 + g_arc2) != inr a0.
Proof. by apply/eqP => E; have : a1 = a0 by case: E. Qed.
Lemma gM_pf : (inl a1 : g_arc2 + g_arc2) != inr a0. Proof. by []. Qed.

(** Source [U] and target [W] of the ADDED arc, and the MERGED vertex [M]. *)
Definition gU : gJ := exist _ (inl a0 : g_arc2 + g_arc2) gU_pf.
Definition gW : gJ := exist _ (inr a1 : g_arc2 + g_arc2) gW_pf.
Definition gM : gJ := exist _ (inl a1 : g_arc2 + g_arc2) gM_pf.

(** Re-confirm the ADDED arc [u w] is present. *)
Lemma gdhajos_added : gU --> gW.
Proof. by []. Qed.

(** THE SECOND DELETION (the new ground): the original arc [v₂ w = a0 a1] of D₂ is
    GONE.  In the carrier, [v₂ = a0] was identified into the merged vertex
    [M = inl a1] (its [inr] copy is deleted), so the arc from the merged vertex
    [M] to [W = inr a1] must NOT be the surviving copy of [v₂ → w]: the [dh_rel]
    branch [inl a == v1] && [arc v2 b] && [~~ (b == w)] is killed by [~~ (b == w)]
    since here [b = a1 = w].  Hence [M --> W] is FALSE — the deleted [v₂ w] is gone. *)
Lemma gdhajos_v2w_deleted : ~~ (gM --> gW).
Proof. by []. Qed.

(** The merged vertex [M = inl v1] still carries D₂'s OTHER out-arcs of [v₂] (rerouted)
    — but [a0] has no out-arc other than [a0 → a1 = w] in [g_arc2], so here the only
    candidate is exactly the deleted one; thus [M] has no [inr]-out-arc at all.  We
    confirm [M] does not point to [W] (already above) and, as a sanity invariant, that
    the added arc's source [U = inl u] is DISTINCT from the merged vertex [M]. *)
Lemma gdhajos_U_ne_M : gU != gM.
Proof. by rewrite /gU /gM -val_eqE /=. Qed.

End DhajosBothDeleted.

(** ** §E — the rim [di_cycle 3]: loopless, Eulerian, digon-free, forest digon graph

    GROUNDS: the rim of a Def-9.1 realisation is a single directed cycle
    ([two_extremal_glue.di_cycle n]).  The committed file proves the general side
    facts; HERE we ground them at the SMALLEST faithful rim [di_cycle 3] (the rim of
    the W₃ / [eleaf_block] base block) — and check the concrete added arc and the
    single-arc (no back-arc) property the rim must have. *)

(** The directed rim arc [0 --> 1] is present. *)
Lemma dicyc3_arc01 :
  (Ordinal (n := 3) (m := 0) isT : di_cycle 3) --> (Ordinal (n := 3) (m := 1) isT).
Proof. by []. Qed.

(** The rim is a SINGLE arc: [1 --> 0] does NOT hold (no back-arc, n ≥ 3).  RED-FLAG
    check: a back-arc would make the rim a digon and break digon-freeness. *)
Lemma dicyc3_no_back :
  ~~ ((Ordinal (n := 3) (m := 1) isT : di_cycle 3) --> (Ordinal (n := 3) (m := 0) isT)).
Proof. by []. Qed.

(** [di_cycle 3] is loopless (committed [di_cycle_loopless], [n ≥ 2]). *)
Lemma dicyc3_loopless : loopless (di_cycle 3).
Proof. by apply: di_cycle_loopless. Qed.

(** [di_cycle 3] is Eulerian (committed [di_cycle_Eulerian]): in = out = 1. *)
Lemma dicyc3_Eulerian : Eulerian (di_cycle 3).
Proof. by apply: di_cycle_Eulerian. Qed.

(** [di_cycle 3] is digon-free (committed [di_cycle_digonfree], [n ≥ 3]). *)
Lemma dicyc3_digonfree :
  forall u v : di_cycle 3, ~~ ((u --> v) && (v --> u)).
Proof. by apply: di_cycle_digonfree. Qed.

(** Hence its digon graph is a FOREST (committed [di_cycle_digonG_forest] via
    [digonfree_forest]) — the rim contributes NO digon edges. *)
Lemma dicyc3_digonG_forest (llD : loopless (di_cycle 3)) :
  is_forest [set: digonG llD].
Proof. by apply: di_cycle_digonG_forest. Qed.

(** The rim base block [eleaf_block] (= [di_cycle 3] anchored at [ord0]) really is the
    rim triangle: loopless, digon-free, Eulerian (committed [eleaf_*] of
    glue_eul_subtype). *)
Lemma eleaf_block_facts :
  [/\ loopless eleaf_block,
      (forall u v : eleaf_block, ~~ ((u --> v) && (v --> u)))
    & Eulerian eleaf_block].
Proof.
split; [exact: eleaf_loopless | exact: eleaf_digonfree | exact: eleaf_Eulerian].
Qed.

(** ** §F — the binary vertex amalgam [vglue]: gluing two single vertices

    GROUNDS: [two_extremal_glue.vglue D1 D2 a b] is the categorical pushout
    identifying [inl a] with [inr b] inside [D1 + D2] (§1).  We exercise it on the
    SMALLEST data: two single-vertex digraphs.  Then [vglue] of two single vertices is
    the expected 2-into-1 amalgam — a ONE-vertex carrier (the two vertices are
    identified).  We check the cardinality collapses from 2 to 1. *)

Section VglueSingletons.

(** The single-vertex (one-point, edgeless) digraph on ['I_1]. *)
Definition pt1_rel (x y : 'I_1) : bool := false.
Definition pt1_car : Type := 'I_1.
HB.instance Definition _ := Finite.on pt1_car.
HB.instance Definition _ := HasArc.Build pt1_car pt1_rel.
Definition pt1 : diGraphType := pt1_car.

Definition o1 : pt1 := Ordinal (n := 1) (m := 0) isT.

(** [pt1] has exactly one vertex. *)
Lemma pt1_card : #|pt1| = 1.
Proof. by rewrite card_ord. Qed.

(** [pt1] is edgeless (loopless, trivially): no arcs at all. *)
Lemma pt1_loopless : loopless pt1.
Proof. by move=> x. Qed.

(** Every vertex of the sum [pt1 + pt1] is either [inl o1] or [inr o1] (each [pt1]
    copy is a singleton). *)
Lemma pt1_sum_cases (x : (pt1 + pt1)%type) :
  x = inl o1 \/ x = inr o1.
Proof.
case: x => [[[|m] hm]|[[|m] hm]] //; [left|right];
  by congr (_ _); apply: val_inj.
Qed.

(** THE GLUE IDENTIFICATION: gluing two single vertices identifies them.  The two
    canonical images [vinj (inl o1)] and [vinj (inr o1)] are EQUAL in the amalgam
    [vglue o1 o1] — exactly the categorical pushout identifying the chosen vertices.
    (Via [eqquotP]: [vequiv o1 o1] relates [inl o1] and [inr o1].) *)
Lemma vglue_singletons_identified :
  vinj (D1:=pt1) (D2:=pt1) o1 o1 (inl o1)
  = vinj (D1:=pt1) (D2:=pt1) o1 o1 (inr o1).
Proof.
apply/eqquotP.
(* [vequiv o1 o1 (inl o1) (inr o1)] = [vrel]; first disjunct [inl o1 == inl o1] *)
by rewrite /vequiv /= /vrel eqxx.
Qed.

(** GLUING two single vertices collapses to ONE vertex: [#|vglue o1 o1| = 1].  The
    disjoint sum [pt1 + pt1] has 2 vertices; the quotient by [vequiv] (which merges
    [inl o1] with [inr o1]) yields a single class.  We show the carrier set is the
    singleton [{vinj (inl o1)}]. *)
Lemma vglue_singletons_card : #|vglue (D1:=pt1) (D2:=pt1) o1 o1| = 1.
Proof.
rewrite -cardsT.
rewrite (_ : [set: vglue (D1:=pt1) (D2:=pt1) o1 o1]
           = [set vinj (D1:=pt1) (D2:=pt1) o1 o1 (inl o1)]); last first.
  apply/setP => z; rewrite !inE.
  apply/idP/eqP => // _.
  (* z = π (repr z); repr z is inl o1 or inr o1; both project to vinj (inl o1) *)
  rewrite -[z](reprK (qT := {eq_quot vequiv o1 o1})).
  case: (pt1_sum_cases (repr (z : {eq_quot vequiv o1 o1}))) => -> //.
  (* goal: π (inr o1) = vinj o1 o1 (inl o1); both are vinj, identified *)
  rewrite -[\pi_({eq_quot vequiv o1 o1}) (inr o1)]/(vinj o1 o1 (inr o1)).
  by rewrite vglue_singletons_identified.
by rewrite cards1.
Qed.

End VglueSingletons.

(** ** §G — non-vacuity of the concrete Conjecture-9.2 instances

    GROUNDS: [conj_9_2_concrete realises] (two_extremal_hajos.v §5) and its
    instantiations [conj_9_2_glued] ([realises_W]) / the wheel realisation
    [realises_gw].  An OPEN biconditional must quantify over a NON-VACUOUS class on
    both sides — else one direction is trivially true (a danger that produced 5 prior
    bugs).  We ground that the H₂ side of each instance is INHABITED by concrete
    objects (the symmetric triangle base AND the wheel / glued assemblies). *)

(** [in_H2_concrete realises_gw] is inhabited on BOTH the base (symmetric triangle)
    and the wheel — so the H₂ side of [conj_9_2_concrete realises_gw] is non-vacuous. *)
Lemma conj_9_2_gw_H2_nonvacuous :
  in_H2_concrete realises_gw (sym_cycle 3)
  /\ in_H2_concrete realises_gw (gwheel 3).
Proof.
split.
- exact: symcyc3_in_H2.
- exact: gwheel_in_H2.
Qed.

(** [in_H2_concrete realises_W] (the [conj_9_2_glued] instance) is inhabited: the
    base symmetric triangle lies in it, and the tree-join generator is non-vacuous
    (committed [is_two_hajos_treejoin_nonvacuous]). *)
Lemma conj_9_2_glued_H2_nonvacuous :
  in_H2_concrete realises_W (sym_cycle 3)
  /\ (exists D : diGraphType,
        is_two_hajos_treejoin (in_H2_concrete realises_W) realises_W D).
Proof.
split.
- exact: symcyc3_in_H2.
- exact: is_two_hajos_treejoin_nonvacuous.
Qed.

(** [in_H2_concrete realises_E] (the degree-unioning [glue_eul_subtype] instance) is
    inhabited via the degree-unioning assembly of [canon_tree] (committed
    [glue_tree_e_in_H2] / [canon_legal]), and on the symmetric base. *)
Lemma conj_9_2_glued_e_H2_nonvacuous :
  in_H2_concrete realises_E (sym_cycle 3)
  /\ in_H2_concrete realises_E (glue_tree_e canon_tree).
Proof.
split.
- exact: symcyc3_in_H2.
- by apply: glue_tree_e_in_H2; exact: canon_legal.
Qed.

(** ** §H — TRIVIALITY / FALSIFICATION probes on [two_extremal] and [conj_9_2]

    RED-FLAG checks: an OPEN conjecture must be NEITHER provable nor refutable, and
    must NOT be vacuous.  We cannot resolve [conj_9_2] (open), but we ground that the
    objects it speaks about are real and that the [two_extremal] side conditions are a
    genuine NON-DEGENERATE conjunction (none collapses to True/False outright). *)

(** [two_extremal] / [k_extremal] is a 4-way conjunction (strong, 2-connected
    underlying, λ = k, χ⃗ = k+1); UNFOLDING it confirms the shape — none of the four
    conjuncts is dropped or made trivial.  We expose the definitional unfolding as a
    faithfulness datum (a mis-encoding that silently dropped a conjunct would fail to
    typecheck against this statement). *)
Lemma two_extremal_is_four_conjuncts (D : diGraphType) (llD : loopless D) :
  two_extremal llD <->
  [/\ strongb D,
      two_connected_sg (underlyingG llD),
      arc_conn D = 2
    & chi_vec_eq D 3].
Proof. by rewrite /two_extremal /k_extremal. Qed.

(** [chi_vec_eq D 3] (the χ⃗ = 3 conjunct of [two_extremal]) is itself a genuine
    conjunction [0 < 3 /\ dicolorableb D 3 /\ ~~ dicolorableb D 2]; the [0 < m] guard
    forbids the degenerate [m = 0] reading.  RED-FLAG check on the χ⃗ encoding. *)
Lemma chi_vec_eq3_shape (D : diGraphType) :
  chi_vec_eq D 3 <->
  [/\ True, dicolorableb D 3 & ~~ dicolorableb D 2].
Proof.
rewrite /chi_vec_eq; split.
- by case=> _ [h2 h3]; split.
- by case=> _ h2 h3; split => //; split.
Qed.

(** The [conj_9_2]-style biconditional, instantiated at the wheel realisation, is a
    GENUINE biconditional over real objects: BOTH the LHS ([two_extremal]) side
    conditions speak of a digraph with [0 < #|D|] (forced, here W₃ has 4 vertices) and
    the RHS ([in_H2]) side is inhabited.  We ground the LHS non-degeneracy: a
    [two_extremal] digraph has a positive number of vertices (so the quantifier is not
    over the empty digraph — the source of two prior vacuously-FALSE bugs). *)
Lemma two_extremal_card_pos (D : diGraphType) (llD : loopless D) :
  two_extremal llD -> (0 < #|D|)%N.
Proof.
case=> _ tc _ _.
by case: tc => h3 _ _; apply: leq_trans h3.
Qed.

(** Sanity: the abstract [conj_9_2] at an EMPTY/trivial [in_H2] is NOT what the file
    states (it would be refutable).  We exhibit the contrapositive datum: if [in_H2]
    were the always-false predicate, then [conj_9_2 in_H2] would FORCE no digraph to be
    two-extremal — but membership [in_H2_concrete] is inhabited, so the faithful
    instance is genuinely non-vacuous.  (We do not assume [conj_9_2]; we only ground
    that the always-false predicate is NOT a faithful [in_H2], since the real one has
    the symmetric triangle.) *)
Lemma faithful_in_H2_nonempty :
  exists D : diGraphType, in_H2_concrete realises_W D.
Proof. by exists (sym_cycle 3); exact: symcyc3_in_H2. Qed.
