(** * Digraph.conjectures.grounding_chi_col — STATEMENT-LEVEL grounding for
    chi_bounded.v and colouring_variants.v.

    This file EXTENDS the pass-1 grounding (grounding_tww_chi_col.v) from the
    DEFINITION level to the STATEMENT level, emphasising the three faithfulness
    axes the assignment calls for:

      (1) NON-VACUITY: every conjecture _statement quantifies over a hypothesis
          class; we exhibit a CONCRETE digraph satisfying each antecedent
          (oriented_dg, oriented_star, P4_underlying, underlying_triangle_free,
          chordal_C3) — a forall over an empty class says nothing.

      (2) SMALL-INSTANCE WITNESSES / VALUES on tiny digraphs (C3, TT 2 = single
          arc, TT 3): a single arc is 2-oriented-colourable; a directed path
          (TT 2) admits a majority colouring; a tiny oriented graph is
          triangle-free; the acyclic number is ≥ 1.

      (3) TRIVIALITY / FALSIFICATION probes on the chi-bounded wrappers: a
          BOUNDED-ORDER class IS χ-bounded (the wrapper is satisfiable), the
          EMPTY class is vacuously χ-bounded, and the chordal class genuinely
          separates objects (C3 in, TT 3 out) — so the OPEN conjecture wrappers
          are neither trivially provable nor trivially refutable.

    Unlike pass 1 (which re-stated the definitions locally), this file IMPORTS
    the COMMITTED conjecture modules chi_bounded and colouring_variants directly,
    so it grounds the EXACT _statement Props. It imports ONLY committed modules.
    No Admitted / Axiom: every lemma is Qed. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra.
From Digraph Require Import prelude interop_graph_theory digraph oriented tournament dipath.
From Digraph Require Import dichromatic heroes chi_bounded colouring_variants.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory.

(** ==================================================================== *)
(** ** A. NON-VACUITY of the chi_bounded.v conjecture ANTECEDENTS

    Each Forb-χ-bounded conjecture is [forall H, antecedent H -> ...].  We must
    show the antecedent class is inhabited, else the statement is vacuous. *)

(** *** A.1  [oriented_dg] (antecedent of conj2_1605_statement) is inhabited. *)

Lemma oriented_dg_C3 : oriented_dg C3.
Proof. by move=> u v uv; rewrite (arc_asymm _ _ uv). Qed.

(** A directed single arc TT 2 is oriented as well — the smallest non-trivial
    oriented graph (it is the directed path P₂). *)
Lemma oriented_dg_TT2 : oriented_dg (TT 2).
Proof. by move=> u v uv; rewrite (arc_asymm _ _ uv). Qed.

(** The antecedent of Conjecture 2 is genuinely inhabited (there exists an
    oriented [H]). *)
Lemma conj2_antecedent_inhabited : exists H : diGraphType, oriented_dg H.
Proof. by exists (C3 : diGraphType); exact: oriented_dg_C3. Qed.

(** *** A.2  [oriented_star]: orientations of K_{1,t} are inhabited.

    C3 is NOT a star (its three vertices are pairwise adjacent), but a single
    arc TT 2 IS the orientation of K_{1,1} = a one-leaf star: centre 0, leaf 1,
    the (unique) leaf condition is vacuous. *)
Lemma oriented_star_TT2 : oriented_star (TT 2).
Proof.
split; first exact: oriented_dg_TT2.
exists (Ordinal (isT : (0 < 2)%N)); split.
- (* the centre 0 is underlying-adjacent to every other vertex *)
  move=> v vne0; rewrite /urel eq_sym vne0 /=.
  (* v != 0 in 'I_2 forces v = 1, and 0 --> 1 *)
  apply/orP; left; rewrite arcTTE.
  by case: v vne0 => -[|[|//]] ?.
- (* the only non-centre vertex in 'I_2 is 1, so u != c and v != c force
     u = v = 1, contradicting u != v *)
  move=> u v; case: u => -[|[|//]] ?; case: v => -[|[|//]] ? //=;
    by rewrite eqxx //=; case/negP.
Qed.

Lemma conj4_antecedent_inhabited : exists S : diGraphType, oriented_star S.
Proof. by exists (TT 2 : diGraphType); exact: oriented_star_TT2. Qed.

(** *** A.3  [P4_underlying]: orientations of P₄ are inhabited.

    TT 4 (the transitive tournament on 4 vertices) is NOT a P₄ (it has chords),
    so we build the directed path 0→1→2→3 honestly: it is the orientation [→P₄]
    whose underlying graph is exactly the path.  We realise it as the digraph on
    'I_4 with arcs exactly the consecutive pairs {(0,1),(1,2),(2,3)}.  Rather
    than instance a fresh digraph (heavy), we exhibit the WITNESS structure of
    [is_dirP4] over a hand-built path digraph below (A.3').  For pure
    non-vacuity at the [P4_underlying] level it suffices to note the directed P₄
    exists; we construct it next. *)

(** A 4-vertex digraph whose arcs are exactly the consecutive forward pairs of
    0–1–2–3: the all-forward orientation of P₄. *)
Definition dP4 : Type := 'I_4.
HB.instance Definition _ := Finite.on dP4.
HB.instance Definition _ :=
  HasArc.Build dP4 [rel u v : 'I_4 | val v == (val u).+1].

Lemma dP4_arcE (u v : dP4) : (u --> v) = (val v == (val u).+1).
Proof. by []. Qed.

Lemma oriented_dg_dP4 : oriented_dg (dP4 : diGraphType).
Proof.
move=> u v; rewrite !dP4_arcE => /eqP vu.
apply/negP=> /eqP uv; move: vu; rewrite uv.
by move/eqP; rewrite -[X in X == _]addn0 -[(val v).+1.+1]addn2 eqn_add2l.
Qed.

(** Underlying adjacency of dP4 is exactly "consecutive": u ~ v iff |u−v| = 1. *)
Lemma dP4_urel (u v : dP4) :
  @urel dP4 u v = ((val v == (val u).+1) || (val u == (val v).+1)).
Proof.
rewrite /urel !dP4_arcE.
case: (boolP ((val v == (val u).+1) || (val u == (val v).+1))) => [H|H];
  last by rewrite andbF.
rewrite andbT; apply/negP=> /eqP eqv; move: H; rewrite eqv orbb.
by rewrite (ltn_eqF (ltnSn _)).
Qed.

(** dP4 is the directed P₄ [→P₄]: it realises [is_dirP4] (hence [P4_underlying],
    the antecedent class of Conjecture 5, is inhabited). *)
Lemma is_dirP4_dP4 : is_dirP4 dP4.
Proof.
pose a : dP4 := Ordinal (isT : (0 < 4)%N).
pose b : dP4 := Ordinal (isT : (1 < 4)%N).
pose c : dP4 := Ordinal (isT : (2 < 4)%N).
pose d : dP4 := Ordinal (isT : (3 < 4)%N).
split.
- split; first exact: oriented_dg_dP4.
  exists a, b, c, d; split.
  + split.
    * by [].
    * by move=> x; rewrite !inE -val_eqE /=; case: x => -[|[|[|[|//]]]] ?.
    * by rewrite dP4_urel.
    * by rewrite dP4_urel.
    * by rewrite dP4_urel.
  + split; first by rewrite dP4_urel.
    split; by rewrite dP4_urel.
- exists a, b, c, d; split.
  + by [].
  + by move=> x; rewrite !inE -val_eqE /=; case: x => -[|[|[|[|//]]]] ?.
  + by rewrite dP4_arcE.
  + by rewrite dP4_arcE.
  + by rewrite dP4_arcE.
Qed.

Lemma conj5_antecedent_inhabited :
  exists P : diGraphType, P4_underlying P.
Proof. by exists (dP4 : diGraphType); case: is_dirP4_dP4. Qed.

(** ==================================================================== *)
(** ** B. NON-VACUITY of the chordal class C₃ (arXiv:2202.01006)

    C3 is the canonical allowed member; TT 3 is excluded (induced TT₃).  This is
    the key check that [chordal_not_dichromatic_bounded_statement] ranges over a
    NON-EMPTY, PROPER class. *)

Lemma C3_no_induced_TT3 : no_induced_TT3 C3.
Proof.
move=> [a [b [c [ab bc ac _ _]]]].
move: ab bc ac; rewrite !arcC3E => /eqP-> /eqP->.
rewrite -[X in _ == X]GRing.addr0.
by move/eqP/GRing.addrI/eqP.
Qed.

Lemma C3_no_long_dicycle : ~ has_induced_long_dicycle C3.
Proof.
move=> [c [c4 [/and3P[_ _ uc] _]]].
have szle : (size c <= #|{: C3}|)%N by rewrite -(card_uniqP uc); exact: max_card.
by move: (leq_trans c4 szle); rewrite card_C3.
Qed.

Lemma chordal_C3_C3 : chordal_C3 C3.
Proof. by split; [exact: oriented_dg_C3 | exact: C3_no_induced_TT3 | exact: C3_no_long_dicycle]. Qed.

Lemma chordal_class_inhabited : exists D : diGraphType, chordal_C3 D.
Proof. by exists (C3 : diGraphType); exact: chordal_C3_C3. Qed.

(** RED-FLAG probe (the class is PROPER, not "everything"): TT 3 has an induced
    transitive triangle, so it is NOT in the chordal class.  Hence the class
    separates objects and the non-χ-boundedness statement is not vacuously about
    a full/empty class. *)
Lemma TT3_has_induced_TT3 : ~ no_induced_TT3 (TT 3).
Proof.
move=> H; apply: H.
exists (Ordinal (isT : (0 < 3)%N)), (Ordinal (isT : (1 < 3)%N)),
       (Ordinal (isT : (2 < 3)%N)).
by split; rewrite ?arcTTE //; split; rewrite arcTTE.
Qed.

Lemma chordal_C3_not_TT3 : ~ chordal_C3 (TT 3).
Proof. by move=> [_ H _]; apply: TT3_has_induced_TT3. Qed.

(** ==================================================================== *)
(** ** C. NON-VACUITY + small values for the ORIENTED-TRIANGLE-FREE cores

    The a⃗ / t⃗ / m(3) statements (arXiv:2403.02298) range over oriented graphs
    whose UNDERLYING graph is triangle-free.  This class is inhabited by every
    small graph; we exhibit TT 2 (a single arc) and prove the easy a⃗ ≥ 1 value. *)

(** *** C.1  [underlying_triangle_free] is inhabited (TT 2: 2 vertices < 3). *)
Lemma underlying_triangle_free_TT2 : underlying_triangle_free (TT 2).
Proof.
move=> [S [cardS _]].
have h : (#|S| <= #|{: underlying (TT 2)}|)%N by exact: max_card.
(* svertex (underlying (TT 2)) is the finType 'I_2, of cardinality 2 *)
by move: h; rewrite cardS card_ord.
Qed.

(** TT 2 is also oriented and nonempty: it satisfies the FULL antecedent of the
    a⃗ / t⃗ cores [0 < #|D| /\ oriented_dg D /\ underlying_triangle_free D]. *)
Lemma avec_antecedent_TT2 :
  (0 < #|{: TT 2}|)%N /\ oriented_dg (TT 2) /\ underlying_triangle_free (TT 2).
Proof.
split; first by rewrite card_TT.
by split; [exact: oriented_dg_TT2 | exact: underlying_triangle_free_TT2].
Qed.

(** *** C.2  Easy value: every nonempty digraph has acyclic number ≥ 1.

    A single vertex induces an arc-free (hence acyclic) subdigraph.  This is the
    smallest concrete value the [acyclic_number_ge] predicate must yield, and
    grounds the a⃗-core's binding lower bound [g] being ≥ 1 on nonempty inputs. *)
Lemma acyclic_number_ge1 (D : diGraphType) (v0 : D) :
  oriented_dg D -> acyclic_number_ge D 1.
Proof.
move=> orD; rewrite /acyclic_number_ge /has_acyclic_set; apply/existsP.
exists [set v0]; rewrite cards1 leqnn /=.
apply/forallP=> x; apply/forallP=> w; apply/implyP.
(* the induced singleton {v0} has no arc: x = w = v0 and an oriented D has no
   loop, so [val x --> val w] would be a loop v0 --> v0, impossible. *)
have ex : val x = v0 by apply/eqP; move: (valP x); rewrite in_set1.
have ew : val w = v0 by apply/eqP; move: (valP w); rewrite in_set1.
rewrite sub_arcE ex ew => xw0.
by move: (orD _ _ xw0); rewrite xw0.
Qed.

(** ==================================================================== *)
(** ** D. ORIENTED CHROMATIC NUMBER on a single arc (colouring_variants.v)

    A single arc is 2-oriented-colourable: TT 2 maps homomorphically onto a
    2-vertex tournament (itself).  This is the smallest non-vacuous value of
    [oriented_kcolouring] / [ochi_le]. *)

Lemma oriented_kcolouring_TT2 : oriented_kcolouring (TT 2) 2.
Proof. by exists (TT 2 : tournament); split; [exact: card_TT | exact: dhom_id]. Qed.

Lemma ochi_le_TT2 : ochi_le (TT 2) 2.
Proof. exact: oriented_kcolouring_TT2. Qed.

(** C3 has an oriented 3-colouring (onto itself). *)
Lemma oriented_kcolouring_C3 : oriented_kcolouring C3 3.
Proof. by exists (C3 : tournament); split; [exact: card_C3 | exact: dhom_id]. Qed.

(** ==================================================================== *)
(** ** E. MAJORITY COLOURING of a tiny digraph (colouring_variants.v)

    A directed path TT 2 (single arc 0→1) admits a majority colouring: colour
    each vertex its own colour (identity 'I_2).  Then no out-neighbour shares
    its source's colour, so the same-colour out-neighbourhood is empty
    everywhere.  This grounds [majority_col] being satisfiable (Conj 2's
    existential head holds on the path). *)

Definition tt2col (v : TT 2) : 'I_2 := v.

Lemma tt2col_same_empty (v : TT 2) : same_col_outnb tt2col v = set0.
Proof.
apply/setP=> w; rewrite inE in_set0.
apply/andP=> -[vw]; rewrite /tt2col => /eqP wv.
by move: vw; rewrite wv arcxx.
Qed.

Lemma majority_col_TT2 : majority_col tt2col.
Proof. by apply/forallP=> v; rewrite tt2col_same_empty cards0 muln0. Qed.

(** Conj 2's existential head [exists col, majority_col col] holds on TT 2. *)
Lemma majority_3col_TT2 : exists col : (TT 2) -> 'I_3, majority_col col.
Proof.
(* lift the 2-colouring into 'I_3 via the canonical 'I_2 -> 'I_3 widening *)
pose col := fun v : TT 2 => widen_ord (isT : (2 <= 3)%N) (tt2col v).
have hempty : forall v : TT 2, same_col_outnb col v = set0.
  move=> v; apply/setP=> w; rewrite inE in_set0.
  apply/andP=> -[vw]; rewrite /col -val_eqE /= /tt2col => /eqP eqval.
  have wv : w = v by apply: val_inj.
  by move: vw; rewrite wv arcxx.
exists col; apply/forallP=> v.
by rewrite hempty cards0 muln0.
Qed.

(** RED-FLAG probe: [majority_col] is NOT vacuously satisfied by ALL colourings.
    The CONSTANT colouring of C3 fails it (each vertex's single out-neighbour
    shares its colour: 2·1 = 2 > 1 = outdeg).  So the existential in Conj 2 has
    real content. *)
Definition c3const (_ : C3) : 'I_3 := ord0.

Lemma c3_outdeg1 (v : C3) : outdeg v = 1%N.
Proof.
rewrite /outdeg.
have -> : [set w | v --> w] = [set (v + 1)%R].
  by apply/setP=> w; rewrite !inE arcC3E.
by rewrite cards1.
Qed.

Lemma c3const_same (v : C3) : same_col_outnb c3const v = [set (v + 1)%R].
Proof. by apply/setP=> w; rewrite !inE arcC3E; case: (w == (v + 1)%R). Qed.

Lemma not_majority_col_c3const : ~~ majority_col c3const.
Proof.
apply/forallPn; exists ord0.
by rewrite c3const_same cards1 c3_outdeg1 muln1.
Qed.

(** ==================================================================== *)
(** ** F. TRIVIALITY probes on the χ-bounded WRAPPER (chi_bounded.v)

    A faithfully-stated OPEN conjecture wrapper must be NEITHER trivially
    provable nor trivially refutable.  We pin the wrapper's behaviour at the two
    degenerate poles:

    (F.1) the EMPTY class is vacuously χ-bounded — expected (says nothing);
    (F.2) any BOUNDED-ORDER class is χ-bounded (constant binding function) —
          so [chi_bounded_under] is genuinely SATISFIABLE.

    Together they show the wrapper is non-degenerate: its content is precisely
    UNBOUNDED classes (which the conjectures address), confirming no encoding
    accident makes the open statements provable/refutable for free. *)

(** (F.1) the empty class is χ-bounded. *)
Lemma chi_bounded_empty : chi_bounded_under (fun _ => False).
Proof. by exists (fun _ => 0)%N => G []. Qed.

(** (F.2) Any class of digraphs of order at most [N] is χ-bounded by the
    constant function [N]: χ(underlying G) ≤ #|underlying G| = #|G| ≤ N. *)
Lemma chi_bounded_bounded_order (N : nat) :
  chi_bounded_under (fun G => (#|G| <= N)%N).
Proof.
exists (fun _ => N) => G [leGN _].
apply: (leq_trans (leq_chi _)).
(* #|[set: underlying G]| = #|underlying G| = #|G| <= N (same carrier finType) *)
by rewrite cardsT.
Qed.

(** Consequently the wrapper is inhabited by a SINGLE-graph class as well: the
    class "is C3" (encoded as "order ≤ 3") is χ-bounded — a sanity instance the
    open conjectures' content (infinite/unbounded families) sits ABOVE. *)
Lemma chi_bounded_singleton_like : chi_bounded_under (fun G => (#|G| <= 3)%N).
Proof. exact: chi_bounded_bounded_order 3. Qed.

(** ==================================================================== *)
(** ** G. The m(3) relative edge is a genuine THEOREM, not the open statement.

    [m3_landmark_refutes_2bound] (proved in chi_bounded.v) is a proof-relative
    consequence: IF the m(3) witness exists THEN the class is not 2-bounded.  We
    re-expose it here to confirm it is a clean implication (no Admit), and record
    that [m3_landmark_statement] itself is NOT proved here (it needs a concrete
    7+-vertex non-2-dicolourable triangle-free witness — correctly hard, NOT a
    red flag). *)
Lemma m3_edge_is_theorem :
  m3_landmark_statement ->
  ~ (forall D : diGraphType,
        (0 < #|D|)%N -> oriented_dg D -> underlying_triangle_free D -> dicolorableb D 2).
Proof. exact: m3_landmark_refutes_2bound. Qed.

(** ==================================================================== *)
(** ** H. The [eulerian] antecedent (colouring_variants.v) discriminates.

    [majority_3col_eulerian_statement] quantifies over Eulerian digraphs
    ([indeg v = outdeg v] everywhere). We ground the antecedent both ways:
    the directed triangle C3 IS Eulerian (a genuine, non-degenerate 3-vertex
    member, unlike the 1-vertex TT 1), while the single arc TT 2 is NOT — so the
    guard has teeth. *)

(** C3 is Eulerian: every vertex has in-degree = out-degree = 1. *)
Lemma eulerian_C3 : eulerian C3.
Proof. by apply/degree_balance.balancedP; exact: degree_balance.balanced_ground_C3. Qed.

(** RED-FLAG teeth: the single arc TT 2 (0 -> 1) is NOT Eulerian — vertex 0 has
    out-degree 1 but in-degree 0. *)
Lemma not_eulerian_TT2 : ~~ eulerian (TT 2).
Proof. by apply/negP => /degree_balance.balancedP; exact: degree_balance.not_balanced_ground_TT2. Qed.

(** ==================================================================== *)
(** ** I. [acyclic_number_ge] teeth (chi_bounded.v, avec_core "attained" clause).

    The edgeless digraph [Edg n] on [n] vertices has acyclic number exactly [n]
    (all of V is arc-free, hence acyclic) but NO acyclic set of size [n+1] — no set
    can exceed the [n] vertices. So [acyclic_number_ge] genuinely FAILS on a real
    order-[n] object, giving the "attained" clause [~ acyclic_number_ge D (g n).+1]
    teeth (without it, [g := 1] would satisfy the lower bound vacuously). *)

Definition Edg (n : nat) : Type := 'I_n.
Section EdgInst.
Variable n : nat.
HB.instance Definition _ := Finite.on (Edg n).
HB.instance Definition _ := HasArc.Build (Edg n) [rel u v : 'I_n | false].
End EdgInst.

Lemma Edg_card (n : nat) : #|{: Edg n}| = n.
Proof. by rewrite /Edg card_ord. Qed.

Lemma not_acyclic_number_ge_Edg_succ (n : nat) : ~ acyclic_number_ge (Edg n) n.+1.
Proof.
rewrite /acyclic_number_ge /has_acyclic_set => /existsP[S /andP[hc _]].
have hle : (#|S| <= #|{: Edg n}|)%N := max_card (mem S).
move: hle; rewrite Edg_card => hle.
by move: (leq_trans hc hle); rewrite leqNgt ltnSn.
Qed.
