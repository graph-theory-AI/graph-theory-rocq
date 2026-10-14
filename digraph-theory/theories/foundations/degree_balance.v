(** * Digraph.foundations.degree_balance — in-degree and balanced digraphs (library migration B16)

    [indeg v] is the in-degree [#|[set u | u --> v]|] of a vertex of a finite digraph, the
    companion of [Digraph.core.oriented.outdeg]; [balanced D] states that every vertex has equal
    in- and out-degree, [forall v, indeg v = outdeg v], and [balancedb D] is its Boolean form
    (registry meta/library_primitives/degree-balance.json).  This is the "Eulerian" condition of
    the corpus's directed rows, kept as degree balance alone: no connectivity, looplessness,
    inhabited-carrier or closed-tour premise enters it.  A loop adds one to both degrees of its
    vertex, so loops preserve balance; a balanced digraph may be disconnected (its components are
    balanced); the empty digraph and arcless digraphs are balanced.  The undirected multigraph
    "Eulerian" of Cycle U6 (connected, all arc-end degrees even) is a different contract.

    Upstream audit (2026-10-03; MathComp 2.5.0, coq-graph-theory 0.9.7, Digraph core).
    coq-graph-theory has no in/out-degree of a finite digraph; the Digraph core has [outdeg]
    ([core/oriented.v]) but no in-degree outside conjecture files ([classic_core.indeg] over
    [Nin], and two file-local copies), and no balance predicate.  [converse] ([core/digraph.v])
    swaps the two degrees.

    Specification, every clause proved below:
    - [indeg] is the cardinality of the in-neighbourhood, and swaps with [outdeg] on the
      [converse] digraph; the degree sums agree ([sum_indeg_outdeg], the handshake);
    - [balancedP] reflects [balancedb] into [balanced]; [balanced_revE] is the reversed-equation
      view [forall v, outdeg v = indeg v];
    - balance is invariant under [converse], holds on arcless digraphs, and is a per-vertex
      condition ([balanced_vertex]);
    - grounding: the empty digraph, an arcless vertex, a vertex with a loop (balanced: the loop
      counts on both sides), the directed triangle [C3], a disconnected balanced digraph (two
      disjoint loops), the directed 2-cycle (a digon), and the single arc [TT 2], which is NOT
      balanced; no connectivity or looplessness guard is assumed anywhere. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra.
From Digraph Require Import prelude digraph oriented tournament.
From Digraph.foundations Require Import neighbourhoods.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Section DegreeBalance.
Variable D : diGraphType.
Implicit Types (u v w : D).

(** The in-degree: the number of in-neighbours. *)
Definition indeg v : nat := #|[set u | u --> v]|.

(** Every vertex has equal in- and out-degree, as a proposition ... *)
Definition balanced : Prop := forall v, indeg v = outdeg v.

(** ... and as a Boolean. *)
Definition balancedb : bool := [forall v, indeg v == outdeg v].

Lemma balancedP : reflect balanced balancedb.
Proof. by apply: (iffP forallP) => h v; apply/eqP/h. Qed.

(** The reversed equation [outdeg v = indeg v]. *)
Lemma balanced_revE : (forall v, outdeg v = indeg v) <-> balanced.
Proof. by split=> h v; rewrite h. Qed.

Lemma balanced_vertex v : balanced -> indeg v = outdeg v.
Proof. exact. Qed.

Lemma indeg_sumE v : indeg v = \sum_(u | u --> v) 1.
Proof. by rewrite /indeg -sum1_card; apply: eq_bigl => u; rewrite inE. Qed.

Lemma outdeg_sumE v : outdeg v = \sum_(w | v --> w) 1.
Proof. by rewrite /outdeg -sum1_card; apply: eq_bigl => w; rewrite inE. Qed.

(** The handshake: the in-degrees and the out-degrees have the same sum, the number of arcs. *)
Lemma sum_indeg_outdeg : \sum_(v : D) indeg v = \sum_(v : D) outdeg v.
Proof.
rewrite (eq_bigr _ (fun v _ => indeg_sumE v)) (eq_bigr _ (fun v _ => outdeg_sumE v)).
under eq_bigr => v _ do rewrite big_mkcond.
under [in RHS]eq_bigr => v _ do rewrite big_mkcond.
by rewrite exchange_big.
Qed.

(** An arcless digraph is balanced. *)
Lemma balanced_arcless : (forall u v, ~~ (u --> v)) -> balanced.
Proof.
move=> none v; rewrite /indeg /outdeg.
by rewrite (eq_card0 (A := [set u | u --> v])) ?(eq_card0 (A := [set w | v --> w])) // => x;
  rewrite inE (negbTE (none _ _)).
Qed.

End DegreeBalance.

(** ** The converse digraph swaps the two degrees *)

Lemma indeg_converse (D : diGraphType) (v : D) : @indeg (converse D) v = outdeg v.
Proof. by []. Qed.

Lemma outdeg_converse (D : diGraphType) (v : D) : @outdeg (converse D) v = indeg v.
Proof. by []. Qed.

Lemma balanced_converse (D : diGraphType) : balanced (converse D) <-> balanced D.
Proof. by split=> h v; move: (h v); rewrite indeg_converse outdeg_converse => ->. Qed.

(** ** Neighbourhood bridges and diregularity (family directed-neighbourhood)

    The two canonical degrees are the cardinalities of the public neighbourhoods of
    [Digraph.foundations.neighbourhoods], by conversion.  [diregular d] is the Boolean "out-degree
    and in-degree are both [d] at every vertex", with the conjunct order of its conjecture-local
    source ([outdeg] first).  It is vacuous on the empty carrier for every [d] ([diregular_card0]);
    a loop counts once on each side, so a vertex with a loop and no other arc is 1-diregular; an
    arcless digraph is 0-diregular ([diregular_arcless]); a diregular digraph is balanced
    ([diregular_balanced]); the converse digraph has the same diregularity ([diregular_converse]). *)

Section Diregular.
Variable D : diGraphType.
Implicit Types (v w : D).

Lemma indeg_NinE v : indeg v = #|Nin v|.
Proof. by []. Qed.

Lemma outdeg_NoutE v : outdeg v = #|Nout v|.
Proof. by []. Qed.

(** Diregular of degree [d]: every vertex has in-degree and out-degree exactly [d].  (The binder is
    ascribed [D]: here both degrees are generalized constants, so nothing else fixes its type.) *)
Definition diregular (d : nat) : bool := [forall v : D, (outdeg v == d) && (indeg v == d)].

Lemma diregularP d : reflect (forall v, outdeg v = d /\ indeg v = d) (diregular d).
Proof.
apply: (iffP forallP) => h v; first by case/andP: (h v) => /eqP-> /eqP->.
by case: (h v) => -> ->; rewrite !eqxx.
Qed.

Lemma diregular_vertex d v : diregular d -> outdeg v = d /\ indeg v = d.
Proof. by move/diregularP. Qed.

Lemma diregular_balanced d : diregular d -> balanced D.
Proof. by move/diregularP=> h v; case: (h v) => -> ->. Qed.

(** Vacuous on the empty carrier, for every degree. *)
Lemma diregular_card0 d : #|D| = 0 -> diregular d.
Proof. by move=> D0; apply/forallP=> v; move: (max_card (pred1 v)); rewrite D0 card1. Qed.

Lemma diregular_arcless : (forall u w : D, ~~ (u --> w)) -> diregular 0.
Proof.
move=> none; apply/diregularP=> v.
by rewrite indeg_NinE outdeg_NoutE (arcless_Nout none) (arcless_Nin none) cards0.
Qed.

End Diregular.

Lemma diregular_converse (D : diGraphType) d : diregular (converse D) d = diregular D d.
Proof.
apply/diregularP/diregularP=> h v; have [o i] := h v.
  by split; [move: i; rewrite indeg_converse | move: o; rewrite outdeg_converse].
by split; [rewrite outdeg_converse | rewrite indeg_converse].
Qed.

(** ** Tournaments: [N_out]/[N_in] are the general neighbourhoods, and the degrees add up to [#|T| - 1] *)

Section TournamentDegrees.
Variable T : tournament.
Implicit Types (u : T).

Lemma tournament_N_outE u : N_out u = Nout u.
Proof. by []. Qed.

Lemma tournament_N_inE u : N_in u = Nin u.
Proof. by []. Qed.

Lemma tournament_outdegE u : outdeg u = #|N_out u|.
Proof. by []. Qed.

Lemma tournament_indegE u : indeg u = #|N_in u|.
Proof. by []. Qed.

Lemma tournament_indeg_outdeg u : indeg u + outdeg u = #|T|.-1.
Proof.
have [part dis] := N_out_in_partition u.
rewrite -(cardsC1 u) part cardsU (disjoint_setI0 dis) cards0 subn0 addnC.
by rewrite tournament_indegE tournament_outdegE.
Qed.

End TournamentDegrees.

(** ** Grounding *)
Section DegreeBalanceGrounding.

(** The empty digraph. *)
Definition empty_dg : Type := 'I_0.
HB.instance Definition _ := Finite.on empty_dg.
HB.instance Definition _ := HasArc.Build empty_dg (fun _ _ : 'I_0 => false).

Lemma balanced_ground_empty : balanced empty_dg.
Proof. by move=> v; have := ltn_ord v; rewrite ltn0. Qed.

(** An arcless vertex is balanced (degrees 0 and 0). *)
Definition arcless1 : Type := 'I_1.
HB.instance Definition _ := Finite.on arcless1.
HB.instance Definition _ := HasArc.Build arcless1 (fun _ _ : 'I_1 => false).

Lemma balanced_ground_arcless : balanced arcless1.
Proof. by apply: balanced_arcless. Qed.

(** A vertex with a loop is balanced: the loop counts once on each side (no looplessness). *)
Definition loop1 : Type := 'I_1.
HB.instance Definition _ := Finite.on loop1.
HB.instance Definition _ := HasArc.Build loop1 (fun _ _ : 'I_1 => true).

Lemma balanced_ground_loop : balanced loop1 /\ forall v : loop1, indeg v = 1.
Proof.
have arcE : forall u w : loop1, (u --> w) = true by [].
have d1 : forall v : loop1, indeg v = 1.
  by move=> v; rewrite /indeg (eq_card1 (x := v)) // => u; rewrite inE arcE (ord1 u) (ord1 v).
split=> [v|//]; rewrite d1 /outdeg.
by rewrite (eq_card1 (x := v)) // => u; rewrite inE arcE (ord1 u) (ord1 v).
Qed.

(** Two disjoint loops: balanced but disconnected (no connectivity). *)
Definition twoloops : Type := 'I_2.
HB.instance Definition _ := Finite.on twoloops.
HB.instance Definition _ := HasArc.Build twoloops (fun u v : 'I_2 => u == v).

Lemma balanced_ground_disconnected :
  balanced twoloops /\ ~~ ((ord0 : twoloops) --> ord_max).
Proof.
have arcE : forall u w : twoloops, (u --> w) = (u == w) by [].
split=> // v; rewrite /indeg /outdeg; apply: eq_card => u.
by rewrite !inE !arcE eq_sym.
Qed.

(** The directed 2-cycle (a digon) and the directed triangle [C3] are balanced. *)
Definition digon : Type := 'I_2.
HB.instance Definition _ := Finite.on digon.
HB.instance Definition _ := HasArc.Build digon (fun u v : 'I_2 => u != v).

Lemma balanced_ground_digon : balanced digon.
Proof.
have arcE : forall u w : digon, (u --> w) = (u != w) by [].
by move=> v; rewrite /indeg /outdeg; apply: eq_card => u; rewrite !inE !arcE eq_sym.
Qed.

Lemma balanced_ground_C3 : balanced C3.
Proof.
move=> v; rewrite /indeg /outdeg.
have -> : [set u | u --> v] = [set (v - 1)%R].
  apply/setP => u; rewrite !inE arcC3E.
  by apply/idP/idP => /eqP H; apply/eqP; rewrite H ?addrK ?subrK.
have -> : [set w | v --> w] = [set (v + 1)%R].
  by apply/setP => w; rewrite !inE arcC3E.
by rewrite !cards1.
Qed.

(** The single arc [TT 2] (0 -> 1) is NOT balanced: vertex 0 has out-degree 1 and in-degree 0. *)
Lemma not_balanced_ground_TT2 : ~ balanced (TT 2).
Proof.
move/(_ ord0); rewrite /indeg /outdeg.
rewrite (eq_card0 (A := [set u : TT 2 | u --> ord0])) => [|u]; last by rewrite inE arcTTE ltn0.
rewrite (eq_card1 (x := (ord_max : TT 2))) // => w; rewrite inE arcTTE /=.
by case: w => -[|[|//]] lt.
Qed.

End DegreeBalanceGrounding.
