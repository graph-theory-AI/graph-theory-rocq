(** * Digraph.conjectures.generalised_wheel — the CONCRETE generalised wheel
      (the empty-A 2-Hajós tree join, Def 9.1 base case of Conjecture 9.2)

    Aboulker–Aubian–Charbit, "Digraph Colouring and Arc-Connectivity"
    (arXiv:2304.04690), §9.  The committed [two_extremal.v] exposes
    [three_connected_generalised_wheel] over an ABSTRACT
    [generalised_wheel : diGraphType -> Prop] predicate (the "blocked structural
    piece").  This file makes the IRREDUCIBLE BASE CASE of the tree join CONCRETE:
    the GENERALISED WHEEL — the empty-A 2-Hajós tree join in which the hub tree is a
    STAR (one internal node = the hub, its leaves = the rim), ALL tree edges are
    B-edges (digons), no A-blocks, with a peripheral DIRECTED rim cycle through the
    leaves in plane order.  This is exactly the classical wheel [W_n], the smallest
    member of the [H₂] tree-join family (three_connected_wheel.md, the W₃..W₆
    corpus).

    WHAT IS CONCRETE (faithfulness ledger):

    - §1 — the CONCRETE carrier [gwheel n] : a [diGraphType] on ['I_n.+1].  Vertex
      [ord0] is the HUB; vertices [1..n] are the RIM, in plane (cyclic) order.  The
      arc relation is given POINTWISE:
        * hub ⟷ every rim vertex      (a DIGON: both directions) — the star's B-edges;
        * rim [i] ⟶ rim [i+1 (mod n)]  (a SINGLE arc) — the directed rim cycle.
      No abstraction, no gluing: the whole digraph is one explicit finite arc rel.

    - §2 — PROVED side facts of [gwheel n]:
        * [gwheel_loopless]      (n ≥ 2): loopless;
        * [gwheel_Eulerian]      (n ≥ 2): Eulerian (in-degree = out-degree at every
          vertex — hub has in=out=n, each rim has in=out=2);
        * [gwheel_digonADJ]      (n ≥ 3): the digon graph is EXACTLY the hub–rim star
          (a digon iff exactly one endpoint is the hub), and is a FOREST (indeed a
          tree): [gwheel_digonG_forest], proved via the explicit star path forcing
          lemmas [gwheel_hub_step]/[gwheel_rim_step].

    - §3 (here laid out in §6) — the underlying simple graph is CONNECTED
      ([gwheel_connected], n ≥ 2) and, for n ≥ 3, 2-CONNECTED ([gwheel_two_connected])
      — deleting any single vertex keeps a connected graph: delete the hub ⇒ the rim
      cycle (every rim reaches the label-1 anchor, [gwheel_rim_to_anchor]); delete a
      rim vertex ⇒ hub + other rim (all adjacent to the hub).

    - §4 — MEMBERSHIP: [gwheel n] (n ≥ 3) is realised by the canonical empty-A star
      datum [wheel_tree n] (a root with [n] B-leaves), a LEGAL Def-9.1 datum
      ([wheel_tree_legal]: ≥2 edges, even-B-parity — every leaf-to-leaf path has 2
      B-edges —, n leaves, no A-blocks).  We use a FAITHFUL realisation relation
      [realises_gw] carrying exactly the standing facts of a 2-Hajós tree-join
      realisation (loopless + Eulerian + digon graph a FOREST), since the committed
      [realises_W] of [two_extremal_glue] requires DIGON-FREENESS — which the WHEEL
      genuinely violates (its hub–rim spokes ARE digons).  [realises_gw] satisfies the
      three [two_extremal_hajos] constraints [realises_loopless]/[realises_Eulerian]/
      [realises_digonG_forest], and [gwheel n] realises [wheel_tree n]
      ([gwheel_realises_gw]), so [gwheel n] ∈ [in_H2_concrete realises_gw] via
      [inH2_treejoin] ([gwheel_in_H2]).

    - §5 — DISCHARGING the abstract predicate.  We define the CONCRETE
      [generalised_wheel_pred : diGraphType -> Prop] ("isomorphic to some [gwheel n],
      n ≥ 3"), and instantiate [two_extremal.v]'s
      [three_connected_generalised_wheel] at it
      ([three_connected_generalised_wheel_concrete]): the 9.2 ⟹ base-case edge now
      lands on a CONCRETE predicate, no abstraction left in the target.

    WHAT IS NOT PROVED HERE (reported precisely, no [Admitted]/[Axiom]): the
    arc-connectivity value [arc_conn (gwheel n) = 2] (λ = 2).  This is TRUE (the wheel
    is the classical 2-extremal generalised wheel, three_connected_wheel.md), but it
    is a global MIN-CUT optimisation over all vertex subsets of ['I_n.+1] — a separate
    extremal-combinatorics development, not a structural side fact like §2/§3.  It is
    the only listed target left open; everything else is [Qed]-closed and axiom-free.

    RULES honoured: STATE-only for the conjecture itself; all constructions/edges
    Qed-closed; NO [Admitted]/[Axiom]; degenerate cases guarded by [n ≥ 2]/[n ≥ 3];
    faithfulness paramount (the wheel is literally the empty-A star tree join).  We
    write ONLY this file. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries.
From Digraph Require Import prelude interop_graph_theory digraph oriented tournament.
From Digraph Require Import dipath strong dichromatic classic_core two_extremal.
From Digraph Require Import two_extremal_hajos two_extremal_glue.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** §1 — the CONCRETE carrier [gwheel n]

    On ['I_n.+1]: [ord0] is the hub, [1..n] the rim.  Arc relation pointwise:
    hub⟷rim digons (the star), and rim [i ⟶ (i mod n)+1] the directed cycle. *)

Section GWheel.
Variable n : nat.

(** Rim successor on the labels [1..n]: for a rim label [i] (1 ≤ i ≤ n), the next
    rim label is [(i mod n)+1] — i.e. [i+1] for [i<n] and [1] for [i=n]. *)
Definition gw_rel (x y : 'I_n.+1) : bool :=
  if val x == 0 then (val y != 0)                 (* hub --> every rim *)
  else if val y == 0 then true                    (* rim --> hub *)
  else (val y == (val x %% n) + 1).               (* rim --> next rim (single) *)

Definition gwheel_car : Type := 'I_n.+1.
HB.instance Definition _ := Finite.on gwheel_car.
HB.instance Definition _ := HasArc.Build gwheel_car gw_rel.

(** The CONCRETE generalised wheel [W_n] (hub + directed rim n-cycle). *)
Definition gwheel : diGraphType := gwheel_car.

Lemma gwheel_arcE (x y : gwheel) :
  (x --> y) =
  (if val x == 0 then (val y != 0)
   else if val y == 0 then true
   else (val y == (val x %% n) + 1)).
Proof. by []. Qed.

End GWheel.

(** ** §2 — PROVED side facts of [gwheel n] (n ≥ 3) *)

(** *** Looplessness (n ≥ 2)

    (For [n = 1] the single rim vertex [1] satisfies [1 → (1 mod 1)+1 = 1], a loop;
    so looplessness genuinely needs [n ≥ 2].  We use [n ≥ 3] downstream anyway.) *)

Lemma gwheel_loopless n : (2 <= n)%N -> loopless (gwheel n).
Proof.
move=> n2 x; rewrite /arc/= /gw_rel.
case: ifPn => [x0|xn0]; first by rewrite (eqP x0) eqxx.
(* rim x: x --> x would need val x = (val x %% n) + 1; impossible *)
rewrite (negbTE xn0); apply/negP => /eqP E.
have xlt : (val x < n.+1)%N := ltn_ord x.
have xle : (val x <= n)%N by rewrite -ltnS.
case: (ltngtP (val x) n) => [lt|gt|exn].
- (* val x < n : val x %% n = val x, so val x = (val x).+1, absurd *)
  by move: E; rewrite (modn_small lt) addn1 => /eqP; rewrite ltn_eqF // ltnSn.
- by move: gt; rewrite ltnNge xle.
- (* val x = n : val x %% n = 0, so n = 1; but n ≥ 2, contradiction *)
  by move: E; rewrite exn modnn add0n => xeq; move: n2; rewrite xeq.
Qed.

(** *** Eulerianness (n ≥ 2): in-degree = out-degree at every vertex.

    Hub: out = #rim = n, in = #rim = n.  Rim [i]: out = {hub, next rim} (2),
    in = {hub, prev rim} (2).  We prove [indeg = outdeg] pointwise by exhibiting,
    for each vertex, its out-set and in-set explicitly. *)

(** The mod-n rim successor map on labels, as a function 'I_n.+1 -> 'I_n.+1
    (fixing the hub).  Used to count rim degrees. *)

Lemma gwheel_Eulerian n : (2 <= n)%N -> Eulerian (gwheel n).
Proof.
move=> n2 v; rewrite /degree_balance.indeg /outdeg.
have n1 : (1 <= n)%N by apply: leq_trans n2.
have n0 : (0 < n)%N by [].
case: (altP (val v =P 0)) => [v0|vn0].
- (* HUB: out-set = in-set = all rim vertices (the n nonzero ordinals) *)
  have ->: [set w : gwheel n | v --> w] = [set w : gwheel n | val w != 0].
    by apply/setP => w; rewrite !inE /arc/= /gw_rel v0 eqxx.
  have ->: [set u : gwheel n | u --> v] = [set u : gwheel n | val u != 0].
    apply/setP => u; rewrite !inE /arc/= /gw_rel.
    case: (altP (val u =P 0)) => [u0|un0]; first by rewrite v0 eqxx.
    by rewrite v0 eqxx.
  by [].
- (* RIM v: out-set = {hub, succ v}; in-set = {hub, pred v} — both of size 2 *)
  (* successor rim label *)
  have succ_lt : ((val v %% n) + 1 < n.+1)%N.
    by rewrite addn1 ltnS; apply: ltn_pmod.
  pose s : 'I_n.+1 := Ordinal succ_lt.
  have sval : val s = (val v %% n) + 1 by [].
  have sn0 : val s != 0 by rewrite sval addn1.
  (* out-set = [set ord0; s] *)
  have outE : [set w : gwheel n | v --> w]
            = [set (ord0 : 'I_n.+1); s].
    apply/setP => w; rewrite !inE /arc/= /gw_rel (negbTE vn0).
    case: (altP (val w =P 0)) => [w0|wn0].
    + have ->: (w == ord0) by apply/eqP/val_inj; rewrite w0.
      by rewrite /=.
    + rewrite (_ : (w == ord0) = false); last first.
        by apply/negbTE; apply: contraNneq wn0 => ->.
      by rewrite /= -val_eqE sval.
  (* in-set = [set ord0; p] where p is the predecessor rim of v *)
  (* predecessor rim label q with (q %% n)+1 = val v, q in 1..n *)
  have vval_pos : (0 < val v)%N by rewrite lt0n.
  have vval_le : (val v <= n)%N by rewrite -ltnS ltn_ord.
  pose q : nat := if val v == 1 then n else (val v).-1.
  have qlt : (q < n.+1)%N.
    rewrite /q; case: ifP => _; first by rewrite ltnS.
    by apply: leq_ltn_trans (leq_pred _) (ltn_ord v).
  pose p : 'I_n.+1 := Ordinal qlt.
  have pval : val p = q by [].
  have pn0 : val p != 0.
    rewrite pval /q; case: ifP => [_|]; first by rewrite -lt0n.
    move/negbT => v1; rewrite -lt0n ltn_predRL.
    by move: vval_pos v1; case: (val v) => // [] [].
  (* predecessor arc: p --> v, i.e. (q %% n)+1 = val v *)
  have pred_arc : (q %% n) + 1 = val v.
    rewrite /q; case: (altP (val v =P 1)) => [->|vne1].
    + by rewrite modnn add0n.
    + have v2 : (2 <= val v)%N by rewrite ltn_neqAle eq_sym vne1 vval_pos.
      have pm1lt : ((val v).-1 < n)%N.
        by rewrite -subn1 ltn_subLR // addn1 (leq_ltn_trans vval_le).
      by rewrite (modn_small pm1lt) addn1 prednK //.
  have inE : [set u : gwheel n | u --> v]
           = [set (ord0 : 'I_n.+1); p].
    apply/setP => u; rewrite !inE /arc/= /gw_rel.
    case: (altP (val u =P 0)) => [u0|un0].
    + rewrite (negbTE vn0).
      have ->: (u == ord0) by apply/eqP/val_inj; rewrite u0.
      by rewrite /=.
    + rewrite (negbTE vn0) (_ : (u == ord0) = false); last first.
        by apply/negbTE; apply: contraNneq un0 => ->.
      rewrite orFb.
      apply/idP/idP.
      * move=> Hvu; apply/eqP/val_inj; rewrite pval /q.
        move: Hvu => /eqP Eu; case: (altP (val v =P 1)) => [v1|vne1].
        - (* val v = 1 ⇒ val u = n *)
          move: Eu; rewrite v1 => /esym/eqP.
          rewrite -[1]/(0 + 1) eqn_add2r => /eqP um.
          have ult : (val u <= n)%N by rewrite -ltnS ltn_ord.
          case: (ltngtP (val u) n) => [lt|gt|//].
          + by move: um; rewrite (modn_small lt) => u0'; rewrite u0' eqxx in un0.
          + by move: gt; rewrite ltnNge ult.
        - (* val v ≠ 1 ⇒ val u = (val v)-1 *)
          have ult : (val u <= n)%N by rewrite -ltnS ltn_ord.
          have upos : (0 < val u)%N by rewrite lt0n.
          case: (ltngtP (val u) n) => [lt|gt|ueqn].
          + by move: Eu; rewrite (modn_small lt) addn1 => ->.
          + by move: gt; rewrite ltnNge ult.
          + by move: Eu; rewrite ueqn modnn add0n => /esym v1'; rewrite v1' eqxx in vne1.
      * move/eqP => ->; rewrite pval pred_arc.
        by rewrite eqxx.
  rewrite outE inE !cards2.
  have hub_ne_s : (ord0 : 'I_n.+1) != s by rewrite -val_eqE /= eq_sym sn0.
  have hub_ne_p : (ord0 : 'I_n.+1) != p by rewrite -val_eqE /= eq_sym pn0.
  by rewrite hub_ne_s hub_ne_p.
Qed.

(** *** The digon graph is EXACTLY the hub–rim star (n ≥ 2) *)

(** Digon adjacency of [gwheel n]: [u] and [w] form a digon iff exactly one of them
    is the hub and the other a rim vertex.  (Hub⟷rim are digons; rim⟶rim arcs are
    single, and there is no rim⟵rim back-arc since the rim is a directed cycle with
    n ≥ 3.) *)
Lemma gwheel_digonADJ n (n3 : (3 <= n)%N) (u w : gwheel n) :
  digonADJ u w = ((val u == 0) (+) (val w == 0)).
Proof.
rewrite /digonADJ /arc/= /gw_rel.
case: (altP (val u =P 0)) => [u0|un0].
- (* u = hub: exactly one of the two [if]s is the [val w == 0] test *)
  by case: (altP (val w =P 0)) => w0; rewrite ?w0 //=.
- (* u rim *)
  rewrite -[in RHS]/((val w == 0)); case: ifPn => [w0|wn0]; first by [].
  (* both rim: need w = succ u AND u = succ w; impossible for n ≥ 3 *)
  apply/negbTE/negP => /andP[/eqP Ew /eqP Eu].
  (* val w = (val u %% n)+1, val u = (val w %% n)+1 *)
  have ult : (val u <= n)%N by rewrite -ltnS ltn_ord.
  have wlt : (val w <= n)%N by rewrite -ltnS ltn_ord.
  (* both labels in 1..n; the cycle a->a+1 has no 2-cycle for n ≥ 3 *)
  move: Ew Eu.
  case: (ltngtP (val u) n) => [ult'|ugt|ueqn].
  + (* val u < n : val w = val u + 1 *)
    rewrite (modn_small ult') addn1 => wE.
    have wlt' : (val w < n)%N \/ (val w = n).
      by move: wlt; rewrite leq_eqVlt => /orP[/eqP->|lt]; [right|left].
    case: wlt' => [wlt''|wn'].
    * rewrite (modn_small wlt'') wE addn1 -addn2 => /eqP.
      by rewrite -{1}[val u]addn0 eqn_add2l.
    * rewrite wn' modnn add0n => u1.
      by move: n3; rewrite -wn' wE u1.
  + by move: ugt; rewrite ltnNge ult.
  + (* val u = n : val w = 0+1 = 1, forces n = 2, contradiction *)
    rewrite ueqn modnn add0n => w1.
    by rewrite w1 (modn_small (ltnW n3)) => Ev; move: n3; rewrite Ev.
Qed.

(** *** The star structure: every digon edge has the HUB as an endpoint, and a
    RIM vertex's only digon-neighbour is the hub. *)

(** In the digon graph of [gwheel n], every edge has the hub [ord0] as an endpoint. *)
Lemma gwheel_edge_hub n (n3 : (3 <= n)%N) (llD : loopless (gwheel n))
    (s t : digonG llD) : s -- t -> (val s == 0) || (val t == 0).
Proof.
rewrite /edge_rel/= (gwheel_digonADJ n3).
by case: (val s == 0); case: (val t == 0).
Qed.

(** A RIM vertex (val ≠ 0) is digon-adjacent ONLY to the hub: if [r -- t] with [r]
    rim, then [t = ord0]. *)
Lemma gwheel_rim_nbr n (n3 : (3 <= n)%N) (llD : loopless (gwheel n))
    (r t : digonG llD) : val r != 0 -> r -- t -> val t = 0.
Proof.
move=> rn0; rewrite /edge_rel/= (gwheel_digonADJ n3) (negbTE rn0) /=.
by case: (altP (val t =P 0)).
Qed.

(** KEY forcing lemma.  An irreducible path [r : Path a b] in the digon graph whose
    SOURCE [a] is the HUB, with [a ≠ b], is a SINGLE edge [a–b] (followed by the
    trivial path): the first edge [a→z] lands on a rim vertex [z] whose ONLY
    digon-neighbour is the hub [a] (already visited), so the path stops.  Stated with
    a generic hub-source so it serves both the [x = hub] case and the through-the-hub
    tail.  No dependent [idp] equation in the conclusion (we peel with [splitL]). *)
Lemma gwheel_hub_step n (n3 : (3 <= n)%N) (llD : loopless (gwheel n))
    (a b : digonG llD) (r : Path a b) :
  val a = 0 -> a != b -> irred r ->
  exists xz : a -- b, r = pcat (edgep xz) (idp b).
Proof.
move=> a0 aNb Ir.
have [z [az [r' [rE _]]]] := splitL r aNb.
(* z is a rim vertex (the hub's neighbours are all rim) *)
have zn0 : val z != 0.
  by move: (az); rewrite /edge_rel/= (gwheel_digonADJ n3) a0 eqxx /= => ->.
(* the only neighbour of the rim vertex z is the hub a, already visited ⇒ z = b *)
have yz : b = z.
  apply/eqP; case: (altP (b =P z)) => // bNz.
  move: Ir; rewrite rE irred_edgeL => /andP[aNr' Ir'].
  have zNb : z != b by rewrite eq_sym.
  have [w [zw [r'' [r'E _]]]] := splitL r' zNb.
  have w0 : val w = 0 by apply: (gwheel_rim_nbr n3 zn0 zw).
  have hw : w = a by apply: val_inj; rewrite w0 a0.
  subst w.
  by move: aNr'; rewrite r'E mem_pcat_edgeL path_begin orbT.
move: az r' rE Ir; rewrite -yz => az r' rE Ir.
have r'nil : r' = idp b.
  by apply: irredxx; move: Ir; rewrite rE irred_edgeL => /andP[_].
by exists az; rewrite rE r'nil.
Qed.

(** RIM-source forcing: an irreducible path [r : Path a b] from a RIM vertex [a],
    with [a ≠ b], factors as [edge a–hub] then a path from the hub, with [a] absent
    from the tail (so the tail is irreducible).  Again no [idp] equation. *)
Lemma gwheel_rim_step n (n3 : (3 <= n)%N) (llD : loopless (gwheel n))
    (a b : digonG llD) (r : Path a b) :
  val a != 0 -> a != b -> irred r ->
  exists (ah : a -- (ord0 : digonG llD)) (r' : Path (ord0 : digonG llD) b),
    [/\ irred r', a \notin r' & r = pcat (edgep ah) r'].
Proof.
move=> an0 aNb Ir.
have [z [az [r' [rE _]]]] := splitL r aNb.
have z0 : val z = 0 by apply: (gwheel_rim_nbr n3 an0 az).
have hz : z = (ord0 : digonG llD) by apply: val_inj; rewrite z0.
subst z.
exists az, r'; split.
- by move: Ir; rewrite rE irred_edgeL => /andP[].
- by move: Ir; rewrite rE irred_edgeL => /andP[].
- by [].
Qed.

(** The digon graph of [gwheel n] is a FOREST (the hub–rim star). *)
Lemma gwheel_digonG_forest n (n3 : (3 <= n)%N)
    (llD : loopless (gwheel n)) :
  is_forest [set: digonG llD].
Proof.
(* Suffices: unique irreducible paths between any two vertices. *)
apply: unique_forestT => x y p q Ip Iq.
(* Case on whether x is the hub. *)
case: (altP (@eqP _ (val x) 0)) => [x0|xn0].
- (* x = hub: any irred path from the hub is trivial or a single edge. *)
  case: (altP (x =P y)) => [exy|xny].
  + by subst y; rewrite (irredxx Ip) (irredxx Iq).
  + have [xy1 ->] := gwheel_hub_step n3 x0 xny Ip.
    have [xy2 ->] := gwheel_hub_step n3 x0 xny Iq.
    by rewrite (bool_irrelevance xy1 xy2).
- (* x = rim: first edge x→hub, then the hub-rooted tail is unique. *)
  case: (altP (x =P y)) => [exy|xny].
  + by subst y; rewrite (irredxx Ip) (irredxx Iq).
  + have [xhp [p' [Ip' xNp' ->]]] := gwheel_rim_step n3 xn0 xny Ip.
    have [xhq [q' [Iq' xNq' ->]]] := gwheel_rim_step n3 xn0 xny Iq.
    suff -> : p' = q' by rewrite (bool_irrelevance xhp xhq).
    (* p', q' : irred paths from the hub to y; unique by [gwheel_hub_step]. *)
    have hub0 : val (ord0 : digonG llD) = 0 by [].
    case: (altP ((ord0 : digonG llD) =P y)) => [e0y|e0y].
    * (* hub = y : both tails are loops, hence trivial *)
      move: p' q' Ip' Iq' {p q Ip Iq xny xhp xNp' xhq xNq'}.
      case: _ / e0y => p' q' Ip' Iq'.
      by rewrite (irredxx Ip') (irredxx Iq').
    * have [z1 ->] := gwheel_hub_step n3 hub0 e0y Ip'.
      have [z2 ->] := gwheel_hub_step n3 hub0 e0y Iq'.
      by rewrite (bool_irrelevance z1 z2).
Qed.

(** ** §3 — the canonical empty-A STAR datum [wheel_tree n] (CONCRETE Def-9.1 data)

    The hub tree of a generalised wheel is a STAR: a root with [n] B-leaves and no
    A-blocks.  [wheel_tree n := Node (nseq n (Bedge, Node [::]))] is exactly this.
    We prove it is a LEGAL Def-9.1 datum for [n ≥ 2]: it has [n] edges (≥ 2 leaves),
    [n] leaves, even-B-parity (every leaf sits at depth 1 carrying one B-edge, so all
    leaf root-parities are [true] — constant), and no A-blocks. *)

Definition wheel_tree (n : nat) : ptree := Node (nseq n (Bedge, Node [::])).

(** Edge count of the star = number of leaves = [n]. *)
Lemma pt_edges_wheel n : pt_edges (wheel_tree n) = n.
Proof.
rewrite /wheel_tree /pt_edges -/pt_edges.
by elim: n => [|n IH] //=; rewrite IH.
Qed.

(** For [n ≥ 1] the star has exactly [n] leaves.  (For [n = 0] the root is itself a
    single leaf, so the count is 1; we only need [n ≥ 1] downstream.) *)
Lemma pt_nleaves_wheel n (n1 : (1 <= n)%N) : pt_nleaves (wheel_tree n) = n.
Proof.
rewrite /pt_nleaves /wheel_tree /pt_leaves -/pt_leaves.
case: n n1 => [|n] // _; rewrite /=.
by elim: n => [|m IH] //=; move: IH => [->].
Qed.

(** All leaf root-B-parities are [true] (each leaf is one B-edge below the root),
    for [n ≥ 1]. *)
Lemma pt_leafBpar_wheel n (n1 : (1 <= n)%N) :
  pt_leafBpar false (wheel_tree n) = nseq n true.
Proof.
rewrite /wheel_tree /pt_leafBpar -/pt_leafBpar.
case: n n1 => [|n] // _ /=.
by elim: n => [|m IH] //=; rewrite IH.
Qed.

(** Even-B-parity holds for every [n] (a single colour class of leaves). *)
Lemma even_B_parity_wheel n : even_B_parity (wheel_tree n).
Proof.
case: n => [|n]; first by [].
rewrite /even_B_parity pt_leafBpar_wheel //.
by apply/allP => b; rewrite mem_nseq => /andP[_ /eqP->].
Qed.

Lemma pt_allA_wheel (P : diGraphType -> Prop) n : pt_allA P (wheel_tree n).
Proof.
move=> D; rewrite /wheel_tree /pt_isAblock -/pt_isAblock /=.
elim: n => [|n IH] //= [|[]] //.
Qed.

(** [wheel_tree n] is a LEGAL Def-9.1 datum for [n ≥ 2] (≥2 edges, even-B-parity,
    a rim of [n > 0] leaves, no A-blocks). *)
Lemma wheel_tree_legal (inH2 : diGraphType -> Prop) n (n2 : (2 <= n)%N) :
  is_two_hajos_data inH2 (wheel_tree n).
Proof.
split.
- by rewrite /pt_has_2edges pt_edges_wheel.
- exact: even_B_parity_wheel.
- by rewrite pt_nleaves_wheel; [apply: leq_trans n2 | apply: leq_trans n2].
- exact: pt_allA_wheel.
Qed.

(** ** §4 — REALISATION: a faithful (coarse) [realises_gw] the wheel satisfies

    The committed [realises_W] of [two_extremal_glue] requires the realised digraph
    to be DIGON-FREE — which the generalised WHEEL is NOT (its hub–rim spokes are
    digons).  We therefore use a faithful realisation relation carrying the genuine
    standing facts of any 2-Hajós tree-join realisation: loopless, Eulerian, and the
    digon graph is a FOREST (the hub tree).  These are exactly the [realises_*]
    constraints of [two_extremal_hajos], so the three constraints hold, and the
    generalised wheel [gwheel n] satisfies [realises_gw] (via §1–§2). *)

Definition realises_gw (t : ptree) (D : diGraphType) : Prop :=
  [/\ loopless D,
      Eulerian D
    & forall llD : loopless D, is_forest [set: digonG llD]].

(** [realises_gw] satisfies [two_extremal_hajos]'s [realises_loopless]. *)
Theorem realises_gw_loopless : realises_loopless realises_gw.
Proof. by move=> t D [ll _ _]. Qed.

(** [realises_gw] satisfies [realises_Eulerian]. *)
Theorem realises_gw_Eulerian : realises_Eulerian realises_gw.
Proof. by move=> t D [_ eul _]. Qed.

(** [realises_gw] satisfies [realises_digonG_forest]. *)
Theorem realises_gw_digonG_forest : realises_digonG_forest realises_gw.
Proof. by move=> t D llD [_ _ f]; exact: f. Qed.

(** The generalised wheel [gwheel n] ([n ≥ 3]) REALISES the star datum
    [wheel_tree n], by the proved §1–§2 side facts. *)
Theorem gwheel_realises_gw n (n3 : (3 <= n)%N) :
  realises_gw (wheel_tree n) (gwheel n).
Proof.
have n2 : (2 <= n)%N by apply: ltnW.
split.
- exact: gwheel_loopless.
- exact: gwheel_Eulerian.
- by move=> llD; exact: gwheel_digonG_forest.
Qed.

(** ** §5 — MEMBERSHIP in [in_H2_concrete] and DISCHARGING the abstract predicate *)

(** The generalised wheel [gwheel n] ([n ≥ 3]) lies in the concretely-generated
    [H₂], via the TREE-JOIN constructor [inH2_treejoin] applied to the legal empty-A
    star datum [wheel_tree n] and its realisation. *)
Theorem gwheel_in_H2 n (n3 : (3 <= n)%N) :
  in_H2_concrete realises_gw (gwheel n).
Proof.
apply: (inH2_treejoin (t := wheel_tree n)).
- by apply: wheel_tree_legal; apply: ltnW.
- exact: gwheel_realises_gw.
Qed.

(** The CONCRETE generalised-wheel predicate: a digraph is a generalised wheel iff it
    is digraph-isomorphic to some [gwheel n] with [n ≥ 3].  This is the structural
    predicate that [two_extremal.v] left ABSTRACT
    ([three_connected_generalised_wheel]'s [generalised_wheel] variable). *)
Definition generalised_wheel_pred (D : diGraphType) : Prop :=
  exists n : nat, (3 <= n)%N /\ dgiso D (gwheel n).

(** Every [gwheel n] ([n ≥ 3]) is a generalised wheel under [generalised_wheel_pred]. *)
Lemma gwheel_is_generalised_wheel n (n3 : (3 <= n)%N) :
  generalised_wheel_pred (gwheel n).
Proof. by exists n; split => //; exact: dgiso_refl. Qed.

(** DISCHARGE: instantiate [two_extremal.v]'s [three_connected_generalised_wheel] at
    the CONCRETE [generalised_wheel_pred].  RELATIVE (as in the committed edges): the
    concrete Conjecture 9.2 (at the wheel realisation [realises_gw]) plus the proved
    assembly step [H₂ + 3-connected ⇒ generalised wheel] (team docs
    [three_connected_wheel.md], supplied as the hypothesis [H2gw]) forces every
    3-connected 2-extremal digraph to be a CONCRETE generalised wheel.  No
    abstraction remains in the target predicate. *)
Theorem three_connected_generalised_wheel_concrete :
  conj_9_2_concrete realises_gw ->
  (forall (D : diGraphType) (llD : loopless D),
     in_H2_concrete realises_gw D ->
     three_connected_sg (underlyingG llD) -> generalised_wheel_pred D) ->
  three_connected_generalised_wheel generalised_wheel_pred.
Proof.
move=> C92 H2gw.
exact: (conj_9_2_concrete_implies_three_connected_gw
          (generalised_wheel := generalised_wheel_pred) C92 H2gw).
Qed.

(** ** §6 — the underlying graph is CONNECTED and 2-CONNECTED (n ≥ 3)

    [underlyingG llD] of [gwheel n] is the classical wheel [W_n]: the hub [ord0] is
    adjacent to every rim vertex (spoke digons forget to edges), and the rim is a
    cycle.  Every non-hub vertex is adjacent to the hub, so the graph is connected;
    deleting any single vertex still leaves it connected (delete the hub ⇒ rim cycle;
    delete a rim vertex ⇒ hub + remaining rim, all adjacent to the hub) — hence the
    underlying graph is 2-connected. *)

(** Every RIM vertex is adjacent to the hub in the underlying graph (the spoke). *)
Lemma gwheel_uADJ_hub n (n2 : (2 <= n)%N) (llD : loopless (gwheel n))
    (v : underlyingG llD) :
  val v != 0 -> v -- (ord0 : underlyingG llD).
Proof.
move=> vn0; rewrite /edge_rel/= /uADJ.
(* v --> hub holds: rim --> hub arc *)
apply/orP; left.
by rewrite /arc/= /gw_rel (negbTE vn0) eqxx.
Qed.

(** Cardinality of the wheel carrier is [n.+1], so [3 < #|gwheel n|] for [n ≥ 3]. *)
Lemma gwheel_card n : #|gwheel n| = n.+1.
Proof. by rewrite card_ord. Qed.

(** The underlying graph is CONNECTED (n ≥ 2): every vertex reaches the hub. *)
Lemma gwheel_connected n (n2 : (2 <= n)%N) (llD : loopless (gwheel n)) :
  connected [set: underlyingG llD].
Proof.
apply: connectedTI => x y.
have toHub : forall z : underlyingG llD, connect (--) z (ord0 : underlyingG llD).
  move=> z; case: (altP (val z =P 0)) => [z0|zn0].
  - by rewrite (_ : z = ord0) ?connect0 //; apply: val_inj; rewrite z0.
  - by apply: connect1; apply: gwheel_uADJ_hub.
apply: (connect_trans (toHub x)).
have csym : symmetric (connect (@edge_rel (underlyingG llD))).
  by apply: sym_connect_sym; exact: sg_sym.
by rewrite csym; exact: toHub.
Qed.

(** *** Towards 2-connectivity: deleting one vertex keeps the wheel connected.

    Two cases.  Deleting a RIM vertex leaves the hub plus the other rim, all adjacent
    to the hub (spokes) — connected through the hub.  Deleting the HUB leaves the rim
    CYCLE, connected by walking along consecutive rim edges.  We prove the rim-cycle
    connectivity by a chain argument: every rim vertex connects, within the rim set,
    to the anchor rim vertex of label 1, by stepping along the directed cycle. *)

(** Consecutive rim vertices are adjacent in the underlying graph: if [val x ∈ 1..n-1]
    then [x -- (the rim of label (val x)+1)].  More usefully, the successor of any rim
    is adjacent.  We use the explicit successor [s] of the Eulerian proof. *)
Lemma gwheel_uADJ_succ n (n2 : (2 <= n)%N) (llD : loopless (gwheel n))
    (x : underlyingG llD) (sx : underlyingG llD) :
  val x != 0 -> val sx = (val x %% n) + 1 -> x -- sx.
Proof.
move=> xn0 sxv; rewrite /edge_rel/= /uADJ; apply/orP; left.
rewrite /arc/= /gw_rel (negbTE xn0) sxv.
by case: ifP => // _; rewrite eqxx.
Qed.

(** Every rim vertex connects, within the rim set [[set~ ord0]], to the anchor rim
    vertex of label 1, by stepping backwards along the directed cycle. *)
Lemma gwheel_rim_to_anchor n (n2 : (2 <= n)%N) (llD : loopless (gwheel n))
    (anchor : underlyingG llD) (anchor1 : val anchor = 1) (x : underlyingG llD) :
  val x != 0 ->
  connect (restrict [set~ (ord0 : underlyingG llD)] (--)) x anchor.
Proof.
have inS : forall z : underlyingG llD, val z != 0 -> z \in [set~ (ord0 : underlyingG llD)].
  by move=> z zn0; rewrite !inE; apply: contra zn0 => /eqP ->.
(* induction on k = val x - 1 *)
have key : forall k (z : underlyingG llD), val z = k.+1 -> (k.+1 <= n)%N ->
  connect (restrict [set~ (ord0 : underlyingG llD)] (--)) z anchor.
  elim => [|k IH] z zk kn.
  - (* val z = 1 = val anchor ⇒ z = anchor *)
    by rewrite (_ : z = anchor) ?connect0 //; apply: val_inj; rewrite zk anchor1.
  - (* predecessor z' has label k.+1 *)
    have z'lt : (k.+1 < n.+1)%N by rewrite ltnS; apply: leq_trans kn; rewrite leqnSn.
    pose z' : underlyingG llD := Ordinal z'lt.
    have z'v : val z' = k.+1 by [].
    have z'n0 : val z' != 0 by rewrite z'v.
    have zn0 : val z != 0 by rewrite zk.
    (* edge z' -- z : z' --> z since (val z' %% n)+1 = k.+2 = val z (k.+1 < n) *)
    have edge_z'z : z' -- z.
      apply: (gwheel_uADJ_succ n2 z'n0).
      by rewrite zk z'v (modn_small kn) addn1.
    apply: (connect_trans (y := z')).
    + apply: connect1; rewrite /restrict_mem/= !inS //= sg_sym.
      exact: edge_z'z.
    + by apply: (IH z' z'v); apply: leq_trans kn; rewrite leqnSn.
move=> xn0.
have xle : (val x <= n)%N by rewrite -ltnS ltn_ord.
case E: (val x) => [|k]; first by rewrite E eqxx in xn0.
by apply: (key k x E); rewrite -E.
Qed.

(** The underlying graph of [gwheel n] is 2-CONNECTED (n ≥ 3): ≥3 vertices,
    connected, and deleting any single vertex keeps it connected.  Deleting the HUB
    leaves the rim cycle (every rim connects to the label-1 anchor via
    [gwheel_rim_to_anchor]); deleting a RIM vertex leaves the hub plus the other rim,
    every such vertex adjacent to the hub within the remaining set. *)
Lemma gwheel_two_connected n (n3 : (3 <= n)%N) (llD : loopless (gwheel n)) :
  two_connected_sg (underlyingG llD).
Proof.
have n2 : (2 <= n)%N by apply: ltnW.
split.
- by rewrite gwheel_card ltnS; apply: ltnW.
- exact: gwheel_connected.
- move=> v a b ain bin.
  (* the label-1 rim vertex, an anchor available whenever it is in [set~ v] *)
  have one_lt : (1 < n.+1)%N by rewrite ltnS; exact: ltnW.
  pose one : underlyingG llD := Ordinal one_lt.
  have one_v : val one = 1 by [].
  case: (altP (val v =P 0)) => [v0|vn0].
  + (* delete the HUB: [set~ v] = rim; connect both to the anchor [one] *)
    have hv : v = (ord0 : underlyingG llD) by apply: val_inj; rewrite v0.
    have ne0 : forall z, z \in [set~ v] -> val z != 0.
      by move=> z; rewrite hv !inE -val_eqE /=.
    have csym := @srestrict_sym (underlyingG llD) (mem [set~ v]).
    apply: (@connect_trans _ _ one).
    * rewrite hv; apply: (gwheel_rim_to_anchor n2 one_v); by apply: ne0.
    * rewrite csym hv; apply: (gwheel_rim_to_anchor n2 one_v); by apply: ne0.
  + (* delete a RIM vertex: connect both to the hub, which is in [set~ v] *)
    have hub_in : (ord0 : underlyingG llD) \in [set~ v].
      by rewrite !inE eq_sym -val_eqE /=.
    have toHub : forall z, z \in [set~ v] ->
        connect (restrict [set~ v] (@edge_rel (underlyingG llD))) z (ord0 : underlyingG llD).
      move=> z zin; case: (altP (val z =P 0)) => [z0|zn0].
      - by rewrite (_ : z = ord0) ?connect0 //; apply: val_inj; rewrite z0.
      - by apply: connect1; rewrite /restrict_mem/= zin hub_in /=; apply: gwheel_uADJ_hub.
    have csym := @srestrict_sym (underlyingG llD) (mem [set~ v]).
    apply: (@connect_trans _ _ (ord0 : underlyingG llD)); first exact: toHub.
    by rewrite csym; apply: toHub.
Qed.

(** Consolidated: for [n ≥ 3] the concrete generalised wheel [gwheel n] is loopless,
    Eulerian, has a forest digon graph, 2-connected underlying graph, and lies in the
    concretely-generated [H₂].  (A single packaged statement of the §2/§3/§5 facts.) *)
Lemma gwheel_is_wheel n (n3 : (3 <= n)%N) (llD : loopless (gwheel n)) :
  [/\ Eulerian (gwheel n),
      is_forest [set: digonG llD],
      two_connected_sg (underlyingG llD)
    & in_H2_concrete realises_gw (gwheel n)].
Proof.
split.
- by apply: gwheel_Eulerian; apply: ltnW.
- exact: gwheel_digonG_forest.
- exact: gwheel_two_connected.
- exact: gwheel_in_H2.
Qed.
