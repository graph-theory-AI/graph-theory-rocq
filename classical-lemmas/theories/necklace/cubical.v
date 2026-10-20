(** * ClassicalLemmas.cubical — the cubical chain complex of the star power R^N

    Stage B foundation for the necklace formalisation (Meunier 2014, §2–3).

    [R] is the star with centre [o] and [p] paths of length [n]; a cell of one
    factor ([cell1]) is either a vertex [Vtx v] ([v : cut = option ('I_n*'I_p)],
    [None] = o) or an edge [Edg k r] (the edge of path [r] with top endpoint
    [Some (k,r)] and bottom endpoint [slide (Some (k,r))]).  A cell of [R^N] is
    a finitely-supported assignment [cellN := {ffun 'I_N -> cell1}]; its
    dimension is the number of edge-coordinates.

    Chains are [{ffun cellN -> R^o}] (via [ClassicalLemmas.chains]).  The
    cubical boundary [bd] orients coordinates by their natural order:

      bd (c) = \sum_{j : c j = edge} (-1)^{rank j} (top-face_j c - bot-face_j c)

    where [rank j] counts the edge-coordinates before [j].  The main result is
    [bd_bd : bd (bd x) = 0], proved by the coordinate-pair cancellation that is
    valid over any ring (no division by 2). *)

(** ** Provenance, sources, and what corresponds to what

    HOW THIS FILE WAS OBTAINED.  It was written with Claude Code (Anthropic),
    driving Rocq interactively through the rocq-mcp-evolve MCP server ("build"
    to list the open goals of a file, "open"/"step"/"try"/"check" to drive a
    single proof), so that a failing tactic was diagnosed on the spot instead
    of by recompiling.  rocq-mcp-evolve is developed by the LLM4Rocq project,
    https://github.com/LLM4Rocq/rocq-mcp-evolve (Apache-2.0; the opam package
    still carries its former slug LLM4Rocq/rocq-tools); it is gratefully
    acknowledged here.  Every error that recurred, together with the tactic
    that fixed it, is recorded in tactics-playbook.md at the root of the
    repository.  No result is admitted: "Print Assumptions" on the results of
    this file answers "Closed under the global context".

    MODELS AND ESTIMATED TOKEN COST FOR THIS FILE.

        Claude Opus 4.8     267k tokens   (09-15 04:31 -> 09-15 05:25 UTC)
        Claude Opus 5         5k tokens   (09-15 08:30 UTC)
        TOTAL               272k tokens   of which 108k were output

      Method: the figures are estimated from the logs of the Claude Code
      session of 14-15 September 2026.  For every assistant message they count
      input + cache-creation + output tokens, i.e. the tokens processed anew,
      excluding the cached conversation that is re-read at each turn (772M
      over the project); a message is charged to the file its tool calls were
      acting on.  Three whole-session context rebuilds (compaction or resume),
      1.61M tokens in all, are charged to no file.  Project totals: 4.10M
      tokens of per-file work, 1.61M of context rebuilds, 5.70M overall.

    SOURCES.

      [M14]  F. Meunier, "Simplotopal maps and necklace splitting",
             Discrete Mathematics 323 (2014) 14-26.
             Local copy: classical-lemmas/Meunier2014-Simplotopal_Necklace_web.pdf

    WHAT CORRESPONDS TO WHAT.

      The chain complex of the cube R^N, i.e. [M14, Sect. 2.1-2.3] specialised
      to simplotopes all of whose factors are a vertex or an edge.

      - [M14, Sect. 2.1], a simplotope sigma_1 x ... x sigma_m and its
        dimension
                                    -> cell1 (a vertex or an edge of R),
                                       cellN, dimN
      - [M14, Sect. 2.2-2.3], the orientation and the boundary operator,
        oriented by the order of the factors
                                    -> fv (faces), rk, edgeterm, bd1, bd
      - [M14, Lemma 2.2], "d o d = 0", for the cubical complex R^N
                                    -> bd_bd
        The proof here is a diagonal-pairing argument (sum_pair_anti,
        Tterm_anti) that is valid over any commutative ring, characteristic 2
        included, rather than the sign cancellation of [M14]. *)

From mathcomp Require Import all_boot all_algebra.
From ClassicalLemmas Require Import necklace.chains.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Section Cubical.
Variables (n p : nat).

Definition cut := option ('I_n * 'I_p).
Definition slide (x : cut) : cut :=
  if x is Some (k, r) then
    (if k == 0 :> nat then None
     else Some (Ordinal (leq_ltn_trans (leq_pred k) (ltn_ord k)), r))
  else None.

Definition cell1 := (cut + ('I_n * 'I_p))%type.
Definition Vtx (v : cut) : cell1 := inl v.
Definition Edg (kr : 'I_n * 'I_p) : cell1 := inr kr.
Definition is_edge (x : cell1) : bool := if x is inr _ then true else false.
Definition etop (kr : 'I_n * 'I_p) : cut := Some kr.
Definition ebot (kr : 'I_n * 'I_p) : cut := slide (Some kr).

Variable N : nat.
Definition cellN := {ffun 'I_N -> cell1}.

Definition dimN (c : cellN) : nat := #|[set j | is_edge (c j)]|.

(** Set coordinate [j] to the vertex [v]. *)
Definition fv (c : cellN) (j : 'I_N) (v : cut) : cellN :=
  [ffun i => if i == j then Vtx v else c i].

Definition rk (c : cellN) (j : 'I_N) : nat :=
  #|[set i : 'I_N | is_edge (c i) && (val i < val j)%N]|.

Section Ring.
Variable R : comNzRingType.

Definition edgeterm (c : cellN) (j : 'I_N) : {ffun cellN -> R^o} :=
  if c j is inr kr then
    (-1) ^+ (rk c j) *: (cc (fv c j (etop kr)) - cc (fv c j (ebot kr)))
  else 0.

Definition bd1 (c : cellN) : {ffun cellN -> R^o} := \sum_(j : 'I_N) edgeterm c j.
Definition bd : {ffun cellN -> R^o} -> {ffun cellN -> R^o} := lin bd1.

Lemma bdD x y : bd (x + y) = bd x + bd y. Proof. exact: linD. Qed.
Lemma bdZ a x : bd (a *: x) = a *: bd x. Proof. exact: linZ. Qed.
Lemma bd_cc c : bd (cc c) = bd1 c. Proof. exact: lin_cc. Qed.

(** ** Face calculus *)

Lemma fvE c j v i : fv c j v i = if i == j then Vtx v else c i.
Proof. by rewrite ffunE. Qed.

Lemma fv_same c j v : fv c j v j = Vtx v.
Proof. by rewrite fvE eqxx. Qed.

Lemma fv_id c j v w : fv (fv c j v) j w = fv c j w.
Proof. by apply/ffunP => i; rewrite !fvE; case: eqP. Qed.

Lemma fvC c j v k w : j != k -> fv (fv c j v) k w = fv (fv c k w) j v.
Proof.
move=> jk; apply/ffunP => i; rewrite !fvE.
case: (eqVneq i k) => [->|_]; last by [].
by rewrite eq_sym (negbTE jk).
Qed.

Lemma is_edge_fv c j v i : is_edge (fv c j v i) = (i != j) && is_edge (c i).
Proof. by rewrite fvE; case: eqP. Qed.

Lemma edgeterm_novtx (c : cellN) j : ~~ is_edge (c j) -> edgeterm c j = 0 :> {ffun cellN -> R^o}.
Proof. by rewrite /edgeterm; case: (c j). Qed.

(** The rank of a coordinate [i] after coordinate [j] has been turned into a
    vertex: unchanged if [i] precedes [j], drops by one otherwise. *)
Lemma rk_fv (c : cellN) j v i : i != j -> is_edge (c j) ->
  rk (fv c j v) i = (rk c i - (val j < val i))%N.
Proof.
move=> ij ej; rewrite /rk.
have hset : [set i0 | is_edge (fv c j v i0) & (val i0 < val i)%N]
          = [set i0 in [set k | is_edge (c k) & (val k < val i)%N] | i0 != j].
  apply/setP => k; rewrite !inE is_edge_fv.
  by case: (is_edge (c k)); case: (val k < val i)%N; case: (k != j).
rewrite hset [in RHS](cardsD1 j) inE ej /=.
rewrite (cardsD1 j [set i0 in _ | i0 != j]) inE inE eqxx andbF add0n.
rewrite addKn.
apply: eq_card => k; rewrite !inE.
by case: (eqVneq k j) => [->|_]; rewrite ?andbF ?andbT.
Qed.

(** top/bottom vertices of a cell coordinate (dummy on vertex coordinates). *)
Definition tc (x : cell1) : cut := if x is inr kr then Some kr else None.
Definition bc (x : cell1) : cut := if x is inr kr then slide (Some kr) else None.

(** The four doubly-faced cells at distinct coordinates [j], [i]. *)
Definition quad (c : cellN) (j i : 'I_N) : {ffun cellN -> R^o} :=
  cc (fv (fv c j (tc (c j))) i (tc (c i)))
  - cc (fv (fv c j (tc (c j))) i (bc (c i)))
  - cc (fv (fv c j (bc (c j))) i (tc (c i)))
  + cc (fv (fv c j (bc (c j))) i (bc (c i))).

Definition coefT (c : cellN) (j i : 'I_N) : R :=
  (-1) ^+ (rk c j) * (-1) ^+ (rk c i - (val j < val i)).

Definition Tterm (c : cellN) (j i : 'I_N) : {ffun cellN -> R^o} :=
  if [&& is_edge (c j), is_edge (c i) & i != j]
  then coefT c j i *: quad c j i else 0.

(** Abstract antisymmetric-pairing lemma (valid over any ring, no /2). *)
Lemma sum_pair_anti (M : zmodType) (F : 'I_N -> 'I_N -> M) :
  (forall i, F i i = 0) -> (forall i j, F i j = - F j i) ->
  \sum_(j : 'I_N) \sum_(i : 'I_N) F j i = 0.
Proof.
move=> Fdiag Fanti.
rewrite pair_big /=.
rewrite (bigID (fun q : 'I_N * 'I_N => (val q.2 < val q.1)%N)) /=.
rewrite [X in _ + X](reindex_inj (h := fun q : 'I_N * 'I_N => (q.2, q.1)));
  first [by move=> [a b] [a' b'] [] -> -> | idtac].
rewrite [X in _ + X](eq_bigr (fun j : 'I_N*'I_N => - F j.1 j.2));
  first [by move=> q _ /=; rewrite Fanti | idtac].
rewrite [X in _ + X]sumrN.
apply/eqP; rewrite subr_eq0; apply/eqP.
rewrite [in RHS]big_mkcond [in LHS]big_mkcond; apply: eq_bigr => q _ /=.
case: (ltngtP (val q.2) (val q.1)) => h.
- by [].
- by [].
- by move/val_inj: h => ->; rewrite Fdiag.
Qed.

Lemma quadC (c : cellN) (j i : 'I_N) : i != j -> quad c j i = quad c i j.
Proof.
move=> ij; rewrite /quad.
rewrite [fv (fv c i (tc (c i))) j (tc (c j))](fvC _ _ _ ij) 1?eq_sym //.
rewrite [fv (fv c i (tc (c i))) j (bc (c j))](fvC _ _ _ ij) 1?eq_sym //.
rewrite [fv (fv c i (bc (c i))) j (tc (c j))](fvC _ _ _ ij) 1?eq_sym //.
rewrite [fv (fv c i (bc (c i))) j (bc (c j))](fvC _ _ _ ij) 1?eq_sym //.
by rewrite -!addrA; congr (_ + _); rewrite addrCA.
Qed.

Lemma coefT_anti (c : cellN) (j i : 'I_N) :
  is_edge (c j) -> is_edge (c i) -> i != j -> coefT c i j = - coefT c j i.
Proof.
move=> ej ei ij; rewrite /coefT.
have sgnB1 (m : nat) : (0 < m)%N -> (-1) ^+ (m - 1) = - ((-1) ^+ m) :> R.
  by case: m => // m _; rewrite subn1 /= exprS mulN1r opprK.
have rkpos (a b : 'I_N) : is_edge (c a) -> (val a < val b)%N -> (0 < rk c b)%N.
  by move=> ea hab; rewrite /rk (cardsD1 a) inE ea hab add1n.
case: (ltngtP (val i) (val j)) => [h|h|/val_inj/eqP]; last by rewrite (negbTE ij).
- by rewrite subn0 sgnB1 ?(rkpos i j) // mulrN mulrC.
- by rewrite subn0 sgnB1 ?(rkpos j i) // mulrN opprK mulrC.
Qed.

Lemma Tterm_diag (c : cellN) (j : 'I_N) : Tterm c j j = 0.
Proof. by rewrite /Tterm; case: ifP => // /and3P[_ _]; rewrite eqxx. Qed.

Lemma Tterm_anti (c : cellN) (j i : 'I_N) : Tterm c i j = - Tterm c j i.
Proof.
rewrite /Tterm; case: (eqVneq i j) => [->|ij]; first by rewrite !andbF oppr0.
rewrite ![~~ false]/= !andbT.
case Ej : (is_edge (c j)); last by rewrite andbF /= oppr0.
case Ei : (is_edge (c i)); last by rewrite andbF /= oppr0.
rewrite /= (coefT_anti Ej Ei ij) scaleNr quadC //.
by rewrite eq_sym.
Qed.

Lemma bd1_fv (c : cellN) j v : is_edge (c j) ->
  bd1 (fv c j v)
  = \sum_(i : 'I_N)
      (if is_edge (c i) && (i != j)
       then (-1) ^+ (rk c i - (val j < val i)) *:
            (cc (fv (fv c j v) i (tc (c i))) - cc (fv (fv c j v) i (bc (c i))))
       else 0).
Proof.
move=> ej; rewrite /bd1; apply: eq_bigr => i _; rewrite /edgeterm.
case: (eqVneq i j) => [->|ij].
  by rewrite fv_same andbF.
rewrite fvE (negbTE ij) andbT.
case E : (c i) => [v'|kr] //=.
rewrite (rk_fv v ij ej).
by rewrite /etop /ebot.
Qed.

Lemma bd_bd1 (c : cellN) : bd (bd1 c) = \sum_(j : 'I_N) \sum_(i : 'I_N) Tterm c j i.
Proof.
rewrite /bd /bd1 lin_sum; apply: eq_bigr => j _.
rewrite /edgeterm.
case Ej : (c j) => [v|kr].
  by rewrite lin0 big1 // => i _; rewrite /Tterm Ej.
rewrite linZ linB !lin_cc.
rewrite -/(bd1 (fv c j (etop kr))) -/(bd1 (fv c j (ebot kr))) !bd1_fv ?Ej //.
rewrite -sumrB scaler_sumr; apply: eq_bigr => i _.
rewrite /Tterm Ej /=.
case: (boolP (is_edge (c i) && (i != j))) => [hi|hi]; last first.
  by rewrite subrr scaler0.
case/andP: hi => ei ij.
rewrite -scalerBr scalerA /coefT; congr (_ *: _).
rewrite /quad.
have et : etop kr = tc (c j) by rewrite Ej.
have eb : ebot kr = bc (c j) by rewrite Ej.
rewrite et eb opprB.
by rewrite addrA addrAC.
Qed.

(** The keystone: [bd (bd x) = 0]. *)
Lemma bd_bd x : bd (bd x) = 0.
Proof.
have dd c : bd (bd1 c) = 0.
  rewrite bd_bd1 sum_pair_anti // => [i|i j]; [exact: Tterm_diag | exact: Tterm_anti].
rewrite {1}/bd lin_comp /lin big1 // => c _.
by rewrite -/(lin bd1 (bd1 c)) -/(bd (bd1 c)) dd scaler0.
Qed.

End Ring.
End Cubical.

(** Make the section parameters implicit for downstream use. *)
Arguments cut : clear implicits.
Arguments slide {n p} x.
Arguments cell1 : clear implicits.
Arguments Vtx {n p} v.
Arguments Edg {n p} kr.
Arguments is_edge {n p} x.
Arguments etop {n p} kr.
Arguments ebot {n p} kr.
Arguments tc {n p} x.
Arguments bc {n p} x.
Arguments cellN : clear implicits.
Arguments dimN {n p N} c.
Arguments fv {n p N} c j v.
Arguments rk {n p N} c j.
Arguments edgeterm {n p N R} c j.
Arguments bd1 {n p N R} c.
Arguments bd {n p N R} x.
Arguments bd_bd {n p N R} x.
Arguments bd1_fv {n p N R} c j v.
Arguments bd_cc {n p N R} c.
Arguments bdD {n p N R} x y.
Arguments bdZ {n p N R} a x.
Arguments fvE {n p N} c j v i.
Arguments fv_same {n p N} c j v.
Arguments fvC {n p N} c j v k w.
Arguments is_edge_fv {n p N} c j v i.
Arguments rk_fv {n p N} c j v i.
