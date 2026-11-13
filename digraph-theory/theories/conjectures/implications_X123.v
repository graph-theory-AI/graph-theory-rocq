(** * Digraph.conjectures.implications_X123 -- a Rocq-only EDGE from X71 to X123 (directed Gyarfas-Sumner).

    X71 (studies:std_aboulker_charbit_naserasr_conjecture_directed_gy,
    [directed_gyarfas_sumner_oriented_forest_dichromatic_statement]): for every oriented forest F some function f
    bounds the dichromatic number of every oriented F-free digraph D by f of the clique number of its underlying
    graph.  X123 (studies:std_directed_gy_rf_s_sumner_conjecture_aboulker_char,
    [directed_gyarfas_sumner_tournament_forest_statement]): when a transitive tournament H is forbidden as well, one
    constant bounds the whole class.  X123's class is X71's with H also forbidden (X123's Notes: forbidding H is
    what turns the function into a constant).  The theorem below records the Rocq-only implication (no corpus
    relation).  Proof, with h = #|H|: if h = 0 the empty map embeds H, so the class is empty.  Otherwise a clique of
    the underlying graph of an oriented D is a tournament; one on at least 2 ^ (h - 1) vertices has a transitive set
    of h vertices ([ramsey_transitive], splitting at a vertex into its out- and in-neighbours), and two transitive
    tournaments of one size are joined by ranks ([out_rank], the number of successors inside the set), so H would
    embed.  Hence the clique number is below 2 ^ (h - 1), and the bound is the maximum of f below 2 ^ (h - 1)
    ([dicolorableb_monoS], iterated).  Axiom-free: only [Qed]-closed results; the lemmas before the theorem are
    stated over plain finite types and relations. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From GTBase Require Import base.
From Digraph Require Import prelude interop_graph_theory digraph oriented.
From Digraph.conjectures Require Import chi_bounded dichromatic heroes grounding_dichromatic X71 X123.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Transitive sets in tournaments (generic: a finite type and a relation) *)

(** The Sections below declare data only (types, relations, sets, a default element); every proposition a lemma
    assumes is an explicit binder of that lemma. *)
Section Linear.
Variables (T : finType) (r : rel T).

(** [r] is semicomplete on [S]: two distinct elements of [S] are related one way or the other. *)
Definition tourn_on (S : {set T}) : Prop :=
  forall u v, u \in S -> v \in S -> u != v -> r u v || r v u.

(** [r] is transitive on [S]. *)
Definition trans_on (S : {set T}) : Prop :=
  forall a b c, a \in S -> b \in S -> c \in S -> r a b -> r b c -> r a c.

Lemma rel_irr (asym : forall u v, r u v -> ~~ r v u) u : r u u = false.
Proof. by apply/negP => uu; move: (asym _ _ uu); rewrite uu. Qed.

Lemma tourn_on_sub (S S' : {set T}) : S' \subset S -> tourn_on S -> tourn_on S'.
Proof. by move=> sub tS u v uS vS; apply: tS; apply: (subsetP sub). Qed.

Lemma trans_on1 (asym : forall u v, r u v -> ~~ r v u) x : trans_on [set x].
Proof. by move=> a b c; rewrite !inE => /eqP-> /eqP-> _; rewrite (rel_irr asym). Qed.

Lemma trans_on_source (asym : forall u v, r u v -> ~~ r v u) (U : {set T}) v :
  trans_on U -> (forall u, u \in U -> r v u) -> trans_on (v |: U).
Proof.
move=> trU vU a b c; rewrite !inE.
case/predU1P=> [->|aU]; case/predU1P=> [->|bU]; case/predU1P=> [->|cU];
  rewrite ?(rel_irr asym) // => ab bc.
- by move: (asym _ _ ab); rewrite bc.
- exact: vU.
- by move: (asym _ _ ab); rewrite vU.
- by move: (asym _ _ bc); rewrite vU.
- exact: trU ab bc.
Qed.

Lemma trans_on_sink (asym : forall u v, r u v -> ~~ r v u) (U : {set T}) v :
  trans_on U -> (forall u, u \in U -> r u v) -> trans_on (v |: U).
Proof.
move=> trU Uv a b c; rewrite !inE.
case/predU1P=> [->|aU]; case/predU1P=> [->|bU]; case/predU1P=> [->|cU];
  rewrite ?(rel_irr asym) // => ab bc.
- by move: (asym _ _ ab); rewrite bc.
- by move: (asym _ _ (Uv _ bU)); rewrite ab.
- by move: (asym _ _ (Uv _ cU)); rewrite bc.
- exact: Uv.
- exact: trU ab bc.
Qed.

(** L1: a tournament on at least [2 ^ n] elements has a transitive set of [n.+1] elements. *)
Lemma ramsey_transitive (asym : forall u v, r u v -> ~~ r v u) n (S : {set T}) :
  tourn_on S -> 2 ^ n <= #|S| ->
  exists U : {set T}, [/\ U \subset S, #|U| = n.+1 & trans_on U].
Proof.
elim: n S => [|n IH] S tS.
  rewrite expn0 card_gt0 => /set0Pn[x xS].
  by exists [set x]; split; [rewrite sub1set | rewrite cards1 | exact: (trans_on1 asym)].
move=> cS.
have /set0Pn[v vS] : S != set0.
  by rewrite -card_gt0; apply: leq_trans cS; rewrite expn_gt0.
pose S' := S :\ v; pose N := [set u | r v u].
have cS' : #|S| = #|S'|.+1 by rewrite (cardsD1 v S) vS.
have cOI : #|S' :&: N| + #|S' :\: N| = #|S'| by rewrite cardsID.
have sS' : S' \subset S by apply: subD1set.
have vnU (U : {set T}) : U \subset S' -> v \notin U.
  by move=> sub; apply/negP => /(subsetP sub); rewrite !inE eqxx.
have grow (U : {set T}) : U \subset S' -> #|U| = n.+1 -> trans_on (v |: U) ->
    exists U' : {set T}, [/\ U' \subset S, #|U'| = n.+2 & trans_on U'].
  move=> sub cU trU'; exists (v |: U); split => //.
    by rewrite subUset sub1set vS (subset_trans sub sS').
  by rewrite cardsU1 (vnU _ sub) cU.
case: (leqP (2 ^ n) #|S' :&: N|) => [big | small].
  have [U [sub cU trU]] := IH _ (tourn_on_sub (subset_trans (subsetIl _ _) sS') tS) big.
  apply: (grow U); [exact: subset_trans sub (subsetIl _ _) | exact: cU |].
  apply: (trans_on_source asym) trU _ => u /(subsetP sub); rewrite !inE.
  by case/andP.
have big : 2 ^ n <= #|S' :\: N|.
  rewrite -(leq_add2l (2 ^ n)); apply: leq_trans (_ : #|S' :&: N|.+1 + #|S' :\: N| <= _).
    by rewrite addSn cOI -cS' addnn -mul2n -expnS.
  by rewrite leq_add2r.
have [U [sub cU trU]] := IH _ (tourn_on_sub (subset_trans (subsetDl _ _) sS') tS) big.
apply: (grow U); [exact: subset_trans sub (subsetDl _ _) | exact: cU |].
apply: (trans_on_sink asym) trU _ => u /(subsetP sub); rewrite !inE.
case/and3P=> /negbTE nvu uv uS.
by have := tS u v uS vS uv; rewrite nvu orbF.
Qed.

Section Rank.
Variable U : {set T}.

(** L2: the rank of [u] in [U] is its number of successors in [U]. *)
Definition out_rank u := #|[set w in U | r u w]|.

Lemma out_rank_lt (asym : forall u v, r u v -> ~~ r v u) (trU : trans_on U) u v :
  u \in U -> v \in U -> r u v -> out_rank v < out_rank u.
Proof.
move=> uU vU uv; apply: proper_card; apply/properP; split.
  apply/subsetP => w; rewrite !inE => /andP[wU vw]; rewrite wU /=.
  exact: trU uU vU wU uv vw.
by exists v; rewrite !inE ?vU ?uv ?(rel_irr asym).
Qed.

Lemma out_rank_ltE (asym : forall u v, r u v -> ~~ r v u) (tU : tourn_on U) (trU : trans_on U) u v :
  u \in U -> v \in U -> r u v = (out_rank v < out_rank u).
Proof.
move=> uU vU; apply/idP/idP => [|lt]; first exact: (out_rank_lt asym trU).
have [e|neq] := eqVneq u v; first by move: lt; rewrite e ltnn.
case/orP: (tU _ _ uU vU neq) => // vu.
by move: (out_rank_lt asym trU vU uU vu); rewrite ltnNge (ltnW lt).
Qed.

Lemma out_rank_inj (asym : forall u v, r u v -> ~~ r v u) (tU : tourn_on U) (trU : trans_on U) :
  {in U &, injective out_rank}.
Proof.
move=> u v uU vU e; apply/eqP; apply: contraT => neq.
by case/orP: (tU _ _ uU vU neq) => [uv|vu];
  [move: (out_rank_lt asym trU uU vU uv) | move: (out_rank_lt asym trU vU uU vu)]; rewrite e ltnn.
Qed.

Lemma out_rank_bound (asym : forall u v, r u v -> ~~ r v u) u : u \in U -> out_rank u < #|U|.
Proof.
move=> uU; apply: proper_card; apply/properP; split.
  by apply/subsetP => w; rewrite inE => /andP[].
by exists u; rewrite // inE (rel_irr asym) andbF.
Qed.

Lemma out_rank_onto (asym : forall u v, r u v -> ~~ r v u) (tU : tourn_on U) (trU : trans_on U) i :
  i < #|U| -> exists2 u, u \in U & out_rank u = i.
Proof.
move=> iU.
have uq : uniq [seq out_rank u | u <- enum U].
  rewrite map_inj_in_uniq ?enum_uniq // => x y; rewrite !mem_enum.
  exact: (out_rank_inj asym tU trU).
have sub : {subset [seq out_rank u | u <- enum U] <= iota 0 #|U|}.
  move=> k /mapP[u]; rewrite mem_enum => uU ->.
  by rewrite mem_iota add0n (out_rank_bound asym).
have le : size (iota 0 #|U|) <= size [seq out_rank u | u <- enum U].
  by rewrite size_map size_iota -cardE.
have eqs := (uniq_min_size uq sub le).2.
have : i \in iota 0 #|U| by rewrite mem_iota add0n iU.
by rewrite -eqs => /mapP[u]; rewrite mem_enum => uU ->; exists u.
Qed.

End Rank.
End Linear.

Section Embed.
Variables (T1 T2 : finType) (r1 : rel T1) (r2 : rel T2) (A : {set T1}) (B : {set T2}) (y0 : T2).

(** L3: two transitive tournaments of one size, joined rank to rank. *)
Definition rank_emb (x : T1) : T2 := odflt y0 [pick y in B | out_rank r2 B y == out_rank r1 A x].

Lemma rank_embP (as1 : forall u v, r1 u v -> ~~ r1 v u) (as2 : forall u v, r2 u v -> ~~ r2 v u)
    (tB : tourn_on r2 B) (trB : trans_on r2 B) (cAB : #|A| = #|B|) x :
  x \in A -> rank_emb x \in B /\ out_rank r2 B (rank_emb x) = out_rank r1 A x.
Proof.
move=> xA; have lt : out_rank r1 A x < #|B|.
  by rewrite -cAB; exact: (out_rank_bound as1 xA).
have [y yB ry] := out_rank_onto as2 tB trB lt.
rewrite /rank_emb; case: pickP => [z /andP[zB /eqP ->] | none] //=.
by move: (none y); rewrite yB ry eqxx.
Qed.

Lemma rank_emb_rel (as1 : forall u v, r1 u v -> ~~ r1 v u) (as2 : forall u v, r2 u v -> ~~ r2 v u)
    (tA : tourn_on r1 A) (trA : trans_on r1 A) (tB : tourn_on r2 B) (trB : trans_on r2 B)
    (cAB : #|A| = #|B|) x y :
  x \in A -> y \in A -> r2 (rank_emb x) (rank_emb y) = r1 x y.
Proof.
move=> xA yA; have [exB ex] := rank_embP as1 as2 tB trB cAB xA.
have [eyB ey] := rank_embP as1 as2 tB trB cAB yA.
by rewrite (out_rank_ltE as2 tB trB exB eyB) ex ey -(out_rank_ltE as1 tA trA xA yA).
Qed.

Lemma rank_emb_inj (as1 : forall u v, r1 u v -> ~~ r1 v u) (as2 : forall u v, r2 u v -> ~~ r2 v u)
    (tA : tourn_on r1 A) (trA : trans_on r1 A) (tB : tourn_on r2 B) (trB : trans_on r2 B)
    (cAB : #|A| = #|B|) :
  {in A &, injective rank_emb}.
Proof.
move=> x y xA yA e; apply: (out_rank_inj as1 tA trA xA yA).
by rewrite -(rank_embP as1 as2 tB trB cAB xA).2 -(rank_embP as1 as2 tB trB cAB yA).2 e.
Qed.

End Embed.

Section Clique.
Variables (G : sgraph) (r : rel G).

(** A clique of [G] is a tournament for [r]. *)
Lemma clique_tourn (adj : forall u v : G, u -- v -> r u v || r v u) (S : {set G}) :
  cliqueb S -> tourn_on r S.
Proof. by move=> /cliqueP cS u v uS vS uv; apply: adj; apply: cS. Qed.

(** With no transitive set of [n.+1] elements, every clique has fewer than [2 ^ n] vertices. *)
Lemma omega_lt_of_no_transitive (asym : forall u v, r u v -> ~~ r v u)
    (adj : forall u v : G, u -- v -> r u v || r v u) n :
  (forall U : {set G}, #|U| = n.+1 -> tourn_on r U -> trans_on r U -> False) ->
  ω([set: G]) < 2 ^ n.
Proof.
move=> no; rewrite omega_setT_maxE.
have := expn_gt0 2 n; case E : (2 ^ n) => [//|m] _.
rewrite ltnS; apply/bigmax_leqP => S cS; rewrite -ltnS -E ltnNge; apply/negP => big.
have tS := clique_tourn adj cS.
have [U [sub cU trU]] := ramsey_transitive asym tS big.
exact: no U cU (tourn_on_sub sub tS) trU.
Qed.

End Clique.

(** L4: a strict total order [r1] on [T1] that does not embed in [(G, r2)], with [r2] oriented along the edges of
    [G], bounds the clique number of [G] by [2 ^ (#|T1| - 1)]. *)
Lemma no_embedding_omega_lt (T1 : finType) (r1 : rel T1) (G : sgraph) (r2 : rel G) :
  (forall u v, r1 u v -> ~~ r1 v u) -> (forall u v : T1, u != v -> r1 u v || r1 v u) -> transitive r1 ->
  (forall u v, r2 u v -> ~~ r2 v u) -> (forall u v : G, u -- v -> r2 u v || r2 v u) ->
  ~ (exists f : T1 -> G, injective f /\ forall u v, r2 (f u) (f v) = r1 u v) ->
  0 < #|T1| -> ω([set: G]) < 2 ^ #|T1|.-1.
Proof.
move=> as1 tot1 tr1 as2 adj noemb pos.
apply: (omega_lt_of_no_transitive as2 adj) => U cU tU trU.
have /set0Pn[y0 _] : U != set0 by rewrite -card_gt0 cU.
have tA : tourn_on r1 [set: T1] by move=> u v _ _; exact: tot1.
have trA : trans_on r1 [set: T1] by move=> a b c _ _ _ ab bc; exact: tr1 ab bc.
have cAB : #|[set: T1]| = #|U| by rewrite cardsT cU prednK.
apply: noemb; exists (rank_emb r1 r2 [set: T1] U y0); split.
  by move=> x y; apply: (rank_emb_inj as1 as2 tA trA tU trU cAB); rewrite inE.
by move=> x y; apply: (rank_emb_rel y0 as1 as2 tA trA tU trU cAB); rewrite inE.
Qed.

(** The empty case: an empty [T1] embeds anywhere. *)
Lemma empty_embedding (T1 T2 : finType) (r1 : rel T1) (r2 : rel T2) :
  #|T1| = 0 -> exists f : T1 -> T2, injective f /\ forall u v, r2 (f u) (f v) = r1 u v.
Proof.
move=> c0; have e (x : T1) : False by move: (card0_eq c0 x); rewrite !inE.
by exists (fun x => match e x with end); split=> [x|x]; case: (e x).
Qed.

(** The bound as a finite maximum, and a successor-monotone property iterated. *)
Lemma le_max_below (f : nat -> nat) N i : i < N -> f i <= \max_(j < N) f j.
Proof. by move=> lt; exact: (@leq_bigmax _ (fun j : 'I_N => f j) (Ordinal lt)). Qed.

Lemma monoS_iter (P : nat -> Prop) : (forall k, P k -> P k.+1) -> forall k k', k <= k' -> P k -> P k'.
Proof.
move=> step k k' /subnK <-; elim: (k' - k) => [|d IH] Pk; first by rewrite add0n.
by rewrite addSn; exact: step (IH Pk).
Qed.

(** ** Directed Gyarfas-Sumner: the function bound (X71) gives the constant bound (X123) *)

(*@EDGE from=directed_gyarfas_sumner_oriented_forest_dichromatic_statement to=directed_gyarfas_sumner_tournament_forest_statement kind=implies status=verified proof=directed_gyarfas_sumner_oriented_forest_dichromatic_implies_directed_gyarfas_sumner_tournament_forest note="Rocq-only edge (no corpus relation), routed by Lancelot's (743), (744): the directed Gyarfas-Sumner conjecture with a function of the clique number (X71, studies:std_aboulker_charbit_naserasr_conjecture_directed_gy: for every oriented forest F, f(omega) dicolours every oriented F-free digraph) implies its case with a transitive tournament H also forbidden and one constant bound (X123, studies:std_directed_gy_rf_s_sumner_conjecture_aboulker_char). X123's class is X71's with H forbidden. With h = |H| > 0, a clique of the underlying graph of an oriented D is a tournament; one on at least 2^(h-1) vertices has a transitive h-set (ramsey_transitive), onto which H embeds rank to rank (rank_emb), so omega < 2^(h-1) and the bound is the maximum of f below 2^(h-1) (dicolorableb_monoS, iterated); h = 0 leaves the class empty. Both rows are open." *)
Theorem directed_gyarfas_sumner_oriented_forest_dichromatic_implies_directed_gyarfas_sumner_tournament_forest :
  directed_gyarfas_sumner_oriented_forest_dichromatic_statement ->
  directed_gyarfas_sumner_tournament_forest_statement.
Proof.
move=> X71 H F [[irrH totH asH] trH] oF fF.
have [f hf] := X71 F oF fF.
have [H0|Hpos] := posnP #|H|.
  by exists 0 => D [_ [hfree _]]; case: hfree; apply: empty_embedding.
exists (\max_(j < 2 ^ #|H|.-1) f j) => D [oD [hfree ffree]].
have om : ω([set: chi_bounded.underlying D]) < 2 ^ #|H|.-1.
  apply: (@no_embedding_omega_lt H (@arc H) (chi_bounded.underlying D) (@arc D)) => //.
  by move=> u v /andP[].
apply: (monoS_iter (@dicolorableb_monoS D) (le_max_below f om)).
exact: hf.
Qed.
