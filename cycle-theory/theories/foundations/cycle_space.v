(** * Cycle.foundations.cycle_space — degree sums, cuts, circuits and the
      circuit decomposition of even subgraphs

    General multigraph helpers, stated on the [mgraph] carrier of the
    cycle-theory rows and phrased WITHOUT the conjecture-level vocabulary of
    [U6.v] (so that this file sits below the conjecture layer): an "even
    subgraph" appears as the unfolded [forall v, ~~ odd (subdeg C v)], a
    "circuit" as [connectivity.is_circuit].

    Contents.
    - [card_setIsum]: a cardinality as a sum of indicators over an edge set.
    - [sum_subdeg_cut]: the HANDSHAKE identity relative to a vertex set [S],
      [\sum_(v in S) subdeg C v = 2 * #|C inside S| + #|C :&: cut S|].
    - [even_cut_even] / [reg_cut_parity]: the parity consequences (an even
      subgraph meets every cut evenly; a [d]-regular multigraph has
      [odd #|cut S| = odd (#|S| * d)]).
    - route (= oriented walk) machinery [rwalk], simple paths, and the master
      lemma [has_circuit]: an edge set with at least one edge and no vertex of
      degree 1 contains a circuit.
    - [even_circuit_decomposition] (F14): every even subgraph is partitioned by
      a list of circuits. *)

From GraphTheory Require Import mgraph.
From GTBase Require Export base.
From Cycle.foundations Require Export connectivity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Cardinalities as sums of indicators *)

Lemma card_setIsum (T : finType) (C : {set T}) (Q : pred T) :
  #|[set e in C | Q e]| = \sum_(e in C) Q e.
Proof.
rewrite -sum1_card big_mkcond /= [RHS]big_mkcond /=.
apply: eq_bigr => e _; rewrite inE.
by case: (e \in C) => //=; case: (Q e).
Qed.

Lemma card_setI_sum (T : finType) (C A : {set T}) :
  #|C :&: A| = \sum_(e in C) (e \in A).
Proof. exact: (card_setIsum C (fun e => e \in A)). Qed.

Lemma sum_eq_mem (T : finType) (S : {set T}) (a : T) :
  \sum_(v in S) (a == v) = (a \in S).
Proof.
have zero : \sum_(i in S | i != a) (a == i) = 0.
  by apply: big1 => i /andP[_]; rewrite eq_sym => /negbTE ->.
case: (boolP (a \in S)) => aS.
- by rewrite (bigD1 a aS) eqxx zero.
- apply: big1 => v vS.
  have av : a != v by apply: contraNneq aS => ->; exact: vS.
  by rewrite (negbTE av).
Qed.

Lemma odd_sum_even (T : finType) (S : {set T}) (f : T -> nat) :
  (forall x, ~~ odd (f x)) -> ~~ odd (\sum_(x in S) f x).
Proof.
move=> hf; apply: (big_ind (fun n : nat => ~~ odd n)) => //.
by move=> x y hx hy; rewrite oddD (negbTE hx) (negbTE hy).
Qed.

Lemma card_count_enum (T : finType) (P : pred T) : #|P| = count P (index_enum T).
Proof. by rewrite cardE /enum_mem size_filter. Qed.

Lemma size_index_enum_ord (n : nat) : size (index_enum 'I_n) = n.
Proof. by rewrite -count_predT -card_count_enum card_ord. Qed.

Lemma odd_sum_even_P (T : finType) (P : pred T) (f : T -> nat) :
  (forall x, P x -> ~~ odd (f x)) -> ~~ odd (\sum_(x | P x) f x).
Proof.
move=> hf; apply: (big_ind (fun n : nat => ~~ odd n)) => //.
by move=> m n hm hn; rewrite oddD (negbTE hm) (negbTE hn).
Qed.

(** ** The handshake identity relative to a vertex set *)

Lemma ends_at_sum (G : mgraph) (C : {set edge G}) (b : bool) (v : G) :
  #|ends_at C b v| = \sum_(e in C) (endpoint b e == v).
Proof. exact: (card_setIsum C (fun e => endpoint b e == v)). Qed.

Lemma sum_ends_at (G : mgraph) (C : {set edge G}) (b : bool) (S : {set G}) :
  \sum_(v in S) #|ends_at C b v| = \sum_(e in C) (endpoint b e \in S).
Proof.
transitivity (\sum_(v in S) \sum_(e in C) (endpoint b e == v)).
  by apply: eq_bigr => v _; exact: ends_at_sum.
rewrite exchange_big /=; apply: eq_bigr => e _; exact: sum_eq_mem.
Qed.

(** The handshake lemma relative to [S]: the [C]-degree sum over [S] counts the
    [C]-edges inside [S] twice and the [C]-edges of the cut once. *)
Lemma sum_subdeg_cut (G : mgraph) (C : {set edge G}) (S : {set G}) :
  \sum_(v in S) subdeg C v
  = 2 * #|C :&: [set e | (source e \in S) && (target e \in S)]| + #|C :&: cut S|.
Proof.
rewrite !card_setI_sum.
transitivity (\sum_(e in C) (source e \in S) + \sum_(e in C) (target e \in S)).
  by rewrite /subdeg big_split /= !sum_ends_at.
rewrite -big_split big_distrr /= -big_split /=.
apply: eq_bigr => e _; rewrite !inE.
by case: (source e \in S); case: (target e \in S).
Qed.

(** ** Parity consequences *)

(** An even subgraph meets every edge cut in an even number of edges. *)
Lemma even_cut_even (G : mgraph) (C : {set edge G}) (S : {set G}) :
  (forall v : G, ~~ odd (subdeg C v)) -> ~~ odd #|C :&: cut S|.
Proof.
move=> Ce; have := odd_sum_even S (fun v => Ce v).
by rewrite sum_subdeg_cut oddD oddM /=.
Qed.

(** In a [d]-regular multigraph the parity of a cut is that of [#|S| * d]. *)
Lemma reg_cut_parity (G : mgraph) (d : nat) (S : {set G}) :
  (forall v : G, mdeg v = d) -> odd #|cut S| = odd (#|S| * d).
Proof.
move=> reg.
have h := sum_subdeg_cut [set: edge G] S; rewrite !setTI in h.
have e1 : \sum_(v in S) subdeg [set: edge G] v = #|S| * d.
  by rewrite -sum_nat_const; apply: eq_bigr => v _; exact: reg v.
by rewrite -e1 h oddD oddM /=.
Qed.

(** ================================================================= *)
(** ** Small seq / finType helpers *)

Lemma count_sum (T : Type) (p : pred T) (s : seq T) :
  count p s = \sum_(y <- s) (p y : nat).
Proof.
elim: s => [|y s IH]; first by rewrite big_nil.
by rewrite big_cons /= IH.
Qed.

Lemma card_seq_filter (T : finType) (s : seq T) (Q : pred T) :
  uniq s -> #|[set y in s | Q y]| = count Q s.
Proof.
move=> us; rewrite -size_filter.
have -> : [set y in s | Q y] = [set y in filter Q s].
  by apply/setP => y; rewrite !inE mem_filter andbC.
by rewrite cardsE; apply/card_uniqP; exact: filter_uniq.
Qed.

Lemma mem_split (T : eqType) (y : T) (s : seq T) :
  y \in s -> exists s1 s2, s = s1 ++ y :: s2.
Proof.
elim: s => // a s IH; rewrite in_cons => /orP[/eqP ->|/IH[s1 [s2 ->]]].
  by exists [::], s.
by exists (a :: s1), s2.
Qed.

Lemma last_mem (T : eqType) (y : T) (s : seq T) : s != [::] -> last y s \in s.
Proof. by case: s => // a s _ /=; exact: mem_last. Qed.

Lemma uniq_size_leq (T : finType) (s : seq T) : uniq s -> (size s <= #|T|)%N.
Proof. by move/card_uniqP => <-; exact: max_card. Qed.

(** ================================================================= *)
(** ** Subgraph degrees: additivity along a set difference *)

Lemma subdeg_setD (G : mgraph) (A B : {set edge G}) (v : G) :
  B \subset A -> subdeg A v = subdeg B v + subdeg (A :\: B) v.
Proof.
move=> sBA.
have step : forall b : bool,
    #|ends_at A b v| = #|ends_at B b v| + #|ends_at (A :\: B) b v|.
  move=> b; rewrite !ends_at_sum (big_setID B) /= setIC (setIidPl sBA).
  by [].
by rewrite /subdeg !step addnACA.
Qed.

Lemma subdeg_setD_even (G : mgraph) (A B : {set edge G}) (v : G) :
  B \subset A -> ~~ odd (subdeg A v) -> ~~ odd (subdeg B v) ->
  ~~ odd (subdeg (A :\: B) v).
Proof.
move=> sBA; rewrite (subdeg_setD v sBA) oddD => hA hB.
by move: hA; rewrite (negbTE hB) addFb.
Qed.

Lemma subdeg_gt0P (G : mgraph) (A : {set edge G}) (v : G) :
  (0 < subdeg A v)%N -> exists2 f : edge G, f \in A & exists b : bool, endpoint b f = v.
Proof.
rewrite /subdeg addn_gt0 => /orP[]/card_gt0P[f]; rewrite inE => /andP[fA /eqP hf].
- by exists f => //; exists false.
- by exists f => //; exists true.
Qed.

(** ================================================================= *)
(** ** Routes: walks carrying an orientation for each step *)

(** A step is an edge together with a direction bit: [(e, b)] is traversed from
    [endpoint b e] to [endpoint (~~ b) e]. *)
Definition rtl (G : mgraph) (a : edge G * bool) : G := endpoint a.2 a.1.
Definition rhd (G : mgraph) (a : edge G * bool) : G := endpoint (~~ a.2) a.1.

Fixpoint rwalk (G : mgraph) (x : G) (r : seq (edge G * bool)) : bool :=
  if r is a :: r' then (rtl a == x) && rwalk (rhd a) r' else true.

Definition rlast (G : mgraph) (x : G) (r : seq (edge G * bool)) : G :=
  last x (map (@rhd G) r).
Definition redges (G : mgraph) (r : seq (edge G * bool)) : seq (edge G) :=
  map (fun a : edge G * bool => a.1) r.
Definition eset (G : mgraph) (r : seq (edge G * bool)) : {set edge G} :=
  [set e in redges r].
Definition rrev (G : mgraph) (r : seq (edge G * bool)) : seq (edge G * bool) :=
  rev (map (fun a : edge G * bool => (a.1, ~~ a.2)) r).

Lemma rtl_flip (G : mgraph) (a : edge G * bool) : rtl (a.1, ~~ a.2) = rhd a.
Proof. by []. Qed.

Lemma rhd_flip (G : mgraph) (a : edge G * bool) : rhd (a.1, ~~ a.2) = rtl a.
Proof. by rewrite /rhd /rtl /= negbK. Qed.

Lemma rlast_cons (G : mgraph) (x : G) (a : edge G * bool)
    (r : seq (edge G * bool)) : rlast x (a :: r) = rlast (rhd a) r.
Proof. by []. Qed.

Lemma rlast_cat (G : mgraph) (x : G) (r1 r2 : seq (edge G * bool)) :
  rlast x (r1 ++ r2) = rlast (rlast x r1) r2.
Proof. by rewrite /rlast map_cat last_cat. Qed.

Lemma rlast_rcons (G : mgraph) (x : G) (r : seq (edge G * bool))
    (a : edge G * bool) : rlast x (rcons r a) = rhd a.
Proof. by rewrite /rlast map_rcons last_rcons. Qed.

Lemma rwalk_cat (G : mgraph) (r1 r2 : seq (edge G * bool)) (x : G) :
  rwalk x (r1 ++ r2) = rwalk x r1 && rwalk (rlast x r1) r2.
Proof.
elim: r1 x => [x|a r1 IH x] //=.
by rewrite IH andbA.
Qed.

Lemma rwalk_rcons (G : mgraph) (x : G) (r : seq (edge G * bool))
    (a : edge G * bool) :
  rwalk x (rcons r a) = rwalk x r && (rtl a == rlast x r).
Proof. by rewrite -cats1 rwalk_cat /= andbT. Qed.

Lemma rrev_cons (G : mgraph) (a : edge G * bool) (r : seq (edge G * bool)) :
  rrev (a :: r) = rcons (rrev r) (a.1, ~~ a.2).
Proof. by rewrite /rrev map_cons rev_cons. Qed.

Lemma redges_cat (G : mgraph) (r1 r2 : seq (edge G * bool)) :
  redges (r1 ++ r2) = redges r1 ++ redges r2.
Proof. exact: map_cat. Qed.

Lemma redges_rrev (G : mgraph) (r : seq (edge G * bool)) :
  redges (rrev r) = rev (redges r).
Proof. by rewrite /rrev /redges map_rev -map_comp. Qed.

(** A route yields an undirected walk on its edges. *)
Lemma rwalk_uwalk (G : mgraph) (r : seq (edge G * bool)) (x : G) :
  rwalk x r -> uwalk x (rlast x r) (redges r).
Proof.
elim: r x => [x _|a r IH x]; first by rewrite /rlast /= eqxx.
case: a => e b; rewrite rlast_cons.
case/andP => /eqP tl wr.
case: b tl wr => tl wr.
- by apply: uwalk_cons_rev; [exact: tl | apply: IH].
- by apply: uwalk_cons; [exact: tl | apply: IH].
Qed.

(** The tails of a route are its start followed by all but the last head. *)
Lemma rwalk_tails (G : mgraph) (r : seq (edge G * bool)) (x : G) :
  rwalk x r -> map (@rtl G) r ++ [:: rlast x r] = x :: map (@rhd G) r.
Proof.
elim: r x => [x _|a r IH x] //.
rewrite rlast_cons.
case/andP => /eqP tl wr.
by rewrite map_cons cat_cons tl (IH _ wr).
Qed.

(** Reversal of a route. *)
Lemma rwalk_rrev (G : mgraph) (r : seq (edge G * bool)) (x : G) :
  rwalk x r -> rwalk (rlast x r) (rrev r) && (rlast (rlast x r) (rrev r) == x).
Proof.
elim: r x => [x _|a r IH x]; first by rewrite /rlast /= eqxx.
rewrite rlast_cons; case/andP => /eqP tl wr.
have /andP[w1 /eqP l1] := IH _ wr.
by rewrite rrev_cons rwalk_rcons rlast_rcons rtl_flip rhd_flip l1 tl w1 !eqxx.
Qed.

(** ** The degree of the edge set of a route with distinct edges *)

Lemma subdeg_eset (G : mgraph) (r : seq (edge G * bool)) (v : G) :
  uniq (redges r) ->
  subdeg (eset r) v
  = count (fun a : edge G * bool => rtl a == v) r
    + count (fun a : edge G * bool => rhd a == v) r.
Proof.
move=> ur.
have step : forall b : bool,
    #|ends_at (eset r) b v| = count (fun a : edge G * bool => endpoint b a.1 == v) r.
  move=> b.
  have -> : ends_at (eset r) b v = [set e in redges r | endpoint b e == v].
    by apply/setP => e; rewrite !inE.
  by rewrite (card_seq_filter _ ur) count_map.
rewrite /subdeg !step !count_sum -!big_split /=.
apply: eq_bigr => a _.
case: a => e [] /=; first by rewrite addnC.
by [].
Qed.

Lemma eset_sub (G : mgraph) (C : {set edge G}) (r : seq (edge G * bool)) :
  all (fun a : edge G * bool => a.1 \in C) r -> eset r \subset C.
Proof.
move=> aC; apply/subsetP => e; rewrite inE => /mapP[a ar ->].
exact: (allP aC).
Qed.

(** Any vertex of a route is the endpoint of a prefix. *)
Lemma rverts_split (G : mgraph) (r : seq (edge G * bool)) (x z : G) :
  z \in x :: map (@rhd G) r ->
  exists r1 r2, r = r1 ++ r2 /\ rlast x r1 = z.
Proof.
rewrite in_cons => /orP[/eqP ->|]; first by exists [::], r.
case/mapP => a ar hz.
have [s1 [s2 req]] := mem_split ar.
exists (rcons s1 a), s2; split; last by rewrite rlast_rcons hz.
by rewrite cat_rcons.
Qed.

(** ** A closed route with distinct edges and distinct heads is a circuit *)

Lemma incident_step (G : mgraph) (a : edge G * bool) (u : G) :
  incident u a.1 -> (u == rtl a) || (u == rhd a).
Proof.
rewrite incidentE => /orP[]/eqP <-; case: a => e [] /=; by rewrite eqxx ?orbT.
Qed.

Lemma closed_route_circuit (G : mgraph) (r : seq (edge G * bool)) (x : G) :
  r != [::] -> rwalk x r -> rlast x r = x ->
  uniq (redges r) -> uniq (map (@rhd G) r) -> is_circuit (eset r).
Proof.
move=> rn0 wr cl ue uh.
have htl : map (@rtl G) r ++ [:: x] = x :: map (@rhd G) r.
  by have := rwalk_tails wr; rewrite cl.
have hcount : forall v : G, count (fun a : edge G * bool => rtl a == v) r
                          = count (fun a : edge G * bool => rhd a == v) r.
  move=> v; have h := congr1 (count (pred1 v)) htl.
  apply/eqP; move: h; rewrite count_cat /= addn0 addnC !count_map.
  by move/eqP; rewrite eqn_add2l.
have hhd : forall v : G, count (fun a : edge G * bool => rhd a == v) r
                       = (v \in map (@rhd G) r).
  move=> v.
  have -> : count (fun a : edge G * bool => rhd a == v) r
          = count (pred1 v) (map (@rhd G) r) by rewrite count_map.
  exact: count_uniq_mem v uh.
split.
- apply/set0Pn.
  have : redges r != [::] by rewrite /redges -size_eq0 size_map size_eq0.
  case E: (redges r) => [//|e s] _; exists e.
  by rewrite inE E inE eqxx.
- move=> v; rewrite (subdeg_eset v ue) hcount hhd.
  by case: (v \in map (@rhd G) r); [right | left].
- have hverts : forall u : G, H_inc (eset r) u -> u \in x :: map (@rhd G) r.
    move=> u /existsP[e /andP[eE iu]].
    move: eE; rewrite inE => /mapP[a ar ae].
    rewrite ae in iu.
    case/orP: (incident_step iu) => /eqP ->.
    + by rewrite -htl mem_cat (map_f _ ar).
    + by rewrite in_cons (map_f _ ar) orbT.
  move=> u u' hu hu'.
  have [r1 [r2 [req r1u]]] := rverts_split (hverts _ hu).
  have [s1 [s2 [seq1 s1u']]] := rverts_split (hverts _ hu').
  have wr1 : rwalk x r1 by move: wr; rewrite req rwalk_cat => /andP[].
  have ws1 : rwalk x s1 by move: wr; rewrite seq1 rwalk_cat => /andP[].
  have /andP[wrev lrev] := rwalk_rrev wr1.
  rewrite r1u in wrev; rewrite r1u in lrev; move/eqP in lrev.
  have hh : rwalk u (rrev r1 ++ s1) by rewrite rwalk_cat wrev lrev ws1.
  have hlast : rlast u (rrev r1 ++ s1) = u' by rewrite rlast_cat lrev s1u'.
  exists (redges (rrev r1 ++ s1)); apply/andP; split.
  + by rewrite -hlast; exact: rwalk_uwalk hh.
  + rewrite redges_cat all_cat; apply/andP; split; apply/allP => e he.
    * rewrite inE req redges_cat mem_cat; apply/orP; left.
      by move: he; rewrite redges_rrev mem_rev.
    * by rewrite inE seq1 redges_cat mem_cat; apply/orP; left.
Qed.

(** ** Simple paths and the extension/circuit dichotomy *)

Definition spath (G : mgraph) (C : {set edge G}) (x : G)
    (r : seq (edge G * bool)) : bool :=
  [&& rwalk x r, all (fun a : edge G * bool => a.1 \in C) r,
      uniq (redges r) & uniq (x :: map (@rhd G) r)].

Lemma spath_step (G : mgraph) (C : {set edge G}) (x : G)
    (r : seq (edge G * bool)) :
  (forall v : G, subdeg C v != 1) -> r != [::] -> spath C x r ->
  (exists D : {set edge G}, D \subset C /\ is_circuit D) \/
  (exists a : edge G * bool, spath C x (rcons r a)).
Proof.
move=> Cdeg rn0 /and4P[wr aC ue uv].
have esC : eset r \subset C := eset_sub aC.
have htl := rwalk_tails wr.
have uh : uniq (map (@rhd G) r) by move: uv => /andP[].
have ynotl : rlast x r \notin map (@rtl G) r.
  move: uv; rewrite -htl cat_uniq => /and3P[_ h _].
  by move: h; rewrite /= orbF.
have yhd : rlast x r \in map (@rhd G) r.
  rewrite /rlast; apply: last_mem.
  by rewrite -size_eq0 size_map size_eq0.
have hdeg : subdeg (eset r) (rlast x r) = 1.
  rewrite (subdeg_eset _ ue).
  have -> : count (fun a : edge G * bool => rtl a == rlast x r) r = 0.
    apply/eqP; rewrite -leqn0 leqNgt -has_count.
    apply/negP => /hasP[a ar /eqP ha].
    by move: ynotl; rewrite -ha (map_f _ ar).
  rewrite add0n.
  have := count_uniq_mem (rlast x r) uh.
  by rewrite count_map yhd.
have ygt : (0 < subdeg (C :\: eset r) (rlast x r))%N.
  have hsum := subdeg_setD (rlast x r) esC.
  rewrite hdeg in hsum.
  case: (posnP (subdeg (C :\: eset r) (rlast x r))) => // h0.
  by move: (Cdeg (rlast x r)); rewrite hsum h0 addn0 eqxx.
have [f fD [b hb]] := subdeg_gt0P ygt.
move: fD; rewrite in_setD inE => /andP[fnotr fC].
case: (boolP (endpoint (~~ b) f \in x :: map (@rhd G) r)) => [zin|znot]; last first.
- right; exists (f, b); apply/and4P; split.
  + by rewrite rwalk_rcons wr /=; apply/eqP; exact: hb.
  + by rewrite all_rcons /= fC.
  + rewrite /redges map_rcons rcons_uniq.
    by apply/andP; split; [exact: fnotr | exact: ue].
  + rewrite map_rcons -rcons_cons rcons_uniq.
    by apply/andP; split; [exact: znot | exact: uv].
- left.
  have [r1 [r2 [req r1z]]] := rverts_split zin.
  have wr2 : rwalk (endpoint (~~ b) f) r2.
    by move: wr; rewrite req rwalk_cat -r1z => /andP[].
  have l2 : rlast (endpoint (~~ b) f) r2 = rlast x r.
    by rewrite -r1z -rlast_cat -req.
  exists (eset (r2 ++ [:: (f, b)])); split.
    apply: eset_sub; rewrite all_cat.
    apply/andP; split; last by rewrite /= fC.
    by move: aC; rewrite req all_cat => /andP[].
  apply: (@closed_route_circuit G (r2 ++ [:: (f, b)]) (endpoint (~~ b) f)).
  + by rewrite -size_eq0 size_cat /= addn1.
  + by rewrite rwalk_cat wr2 /= l2 andbT; apply/eqP; exact: hb.
  + by rewrite rlast_cat /= l2.
  + rewrite redges_cat cat_uniq /=.
    apply/and3P; split; last by [].
    * by move: ue; rewrite req redges_cat cat_uniq => /and3P[_ _].
    * rewrite orbF; apply/negP => hf.
      move: fnotr; rewrite req redges_cat mem_cat hf orbT.
      by move/negP; apply.
  + rewrite map_cat /= cat_uniq /=.
    have uvs : uniq ((x :: map (@rhd G) r1) ++ map (@rhd G) r2).
      by move: uv; rewrite req map_cat.
    move: uvs; rewrite cat_uniq => /and3P[_ hno u2].
    apply/and3P; split; last by [].
    * exact: u2.
    * rewrite orbF; apply/negP => hz.
      have h2 := hasPn hno _ hz.
      have hzr : rhd (f, b) = rlast x r1 by rewrite r1z.
      rewrite hzr in h2.
      by move/negP: h2; apply; exact: mem_last.
Qed.

(** ** The master lemma: an edge set with no vertex of degree one, and at least
       one edge, contains a circuit *)

Lemma has_circuit_bound (G : mgraph) (C : {set edge G}) (n : nat) :
  (forall v : G, subdeg C v != 1) ->
  forall (x : G) (r : seq (edge G * bool)),
    spath C x r -> r != [::] -> (#|G| <= size r + n)%N ->
    exists D : {set edge G}, D \subset C /\ is_circuit D.
Proof.
move=> Cdeg; elim: n => [|n IH] x r sp rn0 hb.
- have uv : uniq (x :: map (@rhd G) r) by case/and4P: sp.
  have h := uniq_size_leq uv.
  rewrite /= size_map in h; rewrite addn0 in hb.
  by move: (leq_trans h hb); rewrite ltnn.
- have [[D hD]|[a spa]] := spath_step Cdeg rn0 sp; first by exists D.
  apply: (IH x (rcons r a) spa).
  + by rewrite -size_eq0 size_rcons.
  + by rewrite size_rcons addSn -addnS.
Qed.

Theorem has_circuit (G : mgraph) (C : {set edge G}) :
  C != set0 -> (forall v : G, subdeg C v != 1) ->
  exists D : {set edge G}, D \subset C /\ is_circuit D.
Proof.
move=> /set0Pn[e eC] Cdeg.
case: (boolP (source e == target e)) => [/eqP loop|nloop].
- exists (eset [:: (e, false)]); split.
    by apply: eset_sub; rewrite /= eC.
  apply: (@closed_route_circuit G [:: (e, false)] (source e)).
  + by [].
  + by rewrite /= eqxx.
  + by rewrite /rlast /rhd /= -loop.
  + by rewrite /redges /=.
  + by rewrite /=.
- apply: (@has_circuit_bound G C #|G| Cdeg (source e) [:: (e, false)]).
  + rewrite /spath; apply/and4P; split.
    * by rewrite /= eqxx.
    * by rewrite /= eC.
    * by rewrite /redges /=.
    * rewrite /= andbT mem_seq1; apply/negP => /eqP h.
      by move: nloop; rewrite h /rhd /= eqxx.
  + by [].
  + by rewrite /= add1n; exact: leqnSn.
Qed.

(** ** F14: every even subgraph is partitioned by a list of circuits *)

Lemma even_circuit_decomposition_bound (G : mgraph) (n : nat) (C : {set edge G}) :
  (#|C| <= n)%N -> (forall v : G, ~~ odd (subdeg C v)) ->
  exists D : seq {set edge G},
    (forall X : {set edge G}, X \in D -> is_circuit X) /\
    (forall e : edge G, count (fun X : {set edge G} => e \in X) D = (e \in C)).
Proof.
elim: n C => [|n IH] C hn Ce.
- have C0 : C = set0 by apply/eqP; rewrite -cards_eq0 -leqn0.
  exists [::]; split => [X|e]; first by rewrite in_nil.
  by rewrite C0 inE.
- case: (boolP (C == set0)) => [/eqP C0|Cn0].
    exists [::]; split => [X|e]; first by rewrite in_nil.
    by rewrite C0 inE.
  have Cd1 : forall v : G, subdeg C v != 1.
    by move=> v; apply: contraNneq (Ce v) => ->.
  have [D [DsubC Dcirc]] := has_circuit Cn0 Cd1.
  have [Dn0 Dreg Dcon] := Dcirc.
  have Dev : forall v : G, ~~ odd (subdeg D v).
    by move=> v; case: (Dreg v) => ->.
  have hlt : (#|C :\: D| <= n)%N.
    rewrite cardsD (setIidPr DsubC).
    have hD1 : (1 <= #|D|)%N by rewrite card_gt0.
    apply: (leq_trans (leq_sub2l #|C| hD1)).
    by rewrite leq_subLR add1n.
  have Dev' : forall v : G, ~~ odd (subdeg (C :\: D) v).
    by move=> v; apply: subdeg_setD_even;
       [exact: DsubC | exact: Ce v | exact: Dev v].
  have [L [Lcirc Lcount]] := IH _ hlt Dev'.
  exists (D :: L); split.
  + by move=> X; rewrite in_cons => /orP[/eqP ->|]; [exact: Dcirc | exact: Lcirc].
  + move=> e; rewrite /= Lcount in_setD.
    case: (boolP (e \in D)) => eD; last by [].
    by rewrite (subsetP DsubC _ eD).
Qed.

Theorem even_circuit_decomposition (G : mgraph) (C : {set edge G}) :
  (forall v : G, ~~ odd (subdeg C v)) ->
  exists D : seq {set edge G},
    (forall X : {set edge G}, X \in D -> is_circuit X) /\
    (forall e : edge G, count (fun X : {set edge G} => e \in X) D = (e \in C)).
Proof. by apply: (even_circuit_decomposition_bound (leqnn #|C|)). Qed.

(** A list of even subgraphs refines into a list of circuits with the same
    per-edge multiplicities. *)
Lemma even_list_circuit_decomposition (G : mgraph) (L : seq {set edge G}) :
  (forall X : {set edge G}, X \in L -> forall v : G, ~~ odd (subdeg X v)) ->
  exists M : seq {set edge G},
    (forall Y : {set edge G}, Y \in M -> is_circuit Y) /\
    (forall e : edge G, count (fun Y : {set edge G} => e \in Y) M
                        = count (fun X : {set edge G} => e \in X) L).
Proof.
elim: L => [|X L IH] Lev; first by exists [::]; split.
have [M1 [M1c M1n]] := even_circuit_decomposition (Lev X (mem_head X L)).
have LevL : forall Y : {set edge G}, Y \in L -> forall v : G, ~~ odd (subdeg Y v).
  by move=> Y hY; apply: Lev; rewrite in_cons hY orbT.
have [M2 [M2c M2n]] := IH LevL.
exists (M1 ++ M2); split.
- by move=> Y; rewrite mem_cat => /orP[]; [exact: M1c | exact: M2c].
- by move=> e; rewrite count_cat M1n M2n.
Qed.
