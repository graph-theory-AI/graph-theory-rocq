(** * Hypergraph.conjectures.implications_U12 — implication/refutation edges for U12

    Milestone U12 has four nodes, each a finite-hypergraph OPEN conjecture stated
    in [Hypergraph.conjectures.U12]:

      - [frankls_union_closed_sets_statement]      (Frankl's union-closed sets)
      - [turans_problem_for_hypergraphs_statement]  (Turán for 3-uniform hypergraphs)
      - [are_critical_k_forests_tight_statement]    (critical k-forests are k-trees)
      - [rysers_statement]                          (Ryser: τ ≤ (r−1)ν)

    EDGE ANALYSIS (per OPG_FULL_FORMALIZATION_PLAN.md §6 — "Implication-edge spine").

    The §6 verified-literature table and the §6 candidate list contain NO edge
    whose endpoints are U12 nodes; every listed edge belongs to other milestones
    (Petersen-colouring ⟹ Berge–Fulkerson / CDC, Berge–Fulkerson ⟹ CDC,
    strong-k-CDC ⟹ CDC, 4-flow ⟺ 3-edge-colouring, …).  This is faithful to the
    mathematics: the four U12 conjectures are MUTUALLY INDEPENDENT open problems,
    connected only by the thematic label "hypergraphs & set systems" (plan §4,
    row U12).  There is no known reduction between any ordered pair:

      • Frankl's union-closed-sets conjecture concerns the element-frequency of a
        union-closed family — no structural bridge to hyperedge counts (Turán),
        Berge-acyclic forest maximality (critical k-forests) or cover/matching
        duality (Ryser).
      • Turán's 3-uniform density bound is an extremal hyperedge-count statement;
        it neither implies nor follows from any of the other three.
      • "critical k-forests are k-trees" is a Berge-acyclicity/connectivity
        statement; independent of the rest.
      • Ryser's τ ≤ (r−1)ν is a min–max cover/matching inequality (König at r=2,
        Aharoni at r=3, open for r ≥ 4); independent of the rest.

    Consequently NO verified-literature edge is schedulable here, and — by the
    edge policy (R4 / §6: "a false edge must FAIL to compile — never force it") —
    we assert NO [Theorem A_statement -> B_statement].  A relative implication
    [A_statement -> B_statement] between two of these would require either that
    [B_statement] be provable outright (it is open) or that [A_statement] be
    contradictory (each is an axiom-free, guard-faithful OPEN statement, hence not
    refutable); neither holds, so no such [Qed] is attainable without resolving an
    endpoint.

    So the U12-INTERNAL implication-edge set is EMPTY: no [@EDGE] below joins two
    U12 nodes.

    INCOMING EDGES (v2 corpus, meta/corpus_relations.json).  [rysers_statement] is
    the TARGET of one confirmed corpus relation whose source lives in this package,
    gc:e144 (arxiv:2505.05339#02 implies opg:rysers_conjecture): the
    Clow-Haxell-Mohar deletion tradeoff of
    [Hypergraph.conjectures.X6.r_partite_matching_deletion_tradeoff_statement]
    implies Ryser's conjecture.  That edge is proved below (the file's PHASE is the
    TARGET's file, U12), together with the vocabulary bridges it needs: the X6 and
    U12 hypergraph vocabularies for matchings, matching numbers and r-partite
    r-uniformity are not merely equivalent but DEFINITIONALLY EQUAL, and the three
    [x6_*_equiv_*] lemmas below record that.

    The file is axiom-free: no Axiom/Parameter/Admitted. *)

From GTBase Require Import base.
From Hypergraph.conjectures Require Import U12 X6.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Anchor: the four U12 node statements are in scope (type-check as [Prop]).
    [Check] is a pure query — it introduces no constant and no assumption. *)
Check frankls_union_closed_sets_statement : Prop.
Check turans_problem_for_hypergraphs_statement : Prop.
Check are_critical_k_forests_tight_statement : Prop.
Check rysers_statement : Prop.

(** ** Vocabulary bridges X6 <-> U12 **************************************

    The two files introduce the same three notions with the same bodies, so the
    bridges hold by conversion; they are recorded as lemmas so that any future
    drift between the two vocabularies breaks this file rather than silently
    changing the meaning of the edge below. *)

Lemma x6_matching_equiv_hg_matching (T : finType) (M E : {set {set T}}) :
  x6_matching M E <-> hg_matching M E.
Proof. by split=> H; exact: H. Qed.

Lemma x6_matching_number_equiv_is_matching_number
    (T : finType) (E : {set {set T}}) (nu : nat) :
  x6_matching_number E nu <-> is_matching_number E nu.
Proof. by split=> H; exact: H. Qed.

Lemma x6_r_partite_uniform_equiv_r_partite_uniform
    (T : finType) (r : nat) (part : T -> 'I_r) (E : {set {set T}}) :
  x6_r_partite_uniform part E <-> r_partite_uniform part E.
Proof. by split=> H; exact: H. Qed.

(** ** Helpers on covers and matchings ************************************)

(** Boolean form of [hg_cover]. *)
Definition hg_coverb (T : finType) (X : {set T}) (E : {set {set T}}) : bool :=
  [forall e in E, X :&: e != set0].

Lemma hg_coverP (T : finType) (X : {set T}) (E : {set {set T}}) :
  reflect (hg_cover X E) (hg_coverb X E).
Proof. exact: forall_inP. Qed.

(** In an r-partite r-uniform hypergraph with [r > 0] every hyperedge is
    nonempty (it has one vertex in each part), so covers exist. *)
Lemma r_partite_edge_neq0 (T : finType) (r : nat) (part : T -> 'I_r)
    (E : {set {set T}}) (j : 'I_r) :
  r_partite_uniform part E -> forall e, e \in E -> e != set0.
Proof.
move=> Hp e eE.
have /card_gt0P[v] : 0 < #|[set v in e | part v == j]| by rewrite (Hp e eE j).
by rewrite inE => /andP[ve _]; apply/set0Pn; exists v.
Qed.

(** The cover number is attained as soon as every hyperedge is nonempty. *)
Lemma is_cover_number_ex (T : finType) (E : {set {set T}}) :
  (forall e, e \in E -> e != set0) -> exists tau, is_cover_number E tau.
Proof.
move=> Hne.
have Pex : exists n, [exists X : {set T}, hg_coverb X E && (#|X| == n)].
  exists #|T|; apply/existsP; exists [set: T]; rewrite cardsT eqxx andbT.
  by apply/hg_coverP => e eE; rewrite setTI; exact: Hne.
have /ex_minnP [m Pm minm] := Pex.
case/existsP: Pm => X /andP[/hg_coverP cX /eqP cardX].
exists m; split; first by exists X.
move=> X' cX'; apply: minm.
by apply/existsP; exists X'; rewrite (introT (hg_coverP X' E) cX') eqxx.
Qed.

(** A single hyperedge is a matching, so [nu = 0] forces an edgeless hypergraph
    and hence [tau = 0]. *)
Lemma is_cover_number0 (T : finType) (E : {set {set T}}) (tau : nat) :
  is_matching_number E 0 -> is_cover_number E tau -> tau = 0.
Proof.
move=> [_ Hmax] [_ Hmin].
have E0 : E = set0.
  apply/eqP; rewrite -subset0; apply/subsetP => e eE.
  have : #|[set e]| <= 0.
    apply: Hmax; split; first by rewrite sub1set.
    by move=> f g; rewrite !inE => /eqP-> /eqP->; rewrite eqxx.
  by rewrite cards1.
have cov0 : hg_cover set0 E by rewrite E0 => e; rewrite inE.
by apply/eqP; rewrite -leqn0 -(cards0 T); exact: Hmin.
Qed.

(** ** gc:e144 -- the deletion tradeoff implies Ryser's conjecture ********)

(** The induction of the corpus argument, with the matching number bounded by an
    external parameter [n] so that the recursive call (on a matching number that
    dropped by at least [k >= 1]) is a structural one. *)
Lemma ryser_by_deletion_aux
    (H : r_partite_matching_deletion_tradeoff_statement) (n : nat) :
  forall (nu : nat), nu <= n ->
  forall (r : nat) (T : finType) (part : T -> 'I_r) (E : {set {set T}}) (tau : nat),
    1 < r -> r_partite_uniform part E ->
    is_matching_number E nu -> is_cover_number E tau ->
    tau <= (r - 1) * nu.
Proof.
elim: n => [|n IH] nu Hn r T part E tau r1 Hp Hnu Htau.
  have nu0 : nu = 0 by apply/eqP; rewrite -leqn0.
  rewrite nu0 in Hnu; rewrite nu0 muln0.
  by rewrite (is_cover_number0 Hnu Htau).
have [nu0|nu_gt0] := posnP nu.
  rewrite nu0 in Hnu; rewrite nu0 muln0.
  by rewrite (is_cover_number0 Hnu Htau).
(* [E] has an edge: a maximum matching is nonempty *)
have EneS : E != set0.
  have [[M [[MsubE _] cardM]] _] := Hnu; apply/set0Pn.
  have /card_gt0P[e eM] : 0 < #|M| by rewrite cardM.
  by exists e; exact: (subsetP MsubE).
have r0 : 0 < r := ltnW r1.
pose j0 := Ordinal r0.
(* the tradeoff step *)
have [k [X [k1 [kr [cardX [nu' [Hnu' Hred]]]]]]] := H r T part E nu r1 EneS Hp Hnu.
pose E' := x6_delete_vertices E X.
have Hp' : r_partite_uniform part E'.
  by move=> e; rewrite /E' inE => /andP[eE _]; exact: Hp.
have [tau' Htau'] := is_cover_number_ex (r_partite_edge_neq0 j0 Hp').
have nu'n : nu' <= n.
  rewrite -ltnS; apply: (leq_trans _ Hn); rewrite -addn1.
  by apply: (leq_trans _ Hred); rewrite leq_add2l.
have IHb := IH nu' nu'n r T part E' tau' r1 Hp' Hnu' Htau'.
(* a cover of [E] from the deleted set and a minimum cover of [E'] *)
have [[X' [cX' cardX']] _] := Htau'.
have cov : hg_cover (X :|: X') E.
  move=> e eE; have [dis|ndis] := boolP [disjoint e & X].
    have eE' : e \in E' by rewrite /E' inE eE dis.
    case/set0Pn: (cX' e eE') => v; rewrite inE => /andP[vX' ve].
    by apply/set0Pn; exists v; rewrite !inE ve andbT vX' orbT.
  move: ndis; rewrite -setI_eq0 => /set0Pn[v]; rewrite inE => /andP[ve vX].
  by apply/set0Pn; exists v; rewrite !inE ve andbT vX.
have taule : tau <= #|X| + #|X'|.
  have [_ Hmin] := Htau; apply: (leq_trans (Hmin _ cov)).
  by rewrite cardsU; exact: leq_subr.
apply: (leq_trans taule); rewrite cardX cardX'.
apply: (leq_trans (leq_add (leqnn (k * (r - 1))) IHb)).
rewrite mulnC -mulnDr; apply: leq_mul => //.
by rewrite addnC; exact: Hred.
Qed.

(*@EDGE from=r_partite_matching_deletion_tradeoff_statement to=rysers_statement kind=implies status=verified proof=r_partite_matching_deletion_tradeoff_implies_rysers cite="gc:e144" note="Induction on the matching number nu, exactly the corpus argument. nu = 0 forces E = set0 (a single hyperedge is a matching), hence tau = 0. For nu > 0 the tradeoff gives 1 <= k <= r-1 and a set X of k(r-1) vertices with nu(E - X) = nu' and nu' + k <= nu; E - X is still r-partite r-uniform, so by induction its cover number tau' satisfies tau' <= (r-1)nu', and X together with a minimum cover of E - X covers E, whence tau <= k(r-1) + (r-1)nu' = (r-1)(nu'+k) <= (r-1)nu. The X6 and U12 vocabularies for matching / matching number / r-partite r-uniformity are definitionally equal (bridges x6_matching_equiv_hg_matching, x6_matching_number_equiv_is_matching_number, x6_r_partite_uniform_equiv_r_partite_uniform); the cover number of the deleted hypergraph is constructed by is_cover_number_ex (every hyperedge has one vertex per part, hence is nonempty, so covers exist and a minimum one is picked by ex_minn)." *)
Theorem r_partite_matching_deletion_tradeoff_implies_rysers :
  r_partite_matching_deletion_tradeoff_statement -> rysers_statement.
Proof.
move=> H r T part E nu tau r1 Hp Hnu Htau.
exact: (ryser_by_deletion_aux H (leqnn nu) r1 Hp Hnu Htau).
Qed.
