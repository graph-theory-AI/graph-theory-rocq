(** * Topological.conjectures.grounding_X228 — grounding lemmas for wave X228.

    Qed-closed, axiom-free sanity results for the two X228 statements
    [random_embedding_expected_faces_third_statement] and
    [random_embedding_expected_faces_linear_statement], and for the finite
    rotation-system enumeration they are built on.

    Contents:
      - BRIDGE to [GTBase.surface]: every member of [x228_rotation_system G] is
        a [surface_embedding] with the same face count, so the boolean subset of
        [{perm surface_dart G}] enumerates exactly the objects surface.v models
        ([x228_rotation_embedding]).  This is the "wrong object" guard.
      - NON-VACUITY: a graph of maximum degree at most one has exactly one
        rotation system (the identity), ['K_2] has a dart, every rotation system
        of a graph with a dart has at least one face, hence
        [0 < x228_total_faces 'K_2] and [x228_nrot 'K_2 = 1]: both statements
        constrain honest, nonzero quantities.
      - GUARD HAS TEETH: dropping the additive "+1" of Conjecture 4 (the [+3] of
        the cleared form) makes it FALSE, and the constant of the O(n) row cannot
        be 0.
      - STRUCTURAL LAWS: a face count never exceeds the number of darts, and a
        graph with no vertex has no face at all. *)

From GTBase Require Import base.
From mathcomp Require Import fingroup perm.
From Topological.conjectures Require Import X228.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Orbits of the identity permutation *)

Lemma x228_porbit1 (T : finType) (x : T) : porbit 1 x = [set x].
Proof.
apply/setP => y; rewrite inE; apply/idP/idP => [|/eqP ->]; last exact: porbit_id.
by case/porbitP => i ->; rewrite expg1n perm1.
Qed.

(** ** Graphs of maximum degree at most one *)

(** In a graph where every vertex has at most one neighbour, a dart is
    determined by its source. *)
Lemma x228_dart_uniq (G : sgraph) :
  (forall x y z : G, x -- y -> x -- z -> y = z) ->
  forall d d' : surface_dart G, (sval d').1 = (sval d).1 -> d' = d.
Proof.
move=> H [[x y] py] [[x' y'] py'] /= exx.
apply: val_inj => /=; move: py'; rewrite exx => py'.
by rewrite (H x y' y py' py).
Qed.

(** NON-VACUITY of [x228_rotation_system]: such a graph has the identity as a
    rotation system. *)
Lemma x228_id_rotation (G : sgraph) :
  (forall x y z : G, x -- y -> x -- z -> y = z) ->
  (1%g : {perm surface_dart G}) \in x228_rotation_system G.
Proof.
move=> H; rewrite inE /x228_rotationb; apply/andP; split; apply/forallP => d.
  by rewrite perm1.
rewrite x228_porbit1; apply/eqP; apply/setP => d'; rewrite !inE.
apply/idP/idP => [/eqP ->|/eqP /(x228_dart_uniq H) ->]; by rewrite eqxx.
Qed.

(** ... and it is the ONLY one: the number of orientable embeddings of a graph
    of maximum degree at most one is 1. *)
Lemma x228_rotation_system_deg1 (G : sgraph) :
  (forall x y z : G, x -- y -> x -- z -> y = z) ->
  x228_rotation_system G = [set 1%g].
Proof.
move=> H; apply/setP => p; rewrite [in RHS]inE.
apply/idP/idP => [|/eqP ->]; last exact: x228_id_rotation.
rewrite inE => /andP[/forallP H1 _]; apply/eqP.
(* [permP] and [perm1] are shadowed by the seq-permutation lemmas of path.v,
   hence the qualified names. *)
apply/perm.permP => d.
by rewrite perm.perm1; apply: (x228_dart_uniq H); apply/eqP; exact: H1.
Qed.

Lemma x228_nrot_deg1 (G : sgraph) :
  (forall x y z : G, x -- y -> x -- z -> y = z) -> x228_nrot G = 1.
Proof. by move=> H; rewrite /x228_nrot x228_rotation_system_deg1 // cards1. Qed.

(** ** Structural laws for the face count *)

(** A face is an orbit of darts, so there are never more faces than darts. *)
Lemma x228_faces_leq_darts (G : sgraph) (p : {perm surface_dart G}) :
  x228_faces p <= #|{: surface_dart G}|.
Proof. exact: leq_imset_card. Qed.

(** As soon as the graph has a dart, every rotation system has a face. *)
Lemma x228_faces_gt0 (G : sgraph) (p : {perm surface_dart G})
    (d : surface_dart G) : 0 < x228_faces p.
Proof.
rewrite /x228_faces card_gt0; apply/set0Pn.
by exists (porbit (p * @surface_edge_perm G)%g d); apply/imsetP; exists d.
Qed.

(** A graph with no vertex has no dart and hence no face. *)
Lemma x228_faces0 (G : sgraph) (p : {perm surface_dart G}) :
  #|G| = 0 -> x228_faces p = 0.
Proof.
move=> c0; apply/eqP; rewrite /x228_faces cards_eq0; apply/eqP.
apply/setP => A; rewrite !inE; apply/negbTE; apply/negP => /imsetP[d _ _].
by have := card0_eq c0 (sval d).1; rewrite inE.
Qed.

(** ... so its total face count over all rotation systems is 0. *)
Lemma x228_total_faces0 (G : sgraph) : #|G| = 0 -> x228_total_faces G = 0.
Proof.
by move=> c0; rewrite /x228_total_faces big1 // => p _; exact: x228_faces0.
Qed.

(** ** Bridge to [GTBase.surface]: the enumerated objects are the embeddings *)

(** Every rotation system in the boolean sense of [X228.v] IS a
    [surface_embedding] of base/theories/surface.v, with the same number of
    faces.  So [x228_total_faces] really averages the face counts of the
    orientable embeddings of the graph — the statements are about the right
    object. *)
Lemma x228_rotation_embedding (G : sgraph) (p : {perm surface_dart G}) :
  p \in x228_rotation_system G ->
  exists E : surface_embedding G, surface_embedding_faces E = x228_faces p.
Proof.
rewrite inE => /andP[/forallP H1 /forallP H2].
by exists (@SurfaceEmbedding G p (fun d => eqP (H1 d)) (fun d => eqP (H2 d))).
Qed.

(** ** The concrete witness ['K_2] *)

Lemma x228_card2_eq (T : finType) (x y z : T) :
  #|T| = 2 -> x != y -> x != z -> y = z.
Proof.
move=> cT xy xz.
have c1 : #|[set: T] :\ x| = 1.
  by have := cardsD1 x [set: T]; rewrite cardsT cT inE /= => -[].
have /cards1P[a Ha] : #|[set: T] :\ x| == 1 by rewrite c1.
have yin : y \in [set: T] :\ x by rewrite !inE eq_sym xy.
have zin : z \in [set: T] :\ x by rewrite !inE eq_sym xz.
by move: yin zin; rewrite Ha !inE => /eqP -> /eqP ->.
Qed.

Lemma x228_K2_deg1 (x y z : 'K_2) : x -- y -> x -- z -> y = z.
Proof. by move=> xy xz; apply: (@x228_card2_eq _ x) => //; rewrite card_ord. Qed.

Lemma x228_K2_dart : surface_dart 'K_2.
Proof. by exists (ord0, @Ordinal 2 1 isT). Qed.

(** NON-VACUITY of both statements: ['K_2] has exactly one rotation system, and
    that embedding has at least one face — so neither statement is an assertion
    about empty sums. *)
Lemma x228_nrot_K2 : x228_nrot 'K_2 = 1.
Proof. by rewrite x228_nrot_deg1 //; exact: x228_K2_deg1. Qed.

Lemma x228_total_faces_K2_gt0 : 0 < x228_total_faces 'K_2.
Proof.
rewrite /x228_total_faces (bigD1 1%g) /=; last exact: x228_id_rotation x228_K2_deg1.
by rewrite addn_gt0 (x228_faces_gt0 _ x228_K2_dart).
Qed.

(** ** Guards have teeth *)

(** TEETH #1 (Conjecture 4, arxiv:2202.07746#00): the additive "+ 1" of
    [E[F] <= n/3 + 1] is load-bearing.  Dropping it — i.e. asking for
    [E[F] <= n/3], the cleared [3 * total <= n * nrot] — is FALSE already for
    ['K_2], where the left side is at least 3 and the right side is 2. *)
Lemma x228_third_without_plus1_fails :
  ~ (forall G : sgraph, 3 * x228_total_faces G <= #|G| * x228_nrot G).
Proof.
move=> /(_ 'K_2); rewrite x228_nrot_K2 muln1 card_ord.
case: (x228_total_faces 'K_2) x228_total_faces_K2_gt0 => [|n] // _.
by rewrite mulnS.
Qed.

(** TEETH #2 (Conjecture 1, arxiv:2103.05036#00): the existential constant
    cannot be 0, so the statement is not satisfiable by a degenerate witness. *)
Lemma x228_linear_c0_fails :
  ~ (forall G : sgraph, x228_total_faces G <= 0 * #|G| * x228_nrot G).
Proof.
move=> /(_ 'K_2); rewrite mul0n mul0n leqn0 => /eqP E.
by move: x228_total_faces_K2_gt0; rewrite E.
Qed.

Print Assumptions random_embedding_expected_faces_third_statement.
Print Assumptions random_embedding_expected_faces_linear_statement.
Print Assumptions x228_rotation_embedding.
Print Assumptions x228_third_without_plus1_fails.
Print Assumptions x228_linear_c0_fails.
