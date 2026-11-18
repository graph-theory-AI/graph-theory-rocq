(** * Topological.conjectures.implications_X228 — wave X228 dependency-graph EDGES

    The two X228 nodes are the random-embedding rows of arXiv:2202.07746
    (Conjecture 4, [E[F] <= n/3 + 1]) and arXiv:2103.05036 (Conjecture 1,
    [E[F] = O(n)]).  The corpus records one confirmed relation between them,
    gc:e125 (arxiv:2202.07746#00 implies arxiv:2103.05036#00): the sharp bound
    [n/3 + 1] is in particular linear in [n].

    STATE OF THE EDGE (verified 2026-11-18; re-audited 2026-09-24).  The two bodies
    are NOT guarded the same way:

      - [random_embedding_expected_faces_third_statement] quantifies over
        CONNECTED graphs only ([connected [set: G]], guard added 2026-09-23: the
        additive "+1" is per connected component, and without the guard the body
        is refuted by four disjoint edges);
      - [random_embedding_expected_faces_linear_statement] quantifies over ALL
        finite simple graphs (its own Notes argue that the unguarded form is
        equivalent to the source, because rotation systems multiply and face
        counts add over connected components; Section E125 below proves it).

    So the edge is not a direct weakening: the source says nothing about a
    disconnected [G], and the target must bound such a [G] too.  The connected half
    is [x228_third_implies_linear_connected]: the source's bound gives the target's
    inequality with the explicit constant [c = 4] for every connected graph, empty
    graph included.  Section E125 proves the reduction of a graph to a vertex set
    that no edge leaves and its complement: the rotation systems are the pairs of
    rotations on the two dart sets ([e125_rot_pairs], [e125_nrot_split]), the faces
    add ([e125_faces_split], [e125_total_split]), and each part is the set of
    rotation systems of the induced subgraph ([e125_transport]).  Strong induction
    on the number of vertices then proves the edge with [c = 4]:
    [e125_random_embedding_expected_faces_third_implies_random_embedding_expected_faces_linear].

    The file is axiom-free: no Axiom/Parameter/Admitted, and every theorem is closed
    under the global context. *)

From GTBase Require Import base.
From mathcomp Require Import fingroup perm action.
From Topological.conjectures Require Import X228 grounding_X228.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The connected half of gc:e125, with the explicit constant [c = 4]: on a
    connected graph the source's cleared bound [3 * total <= (n + 3) * nrot]
    yields the target's [total <= 4 * n * nrot].  (For [n = 0] the total face
    count is [0] by [x228_total_faces0]; for [n >= 1], [n + 3 <= 4 * n].) *)
Lemma x228_third_implies_linear_connected :
  random_embedding_expected_faces_third_statement ->
  forall G : sgraph, connected [set: G] ->
    x228_total_faces G <= 4 * #|G| * x228_nrot G.
Proof.
move=> H G cG; have [n0|n0] := posnP #|G|.
  by rewrite (x228_total_faces0 n0).
have step : x228_total_faces G <= 3 * x228_total_faces G by apply: leq_pmull.
apply: (leq_trans step).
apply: (leq_trans (H G cG)); apply: leq_mul => //.
rewrite mulSn leq_add2l; apply: leq_pmulr; exact: n0.
Qed.

Section E125.

Definition e125_dartset (G : sgraph) (S : {set G}) : {set surface_dart G} :=
  [set d | (sval d).1 \in S].

Definition e125_rot_on (G : sgraph) (S : {set G}) : {set {perm surface_dart G}} :=
  [set p : {perm surface_dart G} | [forall d, (d \notin e125_dartset S) ==> (p d == d)] &&
           [forall d, (d \in e125_dartset S) ==>
              ((sval (p d)).1 == (sval d).1) && (porbit p d == [set d' | (sval d').1 == (sval d).1])]].

Definition e125_faces_on (G : sgraph) (D : {set surface_dart G}) (p : {perm surface_dart G}) : nat :=
  #|[set O in porbits (p * surface_edge_perm G)%g | O \subset D]|.

Lemma e125_edge_permE (G : sgraph) (d : surface_dart G) : surface_edge_perm G d = surface_rev_dart d.
Proof. by rewrite /surface_edge_perm permE. Qed.

Lemma e125_dartset_rev (G : sgraph) (S : {set G}) :
  (forall x y : G, x -- y -> (x \in S) = (y \in S)) ->
  forall d, (surface_rev_dart d \in e125_dartset S) = (d \in e125_dartset S).
Proof.
move=> cS [[x y] xy]; rewrite !inE /=; exact: esym (cS x y xy).
Qed.

Lemma e125_dartsetC (G : sgraph) (S : {set G}) : e125_dartset (~: S) = ~: e125_dartset S.
Proof. by apply/setP => d; rewrite !inE. Qed.

(** Two permutations that agree on a set stable under the second have the same orbits from its points. *)
Lemma e125_porbit_agree (T : finType) (r s : {perm T}) (A : {set T}) (x : T) :
  x \in A -> {in A, forall y, s y \in A} -> {in A, r =1 s} -> porbit r x = porbit s x.
Proof.
move=> xA sA rs.
have H i : (r ^+ i)%g x = (s ^+ i)%g x /\ (s ^+ i)%g x \in A.
  elim: i => [|i [IH1 IH2]]; first by rewrite !expg0 !perm1.
  by rewrite !expgSr !permM IH1 rs // sA.
apply/setP => y; apply/porbitP/porbitP => -[i ->]; exists i; by rewrite (H i).1.
Qed.

(** A rotation system keeps every dart's source, so it stabilises the darts leaving any vertex set. *)
Lemma e125_rot_stab (G : sgraph) (S : {set G}) (p : {perm surface_dart G}) :
  p \in x228_rotation_system G -> p \in 'N(e125_dartset S | 'P)%g.
Proof.
rewrite inE /x228_rotationb => /andP[/forallP H1 _]; apply/astabsP => d.
by rewrite /= /aperm !inE (eqP (H1 d)).
Qed.

(** L3: its restriction to the darts leaving S is a rotation on S. *)
Lemma e125_rot_restr (G : sgraph) (S : {set G}) (p : {perm surface_dart G}) :
  p \in x228_rotation_system G -> restr_perm (e125_dartset S) p \in e125_rot_on S.
Proof.
move=> pr; have N := e125_rot_stab S pr.
move: pr; rewrite inE /x228_rotationb => /andP[/forallP H1 /forallP H2].
rewrite inE; apply/andP; split; apply/forallP => d; apply/implyP => dD.
  apply/eqP; exact: out_perm (restr_perm_on _ p) dD.
rewrite (restr_permE N dD) (eqP (H1 d)) eqxx /=.
rewrite (@e125_porbit_agree _ _ p (e125_dartset S)) //; last by move=> y yD; exact: restr_permE N yD.
by move=> y yD; move/astabsP: N => N; rewrite -(N y) in yD.
Qed.

(** The two parts of a rotation on S and on its complement. *)
Lemma e125_rot_onP (G : sgraph) (S : {set G}) (p : {perm surface_dart G}) :
  p \in e125_rot_on S ->
  [/\ forall d, d \notin e125_dartset S -> p d = d,
      forall d, d \in e125_dartset S -> p d \in e125_dartset S /\ (sval (p d)).1 = (sval d).1 &
      forall d, d \in e125_dartset S -> porbit p d = [set d' | (sval d').1 == (sval d).1]].
Proof.
rewrite inE => /andP[/forallP F /forallP R]; split.
- by move=> d dD; apply/eqP; move: (F d); rewrite dD.
- move=> d dD; move: (R d); rewrite dD => /andP[/eqP s _]; split => //.
  by move: dD; rewrite !inE s.
- by move=> d dD; move: (R d); rewrite dD => /andP[_ /eqP].
Qed.

(** L4: a rotation on S times a rotation on its complement is a rotation system. *)
Lemma e125_rot_mul (G : sgraph) (S : {set G}) (p1 p2 : {perm surface_dart G}) :
  p1 \in e125_rot_on S -> p2 \in e125_rot_on (~: S) -> (p1 * p2)%g \in x228_rotation_system G.
Proof.
move=> /e125_rot_onP[F1 R1 O1] /e125_rot_onP[F2 R2 O2]; rewrite e125_dartsetC in F2 R2 O2.
set D := e125_dartset S in F1 R1 O1 F2 R2 O2 *.
have M1 d : d \in D -> (p1 * p2)%g d = p1 d.
  by move=> dD; rewrite permM F2 // inE negbK; exact: (R1 d dD).1.
have M2 d : d \notin D -> (p1 * p2)%g d = p2 d by move=> dD; rewrite permM F1.
rewrite inE /x228_rotationb; apply/andP; split; apply/forallP => d; case dD: (d \in D).
- by rewrite M1 // (R1 d dD).2.
- have dC : d \in ~: D by rewrite inE dD.
  by rewrite M2 ?dD // (R2 d dC).2.
- rewrite (@e125_porbit_agree _ _ p1 D) // ?O1 //.
  by move=> y /R1 [].
- have dC : d \in ~: D by rewrite inE dD.
  rewrite (@e125_porbit_agree _ _ p2 (~: D)) // ?O2 //.
    by move=> y /R2 [].
  by move=> y; rewrite inE => yD; exact: M2.
Qed.

(** The product acts as its first factor on the darts leaving S and as its second elsewhere. *)
Lemma e125_mulE (G : sgraph) (S : {set G}) (p1 p2 : {perm surface_dart G}) :
  p1 \in e125_rot_on S -> p2 \in e125_rot_on (~: S) ->
  forall d, (p1 * p2)%g d = if d \in e125_dartset S then p1 d else p2 d.
Proof.
move=> /e125_rot_onP[F1 R1 _] /e125_rot_onP[F2 _ _] d; rewrite e125_dartsetC in F2.
rewrite permM; case: ifP => dD; last by rewrite F1 ?dD.
by rewrite F2 // inE negbK; exact: (R1 d dD).1.
Qed.

(** L5: a rotation system is the product of its restrictions to the two parts. *)
Lemma e125_rot_decomp (G : sgraph) (S : {set G}) (p : {perm surface_dart G}) :
  p \in x228_rotation_system G ->
  p = (restr_perm (e125_dartset S) p * restr_perm (e125_dartset (~: S)) p)%g.
Proof.
move=> pr; apply/perm.permP => d; rewrite (e125_mulE (e125_rot_restr S pr) (e125_rot_restr (~: S) pr)).
case: ifP => dD; first by rewrite (restr_permE (e125_rot_stab S pr) dD).
by rewrite (restr_permE (e125_rot_stab (~: S) pr)) // e125_dartsetC inE dD.
Qed.

(** The rotation systems are the products of the pairs: the map is injective on the pairs and onto. *)
Lemma e125_rot_pairs (G : sgraph) (S : {set G}) :
  x228_rotation_system G =
    [set (q.1 * q.2)%g | q in setX (e125_rot_on S) (e125_rot_on (~: S))] /\
  {in setX (e125_rot_on S) (e125_rot_on (~: S)) &,
    injective (fun q : {perm surface_dart G} * {perm surface_dart G} => (q.1 * q.2)%g)}.
Proof.
split.
  apply/setP => p; apply/idP/imsetP => [pr|[[p1 p2]]].
    exists (restr_perm (e125_dartset S) p, restr_perm (e125_dartset (~: S)) p); last exact: e125_rot_decomp.
    by rewrite inE /= !e125_rot_restr.
  move=> /[!in_setX] /= /andP[h1 h2] ->.
  exact: e125_rot_mul h1 h2.
move=> [p1 p2] [q1 q2] /[!in_setX] /= /andP[h1 h2] /andP[k1 k2] E.
have M1 := e125_mulE h1 h2; have M2 := e125_mulE k1 k2.
have := e125_rot_onP h1; have := e125_rot_onP h2; have := e125_rot_onP k1; have := e125_rot_onP k2.
rewrite !e125_dartsetC => -[F4 _ _] [F3 _ _] [F2 _ _] [F1 _ _].
congr (_, _); apply/perm.permP => d; case dD: (d \in e125_dartset S).
- by have := M1 d; rewrite E M2 dD => <-.
- by rewrite F1 ?dD // F3 ?dD.
- have dC : d \notin ~: e125_dartset S by rewrite inE negbK dD.
  by rewrite (F2 d dC) (F4 d dC).
- by have := M1 d; rewrite E M2 dD => <-.
Qed.

(** L6: the number of rotation systems is the product of the numbers of rotations on the two parts. *)
Lemma e125_nrot_split (G : sgraph) (S : {set G}) :
  x228_nrot G = #|e125_rot_on S| * #|e125_rot_on (~: S)|.
Proof. by have [E inj] := e125_rot_pairs S; rewrite /x228_nrot E (card_in_imset inj) cardsX. Qed.

(** An orbit started in a set stable under the permutation stays in it. *)
Lemma e125_porbit_sub (T : finType) (s : {perm T}) (A : {set T}) (x : T) :
  x \in A -> {in A, forall y, s y \in A} -> porbit s x \subset A.
Proof.
move=> xA sA; apply/subsetP => y /porbitP[i ->].
elim: i => [|i IH]; first by rewrite expg0 perm1.
by rewrite expgSr permM sA.
Qed.

(** L7: the faces of a product are the faces of each factor inside its part (S closed). *)
Lemma e125_faces_split (G : sgraph) (S : {set G}) (p1 p2 : {perm surface_dart G}) :
  (forall x y : G, x -- y -> (x \in S) = (y \in S)) ->
  p1 \in e125_rot_on S -> p2 \in e125_rot_on (~: S) ->
  x228_faces (p1 * p2)%g = e125_faces_on (e125_dartset S) p1 + e125_faces_on (e125_dartset (~: S)) p2.
Proof.
move=> cS h1 h2; have M := e125_mulE h1 h2.
have := e125_rot_onP h1; have := e125_rot_onP h2; rewrite e125_dartsetC => -[F2 R2 _] [F1 R1 _].
rewrite /e125_faces_on /x228_faces.
set D := e125_dartset S in M F1 R1 F2 R2 *; set e := surface_edge_perm G.
have eD d : (e d \in D) = (d \in D) by rewrite /e e125_edge_permE e125_dartset_rev.
set r := ((p1 * p2) * e)%g; set r1 := (p1 * e)%g; set r2 := (p2 * e)%g.
have s1 : {in D, forall y, r1 y \in D} by move=> y yD; rewrite /r1 permM eD; exact: (R1 y yD).1.
have s2 : {in ~: D, forall y, r2 y \in ~: D}.
  by move=> y yD; rewrite /r2 permM in_setC eD -in_setC; exact: (R2 y yD).1.
have a1 : {in D, r =1 r1} by move=> y yD; rewrite /r /r1 [LHS]permM [RHS]permM M yD.
have a2 : {in ~: D, r =1 r2}.
  by move=> y; rewrite inE => yD; rewrite /r /r2 [LHS]permM [RHS]permM M (negbTE yD).
have E : porbits r = [set O in porbits r1 | O \subset D] :|: [set O in porbits r2 | O \subset ~: D].
  apply/setP => O; apply/imsetP/setUP => [[x _ ->]|[|]].
  - case xD: (x \in D).
      left; rewrite inE (e125_porbit_agree xD s1 a1) (e125_porbit_sub xD s1) andbT.
      by apply/imsetP; exists x.
    have xC : x \in ~: D by rewrite inE xD.
    right; rewrite inE (e125_porbit_agree xC s2 a2) (e125_porbit_sub xC s2) andbT.
    by apply/imsetP; exists x.
  - rewrite inE => /andP[/imsetP[x _ ->] sub]; exists x => //.
    have xD : x \in D := subsetP sub x (porbit_id r1 x).
    by rewrite (e125_porbit_agree xD s1 a1).
  - rewrite inE => /andP[/imsetP[x _ ->] sub]; exists x => //.
    have xC : x \in ~: D := subsetP sub x (porbit_id r2 x).
    by rewrite (e125_porbit_agree xC s2 a2).
have I : [set O in porbits r1 | O \subset D] :&: [set O in porbits r2 | O \subset ~: D] = set0.
  apply/setP => O; rewrite !inE; apply/negbTE/negP => /andP[/andP[/imsetP[x _ ->] sub1] /andP[_ sub2]].
  have := subsetP sub2 x (porbit_id r1 x); rewrite inE (subsetP sub1 x (porbit_id r1 x)) //.
by rewrite E cardsU I cards0 subn0.
Qed.

(** L8: the total face count of G from the two parts (S closed). *)
Lemma e125_total_split (G : sgraph) (S : {set G}) :
  (forall x y : G, x -- y -> (x \in S) = (y \in S)) ->
  x228_total_faces G =
    (\sum_(p in e125_rot_on S) e125_faces_on (e125_dartset S) p) * #|e125_rot_on (~: S)| +
    #|e125_rot_on S| * \sum_(p in e125_rot_on (~: S)) e125_faces_on (e125_dartset (~: S)) p.
Proof.
move=> cS; have [E inj] := e125_rot_pairs S.
rewrite /x228_total_faces E (big_imset _ inj) /=.
set A := e125_rot_on S; set B := e125_rot_on (~: S).
set f := e125_faces_on (e125_dartset S); set g := e125_faces_on (e125_dartset (~: S)).
rewrite (eq_bigr (fun i => f i.1 + g i.2)); last first.
2: by move=> [p1 p2]; rewrite in_setX => /andP[h1 h2]; exact: e125_faces_split.
rewrite big_split /=.
have SX (F : {perm surface_dart G} -> {perm surface_dart G} -> nat) :
    \sum_(i in setX A B) F i.1 i.2 = \sum_(a in A) \sum_(b in B) F a b.
  by rewrite pair_big; apply: eq_bigl => -[a b]; rewrite in_setX.
have -> : \sum_(i in setX A B) f i.1 = \sum_(a in A) \sum_(b in B) f a by exact: (SX (fun a _ => f a)).
have -> : \sum_(i in setX A B) g i.2 = \sum_(a in A) \sum_(b in B) g b by exact: (SX (fun _ b => g b)).
congr (_ + _); last by rewrite sum_nat_const.
rewrite big_distrl /=; apply: eq_bigr => a _; by rewrite sum_nat_const mulnC.
Qed.

(** An injection intertwining two permutations maps the orbits of the first onto those of the second. *)
Lemma e125_porbit_conj (T1 T2 : finType) (phi : T1 -> T2) (s1 : {perm T1}) (s2 : {perm T2}) (x : T1) :
  (forall y, s2 (phi y) = phi (s1 y)) -> porbit s2 (phi x) = phi @: porbit s1 x.
Proof.
move=> H; have P i : (s2 ^+ i)%g (phi x) = phi ((s1 ^+ i)%g x).
  by elim: i => [|i IH]; rewrite ?expg0 ?perm1 // !expgSr !permM IH H.
apply/setP => y; apply/porbitP/imsetP => [[i ->]|[z /porbitP[i ->] ->]].
  by exists ((s1 ^+ i)%g x); [apply/porbitP; exists i | rewrite P].
by exists i; rewrite P.
Qed.

(** Extension by the identity along an injection [phi] with a partial inverse [lift]: injective, it conjugates
    through [phi], fixes the points outside the image, and every permutation fixing those points is one. *)
Lemma e125_perm_ext (T1 T2 : finType) (phi : T1 -> T2) (lift : T2 -> option T1) :
  (forall x, lift (phi x) = Some x) -> (forall y x, lift y = Some x -> phi x = y) ->
  exists ext : {perm T1} -> {perm T2},
    [/\ injective ext,
        forall q x, ext q (phi x) = phi (q x),
        forall q y, lift y = None -> ext q y = y &
        forall p : {perm T2}, (forall y, lift y = None -> p y = y) -> exists q, ext q = p].
Proof.
move=> liftK liftV.
have phi_inj : injective phi by move=> a b E; have := liftK a; rewrite E liftK => -[].
pose f (q : {perm T1}) y := if lift y is Some x then phi (q x) else y.
have f_inj q : injective (f q).
  move=> y1 y2; rewrite /f.
  case E1: (lift y1) => [x1|]; case E2: (lift y2) => [x2|] => E.
  - by rewrite -(liftV _ _ E1) -(liftV _ _ E2) (perm_inj (phi_inj _ _ E)).
  - by move: E2; rewrite -E liftK.
  - by move: E1; rewrite E liftK.
  - exact: E.
exists (fun q => perm (f_inj q)); split.
- move=> q1 q2 E; apply/perm.permP => x; apply: (phi_inj _ _).
  by have := congr1 (fun r : {perm T2} => r (phi x)) E; rewrite /= !permE /f liftK.
- by move=> q x; rewrite permE /f liftK.
- by move=> q y Ly; rewrite permE /f Ly.
move=> p fixp.
have pim x : lift (p (phi x)) != None.
  apply/eqP => E; have := fixp _ E => /perm_inj E'.
  by move: E; rewrite E' liftK.
pose g x := if lift (p (phi x)) is Some x' then x' else x.
have gE x : phi (g x) = p (phi x).
  rewrite /g; case E: (lift (p (phi x))) => [x'|]; first exact: liftV E.
  by move: (pim x); rewrite E.
have g_inj : injective g by move=> a b E; apply: phi_inj; apply: (@perm_inj _ p); rewrite -!gE E.
exists (perm g_inj); apply/perm.permP => y; rewrite permE /f.
case Ly: (lift y) => [x|]; last by rewrite fixp.
by rewrite permE gE (liftV _ _ Ly).
Qed.

(** L9-L10 transport: the darts of induced S are the darts leaving S (S closed); extending a permutation of
    them by the identity maps the rotation systems of induced S onto the rotations on S and keeps the faces. *)
Lemma e125_transport (G : sgraph) (S : {set G}) :
  (forall x y : G, x -- y -> (x \in S) = (y \in S)) ->
  exists ext : {perm surface_dart (induced S)} -> {perm surface_dart G},
    [/\ injective ext,
        ext @: x228_rotation_system (induced S) = e125_rot_on S &
        forall q, x228_faces q = e125_faces_on (e125_dartset S) (ext q)].
Proof.
move=> cS.
pose phi (d : surface_dart (induced S)) : surface_dart G :=
  exist (fun p : G * G => p.1 -- p.2) (val (sval d).1, val (sval d).2) (svalP d).
pose lift (d : surface_dart G) : option (surface_dart (induced S)) :=
  if insub (sval d).1 is Some a then (if insub (sval d).2 is Some b then insub (a, b) else None) else None.
have insV (a : induced S) : insub (val a) = Some a.
  by rewrite (insubT (mem S) (valP a)); congr Some; apply: val_inj.
have liftK x : lift (phi x) = Some x.
  case: x => [[a b] ab]; rewrite /lift /phi /= !insV.
  by rewrite (insubT (fun p : induced S * induced S => p.1 -- p.2) ab).
have liftV y x : lift y = Some x -> phi x = y.
  case: y => [[u v] uv]; rewrite /lift /=.
  case: insubP => [a aS ea|//]; case: insubP => [b bS eb|//]; case: insubP => [e eP ee|//] [<-].
  by apply: val_inj; rewrite /= ee /= ea eb.
have imD y : (y \in e125_dartset S) = (lift y != None).
  case: y => [[u v] uv]; rewrite inE /lift /=.
  case: insubP => [a aS ea|/negbTE ->//]; case: insubP => [b bS eb|/negP vS].
    rewrite aS (insubT (fun p : induced S * induced S => p.1 -- p.2)) //=.
    by move: uv; rewrite /= -ea -eb.
  by exfalso; apply: vS; rewrite -(cS _ _ uv).
have [ext [ext_inj extE extF extS]] := e125_perm_ext liftK liftV.
have phi_inj : injective phi by move=> a b E; have := liftK a; rewrite E liftK => -[].
have phiD x : phi x \in e125_dartset S by rewrite imD liftK.
have DSphi y : y \in e125_dartset S -> exists x, y = phi x.
  by rewrite imD; case E: (lift y) => [x|] // _; exists x; rewrite (liftV _ _ E).
have revphi x : surface_edge_perm G (phi x) = phi (surface_edge_perm (induced S) x).
  by rewrite !e125_edge_permE; apply: val_inj.
have fixD q y : y \notin e125_dartset S -> ext q y = y.
  by rewrite imD negbK => /eqP; exact: extF.
exists ext; split => //.
  have imsrc x : phi @: [set e | (sval e).1 == (sval x).1] = [set d | (sval d).1 == (sval (phi x)).1].
    apply/setP => d; apply/imsetP/idP => [[e ee ->]|ds].
      by rewrite inE /=; move: ee; rewrite inE => /eqP ->.
    have dD : d \in e125_dartset S by move: ds; rewrite !inE => /eqP ->; exact: valP.
    have [e de] := DSphi d dD; exists e => //.
    by move: ds; rewrite de !inE => /eqP E; apply/eqP; exact: val_inj E.
  apply/setP => p; apply/imsetP/idP => [[q qr ->]|pR].
    move: qr; rewrite inE /x228_rotationb => /andP[/forallP Q1 /forallP Q2].
    rewrite inE; apply/andP; split; apply/forallP => d; apply/implyP => dD; first by rewrite fixD.
    have [x ->] := DSphi d dD; rewrite extE /= (eqP (Q1 x)) eqxx /=.
    by rewrite (e125_porbit_conj _ (extE q)) (eqP (Q2 x)) imsrc.
  have [F R O] := e125_rot_onP pR.
  have Fp y : lift y = None -> p y = y by move=> Ly; apply: F; rewrite imD Ly.
  have [q qp] := extS p Fp.
  exists q => //; rewrite inE /x228_rotationb; apply/andP; split; apply/forallP => x.
    have := (R (phi x) (phiD x)).2; rewrite -qp extE /= => /val_inj ->; exact: eqxx.
  apply/eqP; apply: (imset_inj phi_inj).
  by rewrite -(e125_porbit_conj _ (extE q)) qp (O (phi x) (phiD x)) imsrc.
move=> q; rewrite /x228_faces /e125_faces_on.
set eI := surface_edge_perm (induced S); set eG := surface_edge_perm G.
have conj y : (ext q * eG)%g (phi y) = phi ((q * eI)%g y) by rewrite !permM extE revphi.
have E : [set O in porbits (ext q * eG)%g | O \subset e125_dartset S] =
    (fun O : {set surface_dart (induced S)} => phi @: O) @: porbits (q * eI)%g.
  apply/setP => O; rewrite inE; apply/andP/imsetP => [[/imsetP[d _ ->] sub]|[O' /imsetP[x _ ->] ->]].
    have [x dx] := DSphi d (subsetP sub d (porbit_id _ d)).
    exists (porbit (q * eI)%g x); first by apply/imsetP; exists x.
    by rewrite dx (e125_porbit_conj _ conj).
  split; first by apply/imsetP; exists (phi x) => //; rewrite (e125_porbit_conj _ conj).
  by apply/subsetP => y /imsetP[z _ ->]; exact: phiD.
by rewrite E card_imset //; exact: imset_inj.
Qed.

(** L9: the rotations on S are counted by the rotation systems of induced S (S closed). *)
Lemma e125_nrot_induced (G : sgraph) (S : {set G}) :
  (forall x y : G, x -- y -> (x \in S) = (y \in S)) -> #|e125_rot_on S| = x228_nrot (induced S).
Proof. by move=> cS; have [ext [inj <- _]] := e125_transport cS; rewrite card_imset. Qed.

(** L10: and their faces inside S total the face count of induced S. *)
Lemma e125_total_induced (G : sgraph) (S : {set G}) :
  (forall x y : G, x -- y -> (x \in S) = (y \in S)) ->
  \sum_(p in e125_rot_on S) e125_faces_on (e125_dartset S) p = x228_total_faces (induced S).
Proof.
move=> cS; have [ext [inj <- F]] := e125_transport cS.
rewrite (big_imset _ (in2W inj)) /x228_total_faces; apply: eq_bigr => q _; exact: esym (F q).
Qed.

(** L11: a disconnected graph has a closed, connected, nonempty proper vertex set (a connect class). *)
Lemma e125_split_component (G : sgraph) :
  ~ connected [set: G] ->
  exists S : {set G},
    [/\ forall x y : G, x -- y -> (x \in S) = (y \in S), connected [set: induced S], 0 < #|S| & #|~: S| < #|G|].
Proof.
move=> nc.
have rT : connect (preliminaries.restrict_mem (mem [set: G]) (--)) =2 connect (--).
  by apply: eq_connect => u v; rewrite /= !inE.
have [x [y nxy]] : exists x y : G, ~~ connect (--) x y.
  case: (boolP [forall x : G, [forall y : G, connect (--) x y]]) => [H|].
    by exfalso; apply: nc; apply: connectedTI => x y; exact: (forallP (forallP H x) y).
  by case/forallPn => x /forallPn[y nxy]; exists x, y.
pose S := [set z | connect (preliminaries.restrict_mem (mem [set: G]) (--)) x z].
exists S; split.
- move=> u v uv; rewrite !inE !rT; apply/idP/idP => xu.
    exact: connect_trans xu (connect1 uv).
  by apply: connect_trans xu (connect1 _); rewrite sg_sym.
- by apply: connected_induced; exact: connected_restrict.
- by apply/card_gt0P; exists x; rewrite inE connect0.
- rewrite -[#|G|]cardsT; apply: proper_card; rewrite properT; apply/eqP => /setP E.
  by have := E x; rewrite !inE connect0.
Qed.

End E125.

(** L12, gc:e125: the n/3 + 1 bound on connected graphs gives the linear bound on all graphs, with c = 4. *)
Theorem e125_random_embedding_expected_faces_third_implies_random_embedding_expected_faces_linear :
  random_embedding_expected_faces_third_statement -> random_embedding_expected_faces_linear_statement.
Proof.
move=> H; exists 4.
suff Hn n : forall G : sgraph, #|G| <= n -> x228_total_faces G <= 4 * #|G| * x228_nrot G.
  by move=> G; exact: Hn #|G| G (leqnn _).
elim: n => [|n IH] G.
  by rewrite leqn0 => /eqP n0; rewrite (x228_total_faces0 n0).
move=> Gn; case: (boolP [forall x : G, [forall y : G, connect (--) x y]]) => [Hc|Hnc].
  apply: (x228_third_implies_linear_connected H).
  by apply: connectedTI => x y; exact: (forallP (forallP Hc x) y).
have nc : ~ connected [set: G].
  move/connectedTE => C; apply: (negP Hnc); apply/forallP => x; apply/forallP => y; exact: C.
have [S [cS cIS S0 SC]] := e125_split_component nc.
have cSC x y : x -- y -> (x \in ~: S) = (y \in ~: S) by move=> xy; rewrite !inE (cS x y xy).
rewrite (e125_total_split cS) (e125_nrot_split S) (e125_nrot_induced cS) (e125_total_induced cS).
rewrite (e125_nrot_induced cSC) (e125_total_induced cSC).
set N1 := x228_nrot (induced S); set N2 := x228_nrot (induced (~: S)).
have cI (A : {set G}) : #|induced A| = #|A| by rewrite card_sig; apply: eq_card => z; rewrite !inE.
have T1 := x228_third_implies_linear_connected H cIS; rewrite cI in T1.
have lt2 : #|induced (~: S)| <= n by rewrite cI -ltnS (leq_trans SC Gn).
have T2 := IH (induced (~: S)) lt2; rewrite cI in T2.
apply: leq_trans (leq_add (leq_mul T1 (leqnn N2)) (leq_mul (leqnn N1) T2)) _.
rewrite -/N1 -/N2 -(cardsC S) mulnDr mulnDl -!mulnA; apply: leq_add => //.
by rewrite [N1 * _]mulnCA [N1 * _]mulnCA.
Qed.

(*@EDGE from=random_embedding_expected_faces_third_statement
        to=random_embedding_expected_faces_linear_statement
        kind=implies status=verified
        proof=e125_random_embedding_expected_faces_third_implies_random_embedding_expected_faces_linear
        cite="gc:e125"
        note="The connected half is x228_third_implies_linear_connected (c = 4). For a disconnected G take the connect class S of a vertex: no edge leaves S, so the darts leaving S are stable under the edge reversal and under every rotation system, a rotation system is exactly a pair (its restrictions to the darts leaving S and to the others), and the faces of the product are the faces of each part (e125_rot_pairs, e125_faces_split); hence nrot G = N(S) N(~S) and total G = T(S) N(~S) + N(S) T(~S). The darts of induced S are the darts leaving S, which transports N and T to the induced subgraphs (e125_transport). Strong induction on #|G| with c = 4: induced S is connected, induced ~S has fewer vertices, and 4|S| N N2 + N 4|~S| N2 = 4 n N N2." *)
