(** * Extremal.foundations.edge_cycles — cycles given by supplied families of vertex pairs

    Library migration B29, family [cycle-lengths] (meta/library_primitives/cycle-lengths.json), edge-family class;
    the family's primary sequence contracts in [GTBase.walks_paths] are unchanged.  For an arbitrary supplied family
    [F : {set {set G}}]:

    - [edge_family_support F]: the vertices lying in some member of [F], whatever the size of that member;
    - [edge_family_rel F x y]: the pair [[set x; y]] is a member of [F] (so a singleton member [[set x]] relates [x]
      to itself, [edge_family_rel_singleton]);
    - [edge_family_cycle F], five conjuncts in this order: every member is a host edge ([E(G)], upstream
      [sg_edge_set]); the support has more than two vertices; [#|F|] equals the support size; every support vertex
      has incidence degree two in [F] ([incidence_degree], A10); and every two support vertices are connected by
      [edge_family_rel F] ([edge_family_cycleP] states the Prop view);
    - [edge_family_cycle_count G] counts the qualifying families; [has_edge_family_cycle_length G l]: some qualifying
      family has exactly [l] support vertices, so [l > 2] ([has_edge_family_cycle_length_gt2]).

    No ambient connectivity, spanning, induced, orientation, start point, no-isolated-vertex or traversal condition:
    a triangle beside an uncovered vertex qualifies and host edges outside [F] are irrelevant
    ([edge_family_cycle_triangle]); a family whose members never straddle a vertex set is not connected across it
    ([edge_family_rel_closed]).  Members are never normalized: a malformed member is rejected by the host-edge
    conjunct.  No equivalence with the sequence cycle contracts of [GTBase.walks_paths] is claimed. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries digraph sgraph.
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Three distinct elements. *)
Local Lemma cards3_distinct (T : finType) (x y z : T) : x != y -> x != z -> y != z -> #|[set x; y; z]| = 3.
Proof. by move=> xy xz yz; rewrite setUC cardsU1 cards2 !inE negb_or (eq_sym z x) (eq_sym z y) xz yz xy. Qed.

Section EdgeCycles.
Variable G : sgraph.
Implicit Types (F : {set {set G}}) (e A : {set G}) (x y v a b c : G).

(** The vertices lying in some member of [F]. *)
Definition edge_family_support F : {set G} := [set v : G | [exists e in F, v \in e]].

(** [x] and [y] are related when [[set x; y]] is a member of [F]. *)
Definition edge_family_rel F : rel G := fun x y => [set x; y] \in F.

(** Every two support vertices are connected through members. *)
Definition edge_family_connected F : bool :=
  [forall x in edge_family_support F, [forall y in edge_family_support F, connect (edge_family_rel F) x y]].

(** The five conjuncts, in order. *)
Definition edge_family_cycle F : bool :=
  [&& F \subset sg_edge_set G,
      2 < #|edge_family_support F|,
      #|F| == #|edge_family_support F|,
      [forall v in edge_family_support F, incidence_degree F v == 2]
    & edge_family_connected F].

Lemma in_edge_family_support F v : (v \in edge_family_support F) = [exists e in F, v \in e].
Proof. by rewrite inE. Qed.

Lemma edge_family_support_set0 : edge_family_support set0 = set0.
Proof. by apply/setP => v; rewrite !inE; apply/existsP => -[e]; rewrite inE. Qed.

Lemma edge_family_rel_sym F : symmetric (edge_family_rel F).
Proof. by move=> x y; rewrite /edge_family_rel setUC. Qed.

(** A singleton member relates its vertex to itself: the raw relation is not normalized. *)
Lemma edge_family_rel_singleton F x : [set x] \in F -> edge_family_rel F x x.
Proof. by rewrite /edge_family_rel setUid. Qed.

Lemma edge_family_cycleP F :
  reflect [/\ F \subset sg_edge_set G, 2 < #|edge_family_support F|, #|F| = #|edge_family_support F|,
              forall v, v \in edge_family_support F -> incidence_degree F v = 2
            & forall x y, x \in edge_family_support F -> y \in edge_family_support F ->
                connect (edge_family_rel F) x y]
          (edge_family_cycle F).
Proof.
apply: (iffP and5P) => [[sub big /eqP card /forall_inP deg /forall_inP con] | [sub big card deg con]].
  split=> // [v /deg /eqP // | x y xS yS]; exact: (forall_inP (con x xS)).
split=> //; first exact/eqP.
  by apply/forall_inP => v /deg ->.
by apply/forall_inP => x xS; apply/forall_inP => y yS; exact: con.
Qed.

Lemma edge_family_cycle_subset F : edge_family_cycle F -> F \subset sg_edge_set G.
Proof. by case/edge_family_cycleP. Qed.

Lemma edge_family_cycle_support_gt2 F : edge_family_cycle F -> 2 < #|edge_family_support F|.
Proof. by case/edge_family_cycleP. Qed.

Lemma edge_family_cycle_set0 : ~~ edge_family_cycle set0.
Proof. by apply/negP => /edge_family_cycle_support_gt2; rewrite edge_family_support_set0 cards0. Qed.

(** A cycle needs more than two host vertices. *)
Lemma edge_family_cycle_order F : edge_family_cycle F -> 2 < #|G|.
Proof.
move=> /edge_family_cycle_support_gt2 big; apply: leq_trans big _.
by rewrite -cardsT subset_leq_card ?subsetT.
Qed.

(** Three pairwise adjacent vertices: their three pairs form a cycle on exactly those vertices, whatever the
    other host vertices and edges are. *)
Lemma edge_family_cycle_triangle a b c :
  a -- b -> b -- c -> a -- c ->
  edge_family_cycle [set [set a; b]; [set b; c]; [set a; c]] /\
  edge_family_support [set [set a; b]; [set b; c]; [set a; c]] = [set a; b; c].
Proof.
move=> ab bc ac.
have nab : a != b by apply: contraTneq ab => ->; rewrite sgP.
have nbc : b != c by apply: contraTneq bc => ->; rewrite sgP.
have nac : a != c by apply: contraTneq ac => ->; rewrite sgP.
have nba : b != a by rewrite eq_sym.
have ncb : c != b by rewrite eq_sym.
have nca : c != a by rewrite eq_sym.
set F := [set [set a; b]; [set b; c]; [set a; c]].
have inF e : (e \in F) = [|| e == [set a; b], e == [set b; c] | e == [set a; c]].
  by rewrite !inE -orbA.
have in3 v : (v \in [set a; b; c]) = [|| v == a, v == b | v == c].
  by rewrite !inE -orbA.
have in2 x y v : (v \in [set x; y]) = (v == x) || (v == y) by rewrite !inE.
have suppE : edge_family_support F = [set a; b; c].
  apply/setP => v; rewrite in_edge_family_support in3; apply/existsP/idP => [[e /andP[]] | ].
    by rewrite inF => /or3P[] /eqP-> ; rewrite in2 => /orP[] /eqP->; rewrite !eqxx ?orbT.
  case/or3P => /eqP->; [exists [set a; b] | exists [set b; c] | exists [set a; c]];
    by rewrite inF in2 !eqxx ?orbT.
have ne_ab_bc : [set a; b] != [set b; c].
  by apply/negP => /eqP /setP /(_ a); rewrite !in2 eqxx (negbTE nab) (negbTE nac).
have ne_ab_ac : [set a; b] != [set a; c].
  by apply/negP => /eqP /setP /(_ b); rewrite !in2 eqxx (negbTE nba) (negbTE nbc).
have ne_bc_ac : [set b; c] != [set a; c].
  by apply/negP => /eqP /setP /(_ b); rewrite !in2 eqxx (negbTE nba) (negbTE nbc).
have cardF : #|F| = 3 by apply: cards3_distinct.
have card3 : #|[set a; b; c]| = 3 by apply: cards3_distinct.
(* The members of [F] at a vertex lying in exactly two of them. *)
have deg2 v e1 e2 e3 : (forall e, (e \in F) = [|| e == e1, e == e2 | e == e3]) ->
    e1 != e2 -> v \in e1 -> v \in e2 -> v \notin e3 -> incidence_degree F v = 2.
  move=> mF n12 v1 v2 v3; rewrite /incidence_degree (_ : [set e in F | v \in e] = [set e1; e2]) ?cards2 ?n12 //.
  have n31 : e3 != e1 by apply: contraNneq v3 => ->.
  have n32 : e3 != e2 by apply: contraNneq v3 => ->.
  apply/setP => e; rewrite inE mF !inE.
  case: (eqVneq e e1) => [-> | n1] /=; first by rewrite v1.
  case: (eqVneq e e2) => [-> | n2] /=; first by rewrite v2.
  case: (eqVneq e e3) => [-> | n3] //=.
  by rewrite (negbTE v3) ?(negbTE n31) ?(negbTE n32) ?andbF.
have perm (x y z : bool) : [|| x, y | z] = [|| x, z | y] by case: x; case: y; case: z.
have perm2 (x y z : bool) : [|| x, y | z] = [|| y, z | x] by case: x; case: y; case: z.
split=> //; apply/edge_family_cycleP; rewrite suppE; split.
- by apply/subsetP => e; rewrite inF => /or3P[] /eqP->; rewrite in_edges.
- by rewrite card3.
- by rewrite cardF card3.
- move=> v; rewrite in3 => /or3P[] /eqP->.
  + apply: (@deg2 a [set a; b] [set a; c] [set b; c]).
    * by move=> e; rewrite inF perm.
    * exact: ne_ab_ac.
    * by rewrite in2 eqxx.
    * by rewrite in2 eqxx.
    * by rewrite in2 negb_or nab nac.
  + apply: (@deg2 b [set a; b] [set b; c] [set a; c]).
    * exact: inF.
    * exact: ne_ab_bc.
    * by rewrite in2 eqxx orbT.
    * by rewrite in2 eqxx.
    * by rewrite in2 negb_or nba nbc.
  + apply: (@deg2 c [set b; c] [set a; c] [set a; b]).
    * by move=> e; rewrite inF perm2.
    * exact: ne_bc_ac.
    * by rewrite in2 eqxx orbT.
    * by rewrite in2 eqxx orbT.
    * by rewrite in2 negb_or nca ncb.
- have step x y : [set x; y] \in F -> connect (edge_family_rel F) x y by move=> h; apply: connect1.
  have stepC x y : [set y; x] \in F -> connect (edge_family_rel F) x y by rewrite setUC; exact: step.
  move=> x y; rewrite !in3 => /or3P[] /eqP-> /or3P[] /eqP->; rewrite ?connect0 //;
    first [apply: step; rewrite inF eqxx ?orbT; done | apply: stepC; rewrite inF eqxx ?orbT; done].
Qed.

(** Members that never straddle [A] cannot connect a vertex of [A] to one outside [A]. *)
Lemma edge_family_rel_closed F A x y :
  (forall e, e \in F -> (e \subset A) || [disjoint e & A]) ->
  x \in A -> y \notin A -> ~~ connect (edge_family_rel F) x y.
Proof.
move=> sep xA yA; apply/negP => cxy.
have cl : closed (edge_family_rel F) (fun z => z \in A).
  move=> u w uw; have /orP[sub | dis] := sep _ uw.
    have uA : u \in A by apply: (subsetP sub); rewrite !inE eqxx.
    have wA : w \in A by apply: (subsetP sub); rewrite !inE eqxx orbT.
    by rewrite uA wA.
  have uA : (u \in A) = false by apply: (disjointFr dis); rewrite !inE eqxx.
  have wA : (w \in A) = false by apply: (disjointFr dis); rewrite !inE eqxx orbT.
  by rewrite uA wA.
by have := closed_connect cl cxy; rewrite xA (negbTE yA).
Qed.

End EdgeCycles.

(** The number of qualifying families, and exact support length. *)
Definition edge_family_cycle_count (G : sgraph) : nat :=
  #|[set F : {set {set G}} | edge_family_cycle F]|.

Definition has_edge_family_cycle_length (G : sgraph) (l : nat) : Prop :=
  exists F : {set {set G}}, edge_family_cycle F /\ #|edge_family_support F| = l.

Lemma has_edge_family_cycle_length_gt2 (G : sgraph) (l : nat) : has_edge_family_cycle_length G l -> 2 < l.
Proof. by case=> F [/edge_family_cycle_support_gt2 + <-]. Qed.

Lemma edge_family_cycle_count_small (G : sgraph) : #|G| <= 2 -> edge_family_cycle_count G = 0.
Proof.
move=> small; apply/eqP; rewrite cards_eq0; apply/eqP/setP => F; rewrite !inE.
by apply/negP => /edge_family_cycle_order; rewrite ltnNge small.
Qed.

Lemma edge_family_cycle_count_gt0 (G : sgraph) :
  0 < edge_family_cycle_count G <-> exists l, has_edge_family_cycle_length G l.
Proof.
split=> [/card_gt0P[F] | [l [F [cF _]]]]; first by rewrite inE => cF; exists #|edge_family_support F|, F.
by apply/card_gt0P; exists F; rewrite inE.
Qed.
