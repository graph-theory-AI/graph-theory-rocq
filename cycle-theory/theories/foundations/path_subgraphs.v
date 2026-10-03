(** * Cycle.foundations.path_subgraphs — path subgraphs of a multigraph

    Batch B of the library migration, family [is-path]
    (meta/library_primitives/is-path.json), multigraph class.  A path subgraph is
    given by its EDGE SET [P] of an undirected multigraph ([mgraph]): [P] is
    nonempty, connected, contains no circuit, and every vertex has at most two
    [P]-arc ends ([subdeg], which counts a loop twice).  This is the edge-set
    reading used by the cycle-theory rows; the vertex-sequence reading of a path
    is [GTBase.walks_paths.seq_simple_path] and the two are separate
    representations.

    Upstream audit (2026-10-03; coq-graph-theory 0.9.7).  [mgraph] provides
    edges, endpoints, [incident] and [edges_at]; it has no path-subgraph
    predicate.  Connectivity of an edge set ([subgraph_connected]), circuits
    ([is_circuit]) and arc-end degrees ([subdeg]) are in
    [Cycle.foundations.connectivity]; this file adds acyclicity of an edge set
    (no circuit inside it) and the path predicate over them.

    Specification, every clause proved below:
    - the empty edge set is not a path; every path is nonempty, connected,
      acyclic and of arc-end degree at most two;
    - acyclicity is inherited by subsets, and the empty set is acyclic;
    - a LOOP is a circuit, so no path contains one; a single non-loop edge is a
      path; two distinct PARALLEL edges form a circuit, so no path contains both;
    - no looplessness, simplicity, positivity or size premise is added. *)

From GraphTheory Require Import mgraph.
From GTBase Require Import base.
From Cycle.foundations Require Import connectivity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PathSubgraphs.
Variable G : mgraph.
Implicit Types (C H K P : {set edge G}) (e f : edge G) (u v x y : G).

(** [H] contains no circuit. *)
Definition acyclic_edge_set H : Prop :=
  forall C : {set edge G}, C \subset H -> ~ is_circuit C.

(** [P] is the edge set of a path: nonempty, connected, acyclic, and every
    vertex has at most two [P]-arc ends. *)
Definition path_subgraph P : Prop :=
  [/\ P != set0, subgraph_connected P, acyclic_edge_set P & forall v : G, (subdeg P v <= 2)%N].

Lemma path_subgraph_neq0 P : path_subgraph P -> P != set0.
Proof. by case. Qed.

Lemma path_subgraph_set0 : ~ path_subgraph set0.
Proof. by case; rewrite eqxx. Qed.

Lemma path_subgraph_connected P : path_subgraph P -> subgraph_connected P.
Proof. by case. Qed.

Lemma path_subgraph_acyclic P : path_subgraph P -> acyclic_edge_set P.
Proof. by case. Qed.

Lemma path_subgraph_subdeg P v : path_subgraph P -> (subdeg P v <= 2)%N.
Proof. by case=> _ _ _; apply. Qed.

Lemma acyclic_edge_set0 : acyclic_edge_set set0.
Proof. by move=> C; rewrite subset0 => /eqP -> []; rewrite eqxx. Qed.

Lemma acyclic_edge_set_sub H K : H \subset K -> acyclic_edge_set K -> acyclic_edge_set H.
Proof. by move=> HK aK C CH; apply: aK; exact: subset_trans CH HK. Qed.

(** Arc ends of a one-edge set. *)
Lemma card_ends_at1 e b v : #|ends_at [set e] b v| = (endpoint b e == v).
Proof.
case: (boolP (endpoint b e == v)) => ev.
- rewrite (_ : ends_at _ _ _ = [set e]) ?cards1 //.
  by apply/setP => f; rewrite !inE; case: (f =P e) => // ->.
- rewrite (_ : ends_at _ _ _ = set0) ?cards0 //.
  by apply/setP => f; rewrite !inE; case: (f =P e) => // ->; rewrite (negbTE ev).
Qed.

Lemma subdeg_set1 e v : subdeg [set e] v = (source e == v) + (target e == v).
Proof. by rewrite /subdeg !card_ends_at1. Qed.

(** Arc ends of a set of two distinct edges. *)
Lemma subdeg_set2 e f v : e != f ->
  subdeg [set e; f] v = subdeg [set e] v + subdeg [set f] v.
Proof.
move=> ef; rewrite /subdeg addnACA.
have split_ends b : ends_at [set e; f] b v = ends_at [set e] b v :|: ends_at [set f] b v.
  by apply/setP => g; rewrite !inE andb_orl.
have disj b : [disjoint ends_at [set e] b v & ends_at [set f] b v].
  apply/pred0P => g /=; rewrite !inE; apply/negbTE; apply/negP => /andP[/andP[/eqP-> _] /andP[/eqP fe _]].
  by rewrite fe eqxx in ef.
by rewrite !split_ends !cardsU (disjoint_setI0 (disj _)) (disjoint_setI0 (disj _)) !cards0 !subn0.
Qed.

Lemma incident_set1 e x : H_inc [set e] x = incident x e.
Proof.
apply/existsP/idP => [[f /andP[]]|xe]; first by rewrite inE => /eqP ->.
by exists e; rewrite inE eqxx.
Qed.

(** A loop is a circuit of length one. *)
Lemma is_circuit_loop e : source e = target e -> is_circuit [set e].
Proof.
move=> loop; split.
- by apply/set0Pn; exists e; rewrite inE.
- move=> v; rewrite subdeg_set1 loop.
  by case: (target e =P v) => _; [right | left].
- move=> x y; rewrite !incident_set1 /incident => /existsP[b /eqP <-] /existsP[c /eqP <-].
  exists [::]; rewrite /walk_in /= andbT.
  by case: b; case: c; rewrite ?loop.
Qed.

(** Hence no path contains a loop. *)
Lemma path_subgraph_noloop P e : source e = target e -> e \in P -> ~ path_subgraph P.
Proof.
move=> loop eP [_ _ acyc _]; apply: (acyc [set e]); last exact: is_circuit_loop.
by rewrite sub1set.
Qed.

(** A single non-loop edge is a path. *)
Lemma path_subgraph_edge e : source e != target e -> path_subgraph [set e].
Proof.
move=> ne; split.
- by apply/set0Pn; exists e; rewrite inE.
- move=> x y; rewrite !incident_set1 /incident => /existsP[b /eqP <-] /existsP[c /eqP <-].
  case: b; case: c.
  + by exists [::]; rewrite /walk_in /= eqxx.
  + by exists [:: e]; rewrite /walk_in /= !eqxx orbT inE eqxx.
  + by exists [:: e]; rewrite /walk_in /= !eqxx inE eqxx.
  + by exists [::]; rewrite /walk_in /= eqxx.
- move=> C; rewrite subset1 => /orP[/eqP->|/eqP->] [] //; last by rewrite eqxx.
  move=> _ /(_ (source e)); rewrite subdeg_set1 eqxx eq_sym (negbTE ne).
  by case.
- by move=> v; rewrite subdeg_set1; case: (source e == v); case: (target e == v).
Qed.

(** [e] and [f] join the same two vertices, in either orientation. *)
Definition parallel_edges e f : bool :=
  ((source f == source e) && (target f == target e)) ||
  ((source f == target e) && (target f == source e)).

(** Two distinct parallel non-loop edges form a circuit of length two. *)
Lemma is_circuit_parallel e f :
  e != f -> source e != target e -> parallel_edges e f -> is_circuit [set e; f].
Proof.
move=> ef ne par; split.
- by apply/set0Pn; exists e; rewrite !inE eqxx.
- move=> v; rewrite subdeg_set2 // !subdeg_set1.
  have ne' : (target e == source e) = false by rewrite eq_sym (negbTE ne).
  case: (boolP (source e == v)) => [/eqP <-|/negbTE sv].
  + by case/orP: par => /andP[/eqP-> /eqP->]; rewrite eqxx ne'; right.
  + by case/orP: par => /andP[/eqP-> /eqP->]; rewrite sv; case: (target e == v); [right | left | right | left].
- have inc z : H_inc [set e; f] z -> incident z e.
    case/existsP=> g /andP[]; rewrite !inE => /orP[/eqP->|/eqP->] //.
    case/orP: par => /andP[/eqP fs /eqP ft]; rewrite /incident => /existsP[[] /eqP <-].
    + by apply/existsP; exists true; rewrite ft.
    + by apply/existsP; exists false; rewrite fs.
    + by apply/existsP; exists false; rewrite ft.
    + by apply/existsP; exists true; rewrite fs.
  move=> x y /inc /existsP[b /eqP <-] /inc /existsP[c /eqP <-].
  have ee : e \in [set e; f] by rewrite !inE eqxx.
  case: b; case: c.
  + by exists [::]; rewrite /walk_in /= eqxx.
  + by exists [:: e]; rewrite /walk_in /= !eqxx orbT ee.
  + by exists [:: e]; rewrite /walk_in /= !eqxx ee.
  + by exists [::]; rewrite /walk_in /= eqxx.
Qed.

(** Hence no path contains two distinct parallel edges. *)
Lemma path_subgraph_noparallel P e f :
  e != f -> parallel_edges e f -> e \in P -> f \in P -> ~ path_subgraph P.
Proof.
move=> ef par eP fP pP.
case: (boolP (source e == target e)) => [/eqP loop|ne].
- exact: path_subgraph_noloop loop eP pP.
- case: pP => _ _ acyc _; apply: (acyc [set e; f]); last exact: is_circuit_parallel.
  by apply/subsetP => g; rewrite !inE => /orP[/eqP->|/eqP->].
Qed.

End PathSubgraphs.
