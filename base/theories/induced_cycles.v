(** * GTBase.induced_cycles — induced (chordless) vertex-sequence cycles and holes

    Library migration B23, family [induced-cycle] (meta/library_primitives/induced-cycle.json).  A
    chordless cycle is a MathComp [ucycle] of host adjacency (a closed adjacency walk whose vertex
    list is duplicate-free) without chords: every host edge between two of its vertices joins
    cyclically consecutive entries ([seq_cyclic_consecutiveb], GTBase.walks_paths).  Three views
    share this core and differ only in the length they require:
    - [chordless_ucycle c]: no length bound; the empty list and the two-vertex cycle [u; v] of an
      edge are chordless ucycles (Extremal D2str);
    - [chordless_cycle c]: at least three vertices, a genuine cycle ([seq_cycle]; GTMisc X91 with
      [3 <= size c], Packing XE1 with [2 < size c], the same bound);
    - [hole c]: at least four vertices (Chromatic X3, Minor X27).
    [cyclic_chordless c] is the chord condition alone, stated with the Boolean cyclic
    consecutiveness and no distinctness premise: a host edge already has distinct ends
    ([sg_edgeNeq]).  The bridges [cyclic_chordless_edge_neq], [cyclic_chordless_neq_edge],
    [cyclic_chordless_prop], [cyclic_chordless_prop_edge_neq] and [cyclic_chordless_prop_neq_edge]
    relate the shapes in which conjecture files state chordlessness: with a redundant [u != v]
    premise before or after the edge premise, with the consecutiveness as a Boolean or as the
    proposition [seq_cyclic_consecutive] (through [seq_cyclic_consecutiveP]).  Boolean mirrors
    [cyclic_chordlessb], [chordless_ucycleb], [chordless_cycleb] and [holeb] quantify over the list
    itself, so they compute on concrete sequences; reflection lemmas connect them.  Rotation,
    reversal and injective adjacency-preserving-and-reflecting images (induced copies) preserve each
    view.  Not re-exported by GTBase.base; no conjecture module is imported.  Since B24 the module
    also carries a second, ordinal-map interface for GTMisc U13 (an injective map ['I_k -> G] whose
    images are adjacent exactly for cyclically consecutive positions, with its own k = 0, 1, 2
    behaviour): [ord_cycle_rel], [ordinal_induced_cycle] and [has_ordinal_induced_cycle], at the end
    of this file; it is not identified with the sequence views.  Distinct and untouched: the
    induced-isomorphism copies of [cycle_graph n] (X49, X60, X29), X115's vertex-set odd induced cycle
    counter, X161's bare four-vertex ucycle, chordality through clique trees (X169) and the directed
    [chordal_C3]. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import preliminaries digraph sgraph.
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Membership in a zip is preserved by mapping both components. *)
Local Lemma mem_zip_map (T1 T2 : eqType) (f : T1 -> T2) (s t : seq T1) (a b : T1) :
  (a, b) \in zip s t -> (f a, f b) \in zip (map f s) (map f t).
Proof.
elim: s t => [|x s IH] [|y t] //= h.
rewrite in_cons xpair_eqE; rewrite in_cons xpair_eqE in h.
case/orP: h => [/andP[/eqP-> /eqP->]|/IH ->]; last by rewrite orbT.
by rewrite !eqxx.
Qed.

Section InducedCycles.
Variable G : sgraph.
Implicit Types (c : seq G) (u v x y : G).

(** ** The chord condition *)

(** Every host edge between two entries of [c] joins cyclically consecutive entries of [c]. *)
Definition cyclic_chordless c : Prop :=
  forall u v, u \in c -> v \in c -> u -- v -> seq_cyclic_consecutiveb c u v.

(** The same condition quantified over the list, so that it computes on concrete sequences. *)
Definition cyclic_chordlessb c : bool :=
  all (fun u => all (fun v => (u -- v) ==> seq_cyclic_consecutiveb c u v) c) c.

Lemma cyclic_chordlessP c : reflect (cyclic_chordless c) (cyclic_chordlessb c).
Proof.
apply: (iffP allP) => [h u v uc vc uv | h u uc].
- by have := h u uc => /allP/(_ v vc)/implyP/(_ uv).
- by apply/allP => v vc; apply/implyP => uv; exact: h.
Qed.

(** *** The redundant distinctness premise, in either position, and the Prop consecutiveness

    A host edge has distinct ends, so a premise [u != v] next to [u -- v] adds nothing. *)

Lemma cyclic_chordless_edge_neq c :
  (forall u v, u \in c -> v \in c -> u -- v -> u != v -> seq_cyclic_consecutiveb c u v)
  <-> cyclic_chordless c.
Proof.
split=> h u v uc vc.
- by move=> uv; apply: h => //; rewrite (sg_edgeNeq uv).
- by move=> uv _; exact: h.
Qed.

Lemma cyclic_chordless_neq_edge c :
  (forall u v, u \in c -> v \in c -> u != v -> u -- v -> seq_cyclic_consecutiveb c u v)
  <-> cyclic_chordless c.
Proof.
split=> h u v uc vc.
- by move=> uv; apply: h => //; rewrite (sg_edgeNeq uv).
- by move=> _ uv; exact: h.
Qed.

Lemma cyclic_chordless_prop c :
  (forall u v, u \in c -> v \in c -> u -- v -> seq_cyclic_consecutive c u v)
  <-> cyclic_chordless c.
Proof. by split=> h u v uc vc uv; apply/seq_cyclic_consecutiveP; exact: h. Qed.

Lemma cyclic_chordless_prop_edge_neq c :
  (forall u v, u \in c -> v \in c -> u -- v -> u != v -> seq_cyclic_consecutive c u v)
  <-> cyclic_chordless c.
Proof.
split=> h u v uc vc.
- by move=> uv; apply/seq_cyclic_consecutiveP; apply: h => //; rewrite (sg_edgeNeq uv).
- by move=> uv _; apply/seq_cyclic_consecutiveP; exact: h.
Qed.

Lemma cyclic_chordless_prop_neq_edge c :
  (forall u v, u \in c -> v \in c -> u != v -> u -- v -> seq_cyclic_consecutive c u v)
  <-> cyclic_chordless c.
Proof.
split=> h u v uc vc.
- by move=> uv; apply/seq_cyclic_consecutiveP; apply: h => //; rewrite (sg_edgeNeq uv).
- by move=> _ uv; apply/seq_cyclic_consecutiveP; exact: h.
Qed.

(** ** The three views *)

(** A chordless [ucycle], of any length: the raw contract (D2str). *)
Definition chordless_ucycle c : Prop := ucycle (--) c /\ cyclic_chordless c.

(** A chordless genuine cycle: at least three vertices (X91, XE1). *)
Definition chordless_cycle c : Prop := ucycle (--) c /\ 2 < size c /\ cyclic_chordless c.

(** A hole: a chordless cycle on at least four vertices (X3, X27). *)
Definition hole c : Prop := ucycle (--) c /\ 3 < size c /\ cyclic_chordless c.

Definition chordless_ucycleb c : bool := ucycleb (--) c && cyclic_chordlessb c.
Definition chordless_cycleb c : bool := [&& ucycleb (--) c, 2 < size c & cyclic_chordlessb c].
Definition holeb c : bool := [&& ucycleb (--) c, 3 < size c & cyclic_chordlessb c].

Lemma chordless_ucycleP c : reflect (chordless_ucycle c) (chordless_ucycleb c).
Proof. by apply: (iffP andP) => -[uc ch]; split=> //; apply/cyclic_chordlessP. Qed.

Lemma chordless_cycleP c : reflect (chordless_cycle c) (chordless_cycleb c).
Proof.
apply: (iffP and3P) => [[uc sz ch] | [uc [sz ch]]].
- by split=> //; split=> //; apply/cyclic_chordlessP.
- by split=> //; apply/cyclic_chordlessP.
Qed.

Lemma holeP c : reflect (hole c) (holeb c).
Proof.
apply: (iffP and3P) => [[uc sz ch] | [uc [sz ch]]].
- by split=> //; split=> //; apply/cyclic_chordlessP.
- by split=> //; apply/cyclic_chordlessP.
Qed.

(** *** How the views refine each other *)

Lemma chordless_cycleE c : chordless_cycle c <-> chordless_ucycle c /\ 2 < size c.
Proof. by split=> [[uc [sz ch]] | [[uc ch] sz]]; do ?split=> //. Qed.

Lemma holeE c : hole c <-> chordless_ucycle c /\ 3 < size c.
Proof. by split=> [[uc [sz ch]] | [[uc ch] sz]]; do ?split=> //. Qed.

Lemma chordless_cycle_seq_cycle c :
  chordless_cycle c <-> seq_cycle (--) c /\ cyclic_chordless c.
Proof. by split=> [[uc [sz ch]] | [[uc sz] ch]]; do ?split=> //. Qed.

Lemma hole_chordless_cycle c : hole c -> chordless_cycle c.
Proof. by move=> [uc [sz ch]]; split=> //; split=> //; exact: ltnW. Qed.

Lemma chordless_cycle_chordless_ucycle c : chordless_cycle c -> chordless_ucycle c.
Proof. by move=> [uc [_ ch]]. Qed.

Lemma hole_chordless_ucycle c : hole c -> chordless_ucycle c.
Proof. by move=> [uc [_ ch]]. Qed.

Lemma chordless_ucycle_ucycle c : chordless_ucycle c -> ucycle (--) c.
Proof. by case. Qed.

Lemma chordless_ucycle_chordless c : chordless_ucycle c -> cyclic_chordless c.
Proof. by case. Qed.

Lemma chordless_cycle_size c : chordless_cycle c -> 2 < size c.
Proof. by case=> _ []. Qed.

Lemma hole_size c : hole c -> 3 < size c.
Proof. by case=> _ []. Qed.

(** *** Small sequences

    The raw view accepts the empty list and the two-vertex cycle of an edge; the genuine view
    rejects both; a hole needs four vertices; a triangle is a chordless cycle but not a hole. *)

Lemma chordless_ucycle_nil : chordless_ucycle [::].
Proof. by split=> [|u v]; rewrite ?in_nil. Qed.

Lemma chordless_ucycle_pair u v : u -- v -> chordless_ucycle [:: u; v].
Proof.
move=> uv; have vu : v -- u by rewrite sg_sym.
split; first by apply/andP; split; [rewrite /= uv vu | rewrite /= inE (sg_edgeNeq uv)].
move=> x y; rewrite !inE => /orP[/eqP->|/eqP->] /orP[/eqP->|/eqP->]; rewrite ?sg_irrefl => // _.
- by apply/seq_cyclic_consecutiveP/seq_cyclic_consecutive_pair; left.
- by apply/seq_cyclic_consecutiveP/seq_cyclic_consecutive_pair; right.
Qed.

Lemma chordless_cycle_nil : ~ chordless_cycle [::].
Proof. by case=> _ []. Qed.

Lemma chordless_cycle_seq1 u : ~ chordless_cycle [:: u].
Proof. by case=> _ []. Qed.

Lemma chordless_cycle_pair u v : ~ chordless_cycle [:: u; v].
Proof. by case=> _ []. Qed.

Lemma hole_small c : size c <= 3 -> ~ hole c.
Proof. by move=> sz [_ [sz' _]]; rewrite ltnNge sz in sz'. Qed.

Lemma chordless_cycle_triangle u v w :
  u -- v -> v -- w -> w -- u -> chordless_cycle [:: u; v; w].
Proof.
move=> uv vw wu.
have vu : v -- u by rewrite sg_sym.
have wv : w -- v by rewrite sg_sym.
have uw : u -- w by rewrite sg_sym.
have nuv := sg_edgeNeq uv; have nvw := sg_edgeNeq vw; have nuw := sg_edgeNeq uw.
split; first by apply/andP; split; [rewrite /= uv vw wu | rewrite /= !inE nuv nuw nvw].
split=> // x y; rewrite !inE => /or3P[/eqP->|/eqP->|/eqP->] /or3P[/eqP->|/eqP->|/eqP->];
  rewrite ?sg_irrefl => // _;
  by rewrite /seq_cyclic_consecutiveb /rot /= !inE !xpair_eqE !eqxx ?andbT ?orTb ?orbT.
Qed.

Lemma hole_triangle u v w : ~ hole [:: u; v; w].
Proof. exact: hole_small. Qed.

(** ** Rotation and reversal *)

Lemma cyclic_chordless_rot n c : cyclic_chordless (rot n c) <-> cyclic_chordless c.
Proof.
split=> h u v.
- move=> uc vc uv; rewrite -(seq_cyclic_consecutiveb_rot n).
  by apply: h => //; rewrite mem_rot.
- rewrite !mem_rot => uc vc uv; rewrite seq_cyclic_consecutiveb_rot; exact: h.
Qed.

Lemma chordless_ucycle_rot n c : chordless_ucycle (rot n c) <-> chordless_ucycle c.
Proof.
split=> -[uc ch]; split.
- by rewrite rot_ucycle in uc.
- exact/(cyclic_chordless_rot n).
- by rewrite rot_ucycle.
- exact/(cyclic_chordless_rot n).
Qed.

Lemma chordless_cycle_rot n c : chordless_cycle (rot n c) <-> chordless_cycle c.
Proof.
split=> -[uc [sz ch]].
- rewrite rot_ucycle in uc; rewrite size_rot in sz.
  by split=> //; split=> //; exact/(cyclic_chordless_rot n).
- have uc' : ucycle (--) (rot n c) by rewrite rot_ucycle.
  have sz' : 2 < size (rot n c) by rewrite size_rot.
  by split=> //; split=> //; exact/(cyclic_chordless_rot n).
Qed.

Lemma hole_rot n c : hole (rot n c) <-> hole c.
Proof.
split=> -[uc [sz ch]].
- rewrite rot_ucycle in uc; rewrite size_rot in sz.
  by split=> //; split=> //; exact/(cyclic_chordless_rot n).
- have uc' : ucycle (--) (rot n c) by rewrite rot_ucycle.
  have sz' : 3 < size (rot n c) by rewrite size_rot.
  by split=> //; split=> //; exact/(cyclic_chordless_rot n).
Qed.

(** Host adjacency is symmetric, so a reversed [ucycle] is a [ucycle]. *)
Lemma ucycle_rev c : ucycle (--) (rev c) <-> ucycle (--) c.
Proof.
rewrite /ucycle rev_cycle rev_uniq.
by rewrite (@eq_cycle _ _ (@sedge G)) // => x y /=; exact: sg_sym.
Qed.

Lemma cyclic_chordless_rev c : cyclic_chordless (rev c) <-> cyclic_chordless c.
Proof.
split=> h u v.
- move=> uc vc uv; apply/seq_cyclic_consecutiveP/(seq_cyclic_consecutive_rev c).
  by apply/seq_cyclic_consecutiveP; apply: h => //; rewrite mem_rev.
- rewrite !mem_rev => uc vc uv; apply/seq_cyclic_consecutiveP/seq_cyclic_consecutive_rev.
  by apply/seq_cyclic_consecutiveP; exact: h.
Qed.

Lemma chordless_ucycle_rev c : chordless_ucycle (rev c) <-> chordless_ucycle c.
Proof.
by split=> -[uc ch]; split;
  [apply/ucycle_rev | apply/cyclic_chordless_rev | apply/ucycle_rev | apply/cyclic_chordless_rev].
Qed.

Lemma chordless_cycle_rev c : chordless_cycle (rev c) <-> chordless_cycle c.
Proof.
split=> -[uc [sz ch]].
- rewrite size_rev in sz.
  by split; [apply/ucycle_rev | split=> //; apply/cyclic_chordless_rev].
- by split; [apply/ucycle_rev | rewrite size_rev; split=> //; apply/cyclic_chordless_rev].
Qed.

Lemma hole_rev c : hole (rev c) <-> hole c.
Proof.
split=> -[uc [sz ch]].
- rewrite size_rev in sz.
  by split; [apply/ucycle_rev | split=> //; apply/cyclic_chordless_rev].
- by split; [apply/ucycle_rev | rewrite size_rev; split=> //; apply/cyclic_chordless_rev].
Qed.

End InducedCycles.

Arguments cyclic_chordless {G} c.
Arguments cyclic_chordlessb {G} c.
Arguments chordless_ucycle {G} c.
Arguments chordless_cycle {G} c.
Arguments hole {G} c.
Arguments chordless_ucycleb {G} c.
Arguments chordless_cycleb {G} c.
Arguments holeb {G} c.

(** ** Images under an injective map that preserves and reflects adjacency (an induced copy)

    Chordlessness needs only reflection of adjacency; the cycle itself needs preservation and
    injectivity. *)

Lemma cyclic_chordless_map (G H : sgraph) (f : H -> G) (c : seq H) :
  (forall x y : H, f x -- f y -> x -- y) -> cyclic_chordless c -> cyclic_chordless (map f c).
Proof.
move=> fE ch u v /mapP[x xc ->] /mapP[y yc ->] /fE xy.
have := ch x y xc yc xy; rewrite /seq_cyclic_consecutiveb -map_rot.
by case/orP=> h; apply/orP; [left | right]; exact: mem_zip_map h.
Qed.

Lemma ucycle_map (G H : sgraph) (f : H -> G) (c : seq H) :
  injective f -> (forall x y : H, (f x -- f y) = (x -- y)) ->
  ucycle (--) c -> ucycle (--) (map f c).
Proof.
move=> finj fE /andP[cyc uc]; apply/andP; split; last by rewrite map_inj_uniq.
by rewrite cycle_map (@eq_cycle _ _ (@sedge H)) // => x y; rewrite /relpre /= fE.
Qed.

Lemma chordless_ucycle_map (G H : sgraph) (f : H -> G) (c : seq H) :
  injective f -> (forall x y : H, (f x -- f y) = (x -- y)) ->
  chordless_ucycle c -> chordless_ucycle (map f c).
Proof.
move=> finj fE [uc ch]; split; first exact: ucycle_map.
by apply: (cyclic_chordless_map _ ch) => x y; rewrite fE.
Qed.

Lemma chordless_cycle_map (G H : sgraph) (f : H -> G) (c : seq H) :
  injective f -> (forall x y : H, (f x -- f y) = (x -- y)) ->
  chordless_cycle c -> chordless_cycle (map f c).
Proof.
move=> finj fE [uc [sz ch]]; split; first exact: ucycle_map.
split; first by rewrite size_map.
by apply: (cyclic_chordless_map _ ch) => x y; rewrite fE.
Qed.

Lemma hole_map (G H : sgraph) (f : H -> G) (c : seq H) :
  injective f -> (forall x y : H, (f x -- f y) = (x -- y)) -> hole c -> hole (map f c).
Proof.
move=> finj fE [uc [sz ch]]; split; first exact: ucycle_map.
split; first by rewrite size_map.
by apply: (cyclic_chordless_map _ ch) => x y; rewrite fE.
Qed.

(** ** Ordinal-map induced cycles (library migration B24)

    A second interface, for a cycle given as a map from the [k] cyclic positions ['I_k] rather
    than as a vertex list.  [ord_cycle_rel k i j] holds when [i] and [j] are consecutive modulo [k]
    in either order, with no unequal-index premise: at [k = 1] the single position is its own
    successor.  [ordinal_induced_cycle f] says that [f : 'I_k -> G] is injective and that two
    positions have adjacent images exactly when they are cyclically consecutive (both directions,
    equal positions included); [has_ordinal_induced_cycle G k] is its existential closure.  By
    order: [k = 0] is vacuous ([has_ordinal_induced_cycle G 0] holds in every graph, the empty one
    included); [k = 1] is impossible in every sgraph (the iff forces a loop); [k = 2] is an
    injectively enumerated edge, not a cycle of length three; for [k >= 3] it is an injective
    chordless cyclic enumeration with its closing adjacency.  [GTBase.base.cycle_graph k] drops the
    diagonal, so its adjacency is [ord_cycle_rel k] exactly when [k != 1]: the induced-embedding
    bridges [ordinal_induced_cycle_cycP] and [has_ordinal_induced_cycleP] carry that guard, and
    [cycle_graph1_isubgraph] shows it cannot be dropped.  (GTMisc U13.) *)

Definition ord_cycle_rel (k : nat) : rel 'I_k :=
  fun i j => (val j == (val i).+1 %% k) || (val i == (val j).+1 %% k).

(** [k] stays explicit: [Set Implicit Arguments] would infer it from the [rel 'I_k] result type. *)
Arguments ord_cycle_rel : clear implicits.

Lemma ord_cycle_relC k : symmetric (ord_cycle_rel k).
Proof. by move=> i j; rewrite /ord_cycle_rel orbC. Qed.

(** Away from order one no position is its own neighbour. *)
Lemma ord_cycle_rel_irr k (i : 'I_k) : k != 1 -> ord_cycle_rel k i i = false.
Proof.
move=> k1; rewrite /ord_cycle_rel orbb; apply/negbTE/eqP => e.
have ik := ltn_ord i.
have [lt|ge] := ltnP (val i).+1 k.
  by move: (n_Sn (val i)); rewrite {1}e modn_small // eqxx.
have ek : (val i).+1 = k by apply/eqP; rewrite eqn_leq ik ge.
move: e; rewrite ek modnn => e.
by move: k1; rewrite -ek e.
Qed.

(** ... and the relation is the adjacency of [cycle_graph k]. *)
Lemma ord_cycle_rel_cyc k (i j : 'I_k) : k != 1 -> ord_cycle_rel k i j = @cyc_rel k i j.
Proof.
move=> k1; have [<-|nij] := eqVneq i j.
  by rewrite ord_cycle_rel_irr // /cyc_rel eqxx.
by rewrite /cyc_rel nij /ord_cycle_rel (eq_sym (val j)) (eq_sym (val i)).
Qed.

(** At order one the relation holds on the single position, where [cycle_graph 1] has no loop. *)
Lemma ord_cycle_rel1 (i : 'I_1) : ord_cycle_rel 1 i i.
Proof. by rewrite (fintype.ord1 i) /ord_cycle_rel modn1. Qed.

Section OrdinalCycles.
Variable G : sgraph.

Definition ordinal_induced_cycle (k : nat) (f : 'I_k -> G) : Prop :=
  injective f /\ forall i j : 'I_k, (f i -- f j) <-> ord_cycle_rel k i j.

Definition has_ordinal_induced_cycle (k : nat) : Prop :=
  exists f : 'I_k -> G, ordinal_induced_cycle f.

(** A Boolean mirror quantified over [enum 'I_k]; with [ordinal_induced_cycleP] the predicate is
    decidable.  ([enum 'I_k] goes through [insub] and does not evaluate under [vm_compute].) *)
Definition ordinal_induced_cycleb (k : nat) (f : 'I_k -> G) : bool :=
  injectiveb f &&
  all (fun i => all (fun j => (f i -- f j) == ord_cycle_rel k i j) (enum 'I_k)) (enum 'I_k).

Lemma ordinal_induced_cycleP k (f : 'I_k -> G) :
  reflect (ordinal_induced_cycle f) (ordinal_induced_cycleb f).
Proof.
apply: (iffP andP) => [[/injectiveP inj /allP h] | [inj h]].
- split=> // i j.
  have ei : i \in enum 'I_k by rewrite mem_enum.
  have ej : j \in enum 'I_k by rewrite mem_enum.
  by move/allP: (h i ei) => /(_ j ej)/eqP ->.
- split; first exact/injectiveP.
  by apply/allP => i _; apply/allP => j _; apply/eqP; apply/idP/idP => /(h i j).
Qed.

Lemma ordinal_induced_cycle_inj k (f : 'I_k -> G) : ordinal_induced_cycle f -> injective f.
Proof. by case. Qed.

Lemma ordinal_induced_cycle_adj k (f : 'I_k -> G) :
  ordinal_induced_cycle f -> forall i j : 'I_k, (f i -- f j) = ord_cycle_rel k i j.
Proof. by case=> _ h i j; apply/idP/idP => /(h i j). Qed.

(** An induced [k]-cycle has [k] distinct vertices. *)
Lemma ordinal_induced_cycle_card k (f : 'I_k -> G) : ordinal_induced_cycle f -> k <= #|G|.
Proof. by case=> inj _; rewrite -[k in k <= _]card_ord; apply: leq_card inj. Qed.

Lemma has_ordinal_induced_cycle_card k : has_ordinal_induced_cycle k -> k <= #|G|.
Proof. by case=> f /ordinal_induced_cycle_card. Qed.

(** *** Orders zero, one and two *)

(** Order zero is vacuous: every graph, the empty one included, has the empty induced cycle. *)
Lemma has_ordinal_induced_cycle0 : has_ordinal_induced_cycle 0.
Proof.
exists (fun i : 'I_0 => match i with Ordinal m mlt => False_rect G (notF mlt) end).
by split=> -[m mlt]; exact: (False_rect _ (notF mlt)).
Qed.

(** Order one forces a loop, which no sgraph has. *)
Lemma ordinal_induced_cycle1 (f : 'I_1 -> G) : ~ ordinal_induced_cycle f.
Proof.
case=> _ /(_ ord0 ord0) [_ h].
by move: (h (ord_cycle_rel1 ord0)); rewrite sg_irrefl.
Qed.

Lemma has_ordinal_induced_cycle1 : ~ has_ordinal_induced_cycle 1.
Proof. by case=> f /ordinal_induced_cycle1. Qed.

(** Order two is an injectively enumerated edge, not a cycle of length three. *)
Lemma ordinal_induced_cycle2 (f : 'I_2 -> G) : ordinal_induced_cycle f <-> f ord0 -- f ord_max.
Proof.
have I2 (i : 'I_2) : i = ord0 \/ i = ord_max.
  by case: i => -[|[|//]] i2; [left | right]; apply/val_inj.
split=> [[_ h] | e]; first exact/(h ord0 ord_max).
have e' : f ord_max -- f ord0 by rewrite sg_sym.
split.
- move=> i j; case: (I2 i) => ->; case: (I2 j) => -> // fe.
  + by rewrite fe sg_irrefl in e.
  + by rewrite fe sg_irrefl in e'.
- by move=> i j; case: (I2 i) => ->; case: (I2 j) => ->; rewrite ?sg_irrefl ?e ?e'.
Qed.

Lemma has_ordinal_induced_cycle2 : has_ordinal_induced_cycle 2 <-> exists x y : G, x -- y.
Proof.
split=> [[f /ordinal_induced_cycle2 e] | [x [y xy]]]; first by exists (f ord0), (f ord_max).
exists (fun i : 'I_2 => if val i == 0 then x else y); exact/ordinal_induced_cycle2.
Qed.

(** *** Induced copies of [cycle_graph k], for [k != 1] *)

(** The same map: an ordinal induced cycle is an injective map whose adjacency is exactly the
    adjacency of [cycle_graph k], provided [k != 1]. *)
Lemma ordinal_induced_cycle_cycP k (f : 'I_k -> G) : k != 1 ->
  ordinal_induced_cycle f <-> injective f /\ forall i j : 'I_k, (f i -- f j) = @cyc_rel k i j.
Proof.
move=> k1; split=> [oc | [inj h]].
- split; first exact: ordinal_induced_cycle_inj oc.
  by move=> i j; rewrite (ordinal_induced_cycle_adj oc) ord_cycle_rel_cyc.
- by split=> // i j; rewrite h -ord_cycle_rel_cyc.
Qed.

(** The existential form: an induced [k]-cycle exists exactly when [k != 1] and [cycle_graph k] is
    an induced subgraph. *)
Lemma has_ordinal_induced_cycleP k :
  has_ordinal_induced_cycle k <-> (k != 1) /\ inhabited (cycle_graph k ⇀ G).
Proof.
split=> [[f oc] | [k1 [i]]].
- have k1 : k != 1.
    by apply/eqP => ek; move: f oc; rewrite ek => f /ordinal_induced_cycle1.
  have [inj h] := (ordinal_induced_cycle_cycP f k1).1 oc.
  pose g : cycle_graph k -> G := f.
  have mono : forall a b : cycle_graph k, (g a -- g b) = (a -- b) by move=> a b; exact: h.
  by split=> //; exact: inhabits (@ISubgraph (cycle_graph k) G g inj mono).
- exists (fun a : 'I_k => i a); apply/(ordinal_induced_cycle_cycP _ k1); split.
    by move=> a b /(isubgraph_inj i).
  by move=> a b; rewrite (isubgraph_mono i).
Qed.

(** The guard is needed: [cycle_graph 1] (one vertex, no loop) embeds in every nonempty graph,
    while no graph has an ordinal induced cycle of order one. *)
Lemma cycle_graph1_isubgraph (x : G) : inhabited (cycle_graph 1 ⇀ G).
Proof.
pose g : cycle_graph 1 -> G := fun _ => x.
have inj : injective g by move=> a b _; rewrite (fintype.ord1 a) (fintype.ord1 b).
have mono : forall a b : cycle_graph 1, (g a -- g b) = (a -- b).
  by move=> a b; rewrite /g sg_irrefl (fintype.ord1 a) (fintype.ord1 b) sg_irrefl.
exact: inhabits (@ISubgraph (cycle_graph 1) G g inj mono).
Qed.

End OrdinalCycles.

Arguments ordinal_induced_cycle {G k} f.
Arguments has_ordinal_induced_cycle G k : assert.
Arguments ordinal_induced_cycleb {G k} f.

(** *** Transport along induced copies *)

Lemma ordinal_induced_cycle_comp (H G : sgraph) (i : H ⇀ G) k (f : 'I_k -> H) :
  ordinal_induced_cycle f -> ordinal_induced_cycle (i \o f).
Proof.
case=> inj h; split; first exact: inj_comp (isubgraph_inj i) inj.
by move=> a b /=; rewrite (isubgraph_mono i); exact: h.
Qed.

Lemma has_ordinal_induced_cycle_isubgraph (H G : sgraph) (i : H ⇀ G) k :
  has_ordinal_induced_cycle H k -> has_ordinal_induced_cycle G k.
Proof. by case=> f oc; exists (i \o f); exact: ordinal_induced_cycle_comp oc. Qed.
