(** * Hypergraph.foundations.hypergraph -- shared finite-hypergraph vocabulary

    WP4b foundation for the hypergraph-theory package.  A finite hypergraph is a
    pair of a [finType] of vertices [T] and a family of hyperedges
    [E : {set {set T}}]; nothing in coq-graph-theory / GTBase models that, so the
    package had re-declared the same notions once per conjecture file (the
    improvement ledger meta/STATEMENT_IMPROVEMENTS.md records "k-uniform" defined
    SEVEN times).  This file is the single home for the notions the X217 / X225
    waves need, so that no eighth copy is created.  The pre-existing per-file
    copies are NOT rewritten here: that migration (with the equivalence lemmas
    [x6_uniform E k <-> hg_uniform E k], ...) is WP6 work.

    Contents:
      - basic shape: [hg_uniform] / [hg_uniformb], [hg_loopless], [hg_degree],
        [hg_restrict] (the subhypergraph spanned by a vertex set),
        [hg_partite_uniform];
      - connectivity: [hg_link] (two vertices share a hyperedge), [hg_move]
        (link or stay), [hg_connected], [hg_connected_on];
      - colouring: [hg_proper_colouring] (no monochromatic hyperedge),
        [hg_colourable];
      - minors: [hg_clique_minor_model] / [hg_has_clique_minor] (disjoint
        connected branch sets pairwise joined by a hyperedge inside their union);
      - degeneracy: [hg_degenerate_leb], [hg_degeneracy] (least d such that every
        non-empty vertex set spans a vertex of degree at most d), [hg_skeleton]
        (the (i+1)-sets contained in a hyperedge), [hg_skel_degeneracy],
        [hg_dmax];
      - extremal numbers: [hg_containsb] (an injective copy of a pattern
        hypergraph), [hg_turan] (the Turan number ex(n,H));
      - the cops-and-robbers game: [hg_caught], [hg_cops_move], [hg_win] (the
        finite-horizon cop-win closure on positions), [hg_cop_win],
        [hg_is_cop_number].

    NAME CLASH TO RESOLVE IN WP6: [Hypergraph.conjectures.U12] also declares an
    [hg_connected], but it is Berge EDGE-connectivity (E non-empty, and any two
    hyperedges joined by a chain of pairwise intersecting hyperedges).  The one
    below is VERTEX-connectivity (any two vertices joined by a chain of vertices
    in which consecutive ones share a hyperedge), which is what the
    cops-and-robbers row needs.  The two notions differ on hypergraphs with
    isolated vertices.  No file imports both modules today; the consolidation
    (one canonical name here, the U12 copy replaced by an equivalence lemma) is
    WP6 work, as is the absorption of the seven copies of "k-uniform"
    ([k_uniform], [x6_uniform], [x104_uniform], [x108_uniform], [x119_uniform],
    [x137_uniform], [x209_uniform]) into [hg_uniform].

    Every lemma below is [Qed]-closed and axiom-free. *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Hypergraph.
Variable T : finType.
Implicit Types (E : {set {set T}}) (e S : {set T}) (v : T).

(** ** Shape ************************************************************** *)

(** [k]-uniformity: every hyperedge has exactly [k] vertices. *)
Definition hg_uniform E (k : nat) : Prop := forall e, e \in E -> #|e| = k.

Definition hg_uniformb E (k : nat) : bool := [forall e in E, #|e| == k].

Lemma hg_uniformP E k : reflect (hg_uniform E k) (hg_uniformb E k).
Proof.
apply: (iffP forallP) => [H e eE|H e].
  by apply/eqP; move: (H e); rewrite eE.
by apply/implyP => eE; apply/eqP; exact: H.
Qed.

(** Looplessness: every hyperedge has at least two vertices.  A hyperedge of
    size at most 1 could never be properly coloured. *)
Definition hg_loopless E : Prop := forall e, e \in E -> 2 <= #|e|.

(** Number of hyperedges through a vertex. *)
Definition hg_degree E v : nat := #|[set e in E | v \in e]|.

(** The subhypergraph spanned by a vertex set: the hyperedges inside it. *)
Definition hg_restrict E S : {set {set T}} := [set e in E | e \subset S].

(** [k]-partite [k]-uniform: [part] splits the vertices into [k] classes and
    every hyperedge meets each class exactly once. *)
Definition hg_partite_uniform (k : nat) (part : T -> 'I_k) E : Prop :=
  forall e, e \in E -> forall j : 'I_k, #|[set v in e | part v == j]| = 1.

Lemma hg_degree_le E S v : hg_degree (hg_restrict E S) v <= #|E|.
Proof.
rewrite /hg_degree /hg_restrict; apply: subset_leq_card; apply/subsetP => e.
by rewrite !inE => /andP[/andP[eE _] _].
Qed.

(** ** Connectivity ******************************************************* *)

(** Two vertices are linked when some hyperedge contains both. *)
Definition hg_link E : rel T := fun u v => [exists e in E, (u \in e) && (v \in e)].

(** One move of a player: stay put, or walk to a vertex of a common hyperedge. *)
Definition hg_move E : rel T := fun u v => (u == v) || hg_link E u v.

Definition hg_connected E : Prop := forall u v : T, connect (hg_link E) u v.

(** Connectivity of the subhypergraph spanned by [S] (used for branch sets). *)
Definition hg_connected_on E S : Prop :=
  forall u v : T, u \in S -> v \in S -> connect (hg_link (hg_restrict E S)) u v.

Lemma hg_linkP E (e : {set T}) (u v : T) :
  e \in E -> u \in e -> v \in e -> hg_link E u v.
Proof. by move=> eE ue ve; apply/existsP; exists e; rewrite eE ue ve. Qed.

Lemma hg_link0 (u v : T) : hg_link (set0 : {set {set T}}) u v = false.
Proof. by apply/negbTE; apply/existsPn => e; rewrite inE. Qed.

Lemma hg_connect0 (u v : T) :
  connect (hg_link (set0 : {set {set T}})) u v -> u = v.
Proof.
case/connectP => -[|x p] /=; first by move=> _ ->.
by move=> /andP[]; rewrite hg_link0.
Qed.

Lemma hg_move_refl E : reflexive (hg_move E).
Proof. by move=> v; rewrite /hg_move eqxx. Qed.

Lemma hg_link_sym E : symmetric (hg_link E).
Proof.
move=> u v; rewrite /hg_link.
by apply/existsP/existsP => -[e /andP[eE /andP[ue ve]]]; exists e;
   rewrite eE ue ve.
Qed.

(** ** Colouring ********************************************************** *)

(** A colouring is proper when no hyperedge is monochromatic. *)
Definition hg_proper_colouring (C : finType) E (col : T -> C) : Prop :=
  forall e, e \in E -> exists x y, [/\ x \in e, y \in e & col x != col y].

Definition hg_colourable E (m : nat) : Prop :=
  exists col : T -> 'I_m, hg_proper_colouring E col.

(** ** Minors ************************************************************* *)

(** A [K_t]-minor model: [t] non-empty, pairwise disjoint, connected branch
    sets, any two of them joined by a hyperedge lying inside their union and
    meeting both. *)
Definition hg_branch_family E (t : nat) (B : 'I_t -> {set T}) : Prop :=
  [/\ forall h, B h != set0,
      forall h h', h != h' -> [disjoint B h & B h'] &
      forall h, hg_connected_on E (B h)].

Definition hg_clique_minor_model E (t : nat) (B : 'I_t -> {set T}) : Prop :=
  hg_branch_family E B /\
  forall h h' : 'I_t, h != h' ->
    exists e, [/\ e \in E, e \subset B h :|: B h',
                  e :&: B h != set0 & e :&: B h' != set0].

Definition hg_has_clique_minor E (t : nat) : Prop :=
  exists B : 'I_t -> {set T}, hg_clique_minor_model E B.

(** A hypergraph on fewer than [t] vertices has no [K_t] minor: the branch
    sets are non-empty and pairwise disjoint, so they inject into the vertices. *)
Lemma hg_minor_card E (t : nat) : hg_has_clique_minor E t -> t <= #|T|.
Proof.
case=> B [[Bne Bdis _] _].
pose g (h : 'I_t) := xchoose (set0Pn (B h) (Bne h)).
have gP h : g h \in B h by apply: (xchooseP (set0Pn (B h) (Bne h))).
have ginj : injective g.
  move=> h h' gg; apply/eqP; apply: contraT => neq.
  have := Bdis _ _ neq; rewrite -setI_eq0 => /eqP/setP/(_ (g h)).
  by rewrite !inE gP gg gP.
by rewrite -(card_ord t); apply: (leq_card g ginj).
Qed.

(** ** Degeneracy ********************************************************* *)

(** [d]-degeneracy: every non-empty vertex set spans a vertex of degree at
    most [d] in the subhypergraph it spans. *)
Definition hg_degenerate_leb E (d : nat) : bool :=
  [forall S : {set T}, (S != set0) ==> [exists v in S, hg_degree (hg_restrict E S) v <= d]].

Lemma hg_degenerate_card E : hg_degenerate_leb E #|E|.
Proof.
apply/forallP => S; apply/implyP => /set0Pn[v vS].
by apply/existsP; exists v; rewrite vS hg_degree_le.
Qed.

Lemma hg_degenerate_ex E : exists d, hg_degenerate_leb E d.
Proof. by exists #|E|; apply: hg_degenerate_card. Qed.

(** The degeneracy of a hypergraph: the least such [d]. *)
Definition hg_degeneracy E : nat := ex_minn (hg_degenerate_ex E).

Lemma hg_degeneracyP E : hg_degenerate_leb E (hg_degeneracy E).
Proof. by rewrite /hg_degeneracy; case: ex_minnP. Qed.

Lemma hg_degeneracy_min E d : hg_degenerate_leb E d -> hg_degeneracy E <= d.
Proof. by rewrite /hg_degeneracy; case: ex_minnP => m _ min; apply: min. Qed.

Lemma hg_degeneracy_le E : hg_degeneracy E <= #|E|.
Proof. by apply: hg_degeneracy_min; apply: hg_degenerate_card. Qed.

Lemma hg_degeneracy0 : hg_degeneracy set0 = 0.
Proof.
apply/eqP; rewrite -leqn0.
by apply: leq_trans (hg_degeneracy_le _) _; rewrite cards0.
Qed.

(** The [i]-skeleton: all [(i+1)]-element sets contained in a hyperedge. *)
Definition hg_skeleton E (i : nat) : {set {set T}} :=
  [set f : {set T} | (#|f| == i.+1) && [exists e in E, f \subset e]].

(** The [i]-th skeletal degeneracy [d_i(H)]. *)
Definition hg_skel_degeneracy E (i : nat) : nat := hg_degeneracy (hg_skeleton E i).

(** [d_max(H) = max_{1 <= i < k} d_i(H)]. *)
Definition hg_dmax E (k : nat) : nat := \max_(i < k | 0 < i) hg_skel_degeneracy E i.

Lemma hg_skeleton0 i : hg_skeleton (set0 : {set {set T}}) i = set0.
Proof.
apply/setP => f; rewrite !inE.
suff -> : [exists e in (set0 : {set {set T}}), f \subset e] = false by rewrite andbF.
by apply/negbTE; apply/existsPn => e; rewrite inE.
Qed.

Lemma hg_dmax0 k : hg_dmax (set0 : {set {set T}}) k = 0.
Proof.
apply/eqP; rewrite -leqn0; apply/bigmax_leqP => i _.
by rewrite /hg_skel_degeneracy hg_skeleton0 hg_degeneracy0.
Qed.

(** ** Cops and robbers *************************************************** *)

(** Positions of [c] cops are [c]-tuples of vertices (as finite functions).
    The robber is caught as soon as a cop occupies his vertex. *)
Definition hg_caught (c : nat) (C : {ffun 'I_c -> T}) v : bool :=
  [exists i, C i == v].

Definition hg_cops_move E (c : nat) (C C' : {ffun 'I_c -> T}) : bool :=
  [forall i, hg_move E (C i) (C' i)].

(** [hg_win E c m C r]: from the position with the cops at [C], the robber at
    [r] and the cops to move, the cops catch the robber within [m] rounds.  A
    round is: the cops each move along a hyperedge (or stay) -- catching the
    robber at once if one of them lands on him -- and then the robber moves.
    This is the finite-horizon cop-win closure on positions. *)
Fixpoint hg_win E (c m : nat) (C : {ffun 'I_c -> T}) (r : T) : bool :=
  hg_caught C r ||
  match m with
  | 0 => false
  | m'.+1 =>
      [exists C' : {ffun 'I_c -> T},
         hg_cops_move E C C' &&
         (hg_caught C' r ||
          [forall r' : T, hg_move E r r' ==> @hg_win E c m' C' r'])]
  end.

(** [c] cops have a winning strategy: they have an initial placement and a
    horizon from which they catch every robber start. *)
Definition hg_cop_win E (c : nat) : Prop :=
  exists (m : nat) (C : {ffun 'I_c -> T}), forall r : T, @hg_win E c m C r.

(** [c] is THE cop number: [c] cops win and no smaller number does. *)
Definition hg_is_cop_number E (c : nat) : Prop :=
  hg_cop_win E c /\ forall c' : nat, hg_cop_win E c' -> c <= c'.

Lemma exists_I0 (P : pred 'I_0) : [exists i, P i] = false.
Proof. by apply/existsP => -[[m Hm] _]; rewrite ltn0 in Hm. Qed.

(** No cop at all never catches anybody: the game is not degenerate. *)
Lemma hg_win_no_cop E m (C : {ffun 'I_0 -> T}) (r : T) : @hg_win E 0 m C r = false.
Proof.
elim: m C r => [|m IH] C r /=; first by rewrite /hg_caught exists_I0.
apply/negbTE; rewrite negb_or /hg_caught exists_I0 /=.
apply/existsPn => C'; rewrite negb_and; apply/orP; right.
rewrite negb_or exists_I0 /=; apply/forallPn; exists r.
by rewrite negb_imply hg_move_refl /= IH.
Qed.

Lemma hg_cop_win_no_cop E (v0 : T) : ~ hg_cop_win E 0.
Proof. by move=> [m [C]] /(_ v0); rewrite hg_win_no_cop. Qed.

(** Some number of cops always wins: one cop per vertex. *)
Lemma hg_cop_win_card E : hg_cop_win E #|T|.
Proof.
exists 0, [ffun i => enum_val i] => r.
rewrite /= orbF; apply/existsP; exists (enum_rank r).
by rewrite ffunE enum_rankK.
Qed.

(** One cop suffices when a single vertex reaches every vertex in one move. *)
Lemma hg_cop_win1 E (v0 : T) : (forall u : T, hg_move E v0 u) -> hg_cop_win E 1.
Proof.
move=> Hmv; exists 1, [ffun _ => v0] => r.
apply/orP; right; apply/existsP; exists [ffun _ => r]; apply/andP; split.
  by apply/forallP => i; rewrite !ffunE.
by apply/orP; left; apply/existsP; exists ord0; rewrite ffunE.
Qed.

End Hypergraph.

(** ** Extremal numbers *************************************************** *)

(** [E] contains a copy of the pattern hypergraph [F]: an injective vertex map
    sending every hyperedge of [F] to a hyperedge of [E] (not necessarily an
    induced copy). *)
Definition hg_containsb (S T : finType) (F : {set {set S}}) (E : {set {set T}})
  : bool :=
  [exists f : {ffun S -> T},
     injectiveb f && [forall e in F, [set f x | x in e] \in E]].

(** The Turan number [ex(n,F)] of a [k]-uniform pattern [F]: the largest number
    of hyperedges of an [F]-free [k]-uniform hypergraph on [n] vertices. *)
Definition hg_turan (S : finType) (F : {set {set S}}) (k n : nat) : nat :=
  \max_(E : {set {set 'I_n}} | hg_uniformb E k && ~~ hg_containsb F E) #|E|.

Lemma hg_turan_le (S : finType) (F : {set {set S}}) (k n : nat) :
  hg_turan F k n <= 2 ^ n.
Proof.
have -> : 2 ^ n = #|powerset [set: 'I_n]| by rewrite card_powerset cardsT card_ord.
apply/bigmax_leqP => E _.
by apply: subset_leq_card; apply/subsetP => A _; rewrite powersetE subsetT.
Qed.
