(** * Chromatic.conjectures.U4 — milestone U4 (namespace Chromatic, plan v4)

    Statement-only formalizations (axiom-free: no Conjecture/Axiom/Parameter/
    Admitted) of eleven open/partial problems on LIST colouring (choosability),
    online list colouring (paintability), list edge/total colouring, the list
    Hadwiger conjecture, and strong colouring.

    CORE undirected vocabulary comes from graph-theory-base (GTBase.base, which
    re-exports coq-graph-theory's [sgraph], [x -- y], [N], [χ]=[chi_mem],
    [ω]=[omega_mem], [clique], ['K_n]=[complete n], [≃], [ucycle], plus base's
    cross-area [Delta]).  Two FURTHER coq-graph-theory modules are needed that
    base's undirected surface does not re-export and that base does NOT own:
      - [GraphTheory.minor]  : [minor G H] ("H is a minor of G") for Row 8;
      - [GraphTheory.mgraph] : the labelled multigraph record [graph Lv Le]
        (vertex/edge finTypes + [endpoint]/[incident]/[edges_at]) for the
        edge- and total-colouring rows (4, 5, 9).
    These are imported in addition to base; they are NOT part of base's owned
    surface, so no single-ownership rule is broken.

    KEY AREA PRIMITIVES introduced here (list-colouring vocabulary; candidates
    for a future [list-colouring] sub-layer once a 2nd area needs them):
      - [list_colourable] / [list_colourable_on] : (partial) L-colourability;
      - [choosable] / [is_choice_number] : k-choosability and the choice number
        χ_ℓ = ch (as a relation [is_choice_number G m], i.e. m is the least k
        such that G is k-choosable — avoids a non-constructive [ex_minn]
        obligation in a statement-only file);
      - [colourable_count] / [is_lambda] : λ_L and λ_t (Row 2);
      - [paintableb] / [paintable] / [is_online_choice_number] : the online
        list-colouring (Mr. Paint / Mrs. Correct) game and ch^OL (Row 3);
      - [line_graph] / [total_graph] / [mDelta] / [Delta_edge_critical]
        : multigraph edge/total constructions (Rows 4, 5, 9);
      - [complete_multipartite] : K_{m*k} = complete k-partite, parts of size m
        (Row 7);
      - [acyclic_colouring] / [acyclically_choosable] : Row 10 (PLANARITY-GATED);
      - [strongly_colorable] : Row 11. *)

(* mgraph imported BEFORE base: coq-graph-theory's mgraph defines a DIRECTED `line_graph`
   (DiGraph, target=source); importing it first lets base's undirected sgraph line_graph/
   total_graph shadow it. We use mgraph for the raw edge/incident/edges_at/source/target API. *)
From GraphTheory Require Import minor mgraph.
From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** List-colouring core vocabulary — PROMOTED to graph-theory-base.
    [list_colourable], [list_colourable_on], [choosable], [is_choice_number] now live in base/
    (reusable across U4 list / U5 edge-total / U8 χ-boundedness), reused here via the base export.
    No local definitions remain.  The list-colouring derivatives below ([colourable_count],
    paintability, line/total-graph, multipartite, acyclic, strong) stay area-local. *)

(** ** Partial list colouring : λ_L and λ_t (Row 2) *****************************)

(** [mu] is the maximum number of vertices of [G] colourable from [L]
    (= λ_L in the source). *)
Definition colourable_count (G : sgraph) (C : finType) (L : G -> {set C})
    (mu : nat) : Prop :=
  (exists W : {set G}, list_colourable_on L W /\ #|W| = mu) /\
  (forall W : {set G}, list_colourable_on L W -> #|W| <= mu).

(** [lam] is λ_t : the minimum, over all size-[t] list assignments [L], of the
    maximum number λ_L of [L]-colourable vertices. *)
Definition is_lambda (G : sgraph) (t lam : nat) : Prop :=
  (exists (C : finType) (L : G -> {set C}),
      (forall v : G, #|L v| = t) /\ colourable_count L lam) /\
  (forall (C : finType) (L : G -> {set C}) (mu : nat),
      (forall v : G, #|L v| = t) -> colourable_count L mu -> lam <= mu).

(** ** Online list colouring : the paintability game (Row 3) ********************)

(** The Mr. Paint / Mrs. Correct game on [G] with token budget [f : G -> nat].
    State: [A] = the still-uncoloured ("alive") vertices, [f v] = colours still
    available at [v].  Painter wins from [(A,f)] iff [A] is empty, or every
    alive vertex still has a token and, for every nonempty marked set [M] ⊆ [A]
    (Lister's move), Painter can pick a stable [I] ⊆ [M] to colour (remove),
    decrementing the tokens of the unchosen marked vertices, and win onward.
    [n] is recursion fuel; the wrapper [paintable] supplies enough (the strict
    decrease of [\sum (f v + 1)] each round). *)
Fixpoint paintableb (G : sgraph) (n : nat) (A : {set G}) (f : G -> nat)
    {struct n} : bool :=
  match n with
  | 0 => A == set0
  | n'.+1 =>
      (A == set0) ||
      ([forall v, (v \in A) ==> (0 < f v)] &&
       [forall M : {set G},
          (M \subset A) ==> (M != set0) ==>
          [exists I : {set G},
             [&& I \subset M, dom.stable I &
                 @paintableb G n' (A :\: I)
                   (fun v => if v \in M then (f v).-1 else f v)]]])
  end.

Definition paintable (G : sgraph) (f : G -> nat) : Prop :=
  @paintableb G (\sum_(v in [set: G]) (f v).+1) [set: G] f.

Definition k_paintable (G : sgraph) (k : nat) : Prop :=
  @paintable G (fun _ : G => k).

(** The online choice number ch^OL(G) as a relation: least [m] with [G]
    [m]-paintable. *)
Definition is_online_choice_number (G : sgraph) (m : nat) : Prop :=
  k_paintable G m /\ (forall k, k_paintable G k -> m <= k).

(** ** Multigraph line- and total-graph constructions (Rows 4, 5, 9) ***********)

(** [mgraph], [loopless], [line_graph], [total_graph] (and the helpers
    share_endpoint/line_rel/madj/total_rel) are PROMOTED to graph-theory-base — used here via the
    base export — since edge/total colouring is the U5 milestone too.  [chromatic_index] (χ') and
    [total_chromatic_number] (χ'') also live in base now.  Only the area-local derivatives below
    ([mDelta], [Delta_edge_critical]) remain here. *)

(** [mDelta] (multigraph maximum degree, parallel edges counted) is now in graph-theory-base —
    promoted (U4 ∩ U5) and reused here via the base export. *)

(** [Δ]-edge-critical: deleting ANY edge strictly lowers the chromatic index
    χ'(G) = χ(L(G)).  Deleting edge [e] = deleting vertex [e] of the line
    graph, i.e. χ on [ [set: line_graph G] :\ e ]. *)
Definition Delta_edge_critical (G : mgraph) : Prop :=
  forall e : line_graph G,
    χ([set: line_graph G] :\ e) < χ([set: line_graph G]).

(** ** Complete multipartite graph K_{m*k} (Row 7) *****************************)

Definition cmp_rel (k m : nat) : rel ('I_k * 'I_m) :=
  fun x y => x.1 != y.1.

Lemma cmp_rel_sym (k m : nat) : symmetric (@cmp_rel k m).
Proof. by move=> x y; rewrite /cmp_rel eq_sym. Qed.

Lemma cmp_rel_irrefl (k m : nat) : irreflexive (@cmp_rel k m).
Proof. by move=> x; rewrite /cmp_rel eqxx. Qed.

(** K_{m*k}: complete [k]-partite graph with [k] parts each of size [m]
    (two vertices adjacent iff in different parts). *)
Definition complete_multipartite (k m : nat) : sgraph :=
  SGraph (@cmp_rel_sym k m) (@cmp_rel_irrefl k m).

(** ** Acyclic list colouring (Row 10, PLANARITY-GATED) ************************)

(** An acyclic proper L-colouring: proper, and every cycle of [G] uses MORE
    than two colours (no bichromatic cycle, i.e. every two colour classes
    induce a forest). *)
Definition acyclic_colouring (G : sgraph) (C : finType) (L : G -> {set C})
    (f : G -> C) : Prop :=
  [/\ (forall v : G, f v \in L v),
      (forall x y : G, x -- y -> f x != f y)
    & forall c : seq G, ucycleb (--) c -> 2 < size c ->
        2 < size (undup [seq f x | x <- c])].

Definition acyclically_choosable (G : sgraph) (k : nat) : Prop :=
  forall (C : finType) (L : G -> {set C}),
    (forall v : G, k <= #|L v|) ->
    exists f : G -> C, acyclic_colouring L f.

(** ** Strong colouring (Row 11) ***********************************************)

(** [G] is strongly [r]-colourable: for every partition of V(G) into blocks of
    size at most [r], there is a proper [r]-colouring assigning DISTINCT colours
    within every block. *)
Definition strongly_colorable (G : sgraph) (r : nat) : Prop :=
  forall P : {set {set G}},
    partition P [set: G] -> (forall B : {set G}, B \in P -> #|B| <= r) ->
    exists f : G -> 'I_r,
      (forall x y : G, x -- y -> f x != f y) /\
      (forall B : {set G}, B \in P -> {in B &, injective f}).

(** ============================================================================
    STATEMENTS
    ========================================================================== *)

(** Corpus row: opg:partial_list_coloring
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/partial_list_coloring/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/partial_list_coloring.json
    English statement: (Albertson, Grossman and Haas 2000; Open Problem Garden, "Partial List Coloring")
      For every finite simple graph G, every t and every cl such that cl is the choice number (list
      chromatic number) of G and t <= cl, and for every assignment to each vertex of a list of
      exactly t colours taken from an arbitrary finite palette, some set W of vertices can be
      properly coloured from those lists and satisfies t * |V(G)| <= cl * |W|, the division-free
      form of |W| >= t * n / cl.
    Definitions: [is_choice_number G cl] - cl is the least k such that G is k-choosable (GTBase
      base/theories/base.v); [list_colourable_on L W] - there is a partial colouring, total on W,
      picking each vertex of W a colour from its list and proper on W (GTBase base.v); the palette
      is an arbitrary finType quantified inside the statement, so no fixed colour universe is
      assumed.
    Notes: The source inequality "at least t*n/chi_l vertices can be coloured" is multiplied out
      to avoid nat division; the Rocq form is exactly "some colourable set W has cl * |W| >= t * n".
      Lists have size EXACTLY t, as in the source. The source range 0 <= t <= chi_l is rendered by t
      <= cl, 0 <= t being automatic on nat. *)
Definition partial_list_coloring_statement : Prop :=
  forall (G : sgraph) (t cl : nat),
    is_choice_number G cl -> t <= cl ->
    forall (C : finType) (L : G -> {set C}),
      (forall v : G, #|L v| = t) ->
      exists W : {set G},
        list_colourable_on L W /\ t * #|G| <= cl * #|W|.

(** Corpus row: opg:partial_list_coloring_0
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/partial_list_coloring_0/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/partial_list_coloring_0.json
    English statement: (Open Problem Garden, "Partial List Coloring" (ratio form, second conjecture of the node))
      For every finite simple graph G with choice number cl and all r and s with 1 <= r <= s <= cl,
      if lr is the value of lambda_r and ls the value of lambda_s, then r * ls <= s * lr, the
      division-free form of lambda_r / r >= lambda_s / s.
    Definitions: [is_lambda G t lam] - lam is the minimum, over all assignments of lists of size
      exactly t, of the maximum number of vertices colourable from those lists (this file);
      [colourable_count L mu] - mu is that maximum for one fixed list assignment L, stated as "some
      colourable set has size mu and every colourable set has size at most mu" (this file);
      [is_choice_number] and [list_colourable_on] come from GTBase base/theories/base.v.
    Notes: lambda_r and lambda_s are passed as relationally specified naturals rather than
      computed, so the statement is conditional on their existence; this keeps the file proof-free
      and non-constructive-choice-free. The ratio is cross-multiplied to avoid nat division. *)
Definition partial_list_coloring_0_statement : Prop :=
  forall (G : sgraph) (r s cl lr ls : nat),
    is_choice_number G cl ->
    1 <= r -> r <= s -> s <= cl ->
    is_lambda G r lr -> is_lambda G s ls ->
    r * ls <= s * lr.

(** Corpus row: opg:bounding_the_on_line_choice_number_in_terms_of_the_choice_number
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/bounding_the_on_line_choice_number_in_terms_of_the_choice_number/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/bounding_the_on_line_choice_number_in_terms_of_the_choice_number.json
    English statement: (Zhu 2009; Open Problem Garden, "Bounding the on-line choice number in terms of the choice number")
      For every M there exist a finite simple graph G, its choice number ch and its online choice
      number ch-OL such that M <= ch-OL - ch; that is, the difference between the online choice
      number and the choice number is unbounded.
    Definitions: [is_online_choice_number G m] - m is the least k for which G is k-paintable (this
      file); [k_paintable] / [paintable] / [paintableb] - the Mr. Paint and Mrs. Correct online
      list-colouring game, where Lister marks a nonempty subset of the still-uncoloured vertices and
      Painter answers with a stable subset of it, played with an explicit recursion fuel that the
      wrapper supplies from the total token count (this file); [is_choice_number] (GTBase
      base/theories/base.v).
    Notes: The corpus row is the QUESTION "Are there graphs for which ch-OL - ch is arbitrarily
      large?"; the Rocq body is its affirmative reading. The difference is a truncated nat
      subtraction, which is harmless here because the inequality is M <= ch-OL - ch and is therefore
      equivalent to ch + M <= ch-OL. *)
Definition bounding_the_on_line_choice_number_in_terms_of_the_c_statement : Prop :=
  forall M : nat, exists (G : sgraph) (ch chol : nat),
    [/\ is_choice_number G ch, is_online_choice_number G chol & M <= chol - ch].

(** Corpus row: opg:edge_list_coloring_conjecture
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/edge_list_coloring_conjecture/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/edge_list_coloring_conjecture.json
    English statement: (Vizing, Gupta, Albertson-Collins, Bollobas-Harris; Open Problem Garden, "Edge list coloring conjecture")
      For every loopless multigraph G, the list edge chromatic number of G equals its edge chromatic
      number: if m is the choice number of the line graph of G, then m equals the chromatic number
      of the line graph of G.
    Definitions: [line_graph G] - the simple graph whose vertices are the edges of the multigraph
      G, two of them adjacent when they are distinct and share an endpoint (GTBase
      base/theories/base.v); [loopless G] - no edge has equal source and target (base.v);
      [is_choice_number] (base.v). Edge colouring is thus reduced to vertex colouring of the line
      graph, so the edge chromatic number is chi of the line graph and the list edge chromatic
      number is its choice number.
    Notes: The equation is stated in the direction m = chi, with m universally quantified over the
      relational choice number, so the statement is conditional on a choice number existing; every
      finite graph has one. *)
Definition edge_list_coloring_statement : Prop :=
  forall (G : mgraph) (m : nat),
    loopless G ->
    is_choice_number (line_graph G) m ->
    m = χ([set: line_graph G]).

(** Corpus row: opg:list_colorings_of_edge_critical_graphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/list_colorings_of_edge_critical_graphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/list_colorings_of_edge_critical_graphs.json
    English statement: (Vizing 1976; Open Problem Garden, "List colorings of edge-critical graphs")
      For every loopless multigraph G that is edge-critical for the chromatic index, and for every
      assignment to each edge of a list of exactly Delta(G) colours, either all the lists are equal
      to each other or G admits a proper edge colouring picking each edge's colour from its own
      list.
    Definitions: [Delta_edge_critical G] - deleting any single vertex of the line graph, that is
      any single edge of G, strictly decreases chi of the line graph, i.e. strictly decreases the
      chromatic index (this file); [mDelta G] - the maximum degree of a multigraph, parallel edges
      counted (GTBase base/theories/base.v); [line_graph], [loopless] and [list_colourable] (GTBase
      base.v).
    Notes: Faithfulness caveat: the classical notion of a Delta-edge-critical graph also requires
      the chromatic index to be Delta + 1, whereas [Delta_edge_critical] only requires that removing
      any edge lowers the chromatic index. The Rocq hypothesis is therefore satisfied by more graphs
      than the source's, which makes this statement formally stronger than the conjecture. The
      source's "unless all lists are equal" is encoded as a disjunction whose first branch is "all
      lists are equal". *)
Definition list_colorings_of_edge_critical_graphs_statement : Prop :=
  forall (G : mgraph),
    loopless G -> Delta_edge_critical G ->
    forall (C : finType) (L : line_graph G -> {set C}),
      (forall e : line_graph G, #|L e| = mDelta G) ->
      (forall e e' : line_graph G, L e = L e') \/ list_colourable L.

(** Corpus row: opg:list_colourings_of_complete_multipartite_graphs_with_2_big_parts
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/list_colourings_of_complete_multipartite_graphs_with_2_big_parts/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/list_colourings_of_complete_multipartite_graphs_with_2_big_parts.json
    English statement: (Open Problem Garden, "List Colourings of Complete Multipartite Graphs with 2 Big Parts")
      For all a and b at least 2 there is a smallest t such that the join of the complete bipartite
      graph on parts of sizes a and b with the complete graph on t vertices has choice number equal
      to its chromatic number: the equality holds for that t and fails for every t' < t.
    Definitions: [KB a b] - the complete bipartite graph with parts of size a and b, and [sjoin] -
      the join of two graphs, and [complete t] = ['K_t] (all coq-graph-theory sgraph.v);
      [is_choice_number] (GTBase base/theories/base.v).
    Notes: The corpus row asks for the VALUE of the smallest such t; the Rocq body only asserts
      that this smallest t is well defined, that is, that the set of good t is nonempty and hence
      has a least element. This is a strictly weaker proposition than answering the question, and it
      is the honest statement-only encoding of a "what is" question. *)
Definition list_colourings_of_complete_multipartite_graphs_with_statement : Prop :=
  forall a b : nat, 2 <= a -> 2 <= b ->
    exists t : nat,
      (forall m, is_choice_number (sjoin (KB a b) (complete t)) m ->
                 m = χ([set: sjoin (KB a b) (complete t)])) /\
      (forall t', t' < t ->
         ~ (forall m, is_choice_number (sjoin (KB a b) (complete t')) m ->
                      m = χ([set: sjoin (KB a b) (complete t')]))).

(** Corpus row: opg:choice_number_of_k_chromatic_graphs_of_bounded_order
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/choice_number_of_k_chromatic_graphs_of_bounded_order/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/choice_number_of_k_chromatic_graphs_of_bounded_order.json
    English statement: (Ohba style question; Open Problem Garden, "Choice Number of k-Chromatic Graphs of Bounded Order")
      For every finite simple graph G whose chromatic number is k and which has at most m * k
      vertices, the choice number of G is at most the choice number of the complete k-partite graph
      whose k parts all have size m.
    Definitions: [complete_multipartite k m] - the graph on ['I_k * 'I_m] in which two vertices
      are adjacent exactly when their first coordinates differ, i.e. the complete k-partite graph
      with all parts of size m (this file); [is_choice_number] (GTBase base/theories/base.v).
    Notes: Both choice numbers are passed relationally, so the statement is conditional on their
      existence; every finite graph has a choice number. The argument order of
      [complete_multipartite k m] is parts-then-part-size, matching the source's K_{m*k}. *)
Definition choice_number_of_k_chromatic_graphs_of_bounded_order_statement : Prop :=
  forall (G : sgraph) (k m chG chK : nat),
    χ([set: G]) = k -> #|G| <= m * k ->
    is_choice_number G chG ->
    is_choice_number (complete_multipartite k m) chK ->
    chG <= chK.

(** Corpus row: opg:list_hadwiger_conjecture
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/list_hadwiger_conjecture/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/list_hadwiger_conjecture.json
    English statement: (Kawarabayashi and Mohar 2007; Open Problem Garden, "List Hadwiger Conjecture")
      There is a constant c at least 1 such that, for every t and every finite simple graph G having
      no complete graph on t vertices as a minor, the choice number of G is at most c * t.
    Definitions: [minor G H] - H is a minor of G (coq-graph-theory minor.v), so K_t-minor-freeness
      is the negation of [minor G ('K_t)]; ['K_t] is the complete graph; [is_choice_number] (GTBase
      base/theories/base.v).
    Notes: Quantifier order is load-bearing and matches the source: the constant c is chosen once,
      before G and t, so the bound is uniform. c is a natural number, which is no loss since the
      source asks for a constant at least 1. *)
Definition list_hadwiger_statement : Prop :=
  exists c : nat, 1 <= c /\
    forall (G : sgraph) (t chG : nat),
      ~ minor G ('K_t) -> is_choice_number G chG -> chG <= c * t.

(** Corpus row: opg:list_total_colouring_conjecture
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/list_total_colouring_conjecture/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/list_total_colouring_conjecture.json
    English statement: (Borodin, Kostochka and Woodall 1997; Open Problem Garden, "List Total Colouring Conjecture")
      For every multigraph H, the choice number of the total graph of H equals the chromatic number
      of the total graph of H.
    Definitions: [total_graph H] - the simple graph whose vertices are the vertices and the edges
      of H, with two vertices adjacent when they are joined by an edge, two edges adjacent when they
      share an endpoint, and a vertex adjacent to an edge when it is incident with it (GTBase
      base/theories/base.v); [is_choice_number] (base.v).
    Notes: Unlike the edge-colouring row, no [loopless] guard is imposed here; the source says
      only "the total graph of a multigraph". *)
Definition list_total_colouring_statement : Prop :=
  forall (H : mgraph) (m : nat),
    is_choice_number (total_graph H) m ->
    m = χ([set: total_graph H]).

(** Corpus row: opg:acyclic_list_colouring_of_planar_graphs
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/acyclic_list_colouring_of_planar_graphs/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/acyclic_list_colouring_of_planar_graphs.json
    English statement: (Borodin, Fon-Der-Flaass, Kostochka, Raspaud and Sopena 2002; Open Problem Garden, "Acyclic list colouring of planar graphs")
      Every planar graph is acyclically 5-choosable: for every assignment of lists of at least 5
      colours to the vertices there is a colouring picking each vertex's colour from its list,
      giving different colours to adjacent vertices, and using more than two distinct colours on
      every cycle.
    Definitions: [wagner_planar G] - G has neither K5 nor K3,3 as a minor, which by Wagner's
      theorem is exactly planarity for finite simple graphs; it is used opaquely here (GTBase
      base/theories/base.v); [acyclically_choosable G k] - every list assignment with all lists of
      size at least k admits an [acyclic_colouring] (this file); [acyclic_colouring L f] - f picks
      colours from the lists, is proper, and every [ucycle] of size greater than 2 carries more than
      two distinct colours (this file).
    Notes: Planarity is combinatorial and axiom-free, no abstract planarity placeholder and no
      four-colour-theorem dependency. "No bichromatic cycle" is encoded as "every genuine cycle uses
      at least three colours", the size guard 2 < size c dropping the empty and single-edge [ucycle]
      artefacts. *)
Definition acyclic_list_colouring_of_planar_graphs_statement : Prop :=
  forall (G : sgraph),
    wagner_planar G -> acyclically_choosable G 5.

(** Corpus row: opg:strong_colorability
    Site: https://graph-theory-ai.github.io/graph-conjectures/op/strong_colorability/
    Review: https://github.com/graph-theory-AI/graph-conjectures/blob/main/data/reviews/strong_colorability.json
    English statement: (Alon 1988, Fellows 1990; Open Problem Garden, "Strong colorability")
      Every finite simple graph G with maximum degree at least 1 is strongly 2*Delta(G)-colourable:
      for every partition of the vertex set into blocks of size at most 2*Delta(G) there is a
      colouring by 2*Delta(G) colours that gives different colours to adjacent vertices and distinct
      colours to the vertices of each block.
    Definitions: [strongly_colorable G r] - for every [partition] of the full vertex set into
      blocks of size at most r there is a map into ['I_r] that is proper and injective on every
      block (this file); [Delta G] (GTBase base/theories/base.v); [partition] (mathcomp finset).
    Notes: The source defines strong r-colourability for POSITIVE r, so the formal row carries the
      guard 0 < Delta G: without it, an edgeless nonempty graph would have r = 0 and the conclusion
      would ask for a map into the empty type, making the statement false for a spurious reason. *)
Definition strong_colorability_statement : Prop :=
  forall G : sgraph, 0 < Delta G -> strongly_colorable G (2 * Delta G).
