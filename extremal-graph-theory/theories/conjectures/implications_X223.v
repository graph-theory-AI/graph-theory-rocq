(** * Extremal.conjectures.implications_X223 -- corpus relation edges unlocked by wave X223.

    Five confirmed [implies] relations of meta/corpus_relations.json have both
    endpoints formalised once this wave lands:

      e076  arxiv:1810.00058#00 => #01   VERIFIED below (pure instantiation H = K_3)
      e160  arxiv:1708.07369#00 => #01   VERIFIED below (eventual => infinitely often)
      e077  arxiv:1810.00058#02 => #00   candidate (needs the paper's cleaning argument)
      e109  arxiv:2210.16971#01 => #00   candidate (the #01 endpoint is a BLOCKED placeholder)
      e116  opg:the_erdos_hajnal_conjecture => arxiv:1912.02342#00
                                         VERIFIED below (shattering gadget H_d
                                         + VC-monotonicity, foundations/vc.v)

    NB the derived file meta/corpus_relations.json still records
    [from_formal_name]/[to_formal_name] = null for the endpoints this wave
    authors; it must be regenerated (meta/build_corpus_relations.py) before
    meta/build_edge_graph.py can re-check these [gc:] citations. *)

From GTBase Require Import base.
From Extremal.foundations Require Import degree_bounds ramsey vc.
From Extremal.conjectures Require Import D2ram X58 X118 X120 X195 X196 X223.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Wave-V vocabulary equivalences (2026-09-24) ************************

    meta/STATEMENT_IMPROVEMENTS.md and the X211-X229 faithfulness audit record
    three duplications carried by the X223 vocabulary.  Each is settled below by
    one named lemma; no statement body is changed.

    (1) eps-boundedness is spelled twice: X223 bounds every CLOSED neighbourhood
    ([d * |N[v]| < p * |V(G)|]), X58 bounds the MAXIMUM DEGREE
    ([d * Delta(G) < p * |V(G)|]).  The closed form implies the Delta form on a
    non-empty graph; the reusable half lives in
    [Extremal.foundations.degree_bounds.Delta_lt_of_cln_lt] and this is the
    named bridge between the two conjecture-file predicates.  The e076 edge
    below used to inline it. *)

Lemma x223_eps_bounded_implies_x58_epsilon_bounded (G : sgraph) (p d : nat) :
  0 < #|G| -> x223_eps_bounded G p d -> x58_epsilon_bounded G p d.
Proof. exact: Delta_lt_of_cln_lt. Qed.

(** The converse fails: [Delta G < |N[v]|] for a vertex of maximum degree, so
    the Delta form is strictly weaker and only the direction above is available. *)

(** (2) [x118_edges_between] (X118) and [x120_edges_between] (X120) are the same
    definition as [x223_edges_between] up to the associativity of [&&]: all
    three count the ORDERED pairs [(a,b)] of [A x B] with [a -- b]. *)

Lemma x118_edges_betweenE (G : sgraph) (A B : {set G}) :
  x118_edges_between A B = x223_edges_between A B.
Proof. by apply: eq_card => p; rewrite !inE andbA. Qed.

Lemma x120_edges_betweenE (G : sgraph) (A B : {set G}) :
  x120_edges_between A B = x223_edges_between A B.
Proof. by apply: eq_card => p; rewrite !inE andbA. Qed.

(** (3) On DISJOINT [A] and [B] the ordered-pair count is the cardinality of the
    set of CROSS EDGES of [G] -- the edges of [E(G)] meeting both [A] and [B],
    i.e. the library-level reading |E(A,B)| of the audit note.  Disjointness is
    what makes the two counts agree: it forbids an edge from being counted twice
    (once as [(a,b)] and once as [(b,a)]). *)

Lemma x223_edges_between_card_cross (G : sgraph) (A B : {set G}) :
  [disjoint A & B] ->
  x223_edges_between A B
    = #|[set e in E(G) | (e :&: A != set0) && (e :&: B != set0)]|.
Proof.
move=> dAB.
have Dne (x y : G) : x \in A -> y \in B -> x != y.
  move=> xA yB; apply/eqP => exy.
  by move: (disjointFr dAB xA); rewrite exy yB.
have key : [set e in E(G) | (e :&: A != set0) && (e :&: B != set0)]
         = (fun p : G * G => [set p.1; p.2])
             @: [set uv : G * G | (uv.1 \in A) && (uv.2 \in B) && (uv.1 -- uv.2)].
  apply/setP => e; rewrite !inE; apply/idP/imsetP => [|[p]].
  - case/andP => eE /andP[/set0Pn[a]]; rewrite inE => /andP[ae aA].
    case/set0Pn => b; rewrite inE => /andP[be bB].
    have ab : a != b by exact: Dne.
    move: eE => /edgesP[x [y] [exy xy]].
    rewrite exy !inE in ae be.
    case/orP: ae => /eqP ax; case/orP: be => /eqP bxy.
    + by rewrite ax bxy eqxx in ab.
    + exists (a, b); last by rewrite /= exy ax bxy.
      by rewrite inE /= aA bB ax bxy.
    + exists (a, b); last by rewrite /= exy ax bxy setUC.
      by rewrite inE /= aA bB ax bxy sg_sym.
    + by rewrite ax bxy eqxx in ab.
  - rewrite inE => /andP[/andP[p1 p2] p12] ->.
    apply/andP; split.
      by rewrite in_sg_edge_set; apply/existsP; exists p.1;
         apply/existsP; exists p.2; rewrite p12 eqxx.
    apply/andP; split; apply/set0Pn.
    + by exists p.1; rewrite !inE eqxx p1.
    + by exists p.2; rewrite !inE eqxx orbT p2.
rewrite /x223_edges_between key card_in_imset //.
move=> p q; rewrite !inE => /andP[/andP[p1 p2] _] /andP[/andP[q1 q2] _] eqpq.
have H1 : p.1 = q.1.
  move: eqpq => /setP /(_ p.1); rewrite !inE eqxx => /esym/orP[/eqP//|/eqP pq2].
  by move: (Dne _ _ p1 q2); rewrite pq2 eqxx.
have H2 : p.2 = q.2.
  move: eqpq => /setP /(_ q.2); rewrite !inE eqxx orbT => /orP[/eqP q2p1|/eqP //].
  by move: (Dne _ _ p1 q2); rewrite -q2p1 eqxx.
clear eqpq p1 p2 q1 q2; case: p H1 H2 => a b /= -> ->; by case: q.
Qed.

(** ** e076 -- Conjecture 1.4 for all H implies its open case H = K_3.

    Pure instantiation, plus one weakening step: X58's eps-boundedness uses the
    maximum degree (Delta(G) < eps|G|) whereas the recovered source condition, used
    by this wave, is the CLOSED neighbourhood one (|N[v]| < eps|G| for every v).
    Since Delta(G) = |N(x)| for some x and |N(x)| < |N[x]|, the closed form implies
    the Delta form, so the H-quantified statement applies to every graph this row
    quantifies over. *)
Theorem epsilon_bounded_h_free_anticomplete_pair_implies_triangle_free_eps_bounded_anticomplete_pair :
  epsilon_bounded_h_free_anticomplete_pair_statement ->
  triangle_free_eps_bounded_anticomplete_pair_statement.
Proof.
move=> EH.
have [p [d [p0 [pd Hcore]]]] := EH 'K_3.
exists p, d; split => // G G1 Hfree Heps.
have G0 : 0 < #|G| by apply: leq_trans G1.
have Hfree58 : x58_induced_free G 'K_3 by move=> S [iso]; exact: (Hfree S iso).
have Heps58 : x58_epsilon_bounded G p d.
  exact: x223_eps_bounded_implies_x58_epsilon_bounded G0 Heps.
have [A [B [Hac [HA HB]]]] := Hcore G G1 Hfree58 Heps58.
by exists A, B; split.
Qed.

(*@EDGE from=epsilon_bounded_h_free_anticomplete_pair_statement to=triangle_free_eps_bounded_anticomplete_pair_statement kind=implies status=verified proof=epsilon_bounded_h_free_anticomplete_pair_implies_triangle_free_eps_bounded_anticomplete_pair cite="gc:e076" *)

(** ** e160 -- "k-nice for every large k" implies "k-nice for infinitely many k".

    Elementary: take the maximum of the two thresholds. *)
Theorem ramsey_nice_forest_family_eventual_implies_ramsey_nice_forest_family_infinite :
  ramsey_nice_forest_family_eventual_statement ->
  ramsey_nice_forest_family_infinite_statement.
Proof.
move=> H r Fam r0 Hf k0.
have [k1 Hk1] := H r Fam r0 Hf.
by exists (maxn k0 k1); split; [exact: leq_maxl | apply: Hk1; exact: leq_maxr].
Qed.

(*@EDGE from=ramsey_nice_forest_family_eventual_statement to=ramsey_nice_forest_family_infinite_statement kind=implies status=verified proof=ramsey_nice_forest_family_eventual_implies_ramsey_nice_forest_family_infinite cite="gc:e160" *)

(** ** e077 -- Conjecture 3.4 implies Conjecture 1.4 (CANDIDATE).

    The source itself records the implication 3.3 => 3.4 => 1.4.  It is NOT the
    trivial c = 0 instantiation: at c = 0 the guaranteed size eps*c^s*|G| of the
    A side degenerates to 0, so the sparse pair carries no information.  The real
    step is the paper's cleaning argument, which turns a c-sparse pair with c
    small into a genuinely ANTICOMPLETE pair by deleting the few vertices with
    many cross-neighbours; that argument is not formalised here, so the Qed gate
    refuses the edge and it is recorded as a candidate. *)
(*@EDGE from=h_free_eps_bounded_sparse_pair_statement to=epsilon_bounded_h_free_anticomplete_pair_statement kind=implies status=candidate proved=false cite="gc:e077" note="Literature-stated (the paper asserts 3.3 => 3.4 => 1.4). Not the c=0 instantiation: at c=0 the A-side bound eps*c^s*|G| collapses to 0. Needs the cleaning argument turning a sparse pair into an anticomplete one, which is not in scope here." *)

(** ** e109 -- directed forcing implies directed Sidorenko (CANDIDATE).

    The source endpoint arxiv:2210.16971#01 is recorded BLOCKED: its Rocq body
    ([directed_forcing_cyclic_statement]) is a PLACEHOLDER whose conclusion is
    the Sidorenko property rather than the forcing property, because forcing is a
    graph-limit notion with no finite form available here.  The corpus argument
    (forcing => Sidorenko by an interpolation / intermediate-value argument on
    oriented graphons, plus Theorem 1.5 for oriented forests) therefore has no
    faithful formal counterpart, and the placeholder does NOT entail the target
    either: it carries the extra hypothesis "the underlying graph has a cycle",
    which the bipartite target does not (oriented forests are a genuine case of
    Conjecture 1.4).  Recorded as a candidate. *)
(*@EDGE from=directed_forcing_cyclic_statement to=directed_sidorenko_bipartite_statement kind=implies status=candidate proved=false cite="gc:e109" note="Source endpoint is a BLOCKED placeholder (Sidorenko conclusion, not forcing). Even as stated it does not close: the placeholder assumes a cycle in the underlying graph, while the target also covers oriented forests." *)

(** ** e116 -- Erdos-Hajnal implies its VC-dimension specialisation.

    The reduction is now FORMAL (the two missing ingredients live in
    Extremal.foundations.vc).  For a fixed [d], let [H_d := shatter_graph d.+1]
    be the bipartite gadget on ['I_(d+1) + {set 'I_(d+1)}] in which [inr S] is
    adjacent exactly to the [inl i] with [i \in S].  Then:

    - the ['I_(d+1)]-side [shatter_side d.+1] (of size d+1) is SHATTERED by the
      neighbourhoods -- the subset cut out of it by [N(inr S)] is exactly [S] --
      so [H_d] has VC dimension at least d+1 ([not_vc_dim_leq_shatter_graph]);
    - VC dimension is MONOTONE under induced subgraphs: an [isubgraph]
      [i : F -> G] sends neighbourhood traces to neighbourhood traces
      ([opn_cap_imset]), hence shattered sets to shattered sets of the same size
      ([vc_dim_leq_isubgraph]).

    So a graph [G] of VC dimension at most [d] has no induced copy of [H_d], and
    Erdos-Hajnal for the single graph [H := H_d] applies.  Its conclusion
    [#|G| ^ a <= (maxn omega alpha) ^ b] is turned into the target's
    [#|G| <= #|S| ^ q] with [q := b]: [#|G| <= #|G| ^ a] (as [0 < a] and
    [0 < #|G|]), and [maxn omega alpha] is realised by an actual clique or
    stable set ([clique_witness] / [stable_witness], foundations/ramsey.v), whose
    cardinal is then raised to the b-th power.  The empty host is handled
    separately ([S := set0], a clique, and [#|G| = 0]) because the target has no
    non-emptiness guard while Erdos-Hajnal does. *)
Theorem the_erdos_hajnal_implies_vc_dimension_erdos_hajnal :
  the_erdos_hajnal_statement -> vc_dimension_erdos_hajnal_statement.
Proof.
move=> EH d _.
have [a [b [a0 [ab Hcore]]]] := EH (shatter_graph d.+1).
have b0 : 0 < b by exact: leq_trans a0 ab.
exists b; split => // G Hvc.
have Hfree : ~ has_induced_copy (shatter_graph d.+1) G.
  case=> i; apply: (@not_vc_dim_leq_shatter_graph d).
  exact: (@vc_dim_leq_isubgraph _ _ i d Hvc).
have [G0|G0] := posnP #|G|.
  exists set0; split; last by rewrite G0.
  by apply/orP; left; apply/cliqueP; apply: small_clique; rewrite cards0.
have Hb := Hcore G G0 Hfree.
have [K /and3P[_ clK oK]] := clique_witness [set: G].
have [A /and3P[_ stA aA]] := stable_witness [set: G].
have Hkey : #|G| <= (maxn #|K| #|A|) ^ b.
  apply: leq_trans (leq_trans Hb _); first by rewrite -{1}(expn1 #|G|) leq_pexp2l.
  by rewrite leq_exp2r // geq_max !leq_max oK aA orbT.
case: (leqP #|A| #|K|) => [AK|KA].
  by exists K; rewrite clK; split => //; move: Hkey; rewrite (maxn_idPl AK).
by exists A; rewrite stA orbT; split => //; move: Hkey; rewrite (maxn_idPr (ltnW KA)).
Qed.

(*@EDGE from=the_erdos_hajnal_statement to=vc_dimension_erdos_hajnal_statement kind=implies status=verified proof=the_erdos_hajnal_implies_vc_dimension_erdos_hajnal cite="gc:e116" note="H_d := shatter_graph d.+1 (bipartite gadget on 'I_(d+1) + {set 'I_(d+1)}, inr S ~ inl i iff i in S): its 'I_(d+1)-side is shattered, so VC-dim(H_d) > d (foundations/vc.v, not_vc_dim_leq_shatter_graph), and VC-dim is monotone under isubgraphs (opn_cap_imset, vc_dim_leq_isubgraph); hence every G with x223_vc_dim_leq G d is H_d-induced-free. EH at H = H_d gives #|G|^a <= (maxn omega alpha)^b; q := b, using #|G| <= #|G|^a and the clique/stable witnesses of ramsey.v. Empty host handled by S = set0." *)

Print Assumptions x223_eps_bounded_implies_x58_epsilon_bounded.
Print Assumptions x118_edges_betweenE.
Print Assumptions x120_edges_betweenE.
Print Assumptions x223_edges_between_card_cross.
Print Assumptions epsilon_bounded_h_free_anticomplete_pair_implies_triangle_free_eps_bounded_anticomplete_pair.
Print Assumptions ramsey_nice_forest_family_eventual_implies_ramsey_nice_forest_family_infinite.
Print Assumptions the_erdos_hajnal_implies_vc_dimension_erdos_hajnal.
