(** * Digraph.conjectures.implications_X1 — wave X1 implication edges

    Implication edges of meta/corpus_relations.json whose TARGET row belongs to
    milestone X1 (majority colouring, arXiv:1608.03040; the hero dichotomy,
    arXiv:2009.13319).

      - e016 : arxiv:1608.03040#00 ==> arxiv:1608.03040#03
               (majority 3-colouring of all digraphs ==> of all tournaments).
      - e017 : arxiv:1608.03040#00 ==> arxiv:1608.03040#04
               (majority 3-colouring of all digraphs ==> of Eulerian digraphs).
      - e018 : arxiv:1608.03040#01 ==> arxiv:1608.03040#00
               (the (1/k, k+1 colours) conjecture at k = 2 IS majority
               3-colouring).
      - e104 : arxiv:2009.13319#01 ==> arxiv:2009.13319#02
               (hero dichotomy ==> Conjecture 4.4).  Proved below without
               Berger's theorem: [conj_4_2] takes the inductive [hero], and
               K1 joined l times is a hero and a transitive tournament.

    The three majority edges are class/parameter instantiations already
    Qed-closed inside conjectures/colouring_variants.v; they are restated here
    under the federation naming convention
    [<from without _statement>_implies_<to without _statement>] so that the
    @EDGE records can name their backing theorem. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented tournament.
From Digraph.conjectures Require Import colouring_variants heroes heroes_dichotomy.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*@EDGE from=majority_3col_statement to=majority_3col_tournament_statement kind=implies status=verified proof=majority_3col_implies_majority_3col_tournament cite="gc:e016" note="Class instantiation: a tournament IS a diGraphType (the Tournament structure inherits DiGraph) and is loopless (its arc relation is irreflexive, arcxx), and both rows use the same majority_col predicate, so the universal statement applied to T and its looplessness is literally the conclusion." *)

Theorem majority_3col_implies_majority_3col_tournament :
  majority_3col_statement -> majority_3col_tournament_statement.
Proof. exact: majority_3col_implies_tournament. Qed.

(*@EDGE from=majority_3col_statement to=majority_3col_eulerian_statement kind=implies status=verified proof=majority_3col_implies_majority_3col_eulerian cite="gc:e017" note="Hypothesis dropping: both rows carry the loopless D guard, and the target only adds the eulerian D premise to the same conclusion, so the source applies to D and its looplessness after discarding the eulerian premise." *)

Theorem majority_3col_implies_majority_3col_eulerian :
  majority_3col_statement -> majority_3col_eulerian_statement.
Proof. exact: majority_3col_implies_eulerian. Qed.

(*@EDGE from=majority_k1col_statement to=majority_3col_statement kind=implies status=verified proof=majority_k1col_implies_majority_3col cite="gc:e018" note="Parameter instantiation at k = 2: 'I_k.+1 becomes 'I_3 and kmajority_col 2 col is CONVERTIBLE to majority_col col (kmajority_col2 in colouring_variants.v), so the k = 2 instance, with the loopless D guard passed through, is the target verbatim." *)

Theorem majority_k1col_implies_majority_3col :
  majority_k1col_statement -> majority_3col_statement.
Proof. exact: colouring_variants.majority_k1col_implies_majority_3col. Qed.

(*@EDGE from=conj_4_2 to=conj_4_4 kind=implies status=verified proof=conj_4_2_implies_conj_4_4_unconditional cite="gc:e104" note="Rocq-only, without Berger's theorem: conj_4_2 quantifies over the INDUCTIVE hero of heroes.v (K1, djoin, c3sub), and K1 joined l times in front of K1 is such a hero and a transitive tournament on l + 1 vertices (oriented by the new instance on djoin), so the right disjunct of conj_4_2 bounds the dichromatic number of the class with that hero and F forbidden, which contains the class of conj_4_4 at l + 1 (a tournament on l + 1 vertices is l + 1 pairwise adjacent vertices); at l = 0 the class is empty. The conditional conj_4_2_implies_conj_4_4 of implications.v, whose hypothesis forall l, hero (TT l) fails at l = 0, is not this edge's proof." *)

(** ** e104: the hero dichotomy (Conjecture 4.2) ==> Conjecture 4.4, without Berger's
    theorem.

    [conj_4_2] quantifies over the INDUCTIVE [hero] of heroes.v (K1, domination
    joins, C3-substitutions).  K1 joined l times in front of K1 is such a hero, a
    transitive tournament, and has l + 1 vertices ([transitive_tournament_hero]; it is
    an oriented digraph through the instance on [djoin] below).  At that hero the right
    disjunct of [conj_4_2] holds, so the class with the hero and F forbidden has
    bounded dichromatic number.  A digraph with no l + 1 pairwise adjacent vertices
    has no induced copy of a tournament on l + 1 vertices
    ([noKl_implies_indfree_tournament]), so the class of [conj_4_4] lies inside it.
    For l = 0 the class of [conj_4_4] is empty (the empty set is a K_0).

    implications.v's [conj_4_2_implies_conj_4_4] carries (forall l, hero (TT l)) as a
    hypothesis, which fails at l = 0 for the inductive hero.  It is kept as it is and
    is not this edge's proof. *)

(** A domination join of two oriented digraphs is oriented. *)
Lemma djoin_irrefl (O1 O2 : orientedDigraph) : irreflexive (arc : rel (djoin O1 O2)).
Proof. by case=> u; exact: arc_irrefl. Qed.

Lemma djoin_asymm (O1 O2 : orientedDigraph) (u v : djoin O1 O2) :
  u --> v -> v --> u = false.
Proof. by case: u v => u [] v //=; rewrite /djoin_rel; exact: arc_asymm. Qed.

HB.instance Definition _ (O1 O2 : orientedDigraph) :=
  DiGraph_IsOriented.Build (djoin O1 O2) (@djoin_irrefl O1 O2) (@djoin_asymm O1 O2).

Lemma transitive_tournament_TT1 : transitive_tournament (TT 1).
Proof.
split; first split.
- by move=> u; rewrite arcTTE ltnn.
- by move=> u v; rewrite !fintype.ord1 eqxx.
- by move=> u v; rewrite !arcTTE => uv; rewrite -leqNgt ltnW.
- by move=> v u w; rewrite !arcTTE; exact: ltn_trans.
Qed.

Lemma transitive_tournament_djoin (D1 D2 : diGraphType) :
  transitive_tournament D1 -> transitive_tournament D2 ->
  transitive_tournament (djoin D1 D2).
Proof.
move=> [[irr1 semi1 asym1] tr1] [[irr2 semi2 asym2] tr2]; split; first split.
- by case=> u; rewrite /= /djoin_rel; [exact: irr1 | exact: irr2].
- case=> u [] v //= uv; rewrite /djoin_rel; [apply: semi1 | apply: semi2];
    by apply: contra uv => /eqP ->.
- by case=> u [] v //=; rewrite /djoin_rel; [exact: asym1 | exact: asym2].
- by case=> y [] x [] z //=; rewrite /djoin_rel; [exact: tr1 | exact: tr2].
Qed.

(** For every [l], an oriented digraph that is a hero by Berger's recursion (K1 joined
    [l] times in front of K1, through hero_djoin) and a transitive tournament on [l.+1]
    vertices. *)
Lemma transitive_tournament_hero (l : nat) :
  exists H : orientedDigraph, [/\ hero H, transitive_tournament H & #|H| = l.+1].
Proof.
elim: l => [|l [H [hH tH cH]]].
  exists (TT 1 : orientedDigraph).
  by split; [exact: hero_K1 | exact: transitive_tournament_TT1 | exact: card_TT].
exists (djoin (TT 1) H : orientedDigraph); split.
- exact: hero_djoin hero_K1 hH.
- exact: transitive_tournament_djoin transitive_tournament_TT1 tH.
- by rewrite card_sum card_TT cH.
Qed.

(** A digraph with no [l] pairwise adjacent vertices has no induced copy of a
    transitive tournament on [l] vertices (implications.v's [noKl_implies_indfree_TT]
    for [TT l], generalised). *)
Lemma noKl_implies_indfree_tournament (l : nat) (H D : diGraphType) :
  transitive_tournament H -> #|H| = l -> no_induced_Kl l D -> ind_free H D.
Proof.
move=> [[_ semi _] _] cardH noK [f [finj farc]]; apply: noK.
exists [set f u | u : H]; split; first by rewrite card_imset.
move=> u v /imsetP[a _ ->] /imsetP[b _ ->] hne.
have ab : a != b by apply: contra hne => /eqP ->.
by rewrite !farc; exact: semi.
Qed.

Theorem conj_4_2_implies_conj_4_4_unconditional : conj_4_2 -> conj_4_4.
Proof.
move=> C42 F l Ffor; case: l => [|l].
  exists 0 => D [_ noK _]; exfalso; apply: noK.
  by exists set0; split=> [|u v]; rewrite ?cards0 ?inE.
have [H [hH tH cH]] := transitive_tournament_hero l.
have [B HB] := (C42 H F hH Ffor).2 (or_intror tH).
exists B => D [Dor noK Ffree]; apply: HB; split=> //.
exact: noKl_implies_indfree_tournament tH cH noK.
Qed.

(** ** Print Assumptions audit *)

Print Assumptions majority_3col_implies_majority_3col_tournament.
Print Assumptions majority_3col_implies_majority_3col_eulerian.
Print Assumptions majority_k1col_implies_majority_3col.
Print Assumptions conj_4_2_implies_conj_4_4_unconditional.
Print Assumptions transitive_tournament_hero.
