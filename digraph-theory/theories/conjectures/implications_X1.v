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
               (hero dichotomy ==> Conjecture 4.4).  CANDIDATE: see the
               annotation; the instance H := TT l of [conj_4_2] needs
               [hero (TT l)], an external theorem.

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

(*@EDGE from=majority_3col_statement to=majority_3col_tournament_statement kind=implies status=verified proof=majority_3col_implies_majority_3col_tournament cite="gc:e016" note="Class instantiation: a tournament IS a diGraphType (the Tournament structure inherits DiGraph), and both rows use the same majority_col predicate, so the universal statement applied to T is literally the conclusion." *)

Theorem majority_3col_implies_majority_3col_tournament :
  majority_3col_statement -> majority_3col_tournament_statement.
Proof. exact: majority_3col_implies_tournament. Qed.

(*@EDGE from=majority_3col_statement to=majority_3col_eulerian_statement kind=implies status=verified proof=majority_3col_implies_majority_3col_eulerian cite="gc:e017" note="Hypothesis dropping: the target only adds the eulerian D premise to the same conclusion, so the unrestricted statement applies after discarding it." *)

Theorem majority_3col_implies_majority_3col_eulerian :
  majority_3col_statement -> majority_3col_eulerian_statement.
Proof. exact: majority_3col_implies_eulerian. Qed.

(*@EDGE from=majority_k1col_statement to=majority_3col_statement kind=implies status=verified proof=majority_k1col_implies_majority_3col cite="gc:e018" note="Parameter instantiation at k = 2: 'I_k.+1 becomes 'I_3 and kmajority_col 2 col is CONVERTIBLE to majority_col col (kmajority_col2 in colouring_variants.v), so the k = 2 instance is the target verbatim." *)

Theorem majority_k1col_implies_majority_3col :
  majority_k1col_statement -> majority_3col_statement.
Proof. exact: colouring_variants.majority_k1col_implies_majority_3col. Qed.

(*@EDGE from=conj_4_2 to=conj_4_4 kind=implies status=candidate proved=false cite="gc:e104" note="CONDITIONAL planned: needs the external theorem 'every transitive tournament TT_l is a hero' (Berger-Choromanski-Chudnovsky-Fox-Loebl-Scott-Seymour-Thomasse 2013). [hero H] of conjectures/heroes.v is the Prop 'the H-free oriented digraphs have bounded dichromatic number', NOT a syntactic property of H, so the instance H := TT l of conj_4_2 cannot be taken without it; the rest of the argument IS formalized in conjectures/implications.v as conj_4_2_implies_conj_4_4, which carries (forall l, hero (TT l)) as an explicit hypothesis (plus the class inclusion no_induced_Kl l D -> ind_free (TT l) D)." *)

(** ** Print Assumptions audit *)

Print Assumptions majority_3col_implies_majority_3col_tournament.
Print Assumptions majority_3col_implies_majority_3col_eulerian.
Print Assumptions majority_k1col_implies_majority_3col.
