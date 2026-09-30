(** * Topological.conjectures.vocabulary_topological -- wave-V vocabulary equivalence

    meta/STATEMENT_IMPROVEMENTS.md (section "## topological-graph-theory",
    "### Duplicated vocabulary") records [X158.v:11 x158_edge_set] as a copy of
    the [E(G)] comprehension (identical in shape to the [x15_edge_set] /
    [x5_edge_set] copies of packing-theory).  The bridge is the single rewrite
    [GTBase.common.sg_edge_setE].

    The other two entries of that subsection are NOT plain duplicates and get no
    lemma here:
      - [D3D6_unblocked.v:181 proper_minor] wraps coq-graph-theory's [minor] with
        a strictness condition, so it is a new notion, not a copy;
      - [X23.v:11 x23_genuine_path] is a non-empty [seq] carrying [uniq] and
        [path (--)], while the library's [upath] / [Path] are indexed by their
        two ENDPOINTS; there is no equality or [<->] between them at equal
        arguments, only a translation that has to name the endpoints, so the
        "duplication" is a re-encoding rather than a copy.

    The [girth_geq G 4 <-> triangle_free G] equivalence asked for by the X138
    entry of the same ledger section lives in
    [Topological.foundations.girth] (it mentions only GTBase notions).

    No statement body is changed.  Axiom-free. *)

From GTBase Require Import base common.
From Topological.conjectures Require Import X158.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma x158_edge_setE (G : sgraph) : x158_edge_set G = E(G).
Proof. by rewrite sg_edge_setE. Qed.

Print Assumptions x158_edge_setE.
