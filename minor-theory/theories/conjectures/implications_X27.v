(** * Minor.conjectures.implications_X27 — corpus-relation edges landing in X27

    Edges of [meta/corpus_relations.json] whose TARGET is the X27 row
    [bounded_degree_even_hole_free_bounded_treewidth_statement].  Axiom-free:
    only [Qed]-closed results live here, and the one scheduled edge does not
    close, so it is documented and not stated.

    ** e053 — CANDIDATE, with three independent obstructions.

    [bounded_degree_induced_wall_or_line_wall_statement] (X220) ⟹
    [bounded_degree_even_hole_free_bounded_treewidth_statement] (gc:e053).
    Corpus argument: an even-hole-free graph has no induced [k]-wall for [k >= 2]
    (a brick of the wall is an induced 6-hole) and no induced line graph of a
    [k]-wall (the six edges of a brick induce a [C_6] in the line graph), so the
    source applied at [k = 3] bounds the treewidth of every even-hole-free graph
    of maximum degree at most [d] by [f_d(3)].

    Re-derivation, and what stops it.  ONE of the three gaps is now CLOSED: the
    two rows use different treewidth encodings, and
    [Minor.conjectures.implications_X42.tw_le_iff_x27] (the bridge F1, built on
    [Minor.foundations.width_params.tw_le_tree]) reconciles them.  The two that
    remain are:

    (1) A CHOICE obstruction, which is intrinsic to the pair of statements and
        independent of any graph theory.  The source quantifies [exists f] AFTER
        [d] ([forall d, exists f : nat -> nat, ...]), while the target quantifies
        [exists f] BEFORE [d] ([exists f : nat -> nat, forall d, ...]).  Even
        granting every containment, the re-derivation reaches
        [forall d, exists B, (forall G, Delta G <= d -> x27_even_hole_free G ->
        x27_treewidth_at_most G B)] and must turn it into [exists F : nat -> nat,
        forall d, ...].  That is countable choice [AC_00], which Rocq's logic does
        not provide; and the usual escape — taking the LEAST such [B] with
        [ex_minn] — is unavailable because the predicate quantifies over ALL
        [sgraph]s and is not Boolean.  So the edge cannot be [verified] as the two
        rows are currently stated, however much graph theory is added.

    (2) A witness-extraction obstruction.  The source's hypothesis is
        [tw_ge G (f k)], so the argument must be run contrapositively: from "no
        induced wall and no induced line wall" one gets [~ tw_ge G (f 3)], and
        one then needs [tw_le G (f 3).-1].  [tw_ge] is stated as "every
        admissible width is at least [k]"
        ([Minor.foundations.width_params.tw_ge]), so its negation is a negated
        universal, and extracting the width witness needs either classical logic
        or the decidability of [tw_le G m] — which in turn needs a bound on the
        size of the index forest (an [sdecomp] over a forest with more than
        [#|G|] useful nodes can be pruned).  BLOCKED on: [tw_le_decidable] (or
        [tw_ge_negP : ~ tw_ge G k -> exists m, m < k /\\ tw_le G m]).
        Compare [Minor.foundations.minor_dec.minorNN], which solves exactly this
        kind of problem for [minor] and is what let e043 close.

    (3) The even-hole containments, which are the genuine graph theory.
        BLOCKED on: [wall_has_even_hole] — "[3 <= k] implies that
        [x220_wall k] contains a [c] with [x27_hole c] and [~~ odd (size c)]"
        (the brick [(0,0),(0,1),(0,2),(1,2),(1,1),(1,0)] of [x220_wall 3] is an
        induced [C_6]: its only wall edges are the six consecutive ones, because
        the vertical edges of [x220_wall] exist only where [i + j] is even) —
        and [sline_wall_has_even_hole], its line-graph counterpart (the six
        brick edges pairwise share an endpoint exactly when consecutive), plus
        the transport of an induced copy along an [isubgraph] into an
        [x27_hole] of [G].  Natural home:
        [Minor.foundations.hole_containments.v]. *)

From GTBase Require Import base.
From Minor.foundations Require Import containment width_params.
From Minor.conjectures Require Import X27 X42 X220.
From Minor.conjectures Require Import implications_X42.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The encoding gap of e053 is closed: the two treewidth spellings agree. *)
Lemma x27_tw_le_iff (G : sgraph) (k : nat) :
  x27_treewidth_at_most G k <-> tw_le G k.
Proof. by split; [exact: x27_tw_le|exact: tw_le_x27]. Qed.

(*@EDGE from=bounded_degree_induced_wall_or_line_wall_statement to=bounded_degree_even_hole_free_bounded_treewidth_statement kind=implies status=candidate proved=false cite="gc:e053" note="Corpus argument: an even-hole-free graph has no induced k-wall (a brick is an induced 6-hole) and no induced line graph of a k-wall, so the source at k = 3 bounds the treewidth of every even-hole-free graph of degree at most d. The treewidth-encoding gap is now CLOSED (bridge F1, tw_le_iff_x27 / x27_tw_le_iff). BLOCKED on three things, the first of which is fatal as the rows are stated: (1) CHOICE — the source has 'forall d, exists f' while the target has 'exists f, forall d', so uniformising the bound over d needs countable choice AC_00, and ex_minn is unavailable because the predicate quantifies over all sgraphs and is not Boolean; (2) tw_ge_negP : ~ tw_ge G k -> exists m, m < k /\\ tw_le G m, i.e. decidability of tw_le (needs pruning the index forest to at most #|G| nodes); (3) wall_has_even_hole and sline_wall_has_even_hole, the brick/C_6 analysis of the wall and of its line graph, plus transport of an induced copy along an isubgraph into an x27_hole." *)

Print Assumptions x27_tw_le_iff.
