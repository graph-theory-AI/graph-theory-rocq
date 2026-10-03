(** * Packing.foundations.fair_matching — Conjecture 1.15 of arXiv:1611.03196

    This file proves [bipartite_matching_underrepresentation_llm3_statement],
    [bipartite_matching_underrepresentation_llm2_statement],
    [bipartite_matching_underrepresentation_llm_statement] and
    [bipartite_matching_underrepresentation] of [Packing.conjectures.X15],
    i.e. Conjecture 1.15 of

      R. Aharoni, N. Alon, E. Berger, M. Chudnovsky, D. Kotlar, M. Loebl,
      R. Ziv, "Fair representation by independent sets", arXiv:1611.03196,

    with the explicit constant [c(m) = 12m + 14], *linear* in [m]:

      for every [m] there is a [c(m) <= 12m + 14] such that, for every
      bipartite graph [G] with [Delta G > 0] and any sets of edges
      [E_1, ..., E_m], there is a matching [S] of [G] with

        |S| >= |E(G)| / Delta G - c(m)    and    |S :&: E_i| <= ceil(|E_i| / Delta G).

    The two halves are easy separately and hard together: a maximum matching
    gives the first (this is [x15_big_matching], König's theorem), and the empty
    matching gives the second.  The point is one matching doing both.

    The LLM attack this file follows claims [c(m) <= 32(m+1)^3]; an earlier
    version of this development reached [(m+1)^2 (16m+29)].  The proof below
    reaches [12m + 14] — the [Theta(m)] that [AABCKLZ16] suggests — by
    *synchronizing* the halvings, see step 3.

    ** THE PROOF, IN ENGLISH

    Throughout, [D := Delta G] is the maximum degree, and the *statistics* of a
    matching [M] are the [m+1] numbers [|M|], [|M :&: E_1|], ..., [|M :&: E_m|]
    (the [wpred W l] of a colour [l : 'I_m.+1], with [l = 0] standing for the
    size).  The theorem asks for a matching whose statistics are close to the
    averages [|E(G)|/D, |E_1|/D, ..., |E_m|/D]: at least the first of them, at
    most each of the others.

    *** Step 1 — the edges are [D] matchings.

    [G] is bipartite, so by König's line-colouring theorem ([chi' = Delta]) its
    edges can be coloured with [D] colours in such a way that each colour class
    is a matching:
    [ClassicalLemmas.konig.line_colouring.line_colouring_E].  Call the classes
    [M_1, ..., M_D] ([cls] below).  Every edge gets exactly one colour, so every
    one of the [m+1] statistics is additive over the classes ([cls_partition]).
    In other words the vector of averages that the theorem is aiming at is
    *exactly the average of the [D] statistic vectors* of [M_1, ..., M_D].  If
    matchings could be averaged, we would be done.

    *** Step 2 — averaging two matchings, by splitting a necklace.

    This is where the topology enters.  Given matchings [A] and [B], one wants a
    matching [C] contained in [A :|: B] whose statistics are the averages of
    those of [A] and of [B].

    In the symmetric difference [A △ B] every vertex meets at most one edge of
    [A] and at most one edge of [B], so the relation "these two edges share a
    vertex" has degree at most two — the classical fact that the union of two
    matchings is a union of paths and even cycles.  Because [G] is bipartite
    that relation can be *oriented*: it becomes a partial injection [nxt]
    ([ClassicalLemmas.konig.paths2]), whose orbits linearise [A △ B] into a
    sequence [bl f A B] of edges in which consecutive ones are exactly the
    meeting ones.

    Choosing [C] means choosing, for each edge of that linear order, whether to
    keep it.  Make a necklace of it: each edge contributes a *block* of [m+1]
    consecutive beads, one per statistic, and the *type* of a bead records both
    which of [A], [B] the edge belongs to and which statistic it serves
    ([beadty]) — [2(m+1)] types in all, plus one null type [tnull] for the beads
    of statistics the edge does not serve.  Alon's Splitting Necklace Theorem
    for two thieves
    ([ClassicalLemmas.necklace.necklace.splitting_necklace_seq] at [q = 2])
    hands each of two thieves *exactly half* of every type.  Give each edge to
    the thief of its first bead and keep the edges of [A] belonging to thief 0
    and the edges of [B] belonging to thief 1 ([sel], [Csel], [Chalf]): every
    statistic is then halved on the nose.

    Three things can go wrong, and each is repaired by *throwing edges away*,
    which is the harmless direction for the [m] upper bounds:

      - an edge is not *unanimous*: a cut falls strictly inside its own group of
        beads, so its statistics went to different thieves.  It is thrown away
        ([runan], [rkeep]).  Distinct edges own disjoint groups, so distinct
        non-unanimous edges are witnessed by distinct *interior* cuts, i.e. by
        cuts at a position [p] with [p %% (m+1) <> m] ([rQint],
        [r_nonunan_int]);
      - two kept edges share a vertex.  Both are kept, hence unanimous, so all
        the beads of the one carry a single thief and likewise for the other:
        the thief change between them sits exactly at the *boundary* between
        their two groups ([rQbnd], [r_lin_bnd]).  Interior cuts and boundary
        cuts are disjoint ([r_cuts_split]), so the non-unanimous edges and the
        conflicting ones together are paid for by at most [cuts] cuts, not by
        [3 * cuts].  The one pair that escapes this is the *wrap* pair of a
        cyclic orbit block, whose two ends are adjacent in [G] with no boundary
        between them; there is at most one such pair per block
        ([bl_block_succ], [r_wrap_last]), and it is charged to a thief change
        inside that block ([r_wrap_block], [r_wrap_cuts]).  Altogether the
        conflicting kept edges are [rPk], at most [#boundary cuts + cuts] of
        them ([r_Pk_cuts]);
      - a type occurs an odd number of times, so "exactly half" is impossible.
        Rather than pad the necklace with extra beads of that type (which is
        what the earlier version did, and what costs a factor [m+1] in the end),
        the *first* bead of each odd type is *retyped to the null type*
        ([rmvp], [retys]) and its edge thrown away ([rrmd], [rkeep]).  Only the
        [2m] *class* types need be charged for here: a *size* type ([l = 0])
        lives on the *head* bead of a group, and an edge whose head bead has
        been retyped is already absent from the exact half, so charging it a
        second time would be a double count ([rhnr], [r_count_size], [rrmdc],
        [r_keep_count], [count_rmvp_class]).  After the retyping every non-null
        type has even multiplicity, and one null bead is appended if needed
        ([csq], [csq_even]).

    So the class counts round *down*, exactly, and only the size pays: with
    [2 * cuts + 2m] edges thrown away ([rCr], [rCr_card_le], [rCr_card_ge],
    [round_ind]).

    *** Step 3 — synchronized rounds.

    The earlier version mixed the [D] colour classes pairwise along a binary
    tree, one splitting theorem per pair; the [log] of the tree and a final
    trimming phase were what made [c(m)] cubic.

    The observation that removes both is that Alon's cut budget [t(q-1)] is per
    *splitting*, not per pair.  So all the pairs of one round of the tree are
    halved by a *single* splitting: their necklaces are concatenated ([gtys]),
    the concatenation is split once, and each pair reads its own segment of the
    resulting thief sequence ([rmatch], with an offset accumulator).  The exact
    halves then hold for the *sums over the round*, which is all the induction
    needs ([round_ind], [round_exists]).  Hence:

      - the number of cuts is [<= 2(m+1)+1 = 2m+3] *for the whole round*,
        not per pair;
      - the parity loss charged is [<= 2m] *for the whole round*;
      - one round of [k] pairs replaces [2k] matchings by [k], with

          sum |A_i| + |B_i| <= 2 * sum |C_i| + (12m + 14)   and
          2 * sum |C_i :&: E_l| <= sum (|A_i :&: E_l| + |B_i :&: E_l|)

        ([round_exists]).  The ledger of the constant: [2 * (2m+3)] for the
        discarded edges — one cut each for the non-unanimous edges and the
        boundary conflicts together, since those charge *disjoint* cuts, and one
        cut each for the wrap pairs of the cyclic blocks — plus [2m] for the
        parity repair of the class types, that is [6m+6] per round; doubled
        because the size inequality is stated at scale 2, plus [1] per
        statistic-0 type for the rounding of the two halves:
        [2(6m+6) + 2 = 12m + 14].

    Iterating [L] rounds on [2^L] matchings ([pairup], [rounds_exists]) gives a
    single matching [C] with

      sum_(M in s) |M| <= 2^L |C| + (2^L - 1)(12m+14)   and
      2^L |C :&: E_l| <= sum_(M in s) |M :&: E_l|.

    The errors of the rounds are *added*, but so are the sizes, so after
    dividing by [2^L] the error is [< 12m+14] whatever [L] is: geometric
    decay, no [log].

    *** Step 4 — the leaves, and no Carathéodory.

    The earlier version used Carathéodory's theorem to reduce the [D] colour
    classes to [m+2] of them with prescribed weights.  Here no weights are
    needed: the leaves are simply [q] copies of the list [M_1, ..., M_D] of all
    colour classes, padded with copies of the empty matching up to the next
    power of two ([lv] in [approx_fair_rounds]).  Every statistic of the leaf
    list is then exactly [q] times the corresponding [|X|] ([hsum], from
    [cls_partition]), and [L] is chosen large enough ([L = D(|E(G)|+K+1)]) that
    [q = 2^L %/ D] dwarfs both [|E(G)|] and the constant, so the padding and the
    rounding of [2^L / D] are absorbed.

    The upper bounds come out *exact* — [|C :&: E_i| <= |E_i| %/ D <=
    ceil(|E_i| / D)] — because the class inequality of [rounds_exists] points
    the right way and the halvings round down.  There is no trimming phase, and
    therefore no [m]-fold amplification of the error: [approx_fair_rounds]
    already is the conjecture, with

      c(m) = 12m + 14.

    In the X15 vocabulary that is [x15_rounds_instance], hence [x15_llm3_proof]
    ([c <= 12m+14], the bound stated in X15.v), and a fortiori
    [x15_llm2_proof], [x15_llm_proof] and
    [bipartite_matching_underrepresentation], Conjecture 1.15 itself.

    ** POSSIBLE FUTURE IMPROVEMENTS: [c(m)] from [12m+14] down to [8m+6]

    The constant is linear, so what is left is the *coefficient*.  Write [D] for
    the number of edges a round discards and [C] for the number of cuts of its
    splitting.  The proof below charges

      D <= 2C + 2m,

    namely [C] cuts for the non-unanimous edges and the boundary conflicts
    together (they charge *disjoint* cuts, [r_cuts_split]), [C] more for the
    wrap pairs of the cyclic orbit blocks ([r_wrap_cuts]), and [2m] for the
    parity repair of the class types ([count_rmvp_class]).  With [C <= 2m+3]
    that is [6m+6] per round and [K = 2 + 2D = 12m + 14].

    *** (a) the wrap term: [2C] down to [C].

    The second [C] pays for the *wrap* pair of a cyclic orbit block: its two
    ends are adjacent in [G] but have no bead boundary between them, so no cut
    witnesses the conflict directly.  The proof charges such a pair to a thief
    change *inside* the block ([r_wrap_block]), and bounds the number of blocks
    that wrap by [C].  That charge is crude: a cut inside a block may already be
    paying for a non-unanimous edge of the same block.  If [A △ B] has no cycles
    at all — every orbit block a path — the wrap term vanishes outright and

      D <= C + 2m,   K = 2 + 2D = 8m + 8.

    In general one would have to show that the interior cut charged to a wrap
    can be chosen distinct from the interior cuts charged to hits, e.g. by
    charging the wrap of a block to the *boundary* cut that must exist inside
    the block when it wraps.  This is the cheapest remaining gain.

    *** (b) the null type costs one cut: use variable-size bead groups.

    Every edge contributes a full group of [m+1] beads, one per statistic, and
    the beads of the statistics it does not serve are given the null type
    [tnull].  That extra type raises the number of types from [2m+2] to [2m+3],
    hence the cut budget [t(q-1)] of [A87] from [2m+2] to [2m+3].  Letting an
    edge contribute only the beads of the statistics it serves — groups of
    variable size — removes it, at the price of replacing the constant group
    size [m.+1] by a prefix-sum index in every positional lemma ([beadty],
    [count_block_tix_gen], [pos_lt], [r_block_lt], [r_mod_block], ...), and of
    redoing the interior/boundary split of the cuts, which is currently a
    statement about [p %% (m+1)].  On its own that gives [C <= 2m+2],
    [D <= 6m+4] and [K = 12m + 10]; with (a), [D <= 4m+2] and

      K = 8m + 6.

    *** the floor for this technique

    One round must lose [Theta(m)] in size: splitting [m+1] statistics exactly
    needs [Omega(m)] cuts, and at a cut the selected edge of [A] and the
    selected edge of [B] may share a vertex, forcing a deletion.  So [c(m) =
    Omega(m)] for any argument of this shape, and [12m + 14] — or [8m + 6]
    after (a) and (b) — is within a constant factor of it.  [AABCKLZ16]
    suggests [c(m) = m/2]; closing that last constant factor would need a
    different argument.

    The natural discrepancy route does not work: every edge lies in at most [m]
    of the classes, so Beck-Fiala would give discrepancy below [m], but its
    proof relaxes constraints once they hold few floating variables, and the
    vertex constraints of a matching cannot be relaxed at all.  That is
    presumably why Conjecture 1.15 is still open.

    ** CONTENTS

    Vocabulary and elementary facts:
    - [x15_edge_setE], [matching_x15] : the local X15 vocabulary of [X15.v] is
      the coq-graph-theory vocabulary ([E(G)], [matching]), so the library's
      König/Hall infrastructure applies verbatim;
    - [edges_leq_cover] : a vertex cover [V] bounds [#|E(G)| <= #|V| * Delta G];
    - [x15_big_matching] : a bipartite [G] with [Delta G > 0] has a matching of
      size at least [#|E(G)| %/ Delta G] (König min-cover = max-matching).
      Not used below; it is the [m = 0] case, and the sanity check that the size
      half of the conjecture alone is König's theorem.

    Counting along a necklace cut into blocks (step 2):
    - [cuts_seq_cat], [cuts_seq_flatten], [cuts_seq_subseq],
      [cuts_seq_map_nth], [cyc_le] : the number of changes along a sequence;
    - [conflict_count] : conflicting pairs of kept edges are consecutive;
    - [bl_block_succ] : the successor of a non-last edge of an orbit block, in
      the flattened list, is its successor in the block;
    - [count_iota_blocks], [count_iota_split], [count_block_tix_gen],
      [count_creal_tix], [pos_lt] : counting a type over the blocks.

    Halving one pair (step 2), [Section Halving] and [Section WithSplit]:
    - [beadty], [creal], [cs] : the necklace, one block of [m+1] beads per edge;
    - [thj], [thE], [sel], [Csel], [Psrc], [Chalf] : the thief of an edge, the
      selection it defines, the conflicting edges and the matching kept;
    - [Chalf_matching], [card_Chalf_ge], [card_Csel_count], [card_split] : what
      the selection is worth, in the form the round needs.

    One pair inside a round, [Section PairRound]:
    - [rbth], [runan], [rrmd], [rkeep] : the pair reads its own segment of the
      round's thief sequence, and keeps only the unanimous, non-retyped edges;
    - [rCr] : the pair's matching, [Chalf] minus the discarded edges;
    - [rhnr], [rrmdc] : the head bead of an edge's group carries a *size* type,
      so a removal there needs no charge in the ledger; only the removals at the
      *class* beads do;
    - [rQint], [rQbnd], [r_cuts_split] : the cuts interior to a bead group and
      the cuts at a group boundary, which are disjoint;
    - [r_nonunan_int] : the non-unanimous edges are charged to interior cuts;
    - [r_lin_bnd], [r_wrap_block], [r_wrap_cuts], [r_Pk_cuts] : the conflicting
      kept edges are charged to boundary cuts, except one wrap pair per cyclic
      orbit block;
    - [r_keep_count], [r_rmd_count] : the discarded edges, split into the
      non-unanimous ones and those hit by a class removal;
    - [r_nonunan_cuts], [r_Psrc_cuts] : the coarser bounds of the previous
      ledger ([cuts] and [2 * cuts]), kept for reference;
    - [rCr_card_le], [rCr_card_ge] : the two set-level bounds.

    One round and the rounds, [Section Round]:
    - [gtys] : the concatenated necklace of a list of pairs;
    - [rmvp], [retys], [csq], [csq_even] : the parity repair, by retyping one
      bead of each odd type to the null type;
    - [gtys_class], [size_class_types], [count_rmvp_class] : only the [2m]
      *class* types are charged for ([count_rmvp], the coarser [2m+2], is kept
      for reference);
    - [rmatch], [gok], [Ycnt], [round_ind] : the induction over the pairs of a
      round, at a shared thief sequence;
    - [round_exists] : one round, with the error [12m + 14];
    - [pairup], [rounds_exists] : [L] rounds on [2^L] matchings.

    The assembly:
    - [cls], [cls_partition] : the colour classes of a line colouring and their
      additivity;
    - [approx_fair_rounds] : the conjecture, for a graph equipped with a proper
      line colouring;
    - [x15_rounds_instance] : the same in the vocabulary of [X15];
    - [x15_llm3_proof], [x15_llm2_proof], [x15_llm_proof],
      [bipartite_matching_underrepresentation] : the four statements of X15.v.

    ** Provenance, sources, and what corresponds to what

    HOW THIS FILE WAS OBTAINED.  It was written with Claude Code (Anthropic),
    models Claude Opus 5 and (for the first sections) Claude Opus 4.8, between
    11 and 19 September 2026.  Rocq was driven interactively.  The
    rocq-mcp-evolve MCP server of the LLM4Rocq project,
    https://github.com/LLM4Rocq/rocq-mcp-evolve (Apache-2.0; the opam package
    still carries its former slug LLM4Rocq/rocq-tools), is used throughout this
    repository for that purpose and is gratefully acknowledged.  Every error
    that recurred, together with the tactic that fixed it, is recorded in
    tactics-playbook.md at the root of the repository.  Nothing is admitted:
    [Print Assumptions] on the results of this file answers "Closed under the
    global context".

    ESTIMATED TOKEN COST FOR THIS FILE.  About 3.6M tokens, of which about
    1.1M output, in three phases:

      1.69M (670k output)  the version with [c(m) = (m+1)^2(16m+29)]:
                           vocabulary, Koenig bound, reduction, the padded
                           halving, the dyadic mixing and the trimming
                           assembly, 11-16 September;
      1.4M  (~0.3M)        the synchronized-rounds rewrite down to
                           [c(m) = 16m+24] — design, the per-pair section, the
                           round and its induction, the assembly, the merge and
                           the deletion of the superseded code, 18 September;
                           0.39M of it spent in two background agents;
      0.5M  (~0.1M)        the sharpened ledger taking [16m+24] to [12m+14]:
                           interior versus boundary cuts, the wrap of a cyclic
                           block, the head-bead correction, 18-19 September;
                           0.23M of it spent in one background agent.

    Not counted here: the classical-lemmas files this one rests on, about 0.3M
    tokens for konig/paths2.v and konig/line_colouring.v and 3.9M for
    necklace/.  Method: as in ClassicalLemmas.necklace.necklace — for every
    assistant message of the Claude Code session, input + cache-creation +
    output tokens (the tokens processed anew, excluding the cached conversation
    that is re-read at each turn), charged to the file the message's tool calls
    were acting on; a background agent is charged the token total its
    completion notice reports.  The figures for 18-19 September are estimates:
    the session transcript is flushed only up to its last checkpoint, and the
    output share of the background agents is not reported separately.

    SOURCES.

      [AABCKLZ16]  R. Aharoni, N. Alon, E. Berger, M. Chudnovsky, D. Kotlar,
             M. Loebl, R. Ziv, "Fair representation by independent sets",
             arXiv:1611.03196.  Conjecture 1.15 is the target; it is stated in
             packing-theory/theories/conjectures/X15.v.

      [A87]  N. Alon, "Splitting necklaces", Advances in Mathematics 63 (1987)
             247-253, formalized in this repository as
             [ClassicalLemmas.necklace.necklace.splitting_necklace_seq]
             (through Meunier's simplotopal Tucker lemma); used at [q = 2],
             once per round.

      [LLM]  The proof sketch attacked here,
             https://github.com/graph-theory-AI/Graph-Theory-LLM-Proofs/blob/main/attacks/1611.03196__03/output.md
             (five steps: line colouring, Carathéodory, interpolation of two
             matchings, iterated interpolation, trimming), referenced from the
             comment on [bipartite_matching_underrepresentation_llm_statement]
             in X15.v.

      WHAT THE IMPROVEMENT OVER [LLM] IS DUE TO.  The write-up [LLM] yields
      [c(m) = 32(m+1)^3 = O(m^3)].  Two suggestions of Laurent Viennot turned
      that into [O(m)], and a third sharpened the coefficient.

      1. *Remove one bead of every odd type — and throw its edge away —
      instead of padding the type to an even count.*  The shares are then
      rounded *down* rather than up, floors compose along the mixing, the
      per-class ceilings [|C :&: E_i| <= ceil(|E_i|/Delta)] hold *by
      construction*, and the whole trimming phase of [LLM] disappears together
      with the outer factor [m+1] it cost.  This is what makes step 2 above,
      the exact halving, exact.

      2. *Combine the chain of halvings with the balanced mixing tree.*  Alon's
      budget [t(q-1)] counts the cuts of ONE split, not of one pair, so a whole
      level of the tree is halved by a single split of the concatenated
      necklaces of its pairs — the types are shared, and exact halves for the
      *sums* over the level are all the argument needs.  The per-round loss is
      then paid once per level instead of once per pair, the losses telescope
      ([sum_r 2^-r K <= 2K]), and both the [log m] of a balanced tree and the
      second factor [m+1] disappear.  This is step 3 above, the synchronized
      rounds, and it also removes the need for Carathéodory: the leaves are
      [2^L] copies of the colour classes padded with the empty matching.

      Together: [c(m) = O(m)] where the write-up gives [O(m^3)].

      3. *Hits and conflicts charge disjoint cuts, and a conflict costs one
      edge, not two.*  A cut interior to a bead group makes its edge
      non-unanimous, so that edge is thrown away; it cannot also witness a
      conflict, because a conflict is between two *kept* — hence unanimous —
      edges, whose thief change therefore sits exactly at a group boundary.
      Together with the observation that a removed *size* bead is a head bead,
      whose edge is already absent from the exact half and so must not be
      charged twice, the ledger of a round becomes [2 * #cuts + 2m] instead of
      [3 * #cuts + t], i.e. [c(m) = 12m + 14] instead of [16m + 24].

      DEVIATIONS FROM [LLM].  Three, all of which improve the constant.

      (i) Step 3 of [LLM] invokes a *prescribed-ratio* continuous splitting
      theorem (its Lemma 1, Hobby-Rice style): for any ratio theta, a union of
      O(r) intervals carrying exactly a theta-share of r measures.  That
      statement does not follow from the equal-share Splitting Necklace Theorem
      with a number of cuts independent of theta: reading theta = a/q off a
      q-splitting costs t(q-1) cuts, so the error would grow with the
      denominator.  Here every interpolation is a halving (theta = 1/2), which
      is exactly [necklace.splitting_necklace_seq] at [q = 2].

      (ii) Steps 2 and 4 of [LLM] (Carathéodory, then one interpolation per
      pair) are replaced by the synchronized rounds of step 3 above: one
      splitting per *round* rather than per pair, on the concatenation of the
      pairs' necklaces.  This is what turns [Theta(m^3)] into [Theta(m)], and
      it makes Carathéodory unnecessary: the leaves are [2^L] copies of the
      colour classes padded with the empty matching.

      (iii) Step 5 of [LLM] (trimming the classes that exceed their ceiling,
      which costs a further factor [m+1] in the size) disappears: because each
      round halves the class counts *exactly*, rounding down, the upper bounds
      hold already.

    WHAT CORRESPONDS TO WHAT.

      - the vocabulary of [AABCKLZ16] Conj. 1.15 versus that of
        coq-graph-theory  -> [x15_edge_setE], [matching_x15]
      - [LLM] step 1, König line colouring, instantiated at the colour classes
                          -> [cls], [cls_partition]
      - [LLM] step 2, Carathéodory                -> not needed, see (ii)
      - [LLM] step 3, the interpolation of two matchings, from [A87] at [q = 2]
                          -> [beadty], [thj], [sel], [Chalf], [card_Chalf_ge],
                             [card_Csel_count], and, inside a round, [rCr],
                             [rCr_card_le], [rCr_card_ge]
      - [LLM] step 4, the iterated interpolation, by synchronized rounds rather
        than by the prescribed-ratio Lemma 1
                          -> [gtys], [csq], [rmatch], [round_ind],
                             [round_exists], [pairup], [rounds_exists]
      - [LLM] step 5, trimming                    -> not needed, see (iii)
      - the assembly and the passage from the leaf list back to the averages
        |E(G)|/D and |E_i|/D
                          -> [approx_fair_rounds], [x15_rounds_instance]
      - bookkeeping with no counterpart in [LLM]: the cut counting needed to
        pass between the flat necklace, the blocks of
        [ClassicalLemmas.konig.paths2] and the edge sets
                          -> [cuts_seq_cat], [cuts_seq_flatten],
                             [cuts_seq_subseq], [conflict_count],
                             [bl_block_succ], [r_nonunan_int], [r_Pk_cuts]
      - the constant: one round costs 2(2m+3) cuts-worth of edges plus 2m
        class-parity edges, i.e. 6m+6; at scale 2 with the two roundings that is
        [12m + 14], and the rounds' errors are absorbed by the geometric growth
        of the leaf count
                          -> [round_exists], [rounds_exists], [x15_llm3_proof]
      - with no counterpart in [LLM]: [edges_leq_cover], [x15_big_matching]
        (the case m = 0, and the sanity check that the size bound alone is
        König's theorem) *)

From GTBase Require Export base.
From GraphTheory Require Import preliminaries digraph sgraph connectivity.
From Packing Require Import X15.
From Stdlib Require Import Lia.
From ClassicalLemmas Require Import necklace.necklace konig.paths2
                                    konig.line_colouring.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Bridging the X15 vocabulary with coq-graph-theory *********************)

Lemma x15_edge_setE (G : sgraph) : x15_edge_set G = E(G).
Proof. by []. Qed.

(** [x15_matching] is a transparent alias of [matching] since the C1 library
    migration (2026-10-02); the lemma is kept for its consumers below. *)
Lemma matching_x15 (G : sgraph) (M : {set {set G}}) :
  matching M -> x15_matching M.
Proof. by []. Qed.

(** ** A vertex cover bounds the number of edges ****************************)

Lemma leq_card_bigcup (I T : finType) (P : pred I) (F : I -> {set T}) :
  #|\bigcup_(i | P i) F i| <= \sum_(i | P i) #|F i|.
Proof.
elim/big_rec2: _ => [|i n U _ leUn]; first by rewrite cards0.
by rewrite (leq_trans (leq_card_setU (F i) U).1) ?leq_add2l.
Qed.

Lemma set2C (T : finType) (x y : T) : [set x; y] = [set y; x].
Proof. by apply/setP => z; rewrite !inE orbC. Qed.

Lemma edges_leq_cover (G : sgraph) (V : {set G}) :
  vcover V -> #|E(G)| <= #|V| * Delta G.
Proof.
move=> covV.
move/(vcoverP V): (covV) => covP.
have sub : E(G) \subset \bigcup_(v in V) [set [set v; y] | y in N(v)].
  apply/subsetP => e /edgesP [x [y [-> xy]]].
  case: (covP _ _ xy) => [xV|yV]; apply/bigcupP.
  - by exists x => //; apply/imsetP; exists y => //; rewrite in_opn.
  - exists y => //; apply/imsetP; exists x; first by rewrite in_opn sgP.
    by rewrite set2C.
apply: leq_trans (subset_leq_card sub) _.
apply: leq_trans (leq_card_bigcup _ _) _.
rewrite -[X in _ <= X]sum_nat_const.
apply: leq_sum => v _.
apply: leq_trans (leq_imset_card _ _) _.
exact: leq_bigmax.
Qed.

(** ** König: a matching of size at least ⌊|E(G)|/Δ(G)⌋ *********************)

Theorem x15_big_matching (G : sgraph) :
  bipartite G -> 0 < Delta G ->
  exists M : {set {set G}},
    x15_matching M /\ #|x15_edge_set G| %/ Delta G <= #|M|.
Proof.
move=> [f fP] dpos.
have bipA : bipartition [set x : G | f x].
  move=> x y xy; rewrite !inE; move: (fP _ _ xy).
  by case: (f x) (f y) => [] [].
have covT : @vcover G setT by apply/vcoverP => x y _; left; rewrite inE.
have smV := @argmin_smallest _ (@vcover G) setT covT.
set V := [arg min_(B < setT | vcover B) #|B|] in smV.
have [M mM defM] := min_vcover_matching bipA smV.
exists M; split; first exact: matching_x15.
rewrite x15_edge_setE -defM -(mulnK #|V| dpos).
by apply: leq_div2r; apply: edges_leq_cover; case: smV.
Qed.

(** * Step 3: halving two matchings with the Splitting Necklace Theorem ******)

(** Everything up to [matching_halving] is independent of the X15 vocabulary:
    it is the interpolation of two matchings of a bipartite graph, through the
    necklace of their symmetric difference.  See step 3 of the header. *)

(** ** Counting changes in a sequence *)

Lemma bool_tri (Q : eqType) (y w z : Q) : (y != z) <= (y != w) + (w != z).
Proof.
case hyw : (y == w); first by rewrite (eqP hyw) /= add0n.
case hwz : (w == z); first by rewrite -(eqP hwz) /=; case: (y == w).
by rewrite /=; case: (y == z).
Qed.

Lemma cuts_seq_cons_le (Q : eqType) (y w : Q) (s : seq Q) :
  cuts_seq (y :: s) <= cuts_seq (y :: w :: s).
Proof.
case: s => [|z s]; first by rewrite cuts_seq_cons2 /=.
rewrite !cuts_seq_cons2 [X in _ <= X]addnA leq_add2r.
exact: bool_tri.
Qed.

Lemma cuts_seq_sub (Q : eqType) (s2 s1 : seq Q) :
  subseq s1 s2 -> forall y : Q, cuts_seq (y :: s1) <= cuts_seq (y :: s2).
Proof.
elim: s2 s1 => [|w s2 IH] s1.
  by move/eqP => -> y.
case: s1 => [_ y|x s1]; first by rewrite /cuts_seq /=.
rewrite [subseq _ _]/=; case: eqP => [hxw hs y|hne hs y].
  by rewrite hxw !cuts_seq_cons2 leq_add2l; apply: IH.
by apply: (leq_trans (IH _ hs y)); exact: cuts_seq_cons_le.
Qed.

Lemma cuts_seq_subseq (Q : eqType) (s1 s2 : seq Q) :
  subseq s1 s2 -> cuts_seq s1 <= cuts_seq s2.
Proof.
case: s1 => [|x s1] //.
elim: s2 => [|y s2 IH] //.
rewrite [subseq _ _]/=; case: eqP => [hxy hs|hne hs].
  by rewrite hxy; apply: cuts_seq_sub.
by apply: (leq_trans (IH hs)); exact: leq_cuts_seq_behead.
Qed.

Lemma cuts_seq_cat (Q : eqType) (s t : seq Q) :
  cuts_seq s + cuts_seq t <= cuts_seq (s ++ t).
Proof.
elim: s => [|x s IH]; first by rewrite /cuts_seq /= add0n.
case: s IH => [_|y s IH].
  have -> : cuts_seq [:: x] = 0 by [].
  by rewrite add0n cat_cons cat0s; exact: (leq_cuts_seq_behead (x :: t)).
by rewrite cat_cons !cuts_seq_cons2 -addnA leq_add2l.
Qed.

Lemma cuts_seq_flatten (Q : eqType) (ss : seq (seq Q)) :
  \sum_(s <- ss) cuts_seq s <= cuts_seq (flatten ss).
Proof.
elim: ss => [|s ss IH]; first by rewrite big_nil.
rewrite big_cons /=.
by apply: leq_trans (cuts_seq_cat s (flatten ss)); rewrite leq_add2l.
Qed.

(** ** Cyclic versus linear changes along a block *)

Lemma const_iota (Q : eqType) (g : nat -> Q) (n : nat) :
  count (fun k => (k.+1 < n) && (g k != g k.+1)) (iota 0 n) = 0 ->
  forall j, j < n -> g j = g 0.
Proof.
move=> h0 j; elim: j => [//|j IH hj].
have hj' : j < n by apply: ltn_trans hj.
have hnh : ~~ has (fun k => (k.+1 < n) && (g k != g k.+1)) (iota 0 n).
  by rewrite has_count h0 ltnn.
move: (hasPn hnh j); rewrite mem_iota /= add0n hj' => /(_ isT).
rewrite negb_and hj /= negbK => /eqP h.
by rewrite -h IH.
Qed.

Lemma cyc_le (Q : eqType) (g : nat -> Q) (n : nat) : 0 < n ->
  count (fun k => g k != g (k.+1 %% n)) (iota 0 n)
    <= 2 * count (fun k => (k.+1 < n) && (g k != g k.+1)) (iota 0 n).
Proof.
move=> hn.
have hsplit : iota 0 n = iota 0 n.-1 ++ [:: n.-1].
  by rewrite -{1}(prednK hn) -addn1 iotaD /= add0n.
set Pl := (fun k => (k.+1 < n) && (g k != g k.+1)).
set Pc := (fun k => g k != g (k.+1 %% n)).
have hlin : count Pl (iota 0 n) = count Pl (iota 0 n.-1).
  by rewrite hsplit count_cat /Pl /= (prednK hn) ltnn /= add0n addn0.
have hcyc : count Pc (iota 0 n) = count Pl (iota 0 n.-1) + (g n.-1 != g 0).
  rewrite hsplit count_cat; congr (_ + _).
    apply: eq_in_count => k; rewrite mem_iota /= add0n => hk.
    have hk1 : k.+1 < n by rewrite -(prednK hn) ltnS.
    by rewrite /Pc /Pl modn_small // hk1.
  by rewrite /= /Pc (prednK hn) modnn addn0.
rewrite hlin hcyc.
case: (boolP (g n.-1 != g 0)) => [hne|hne]; last by rewrite /= addn0 leq_pmull.
have h1 : 1 <= count Pl (iota 0 n.-1).
  rewrite lt0n; apply/eqP => h0.
  have hc0 : count Pl (iota 0 n) = 0 by rewrite hlin h0.
  have hlt : n.-1 < n by rewrite ltn_predL.
  by move: hne; rewrite (const_iota hc0 hlt) eqxx.
by rewrite mul2n -addnn leq_add2l.
Qed.

Lemma cuts_seq_map_nth (T Q : eqType) (x0 : T) (th : T -> Q) (b : seq T) :
  cuts_seq (map th b)
  = count (fun k => (k.+1 < size b) && (th (nth x0 b k) != th (nth x0 b k.+1)))
          (iota 0 (size b)).
Proof.
rewrite (cuts_seq_nth (th x0)) size_map.
apply: eq_in_count => k; rewrite mem_iota /= add0n => hk.
case: (ltnP k.+1 (size b)) => hk1 //=.
by rewrite !(nth_map x0).
Qed.

(** ** Conflicts of a selection sit at the cuts *)

Section Conflicts.
Variables (G : sgraph) (f : G -> bool) (A B : {set {set G}}).
Hypothesis bipf : forall x y : G, x -- y -> f x != f y.
Hypothesis mA : matching A.
Hypothesis mB : matching B.

Lemma conflict_count (th : {set G} -> bool) (P : pred {set G}) :
  (forall e, P e -> [/\ e \in SS A B, nxt f A B e != set0 &
                        th e != th (nxt f A B e)]) ->
  count P (bl f A B) <= 2 * cuts_seq (map th (bl f A B)).
Proof.
move=> hP.
have hblock (b : seq {set G}) : b \in blocks f A B ->
    count P b <= 2 * cuts_seq (map th b).
  move=> hb.
  have hn : 0 < size b by exact: (block_size hb).
  have hbe : b = [seq nth set0 b j | j <- iota 0 (size b)].
    by rewrite map_nth_iota0 // take_size.
  rewrite {1}hbe count_map.
  rewrite (@eq_in_count _ _ (fun k => (k < size b) && P (nth set0 b k))); last first.
    by move=> k; rewrite mem_iota /= add0n => ->.
  apply: (leq_trans (_ : _ <=
    count (fun k => th (nth set0 b k) != th (nth set0 b (k.+1 %% size b)))
          (iota 0 (size b)))).
    apply: sub_count => k /= /andP[hk hPk].
    have [hSS hn0 hth] := hP _ hPk.
    by rewrite -(block_nth bipf mA mB hb hk) (sigma_nxt hn0).
  apply: (leq_trans (cyc_le _ hn)).
  by rewrite leq_pmul2l // (cuts_seq_map_nth set0).
rewrite /bl count_flatten sumnE big_map.
apply: (leq_trans (_ : _ <= \sum_(b <- blocks f A B) (2 * cuts_seq (map th b)))).
  rewrite big_seq_cond [X in _ <= X]big_seq_cond.
  by apply: leq_sum => b /andP[hb _]; exact: hblock.
rewrite -big_distrr /= leq_pmul2l //.
rewrite map_flatten -(big_map (fun b => map th b) xpredT (fun s : seq bool => cuts_seq s)).
exact: cuts_seq_flatten.
Qed.

(** The flat order [bl] follows each block: the successor, in [bl], of the
    [k]-th edge of a block is the [k.+1]-th edge of that block. *)
Lemma bl_block_succ (b : seq {set G}) (k : nat) :
  b \in blocks f A B -> k.+1 < size b ->
  nth set0 (bl f A B) (index (nth set0 b k) (bl f A B)).+1 = nth set0 b k.+1.
Proof.
move=> hb hk.
have hkk : k < size b by apply: ltn_trans hk; exact: ltnSn.
have hub : uniq (bl f A B) by exact: uniq_bl.
set i := index b (blocks f A B).
have hi : i < size (blocks f A B) by rewrite index_mem.
have hdec : blocks f A B = take i (blocks f A B) ++ b :: drop i.+1 (blocks f A B).
  by rewrite -{1}(cat_take_drop i (blocks f A B)) (drop_nth [::] hi) nth_index.
move: hub; rewrite /bl hdec flatten_cat /= => hub.
have hmem : nth set0 b k \in b by exact: mem_nth.
have hnot : nth set0 b k \notin flatten (take i (blocks f A B)).
  move: hub; rewrite cat_uniq => /and3P[_ /hasPn hh _].
  by apply: hh; rewrite mem_cat hmem.
have hbu : uniq b.
  by move: hub; rewrite cat_uniq => /and3P[_ _]; rewrite cat_uniq => /and3P[].
rewrite index_cat (negbTE hnot) index_cat hmem index_uniq //.
by rewrite -addnS nth_cat ltnNge leq_addr /= addKn nth_cat hk.
Qed.

End Conflicts.

(** ** Counting over a sequence cut into blocks of constant size *)

Lemma count_iota_blocks (Q : pred nat) (N c : nat) :
  count Q (iota 0 (N * c)) = \sum_(j < N) count (fun l => Q (j * c + l)) (iota 0 c).
Proof.
elim: N => [|N IH]; first by rewrite mul0n big_ord0.
rewrite big_ord_recr /= -IH mulSn addnC iotaD count_cat; congr (_ + _).
by rewrite add0n -{1}(addn0 (N * c)) iotaDl count_map.
Qed.

Lemma count_iota_sum (Q : pred nat) (n : nat) :
  count Q (iota 0 n) = \sum_(j < n) (Q j : nat).
Proof.
rewrite -(big_mkord xpredT (fun j => (Q j : nat))) /index_iota subn0.
exact: sum_count.
Qed.

Lemma count_iota_split (Q : pred nat) (n p : nat) :
  count Q (iota 0 (n + p)) = count Q (iota 0 n) + count (fun i => Q (n + i)) (iota 0 p).
Proof.
rewrite iotaD count_cat; congr (_ + _).
by rewrite add0n -{1}(addn0 n) iotaDl count_map.
Qed.

Lemma count_split (T : eqType) (s : seq T) (P Q : pred T) :
  count P s = count (fun e => P e && Q e) s + count (fun e => P e && ~~ Q e) s.
Proof.
elim: s => [//|x s IH] /=; rewrite IH.
case: (P x) => /=; last by rewrite !add0n.
by case: (Q x) => /=; rewrite ?add0n ?addSn ?addnS.
Qed.

Lemma card_seq_count (T : finType) (s : seq T) (S : {set T}) (P : pred T) :
  uniq s -> (forall x, (x \in s) = (x \in S)) ->
  #|[set x in S | P x]| = count P s.
Proof.
move=> hu hs.
have -> : [set x in S | P x] = [set x in [seq y <- s | P y]].
  by apply/setP => x; rewrite !inE mem_filter hs andbC.
by rewrite cardsE -size_filter; apply/card_uniqP; apply: filter_uniq.
Qed.

Lemma count_nth_iota (T : eqType) (x0 : T) (s : seq T) (P : pred T) :
  count (fun i => P (nth x0 s i)) (iota 0 (size s)) = count P s.
Proof.
have he : s = [seq nth x0 s i | i <- iota 0 (size s)].
  by rewrite map_nth_iota0 // take_size.
by rewrite [in RHS]he count_map.
Qed.

Lemma diff_count (Q : eqType) (g : nat -> Q) (r : nat) :
  ((g 0 != g r) : nat) <= count (fun i => g i != g i.+1) (iota 0 r).
Proof.
case: (posnP (count (fun i => g i != g i.+1) (iota 0 r))) => [h0|]; last first.
  by move=> hgt; apply: leq_trans hgt; exact: leq_b1.
suff -> : g 0 = g r by rewrite eqxx.
have hcst : forall j, j <= r -> g j = g 0.
  elim=> [//|j IH hj].
  have hj' : j < r by [].
  have hnh : ~~ has (fun i => g i != g i.+1) (iota 0 r).
    by rewrite has_count h0.
  move: (hasPn hnh j); rewrite mem_iota /= add0n hj' => /(_ isT).
  by rewrite negbK => /eqP h; rewrite -h IH // ltnW.
by rewrite hcst.
Qed.

Lemma count_iota_le (Q : pred nat) (r1 r2 : nat) :
  r1 <= r2 -> count Q (iota 0 r1) <= count Q (iota 0 r2).
Proof.
move=> h12; rewrite -(subnKC h12) iotaD count_cat leq_addr //.
Qed.

Lemma sum_ord_count (T : eqType) (x0 : T) (s : seq T) (Q : pred T) :
  \sum_(j < size s) (Q (nth x0 s j) : nat) = count Q s.
Proof.
rewrite -(big_mkord xpredT (fun j => (Q (nth x0 s j) : nat))).
rewrite -(big_nth x0 xpredT (fun x => (Q x : nat))) /=.
by rewrite sum_count.
Qed.

(** ** Halving two matchings *)

Section Halving.
Variables (G : sgraph) (f : G -> bool) (A B : {set {set G}}) (m : nat).
Variable W : 'I_m -> {set {set G}}.
Hypothesis bipf : forall x y : G, x -- y -> f x != f y.
Hypothesis mA : matching A.
Hypothesis mB : matching B.

Local Notation es := (bl f A B).
Local Notation N := (size (bl f A B)).
Local Notation t := (#|{: bool * 'I_m.+1}|.+1).

(** The [m.+1] statistics: the total number of edges, and the [m] classes. *)
Definition wpred (l : 'I_m.+1) (e : {set G}) : bool :=
  if unlift ord0 l is Some k then e \in W k else true.

Local Notation TT := (bool * 'I_m.+1)%type.

Lemma card_TT : #|{: TT}| = 2 * m.+1.
Proof. by rewrite card_prod card_bool card_ord. Qed.

Definition tix (s : bool) (l : 'I_m.+1) : 'I_t :=
  widen_ord (leqnSn _) (enum_rank (s, l)).
Definition tnull : 'I_t := ord_max.

Lemma tixE (s s' : bool) (l l' : 'I_m.+1) :
  (tix s l == tix s' l') = (s == s') && (l == l').
Proof.
rewrite -xpair_eqE; apply/idP/idP.
  by move/eqP/(congr1 val) => /= /val_inj/enum_rank_inj ->.
by move/eqP => [-> ->].
Qed.

Lemma tix_null (s : bool) (l : 'I_m.+1) : (tix s l == tnull) = false.
Proof.
apply/negbTE/negP => /eqP/(congr1 val) /=.
by move/eqP; rewrite -[X in _ == X]/(#|{: TT}|) ltn_eqF // ltn_ord.
Qed.

Definition sd (e : {set G}) : bool := e \in B.

Definition beadty (p : nat) : 'I_t :=
  let e := nth set0 es (p %/ m.+1) in
  let l := inord (p %% m.+1) : 'I_m.+1 in
  if wpred l e then tix (sd e) l else tnull.

Definition creal : seq 'I_t := [seq beadty p | p <- iota 0 (N * m.+1)].
Definition padding : seq 'I_t := [seq k <- enum 'I_t | odd (count (pred1 k) creal)].
Definition cs : seq 'I_t := creal ++ padding.

Lemma size_creal : size creal = N * m.+1.
Proof. by rewrite size_map size_iota. Qed.

Lemma nth_creal (p : nat) : p < N * m.+1 -> nth tnull creal p = beadty p.
Proof.
move=> hp; rewrite (nth_map 0) ?size_iota // nth_iota //.
Qed.

Lemma beadty_block (j l : nat) : l < m.+1 ->
  beadty (j * m.+1 + l) =
  (let e := nth set0 es j in
   if wpred (inord l) e then tix (sd e) (inord l) else tnull).
Proof.
move=> hl; rewrite /beadty divnMDl // modnMDl.
by rewrite (divn_small hl) (modn_small hl) addn0.
Qed.

(** Positions of the necklace. *)

Lemma count_pair_pos (T Q : eqType) (x0 : T) (y0 : Q) (k : T) (j : Q)
    (c : seq T) (u : seq Q) :
  size u = size c ->
  count_pair k j c u
  = count (fun p => (nth x0 c p == k) && (nth y0 u p == j)) (iota 0 (size c)).
Proof.
move=> hsz; rewrite /count_pair.
have hz : size (zip c u) = size c by rewrite size_zip hsz minnn.
have hzip : zip c u = [seq nth (x0, y0) (zip c u) p | p <- iota 0 (size c)].
  by rewrite -hz map_nth_iota0 // take_size.
rewrite {1}hzip count_map; apply: eq_in_count => p _ /=.
by rewrite nth_zip.
Qed.


Lemma count_block_tix (j : nat) (s : bool) (l : 'I_m.+1) :
  count (fun l' => beadty (j * m.+1 + l') == tix s l) (iota 0 m.+1)
  = (wpred l (nth set0 es j) && (sd (nth set0 es j) == s) : nat).
Proof.
rewrite (@eq_in_count _ _
   (fun l' => (l' == val l) &&
              (wpred l (nth set0 es j) && (sd (nth set0 es j) == s)))); last first.
  move=> l'; rewrite mem_iota /= add0n => hl'.
  rewrite beadty_block //.
  case: (altP (l' =P val l)) => [hl'e|hne] /=.
    rewrite hl'e inord_val.
    case: (boolP (wpred l (nth set0 es j))) => hw /=.
      by rewrite tixE eqxx andbT.
    by rewrite eq_sym tix_null.
  have hvi : val (@inord m l') = l' by exact: (inordK hl').
  have hii : inord l' != l by apply: contra hne => /eqP <-; rewrite hvi.
  case: (boolP (wpred (inord l') (nth set0 es j))) => hw /=.
    by rewrite tixE (negbTE hii) andbF.
  by rewrite eq_sym tix_null.
case: (boolP (wpred l (nth set0 es j) && (sd (nth set0 es j) == s))) => hX.
  rewrite (@eq_count _ _ (pred1 (val l))); last by move=> l' /=; rewrite andbT.
  by rewrite count_uniq_mem ?iota_uniq // mem_iota /= add0n ltn_ord.
rewrite (@eq_count _ _ pred0); last by move=> l' /=; rewrite andbF.
by rewrite count_pred0.
Qed.

Lemma count_creal_tix (s : bool) (l : 'I_m.+1) :
  count (pred1 (tix s l)) creal
  = count (fun e => wpred l e && (sd e == s)) es.
Proof.
rewrite /creal count_map count_iota_blocks.
rewrite (eq_bigr (fun j : 'I_N =>
   (wpred l (nth set0 es j) && (sd (nth set0 es j) == s) : nat))); last first.
  by move=> j _; exact: count_block_tix.
exact: (sum_ord_count set0 es (fun e => wpred l e && (sd e == s))).
Qed.


Lemma pos_lt (j l' : nat) : j < N -> l' < m.+1 -> j * m.+1 + l' < N * m.+1.
Proof.
move=> hj hl'.
apply: (leq_trans (_ : j * m.+1 + l' < j.+1 * m.+1)).
  by rewrite mulSn addnC ltn_add2r.
by rewrite leq_mul2r hj orbT.
Qed.

Lemma count_block_tix_gen (j : nat) (s : bool) (l : 'I_m.+1) (R : nat -> bool) :
  count (fun l' => (beadty (j * m.+1 + l') == tix s l) && R (j * m.+1 + l'))
        (iota 0 m.+1)
  = (wpred l (nth set0 es j) && (sd (nth set0 es j) == s)
     && R (j * m.+1 + val l) : nat).
Proof.
rewrite (@eq_in_count _ _
   (fun l' => (l' == val l) &&
      (wpred l (nth set0 es j) && (sd (nth set0 es j) == s)
       && R (j * m.+1 + val l)))); last first.
  move=> l'; rewrite mem_iota /= add0n => hl'.
  rewrite beadty_block //.
  case: (altP (l' =P val l)) => [hl'e|hne] /=.
    rewrite hl'e inord_val.
    case: (boolP (wpred l (nth set0 es j))) => hw /=.
      by rewrite tixE eqxx andbT.
    by rewrite eq_sym tix_null.
  have hvi : val (@inord m l') = l' by exact: (inordK hl').
  have hii : inord l' != l by apply: contra hne => /eqP <-; rewrite hvi.
  case: (boolP (wpred (inord l') (nth set0 es j))) => hw /=.
    by rewrite tixE (negbTE hii) andbF.
  by rewrite eq_sym tix_null.
case: (boolP (wpred l (nth set0 es j) && (sd (nth set0 es j) == s)
              && R (j * m.+1 + val l))) => hX.
  rewrite (@eq_count _ _ (pred1 (val l))); last by move=> l' /=; rewrite andbT.
  by rewrite count_uniq_mem ?iota_uniq // mem_iota /= add0n ltn_ord.
rewrite (@eq_count _ _ pred0); last by move=> l' /=; rewrite andbF.
by rewrite count_pred0.
Qed.

Section WithSplit.
Variable a : seq 'I_2.
Hypothesis size_a : size a = size cs.
Hypothesis share_a : forall (k : 'I_t) (j : 'I_2),
  count_pair k j cs a = count (pred1 k) cs %/ 2.

Definition bth (p : nat) : 'I_2 := nth ord0 a p.

(** The thief of an edge, and the selection it defines. *)

Definition thj (j : nat) : bool := bth (j * m.+1) == ord0.
Definition thE (e : {set G}) : bool := thj (index e es).
Definition sel (e : {set G}) : bool := if e \in A then thE e else ~~ thE e.

Lemma thE_nth (j : nat) : j < N -> thE (nth set0 es j) = thj j.
Proof.
by move=> hj; rewrite /thE index_uniq // (uniq_bl bipf mA mB).
Qed.

Lemma map_thE_es : [seq thE e | e <- es] = [seq thj j | j <- iota 0 N].
Proof.
have hes : es = [seq nth set0 es j | j <- iota 0 N].
  by rewrite map_nth_iota0 // take_size.
rewrite {1}hes -map_comp; apply/eq_in_map => j.
by rewrite mem_iota /= add0n => hj; rewrite /= thE_nth.
Qed.

(** The selected edges, minus those that start a conflict. *)

Definition Csel : {set {set G}} := [set e in SS A B | sel e].
Definition Psrc : {set {set G}} :=
  [set e in SS A B | sel e && ((nxt f A B e != set0) && (nxt f A B e \in Csel))].
Definition Chalf : {set {set G}} := (A :&: B) :|: (Csel :\: Psrc).

Lemma mem_Csel (e : {set G}) : (e \in Csel) = (e \in SS A B) && sel e.
Proof. by rewrite inE. Qed.

Lemma mem_Psrc (e : {set G}) :
  (e \in Psrc) = (e \in SS A B) &&
     (sel e && ((nxt f A B e != set0) && (nxt f A B e \in Csel))).
Proof. by rewrite inE. Qed.

Lemma sel_opp (e : {set G}) :
  e \in SS A B -> nxt f A B e != set0 -> sel e -> sel (nxt f A B e) ->
  thE e != thE (nxt f A B e).
Proof.
move=> /SSP/orP[he|he] hn hs hsn.
  have hnB := nxt_SA he hn.
  have hnA' : nxt f A B e \notin A.
    by move: (proj1 (andP hnB)); rewrite inE => /andP[].
  move: hs; rewrite /sel (SA_A he) => hs.
  move: hsn; rewrite /sel (negbTE hnA') => hsn.
  by rewrite hs; move: hsn; case: (thE (nxt f A B e)).
have hnA := nxt_SB he hn.
have heA : e \notin A by move: he; rewrite inE => /andP[].
move: hs; rewrite /sel (negbTE heA) => hs.
move: hsn; rewrite /sel (SA_A (proj1 (andP hnA))) => hsn.
by rewrite hsn; move: hs; case: (thE e).
Qed.

(** Set-theoretic bookkeeping. *)

Lemma Csel_SS (e : {set G}) : e \in Csel -> e \in SS A B.
Proof. by rewrite mem_Csel => /andP[]. Qed.

Lemma AB_SS (e : {set G}) : e \in A :&: B -> e \notin SS A B.
Proof.
rewrite inE => /andP[hA hB]; apply/negP => /SSP/orP[]; rewrite inE.
  by move=> /andP[]; rewrite hB.
by move=> /andP[]; rewrite hA.
Qed.

Lemma Chalf_matching : matching Chalf.
Proof.
have hsub : forall e, e \in Chalf -> (e \in A) || (e \in B).
  move=> e; rewrite inE => /orP[|].
    by rewrite inE => /andP[-> _].
  rewrite inE => /andP[_ /Csel_SS /SSP/orP[/SA_A ->|/SB_B ->]] //.
  by rewrite orbT.
split.
  move=> e /hsub /orP[hA|hB].
    by case: mA => hs _; exact: (hs _ hA).
  by case: mB => hs _; exact: (hs _ hB).
move=> e1 e2 h1 h2 v hv1 hv2.
case: (e1 =P e2) => // hne.
have hne1 : e1 != e2 by apply/eqP.
have key : forall x y : {set G}, x \in Chalf -> y \in Chalf -> x != y ->
    v \in x -> v \in y -> (x \in A :&: B) -> x = y.
  move=> x y hx hy hxy hvx hvy hxAB.
  have hxA : x \in A by move: hxAB; rewrite inE => /andP[].
  have hxB : x \in B by move: hxAB; rewrite inE => /andP[].
  case/orP: (hsub _ hy) => hym.
    by case: mA => _ hu; apply: (hu _ _ hxA hym v).
  by case: mB => _ hu; apply: (hu _ _ hxB hym v).
case: (boolP (e1 \in A :&: B)) => h1AB; first exact: (key e1 e2).
case: (boolP (e2 \in A :&: B)) => h2AB.
  by apply/esym; apply: (key e2 e1) => //; rewrite eq_sym.
have hC1 : e1 \in Csel :\: Psrc by move: h1; rewrite inE (negbTE h1AB).
have hC2 : e2 \in Csel :\: Psrc by move: h2; rewrite inE (negbTE h2AB).
have hin1 : e1 \in Csel by move: hC1; rewrite inE => /andP[_].
have hin2 : e2 \in Csel by move: hC2; rewrite inE => /andP[_].
have hnp1 : e1 \notin Psrc by move: hC1; rewrite inE => /andP[].
have hnp2 : e2 \notin Psrc by move: hC2; rewrite inE => /andP[].
have hs1 : e1 \in SS A B by exact: Csel_SS.
have hs2 : e2 \in SS A B by exact: Csel_SS.
have hsel1 : sel e1 by move: hin1; rewrite mem_Csel => /andP[].
have hsel2 : sel e2 by move: hin2; rewrite mem_Csel => /andP[].
exfalso.
case/orP: (meetP bipf mA mB hs1 hs2 hne1 hv1 hv2) => /eqP hnx.
  by move: hnp1; rewrite mem_Psrc hs1 hsel1 hnx hin2 (SS_neq0 mA mB hs2).
have hne2 : e2 != e1 by rewrite eq_sym.
by move: hnp2; rewrite mem_Psrc hs2 hsel2 hnx hin1 (SS_neq0 mA mB hs1).
Qed.

Lemma card_split (P : pred {set G}) :
  #|[set e in A | P e]| + #|[set e in B | P e]|
  = 2 * #|[set e in A :&: B | P e]| + count P es.
Proof.
have hA : #|[set e in A | P e]|
        = #|[set e in A :&: B | P e]| + #|[set e in SA A B | P e]|.
  have -> : [set e in A :&: B | P e] = [set e in A | P e] :&: B.
    apply/setP => e; rewrite !inE.
    by case: (P e); case: (e \in A); case: (e \in B).
  have -> : [set e in SA A B | P e] = [set e in A | P e] :\: B.
    apply/setP => e; rewrite !inE.
    by case: (P e); case: (e \in A); case: (e \in B).
  by rewrite cardsID.
have hB : #|[set e in B | P e]|
        = #|[set e in A :&: B | P e]| + #|[set e in SB A B | P e]|.
  have -> : [set e in A :&: B | P e] = [set e in B | P e] :&: A.
    apply/setP => e; rewrite !inE.
    by case: (P e); case: (e \in A); case: (e \in B).
  have -> : [set e in SB A B | P e] = [set e in B | P e] :\: A.
    apply/setP => e; rewrite !inE.
    by case: (P e); case: (e \in A); case: (e \in B).
  by rewrite cardsID.
have hSS : count P es = #|[set e in SA A B | P e]| + #|[set e in SB A B | P e]|.
  rewrite -(@card_seq_count _ es (SS A B) P (uniq_bl bipf mA mB) (mem_bl bipf mA mB)).
  have -> : [set e in SS A B | P e]
          = [set e in SA A B | P e] :|: [set e in SB A B | P e].
    by apply/setP => e; rewrite !inE -andb_orl.
  rewrite cardsU.
  have -> : [set e in SA A B | P e] :&: [set e in SB A B | P e] = set0.
    apply/setP => e; rewrite !inE.
    by case: (P e); case: (e \in A); case: (e \in B).
  by rewrite cards0 subn0.
by rewrite hA hB hSS -!plusE -!multE; lia.
Qed.

Lemma memsetP (X : {set {set G}}) (P : pred {set G}) (e : {set G}) :
  (e \in [set x in X | P x]) = (e \in X) && P e.
Proof. by rewrite inE. Qed.

Lemma card_Chalf (P : pred {set G}) :
  #|[set e in Chalf | P e]|
  = #|[set e in A :&: B | P e]| + #|[set e in Csel :\: Psrc | P e]|.
Proof.
have hmem : forall e, (e \in Chalf) = (e \in A :&: B) || (e \in Csel :\: Psrc).
  by move=> e; rewrite /Chalf inE.
have -> : [set e in Chalf | P e]
        = [set e in A :&: B | P e] :|: [set e in Csel :\: Psrc | P e].
  by apply/setP => e; rewrite memsetP hmem in_setU !memsetP andb_orl.
rewrite cardsU.
have -> : [set e in A :&: B | P e] :&: [set e in Csel :\: Psrc | P e] = set0.
  apply/setP => e; rewrite in_setI !memsetP in_set0 in_setD.
  case: (boolP ((e \in A) && (e \in B))) => hab /=; last by [].
  have hab' : e \in A :&: B by rewrite in_setI.
  have -> : (e \in Csel) = false.
    by apply/negbTE; apply: contra (AB_SS hab') => /Csel_SS.
  by rewrite andbF andbF.
by rewrite cards0 subn0.
Qed.

Lemma card_Csel_count (P : pred {set G}) :
  #|[set e in Csel | P e]| = count (fun e => sel e && P e) es.
Proof.
have -> : [set e in Csel | P e] = [set e in SS A B | sel e && P e].
  by apply/setP => e; rewrite !memsetP andbA.
exact: (@card_seq_count _ es (SS A B) (fun e => sel e && P e)
                        (uniq_bl bipf mA mB) (mem_bl bipf mA mB)).
Qed.

Lemma card_Chalf_ge (P : pred {set G}) :
  #|[set e in A :&: B | P e]| + count (fun e => sel e && P e) es
  <= #|[set e in Chalf | P e]| + #|Psrc|.
Proof.
rewrite card_Chalf -card_Csel_count -addnA leq_add2l.
apply: (leq_trans (_ : _ <= #|[set e in Csel :\: Psrc | P e] :|: Psrc|)).
  apply: subset_leq_card; apply/subsetP => e.
  rewrite memsetP => /andP[hc hP].
  case: (boolP (e \in Psrc)) => hp; first by rewrite in_setU hp orbT.
  by rewrite in_setU memsetP in_setD hp hc hP.
apply: (leq_trans (leq_card_setU _ _).1) => //.
Qed.

Lemma wpred0 (e : {set G}) : wpred ord0 e = true.
Proof. by rewrite /wpred unlift_none. Qed.

Lemma set_wpred0 (X : {set {set G}}) : [set e in X | wpred ord0 e] = X.
Proof. by apply/setP => e; rewrite memsetP wpred0 andbT. Qed.

End WithSplit.

End Halving.
(** ** The colour classes of a line colouring, as a family indexed by ['I_D] *)

Section Assembly.
Variables (G : sgraph) (f : G -> bool) (m : nat) (E : 'I_m -> {set {set G}}).
Hypothesis bipf : forall x y : G, x -- y -> f x != f y.
Hypothesis subE : forall i : 'I_m, E i \subset E(G).
Variable D : nat.
Hypothesis D_gt0 : 0 < D.
Hypothesis D_deg : forall v : G, #|N(v)| <= D.

Variable col : {set G} -> nat.
Hypothesis col_lt : forall e : {set G}, e \in E(G) -> col e < D.
Hypothesis col_match : forall j : nat, matching [set e in E(G) | col e == j].

Definition cls (j : 'I_D) : {set {set G}} := [set e in E(G) | col e == val j].

Lemma cls_matching (j : 'I_D) : matching (cls j).
Proof. exact: col_match. Qed.

Lemma cls_sub (j : 'I_D) : cls j \subset E(G).
Proof. by apply/subsetP => e; rewrite inE => /andP[]. Qed.

(** The colour classes partition [E(G)], hence partition every [X \subset E(G)]. *)
Lemma cls_card (X : {set {set G}}) (j : 'I_D) :
  #|X :&: cls j| = \sum_(e in X) (e \in cls j : nat).
Proof.
rewrite -sum1_card big_mkcond /= [RHS]big_mkcond /=.
by apply: eq_bigr => e _; rewrite inE; case: (e \in X); case: (e \in cls j).
Qed.

Lemma cls_uniq (e : {set G}) : e \in E(G) -> \sum_(j < D) (e \in cls j : nat) = 1.
Proof.
move=> he.
rewrite (bigD1 (Ordinal (col_lt he))) //= big1 ?addn0.
  by rewrite !inE he eqxx.
move=> j hj; apply/eqP; rewrite eqb0 !inE he /=.
by apply: contra hj => /eqP hcol; apply/eqP/val_inj.
Qed.

Lemma cls_partition (X : {set {set G}}) :
  X \subset E(G) -> \sum_(j < D) #|X :&: cls j| = #|X|.
Proof.
move=> hX.
rewrite (eq_bigr _ (fun j _ => cls_card X j)) exchange_big /=.
rewrite -sum1_card big_mkcond [RHS]big_mkcond /=.
apply: eq_bigr => e _.
case: (boolP (e \in X)) => heX //=.
by rewrite (cls_uniq (subsetP hX _ heX)).
Qed.

End Assembly.


Lemma sub_matching (G : sgraph) (M M' : {set {set G}}) :
  M' \subset M -> matching M -> matching M'.
Proof.
move=> hsub [h1 h2]; split; first by move=> e he; apply: h1; exact: (subsetP hsub).
by move=> e1 e2 h1' h2'; apply: h2; exact: (subsetP hsub).
Qed.

Definition gd (s : bool) : 'I_2 := if s then inord 1 else ord0.

Lemma gdE (x : 'I_2) (s : bool) : (x == gd s) = ((x == ord0) == ~~ s).
Proof.
rewrite -!val_eqE /gd; case: s => /=; last by case: (val x).
by rewrite inordK //; case: x => [[|[|i]] hi].
Qed.

(** ** One pair inside a round *)

Section PairRound.
Variables (G : sgraph) (f : G -> bool) (m : nat) (W : 'I_m -> {set {set G}}).
Hypothesis bipf : forall x y : G, x -- y -> f x != f y.
Variables (A B : {set {set G}}).
Hypothesis mA : matching A.
Hypothesis mB : matching B.
Variables (a : seq 'I_2) (gty : nat -> 'I_#|{: bool * 'I_m.+1}|.+1).
Variables (rm : pred nat) (off : nat).

Local Notation es := (bl f A B).
Local Notation N := (size (bl f A B)).
Local Notation nul := (tnull m).
Local Notation seg := (take (size (bl f A B) * m.+1) (drop off a)).

Hypothesis hoff : off + N * m.+1 <= size a.
Hypothesis hgty : forall p, p < N * m.+1 ->
  gty (off + p) = (if rm (off + p) then nul else beadty f A B W p).

(** the thief of position [p] of this pair *)
Definition rbth (p : nat) : 'I_2 := nth ord0 a (off + p).

Definition runan (j : nat) : bool :=
  all (fun l => rbth (j * m.+1 + l) == rbth (j * m.+1)) (iota 0 m.+1).
Definition rrmd (j : nat) : bool := has (fun l => rm (off + (j * m.+1 + l))) (iota 0 m.+1).
Definition rkeep (j : nat) : bool := runan j && ~~ rrmd j.
Definition rkeepE (e : {set G}) : bool := rkeep (index e es).

(** [rhnr e]: the *head* bead of [e]'s group was not removed.  Vacuously true
    off [es]; in particular on [A :&: B] ([set_rhnr]).  Removing a head bead is
    removing a bead of a *size* type, and such an edge is already absent from
    the exact half, so it must not be charged a second time in the ledger. *)
Definition rhnr (e : {set G}) : bool :=
  (e \notin SS A B) || ~~ rm (off + (index e es) * m.+1).

(** a removal at a *class* bead of [e]'s group, i.e. strictly inside it *)
Definition rrmdc (j : nat) : bool :=
  has (fun l => rm (off + (j * m.+1 + l))) (iota 1 m).

Lemma rrmdE (j : nat) : rrmd j = rm (off + j * m.+1) || rrmdc j.
Proof. by rewrite /rrmd /rrmdc -[iota 0 m.+1]/(0 :: iota 1 m) /= addn0. Qed.

Lemma set_rhnr : [set e in A :&: B | rhnr e] = A :&: B.
Proof.
apply/setP => e; rewrite memsetP.
case: (boolP (e \in A :&: B)) => he /=; last by [].
by rewrite /rhnr (AB_SS he).
Qed.

Definition rBad : {set {set G}} := [set e in SS A B | ~~ rkeepE e].
Definition rCr : {set {set G}} := Chalf f A B m (drop off a) :\: rBad.

Definition rYc (s : bool) (l : 'I_m.+1) : nat :=
  count (fun p => (gty (off + p) == tix s l) && (nth ord0 a (off + p) == gd s))
        (iota 0 (N * m.+1)).

(** *** the pair's matching *)

Lemma rCr_matching : matching rCr.
Proof.
apply: (sub_matching (M := Chalf f A B m (drop off a))); first exact: subsetDl.
exact: (Chalf_matching m bipf mA mB).
Qed.

(** *** positional form of [rYc] *)

Lemma rbth_seg (p : nat) : p < N * m.+1 -> nth ord0 seg p = rbth p.
Proof. by move=> hp; rewrite nth_take // nth_drop. Qed.

Lemma size_seg : size seg = N * m.+1.
Proof.
rewrite size_take size_drop.
have hoa : off <= size a by apply: leq_trans hoff; exact: leq_addr.
have h : N * m.+1 <= size a - off by rewrite -(leq_add2l off) subnKC.
by case: ltnP => // h2; apply/eqP; rewrite eqn_leq h2 h.
Qed.

Lemma rYcE (s : bool) (l : 'I_m.+1) :
  rYc s l = \sum_(j < N)
    ((wpred W l (nth set0 es j) && (sd B (nth set0 es j) == s)
      && (~~ rm (off + (j * m.+1 + val l)) && (nth ord0 a (off + (j * m.+1 + val l)) == gd s)))
     : nat).
Proof.
rewrite /rYc count_iota_blocks; apply: eq_bigr => j _.
rewrite -(count_block_tix_gen f A B W j s l
            (fun p => ~~ rm (off + p) && (nth ord0 a (off + p) == gd s))).
apply: eq_in_count => l'; rewrite mem_iota /= add0n => hl'.
have hp : j * m.+1 + l' < N * m.+1 by apply: pos_lt => //; exact: ltn_ord j.
rewrite (hgty hp); case: ifP => hr /=; last by [].
by rewrite eq_sym tix_null andbF.
Qed.

(** *** the edges of the pair, indexed by position in [es] *)

Lemma r_index (j : nat) : j < N -> index (nth set0 es j) es = j.
Proof. by move=> hj; rewrite index_uniq // (uniq_bl bipf mA mB). Qed.

Lemma r_mem (j : nat) : j < N -> nth set0 es j \in SS A B.
Proof. by move=> hj; rewrite -(mem_bl bipf mA mB) mem_nth. Qed.

Lemma r_bth_drop (p : nat) : nth ord0 (drop off a) p = rbth p.
Proof. by rewrite nth_drop. Qed.

Lemma r_selE (j : nat) : j < N ->
  sel f A B m (drop off a) (nth set0 es j)
  = (rbth (j * m.+1) == gd (sd B (nth set0 es j))).
Proof.
move=> hj; set e := nth set0 es j.
have he : e \in SS A B by exact: r_mem.
have hth : thE f A B m (drop off a) e = (rbth (j * m.+1) == ord0).
  by rewrite /thE r_index // /thj /bth r_bth_drop.
rewrite gdE /sel hth /sd.
case/orP: (SSP he) => hs.
  have hA : e \in A := @SA_A _ _ _ _ hs.
  have hB : (e \in B) = false by apply/negbTE; move: hs; rewrite inE => /andP[].
  by rewrite hA hB /= eqb_id.
have hB : e \in B := @SB_B _ _ _ _ hs.
have hA : (e \in A) = false by apply/negbTE; move: hs; rewrite inE => /andP[].
by rewrite hA hB /= eqbF_neg.
Qed.

(** *** the class bound *)

Lemma r_count_class (l : 'I_m.+1) :
  count (fun e => sel f A B m (drop off a) e && (rkeepE e && wpred W l e)) es
  <= rYc false l + rYc true l.
Proof.
rewrite -(sum_ord_count set0 es) !rYcE -big_split /=.
apply: leq_sum => j _; set e := nth set0 es j.
have hj : j < N by exact: ltn_ord.
case: (boolP (sel f A B m (drop off a) e && (rkeepE e && wpred W l e))) => [hc|_] //=.
move: hc => /andP[hsel /andP[hkeep hw]].
have hk : rkeep j by move: hkeep; rewrite /rkeepE r_index.
have hun : rbth (j * m.+1 + val l) == rbth (j * m.+1).
  move: hk => /andP[/allP hall _]; apply: hall.
  by rewrite mem_iota /= add0n ltn_ord.
have hnr : ~~ rm (off + (j * m.+1 + val l)).
  move: hk => /andP[_]; apply: contra => hr.
  by apply/hasP; exists (val l) => //; rewrite mem_iota /= add0n ltn_ord.
have hgood : nth ord0 a (off + (j * m.+1 + val l)) == gd (sd B e).
  by rewrite -/(rbth _) (eqP hun) -(r_selE hj).
case: (sd B e) hgood => hgood; rewrite ?addn0 ?add0n.
  by rewrite hw /= hnr hgood.
by rewrite hw /= hnr hgood.
Qed.

(** *** the size bound *)

Lemma r_count_size :
  rYc false ord0 + rYc true ord0
  <= count (fun e => sel f A B m (drop off a) e && rhnr e) es.
Proof.
rewrite -(sum_ord_count set0 es) !rYcE -big_split /=.
apply: leq_sum => j _; set e := nth set0 es j.
have hj : j < N by exact: ltn_ord.
have he : e \in SS A B by exact: r_mem.
have hi : index e es = j by exact: r_index.
rewrite (r_selE hj) /rhnr he /= hi /=.
rewrite !wpred0 !addn0 /=.
by case: (rm (off + j * m.+1)); case: (sd B e) => /=;
   rewrite ?andbF ?andbT //=; case: (_ == _).
Qed.

(** *** cuts inside the pair's segment *)

Lemma r_cuts_seg :
  cuts_seq seg
  = count (fun p => (p.+1 < N * m.+1) && (rbth p != rbth p.+1)) (iota 0 (N * m.+1)).
Proof.
rewrite (cuts_seq_nth ord0) size_seg; apply: eq_in_count => k.
rewrite mem_iota /= add0n => hk.
case: (boolP (k.+1 < N * m.+1)) => hk1 /=; last by [].
by rewrite !rbth_seg.
Qed.

Lemma r_block_lt (j i : nat) : j < N -> i < m.+1 -> j * m.+1 + i < N * m.+1.
Proof. by move=> hj hi; exact: pos_lt. Qed.

Lemma r_block_cut (j : nat) : j < N -> ~~ runan j ->
  0 < count (fun i => (j * m.+1 + i.+1 < N * m.+1)
                      && (rbth (j * m.+1 + i) != rbth (j * m.+1 + i.+1))) (iota 0 m).
Proof.
move=> hj; rewrite /runan -has_predC => /hasP[l]; rewrite mem_iota /= add0n => hl hne.
apply: (leq_trans (_ : _ <= count (fun i => rbth (j * m.+1 + i)
                                         != rbth (j * m.+1 + i.+1)) (iota 0 l))).
  apply: (leq_trans (_ : _ <= ((rbth (j * m.+1 + 0) != rbth (j * m.+1 + l)) : nat))).
    by rewrite addn0 eq_sym hne.
  exact: (diff_count (fun i => rbth (j * m.+1 + i)) l).
apply: (leq_trans (_ : _ <= count (fun i => rbth (j * m.+1 + i)
                                         != rbth (j * m.+1 + i.+1)) (iota 0 m))).
  by apply: count_iota_le; rewrite -ltnS.
apply: eq_leq; apply: eq_in_count => i; rewrite mem_iota /= add0n => hi.
have hlt : j * m.+1 + i.+1 < N * m.+1.
  apply: (leq_ltn_trans (_ : j * m.+1 + i.+1 <= j * m.+1 + m)).
    by rewrite leq_add2l.
  by apply: r_block_lt.
by rewrite hlt.
Qed.

(** Superseded by [r_nonunan_int], which charges the non-unanimous edges to the
    *interior* cuts only; kept as the coarse bound. *)
Lemma r_nonunan_cuts : count (fun j => ~~ runan j) (iota 0 N) <= cuts_seq seg.
Proof.
rewrite r_cuts_seg count_iota_sum count_iota_blocks.
apply: leq_sum => j _.
have hj : j < N by exact: ltn_ord.
case: (boolP (runan j)) => hu; first by [].
apply: (leq_trans (leq_b1 _)).
apply: (leq_trans (r_block_cut hj hu)).
rewrite (@eq_in_count _ _ (fun i => (j * m.+1 + i.+1 < N * m.+1)
          && (rbth (j * m.+1 + i) != rbth (j * m.+1 + i.+1))) (iota 0 m.+1));
  first exact: count_iota_le.
by move=> i _; rewrite -addnS.
Qed.

Lemma r_cuts_thE :
  cuts_seq [seq thE f A B m (drop off a) e | e <- es] <= cuts_seq seg.
Proof.
rewrite (map_thE_es m bipf mA mB) (cuts_seq_map_nth 0) size_iota r_cuts_seg.
rewrite (@eq_in_count _ _ (fun k => (k.+1 < N) && (thj m (drop off a) k
                                                != thj m (drop off a) k.+1))); last first.
  move=> k; rewrite mem_iota /= add0n => hk.
  case: (boolP (k.+1 < N)) => hk1 /=; last by [].
  by rewrite !nth_iota // ?add0n //; apply: ltn_trans hk1.
rewrite [X in X <= _]count_iota_sum count_iota_blocks.
apply: leq_sum => j _.
have hj : j < N by exact: ltn_ord.
case: (boolP (j.+1 < N)) => hj1; last by [].
apply: (leq_trans (_ : _ <= ((rbth (j * m.+1) != rbth (j * m.+1 + m.+1)) : nat))).
  rewrite andTb /thj /bth !r_bth_drop (_ : j.+1 * m.+1 = j * m.+1 + m.+1);
    last by rewrite mulSnr.
  case: (altP (rbth (j * m.+1) =P rbth (j * m.+1 + m.+1))) => [heq|hne];
    first by rewrite heq eqxx.
  exact: leq_b1.
apply: (leq_trans (_ : _ <= count (fun i => rbth (j * m.+1 + i)
                                         != rbth (j * m.+1 + i.+1)) (iota 0 m.+1))).
  rewrite -{1}(addn0 (j * m.+1)).
  exact: (diff_count (fun i => rbth (j * m.+1 + i)) m.+1).
apply: eq_leq; apply: eq_in_count => i; rewrite mem_iota /= add0n => hi.
have hlt : j * m.+1 + i.+1 < N * m.+1.
  apply: (leq_ltn_trans (_ : j * m.+1 + i.+1 <= j * m.+1 + m.+1));
    first by rewrite leq_add2l.
  by rewrite -mulSnr ltn_mul2r /= hj1.
by rewrite -addnS hlt.
Qed.

(** Superseded by [r_Pk_cuts], which charges only the conflicts between *kept*
    edges, to boundary cuts; kept as the coarse bound. *)
Lemma r_Psrc_cuts : #|Psrc f A B m (drop off a)| <= 2 * cuts_seq seg.
Proof.
apply: (leq_trans (_ : _ <= 2 * cuts_seq [seq thE f A B m (drop off a) e | e <- es]));
  last by rewrite leq_pmul2l //; exact: r_cuts_thE.
pose P := fun e : {set G} => (e \in SS A B) && (sel f A B m (drop off a) e
            && ((nxt f A B e != set0) && (nxt f A B e \in Csel f A B m (drop off a)))).
have hP : #|Psrc f A B m (drop off a)| = count P es.
  rewrite (@card_seq_count _ es (SS A B) _ (uniq_bl bipf mA mB) (mem_bl bipf mA mB)).
  apply: eq_in_count => e; rewrite (mem_bl bipf mA mB) => he.
  by rewrite /P he.
rewrite hP.
apply: (conflict_count bipf mA mB) => e /and4P[he hs hn hin].
split=> //.
apply: (@sel_opp _ _ _ _ _ _ _ he hn hs).
by move: hin; rewrite mem_Csel => /andP[].
Qed.

Lemma r_rmd_count :
  count (fun j => rrmdc j) (iota 0 N)
  <= count (fun p => rm (off + p) && (p %% m.+1 != 0)) (iota 0 (N * m.+1)).
Proof.
rewrite count_iota_sum count_iota_blocks; apply: leq_sum => j _.
have hQ : count (fun l => rm (off + (j * m.+1 + l))
                          && ((j * m.+1 + l) %% m.+1 != 0)) (iota 0 m.+1)
        = count (fun l => rm (off + (j * m.+1 + l))) (iota 1 m).
  rewrite -[iota 0 m.+1]/(0 :: iota 1 m) /= modnMDl mod0n eqxx andbF add0n.
  apply: eq_in_count => l; rewrite mem_iota /= add1n => /andP[hl1 hl2].
  by rewrite modnMDl (modn_small hl2) -lt0n hl1 andbT.
rewrite hQ /rrmdc has_count.
by case: (count (fun l => rm (off + (j * m.+1 + l))) (iota 1 m)).
Qed.

Lemma r_keep_count :
  count (fun e => rhnr e && ~~ rkeepE e) es
  <= count (fun j => ~~ runan j) (iota 0 N) + count (fun j => rrmdc j) (iota 0 N).
Proof.
rewrite -(sum_ord_count set0 es) !count_iota_sum -big_split /=.
apply: leq_sum => j _; set e := nth set0 es j.
have hj : j < N by exact: ltn_ord.
have he : e \in SS A B by exact: r_mem.
have hi : index e es = j by exact: r_index.
rewrite /rkeepE hi /rhnr he /= hi /rkeep negb_and negbK rrmdE.
by case: (rm (off + j * m.+1)); case: (runan j); case: (rrmdc j).
Qed.

(** *** interior cuts versus boundary cuts

    A cut strictly inside an edge's bead group makes that edge non-unanimous
    (it is thrown away); a cut at the boundary between two groups is what a
    conflict between two *kept* edges needs.  The two are disjoint. *)

Definition rQbnd (p : nat) : bool :=
  ((p.+1 < N * m.+1) && (rbth p != rbth p.+1)) && (p %% m.+1 == m).
Definition rQint (p : nat) : bool :=
  ((p.+1 < N * m.+1) && (rbth p != rbth p.+1)) && (p %% m.+1 != m).

Lemma r_cuts_split :
  count rQbnd (iota 0 (N * m.+1)) + count rQint (iota 0 (N * m.+1)) = cuts_seq seg.
Proof.
by rewrite r_cuts_seg (count_split (iota 0 (N * m.+1))
     (fun p => (p.+1 < N * m.+1) && (rbth p != rbth p.+1))
     (fun p => p %% m.+1 == m)).
Qed.

Lemma r_mod_block (j i : nat) : i < m.+1 -> (j * m.+1 + i) %% m.+1 = i.
Proof. by move=> hi; rewrite modnMDl modn_small. Qed.

Lemma r_nonunan_int :
  count (fun j => ~~ runan j) (iota 0 N) <= count rQint (iota 0 (N * m.+1)).
Proof.
rewrite count_iota_sum count_iota_blocks.
apply: leq_sum => j _.
have hj : j < N by exact: ltn_ord.
case: (boolP (runan j)) => hu; first by [].
apply: (leq_trans (leq_b1 _)).
apply: (leq_trans (r_block_cut hj hu)).
apply: (leq_trans (_ : _ <= count (fun l => rQint (j * m.+1 + l)) (iota 0 m)));
  last exact: count_iota_le.
apply: eq_leq; apply: eq_in_count => i; rewrite mem_iota /= add0n => hi.
have hi1 : i < m.+1 by exact: (ltn_trans hi (ltnSn m)).
rewrite /rQint -addnS r_mod_block // ltn_eqF //.
by rewrite andbT !addnS.
Qed.

(** *** the conflicting edges that are kept *)

Definition rPkp (e : {set G}) : bool :=
  (sel f A B m (drop off a) e
   && ((nxt f A B e != set0) && (nxt f A B e \in Csel f A B m (drop off a))))
  && rkeepE e.

Definition rlin (e : {set G}) : bool := nxt f A B e == nth set0 es (index e es).+1.

Lemma r_thE_nth (j : nat) : j < N ->
  thE f A B m (drop off a) (nth set0 es j) = (rbth (j * m.+1) == ord0).
Proof. by move=> hj; rewrite /thE r_index // /thj /bth r_bth_drop. Qed.

Lemma r_lin_bnd :
  count (fun e => rPkp e && rlin e) es <= count rQbnd (iota 0 (N * m.+1)).
Proof.
rewrite -(sum_ord_count set0 es) count_iota_blocks.
apply: leq_sum => j _.
have hj : j < N by exact: ltn_ord.
set e := nth set0 es j.
case: (boolP (rPkp e && rlin e)) => [/andP[hP hlin]|_]; last by [].
move: hP => /andP[/andP[hsel /andP[hn0 hin]] hkeep].
have hj1 : j.+1 < N.
  case: (ltnP j.+1 N) => // hge; move: hn0.
  by rewrite (eqP hlin) /es r_index // nth_default ?eqxx.
have hthne : thE f A B m (drop off a) e != thE f A B m (drop off a) (nxt f A B e).
  apply: (@sel_opp _ _ _ _ _ _ _ (r_mem hj) hn0 hsel).
  by move: hin; rewrite mem_Csel => /andP[].
have hun : rbth (j * m.+1 + m) = rbth (j * m.+1).
  move: hkeep; rewrite /rkeepE r_index // => /andP[/allP hall _].
  by apply/eqP; apply: hall; rewrite mem_iota /= add0n ltnSn.
rewrite -has_count.
apply/hasP; exists m; first by rewrite mem_iota /= add0n ltnSn.
have hsucc : (j * m.+1 + m).+1 = j.+1 * m.+1 by rewrite -addnS mulSnr.
rewrite /rQbnd hsucc r_mod_block ?ltnSn // eqxx andbT.
rewrite (_ : j.+1 * m.+1 < N * m.+1); last by rewrite ltn_mul2r /= hj1.
rewrite andTb hun.
apply: contra hthne => /eqP heq.
by rewrite -/e (r_thE_nth hj) (eqP hlin) /es r_index // (r_thE_nth hj1) heq.
Qed.

Lemma r_wrap_last (b : seq {set G}) (k : nat) :
  b \in blocks f A B -> k.+1 < size b ->
  ~~ (rPkp (nth set0 b k) && ~~ rlin (nth set0 b k)).
Proof.
move=> hb hk; apply/negP => /andP[hP hnl].
move: hP => /andP[/andP[_ /andP[hn0 _]] _].
have hkk : k < size b by apply: ltn_trans hk; exact: ltnSn.
have hs : nxt f A B (nth set0 b k) = nth set0 b k.+1.
  by rewrite -(sigma_nxt hn0) (block_nth bipf mA mB hb hkk) modn_small.
by move: hnl; rewrite /rlin (bl_block_succ bipf mA mB hb hk) hs eqxx.
Qed.

Lemma r_wrap_block (b : seq {set G}) :
  b \in blocks f A B ->
  count (fun e => rPkp e && ~~ rlin e) b
  <= cuts_seq [seq thE f A B m (drop off a) e | e <- b].
Proof.
move=> hb.
set Wp := fun e => rPkp e && ~~ rlin e.
have hn : 0 < size b by exact: (block_size hb).
have hle1 : count Wp b <= 1.
  rewrite -(count_nth_iota set0 b Wp) count_iota_sum.
  apply: (leq_trans (_ : _ <=
     \sum_(j < size b) ((nat_of_ord j == (size b).-1 : bool) : nat))); last first.
    rewrite -big_mkcond /= sum1dep_card.
    apply/card_le1P => x y.
    move: y; rewrite inE => /eqP hx z; rewrite !inE.
    apply/idP/idP => [/eqP hz|/eqP ->]; last by rewrite hx.
    by apply/eqP; apply: val_inj; rewrite /= hz hx.
  apply: leq_sum => j _.
  case: (boolP (Wp (nth set0 b j))) => hW //=.
  have hj : j < size b by exact: ltn_ord.
  have hnl : ~~ (j.+1 < size b).
    apply/negP => hlt.
    have := r_wrap_last hb hlt.
    by rewrite -/(Wp _) (eqP (introT eqP hW)).
  rewrite lt0n eqb0 negbK.
  move: hnl; rewrite -leqNgt => hnl.
  rewrite eqn_leq.
  apply/andP; split; first by rewrite -ltnS prednK.
  by rewrite -ltnS prednK // ltnS -ltnS prednK.
case: (posnP (count Wp b)) => [-> //|hpos].
apply: (leq_trans hle1).
rewrite (cuts_seq_map_nth set0).
apply/negPn/negP; rewrite -ltnNge ltnS leqn0 => /eqP h0.
have hconst : forall j, j < size b ->
    thE f A B m (drop off a) (nth set0 b j)
  = thE f A B m (drop off a) (nth set0 b 0).
  apply: (@const_iota _ (fun i => thE f A B m (drop off a) (nth set0 b i)) (size b)).
  exact: h0.
move: hpos; rewrite -has_count => /hasP[e he hWe].
set j := index e b.
have hj : j < size b by rewrite index_mem.
have hej : nth set0 b j = e by rewrite nth_index.
have hnl : ~~ (j.+1 < size b).
  apply/negP => hlt.
  have := r_wrap_last hb hlt.
  by rewrite hej -/(Wp e) hWe.
have hjl : j.+1 = size b.
  move: hnl; rewrite -leqNgt => hnl.
  by apply/eqP; rewrite eqn_leq hnl hj.
move: hWe => /andP[hP _]; move: hP => /andP[/andP[hsel /andP[hn0 hin]] _].
have hnxt : nxt f A B e = nth set0 b 0.
  by rewrite -(sigma_nxt hn0) -hej (block_nth bipf mA mB hb hj) hjl modnn.
have hthne : thE f A B m (drop off a) e != thE f A B m (drop off a) (nxt f A B e).
  apply: (@sel_opp _ _ _ _ _ _ _ _ hn0 hsel).
    by apply: (block_sub bipf mA mB hb he).
  by move: hin; rewrite mem_Csel => /andP[].
by move: hthne; rewrite hnxt -hej (hconst j hj) eqxx.
Qed.

Lemma r_wrap_cuts :
  count (fun e => rPkp e && ~~ rlin e) es <= cuts_seq seg.
Proof.
apply: (leq_trans (_ : _ <= cuts_seq [seq thE f A B m (drop off a) e | e <- es]));
  last exact: r_cuts_thE.
rewrite /es /bl count_flatten sumnE big_map.
apply: (leq_trans (_ : _ <= \sum_(b <- blocks f A B)
                     cuts_seq [seq thE f A B m (drop off a) e | e <- b])); last first.
  rewrite map_flatten
    -(big_map (fun b => [seq thE f A B m (drop off a) e | e <- b]) xpredT
              (fun s : seq bool => cuts_seq s)).
  exact: cuts_seq_flatten.
rewrite big_seq_cond [X in _ <= X]big_seq_cond.
by apply: leq_sum => b /andP[hb _]; exact: r_wrap_block.
Qed.

(** *** the two set-level bounds *)

Definition rPk : {set {set G}} := [set e in SS A B | rPkp e].

Lemma r_Pk_cuts :
  #|rPk| <= count rQbnd (iota 0 (N * m.+1)) + cuts_seq seg.
Proof.
rewrite (@card_seq_count _ es (SS A B) _ (uniq_bl bipf mA mB) (mem_bl bipf mA mB)).
rewrite (count_split es rPkp rlin).
by apply: leq_add; [exact: r_lin_bnd | exact: r_wrap_cuts].
Qed.

Lemma rCr_card_le (P : pred {set G}) :
  #|[set e in rCr | P e]|
  <= #|[set e in A :&: B | P e]|
     + count (fun e => sel f A B m (drop off a) e && (rkeepE e && P e)) es.
Proof.
rewrite -(card_Csel_count m bipf mA mB (drop off a) (fun e => rkeepE e && P e)).
apply: (leq_trans (_ : _ <= #|[set e in A :&: B | P e]
                             :|: [set e in Csel f A B m (drop off a) | rkeepE e && P e]|));
  last by apply: (leq_trans (leq_card_setU _ _).1).
apply: subset_leq_card; apply/subsetP => e.
rewrite memsetP in_setD /rCr => /andP[/andP[hb hch] hP].
rewrite inE !memsetP.
move: hch; rewrite /Chalf inE => /orP[hab|hcs]; first by rewrite -in_setI hab hP.
have hcsel : e \in Csel f A B m (drop off a) by move: hcs; rewrite inE => /andP[].
have hss : e \in SS A B by exact: (Csel_SS hcsel).
have hk : rkeepE e by move: hb; rewrite /rBad memsetP hss /= negbK.
move: hcsel; rewrite mem_Csel => /andP[_ hsel].
by rewrite hss hsel hk hP orbT.
Qed.

Lemma rCr_card_ge (P : pred {set G}) :
  #|[set e in A :&: B | P e]| + count (fun e => sel f A B m (drop off a) e && P e) es
  <= #|[set e in rCr | P e]| + #|rPk| + count (fun e => P e && ~~ rkeepE e) es.
Proof.
rewrite -(card_Csel_count m bipf mA mB (drop off a) P).
have hdisj : [set e in A :&: B | P e]
             :&: [set e in Csel f A B m (drop off a) | P e] = set0.
  apply/setP => e; rewrite !inE.
  by case: (e \in A); case: (e \in B); rewrite //= ?andbF.
have hsum : #|[set e in A :&: B | P e]|
          + #|[set e in Csel f A B m (drop off a) | P e]|
          = #|[set e in A :&: B | P e]
              :|: [set e in Csel f A B m (drop off a) | P e]|.
  by rewrite cardsU hdisj cards0 subn0.
rewrite hsum.
apply: (leq_trans (_ : _ <= #|([set e in rCr | P e] :|: rPk) :|: [set e in SS A B | P e && ~~ rkeepE e]|)); last first.
  apply: (leq_trans (leq_card_setU _ _).1).
  rewrite (@card_seq_count _ es (SS A B) _ (uniq_bl bipf mA mB) (mem_bl bipf mA mB))
          leq_add2r.
  exact: (leq_card_setU _ _).1.
apply: subset_leq_card; apply/subsetP => e.
rewrite in_setU !memsetP => /orP[] /andP[hmem hP]; rewrite !in_setU.
  have hmemI : e \in A :&: B by rewrite in_setI hmem.
  have hnb : e \notin rBad by rewrite /rBad memsetP negb_and negbK (AB_SS hmemI).
  rewrite memsetP hP andbT /rCr in_setD hnb /=.
  by rewrite /Chalf in_setU hmemI.
move: hmem => /andP[hss hsel].
case: (boolP (e \in [set e0 in SS A B | P e0 && ~~ rkeepE e0])) => hb;
  first by rewrite orbT.
have hkeep : rkeepE e.
  by move: hb; rewrite memsetP hss /= negb_and hP /= negbK.
have hnb : e \notin rBad by rewrite /rBad memsetP hss /= negbK.
case: (boolP (e \in Psrc f A B m (drop off a))) => hps.
  have hpk : e \in rPk.
    rewrite /rPk memsetP hss /= /rPkp hkeep andbT.
    by move: hps; rewrite mem_Psrc => /andP[_].
  by rewrite hpk orbT.
rewrite memsetP hP andbT /rCr in_setD hnb /= /Chalf in_setU.
rewrite in_setD hps /=.
by rewrite mem_Csel hss hsel orbT.
Qed.

End PairRound.

(** ** One round: all the pairs split by a single necklace splitting *)

Section Round.
Variables (G : sgraph) (f : G -> bool) (m : nat) (W : 'I_m -> {set {set G}}).
Hypothesis bipf : forall x y : G, x -- y -> f x != f y.

Local Notation MM := ({set {set G}}).
Local Notation TY := ('I_#|{: bool * 'I_m.+1}|.+1).
Local Notation nul := (tnull m).

Definition plen (p : MM * MM) : nat := size (bl f p.1 p.2) * m.+1.

Fixpoint gtys (ps : seq (MM * MM)) : seq TY :=
  if ps is p :: ps' then creal f p.1 p.2 W ++ gtys ps' else [::].

Lemma size_gtys (ps : seq (MM * MM)) : size (gtys ps) = \sum_(p <- ps) plen p.
Proof.
elim: ps => [|p ps IH]; first by rewrite big_nil.
by rewrite /= size_cat size_creal IH big_cons.
Qed.

(** *** parity: retype one bead of each odd (non-null) type *)

Definition rmvp (r : seq TY) (p : nat) : bool :=
  [&& nth nul r p != nul, odd (count_mem (nth nul r p) r) & index (nth nul r p) r == p].

Definition retys (r : seq TY) : seq TY :=
  [seq (if rmvp r p then nul else nth nul r p) | p <- iota 0 (size r)].

Definition csq (r : seq TY) : seq TY :=
  retys r ++ nseq (odd (count_mem nul (retys r))) nul.

Lemma size_retys (r : seq TY) : size (retys r) = size r.
Proof. by rewrite size_map size_iota. Qed.

Lemma nth_retys (r : seq TY) (p : nat) : p < size r ->
  nth nul (retys r) p = (if rmvp r p then nul else nth nul r p).
Proof. by move=> hp; rewrite (nth_map 0) ?size_iota // nth_iota. Qed.

Lemma nth_csq (r : seq TY) (p : nat) : p < size r ->
  nth nul (csq r) p = (if rmvp r p then nul else nth nul r p).
Proof. by move=> hp; rewrite nth_cat size_retys hp nth_retys. Qed.

Lemma size_csq (r : seq TY) : size r <= size (csq r).
Proof. by rewrite size_cat size_retys leq_addr. Qed.

Lemma count_retys (r : seq TY) (k : TY) : k != nul ->
  count_mem k (retys r) = count_mem k r - (odd (count_mem k r) : nat).
Proof.
move=> hk.
rewrite /retys count_map.
rewrite (@eq_in_count _ _ (fun p => (nth nul r p == k) && ~~ rmvp r p)); last first.
  move=> p _ /=.
  case: ifP => hr /=; last by rewrite andbT.
  by rewrite andbF eq_sym (negbTE hk).
have hall : count (fun p => nth nul r p == k) (iota 0 (size r)) = count_mem k r.
  exact: (count_nth_iota nul).
have hsplit := count_split (iota 0 (size r)) (fun p => nth nul r p == k) (rmvp r).
have hbad : count (fun p => (nth nul r p == k) && rmvp r p) (iota 0 (size r))
          = (odd (count_mem k r) : nat).
  case: (boolP (odd (count_mem k r))) => ho; last first.
    rewrite (@eq_in_count _ _ pred0) ?count_pred0 // => p _ /=.
    apply/negP => /andP[/eqP hnp /and3P[_ ho' _]].
    by move: ho'; rewrite hnp (negbTE ho).
  have hin : k \in r by rewrite -has_pred1 has_count; case: (count_mem k r) ho.
  rewrite (@eq_in_count _ _ (pred1 (index k r))); last first.
    move=> p _ /=; apply/idP/idP.
      by move=> /andP[/eqP hnp /and3P[_ _ /eqP heq]]; rewrite -hnp heq.
    move=> /eqP ->; rewrite nth_index //= eqxx /rmvp nth_index //.
    by rewrite hk ho eqxx.
  by rewrite count_uniq_mem ?iota_uniq // mem_iota /= add0n index_mem hin.
rewrite -hall hsplit hbad.
have hc : count_mem k r = (odd (count_mem k r) : nat)
        + count (fun p => (nth nul r p == k) && ~~ rmvp r p) (iota 0 (size r)).
  by rewrite -hbad -hsplit hall.
rewrite -hc.
have hle : (odd (count_mem k r) : nat) <= count_mem k r.
  by case: (boolP (odd (count_mem k r))) => ho; [case: (count_mem k r) ho|].
apply/eqP; rewrite -(eqn_add2r ((odd (count_mem k r)) : nat)) (subnK hle).
by rewrite [X in _ == X]hc addnC.
Qed.

Lemma csq_even (r : seq TY) (k : TY) : 2 %| count_mem k (csq r).
Proof.
rewrite /csq count_cat dvdn2.
case: (altP (k =P nul)) => [->|hk].
  by rewrite count_nseq /= eqxx mul1n oddD; case: (odd _).
rewrite count_nseq.
rewrite /= eq_sym (negbTE hk) mul0n addn0 count_retys //.
case: (boolP (odd (count_mem k r))) => ho; last by rewrite subn0 (negbTE ho).
by rewrite oddB ?ho //; case: (count_mem k r) ho.
Qed.

Lemma card_TY : #|TY| = (2 * m.+1).+1.
Proof. by rewrite card_ord card_TT. Qed.

Lemma size_class_types :
  size [seq k <- enum TY | [&& k != nul, k != tix false ord0 & k != tix true ord0]]
  = 2 * m.
Proof.
have h1 : (nul == tix false ord0) = false by rewrite eq_sym tix_null.
have h2 : (nul == tix true ord0) = false by rewrite eq_sym tix_null.
have h3 : (tix false (@ord0 m) == tix true (@ord0 m)) = false by rewrite tixE.
pose L : seq TY := [:: nul; tix false ord0; tix true ord0].
have hu : uniq L by rewrite /L /= !inE h1 h2 h3.
have hmem : L =i [seq k <- enum TY | k \in L].
  by move=> x; rewrite mem_filter mem_enum andbT.
have hsz := uniq_size_uniq hu hmem.
have hsz3 : size [seq k <- enum TY | k \in L] = 3.
  by apply/eqP; rewrite -hsz filter_uniq // enum_uniq.
have hC := count_predC (fun k : TY => k \in L) (enum TY).
rewrite -!size_filter -cardE card_TY hsz3 in hC.
rewrite (@eq_filter _ _ [predC L]); last by move=> k; rewrite /L /= !inE !negb_or.
by apply/eqP; rewrite -(eqn_add2l 3) hC; apply/eqP; rewrite mulnS.
Qed.

(** Only the [2m] *class* types can be removed at a bead that is not the head
    of its group: the head beads are exactly the ones carrying a *size* type. *)
Lemma count_rmvp_class (r : seq TY) :
  (forall q s, q %% m.+1 != 0 -> nth nul r q != tix s ord0) ->
  count (fun q => rmvp r q && (q %% m.+1 != 0)) (iota 0 (size r)) <= 2 * m.
Proof.
move=> hcl; rewrite -size_filter.
apply: (leq_trans (_ : _ <= size [seq k <- enum TY |
          [&& k != nul, k != tix false ord0 & k != tix true ord0]])); last first.
  by rewrite size_class_types.
rewrite -(size_map (fun q => nth nul r q)).
apply: uniq_leq_size.
  rewrite map_inj_in_uniq ?filter_uniq ?iota_uniq // => q1 q2.
  rewrite !mem_filter => /andP[/andP[/and3P[_ _ /eqP hp] _] _].
  by move=> /andP[/andP[/and3P[_ _ /eqP hq] _] _] heq; rewrite -hp -hq heq.
move=> k /mapP[q]; rewrite mem_filter mem_filter.
move=> /andP[/andP[/and3P[hn _ _] hmod] _] ->.
by rewrite mem_enum andbT hn (hcl q false hmod) (hcl q true hmod).
Qed.

(** Superseded by [count_rmvp_class]; kept as the coarse bound over all the
    [2m+2] real types. *)
Lemma count_rmvp (r : seq TY) : count (rmvp r) (iota 0 (size r)) <= 2 * m + 2.
Proof.
rewrite -size_filter.
apply: (leq_trans (_ : _ <= size [seq k <- enum TY | k != nul])); last first.
  rewrite size_filter.
  have hcp := count_predC (pred1 nul) (enum TY).
  rewrite count_uniq_mem ?enum_uniq // mem_enum /= -cardE card_TY in hcp.
  rewrite (@eq_count _ _ (predC (pred1 nul))); last by move=> x /=.
  move: hcp; set X := count _ _ => hcp.
  by move: hcp; rewrite add1n mulnS => [] [->]; rewrite addnC.
rewrite -(size_map (fun p => nth nul r p)).
apply: uniq_leq_size.
  rewrite map_inj_in_uniq ?filter_uniq ?iota_uniq // => p q.
  rewrite !mem_filter => /andP[/and3P[_ _ /eqP hp] _] /andP[/and3P[_ _ /eqP hq] _] heq.
  by rewrite -hp -hq heq.
move=> k /mapP[p]; rewrite mem_filter mem_filter.
by move=> /andP[/and3P[hn _ _] _] ->; rewrite mem_enum andbT.
Qed.

(** *** the pairs of one round, with a shared thief sequence *)

Fixpoint rmatch (a : seq 'I_2) (rm : pred nat) (off : nat) (ps : seq (MM * MM)) : seq MM :=
  if ps is p :: ps' then rCr f m p.1 p.2 a rm off :: rmatch a rm (off + plen p) ps'
  else [::].

Definition Ycnt (a : seq 'I_2) (gty : nat -> TY) (s : bool) (l : 'I_m.+1)
    (off n : nat) : nat :=
  count (fun q => (gty (off + q) == tix s l) && (nth ord0 a (off + q) == gd s)) (iota 0 n).

Fixpoint gok (gty : nat -> TY) (rm : pred nat) (off : nat) (ps : seq (MM * MM)) : Prop :=
  if ps is p :: ps'
  then (forall q, q < plen p ->
          gty (off + q) = (if rm (off + q) then nul else beadty f p.1 p.2 W q))
       /\ gok gty rm (off + plen p) ps'
  else True.

Lemma YcntE (a : seq 'I_2) (gty : nat -> TY) (s : bool) (l : 'I_m.+1)
    (off : nat) (p : MM * MM) :
  Ycnt a gty s l off (plen p) = rYc f p.1 p.2 a gty off s l.
Proof. by []. Qed.

Lemma Ycnt_split (a : seq 'I_2) (gty : nat -> TY) (s : bool) (l : 'I_m.+1)
    (off n1 n2 : nat) :
  Ycnt a gty s l off (n1 + n2) = Ycnt a gty s l off n1 + Ycnt a gty s l (off + n1) n2.
Proof.
rewrite /Ycnt count_iota_split; congr (_ + _).
by apply: eq_in_count => i _; rewrite addnA.
Qed.

Lemma round_ind (a : seq 'I_2) (gty : nat -> TY) (rm : pred nat)
    (ps : seq (MM * MM)) (off : nat) :
  (forall p, p \in ps -> matching p.1) -> (forall p, p \in ps -> matching p.2) ->
  off + \sum_(p <- ps) plen p <= size a ->
  gok gty rm off ps ->
  [/\ size (rmatch a rm off ps) = size ps,
      (forall C, C \in rmatch a rm off ps -> matching C),
      (forall l : 'I_m.+1,
        \sum_(C <- rmatch a rm off ps) #|[set e in C | wpred W l e]|
        <= \sum_(p <- ps) #|[set e in p.1 :&: p.2 | wpred W l e]|
           + Ycnt a gty false l off (\sum_(p <- ps) plen p)
           + Ycnt a gty true l off (\sum_(p <- ps) plen p)) &
      \sum_(p <- ps) #|p.1 :&: p.2|
      + Ycnt a gty false ord0 off (\sum_(p <- ps) plen p)
      + Ycnt a gty true ord0 off (\sum_(p <- ps) plen p)
      <= \sum_(C <- rmatch a rm off ps) #|C|
         + (2 * cuts_seq (take (\sum_(p <- ps) plen p) (drop off a))
            + count (fun q => rm (off + q) && (q %% m.+1 != 0))
                    (iota 0 (\sum_(p <- ps) plen p)))].
Proof.
elim: ps off => [|p ps IH] off hmA hmB hsz hg.
  rewrite !big_nil /Ycnt /=.
  split; [by [] | by move=> C | by move=> l; rewrite !big_nil | by []].
rewrite !big_cons /= Ycnt_split [Ycnt a gty true _ _ _]Ycnt_split.
have hmp1 : matching p.1 by apply: hmA; rewrite in_cons eqxx.
have hmp2 : matching p.2 by apply: hmB; rewrite in_cons eqxx.
have hmtA : forall q, q \in ps -> matching q.1.
  by move=> q hq; apply: hmA; rewrite in_cons hq orbT.
have hmtB : forall q, q \in ps -> matching q.2.
  by move=> q hq; apply: hmB; rewrite in_cons hq orbT.
move: hg => /= [hgp hgt].
have hszt : off + plen p + \sum_(j <- ps) plen j <= size a.
  by move: hsz; rewrite big_cons addnA.
have hszp : off + plen p <= size a by apply: leq_trans hszt; exact: leq_addr.
have [hs1 hs2 hs3 hs4] := IH (off + plen p) hmtA hmtB hszt hgt.
have hcut : cuts_seq (take (plen p) (drop off a))
          + cuts_seq (take (\sum_(j <- ps) plen j) (drop (off + plen p) a))
         <= cuts_seq (take (plen p + \sum_(j <- ps) plen j) (drop off a)).
  rewrite takeD drop_drop [plen p + off]addnC; exact: cuts_seq_cat.
have hrm : count (fun q => rm (off + q) && (q %% m.+1 != 0))
                 (iota 0 (plen p + \sum_(j <- ps) plen j))
         = count (fun q => rm (off + q) && (q %% m.+1 != 0)) (iota 0 (plen p))
         + count (fun q => rm (off + plen p + q) && (q %% m.+1 != 0))
                 (iota 0 (\sum_(j <- ps) plen j)).
  rewrite count_iota_split; congr (_ + _).
  apply: eq_in_count => i _ /=; rewrite addnA.
  by rewrite /plen modnMDl.
split; first by rewrite hs1.
- move=> C; rewrite in_cons => /orP[/eqP ->|hC]; last exact: hs2.
  exact: (@rCr_matching _ f m bipf p.1 p.2 hmp1 hmp2 a rm off).
- move=> l; rewrite !big_cons !Ycnt_split !YcntE.
  have h1 := @rCr_card_le _ f m bipf p.1 p.2 hmp1 hmp2 a rm off (wpred W l).
  have h2 := @r_count_class _ f m W bipf p.1 p.2 hmp1 hmp2 a gty rm off hgp l.
  have h3 := hs3 l.
  apply: (leq_trans (leq_add h1 h3)).
  apply: (leq_trans (leq_add (leq_add (leqnn _) h2) (leqnn _))).
  apply: eq_leq.
  set D := #|[set e in p.1 :&: p.2 | wpred W l e]|.
  set Rf := rYc f p.1 p.2 a gty off false l.
  set Rt := rYc f p.1 p.2 a gty off true l.
  set Sp := \sum_(p0 <- ps) #|[set e in p0.1 :&: p0.2 | wpred W l e]|.
  set Yf := Ycnt a gty false l (off + plen p) (\sum_(p0 <- ps) plen p0).
  set Yt := Ycnt a gty true l (off + plen p) (\sum_(p0 <- ps) plen p0).
  by rewrite -!plusE; lia.
rewrite !YcntE.
have hge := @rCr_card_ge _ f m bipf p.1 p.2 hmp1 hmp2 a rm off
              (@rhnr _ f m p.1 p.2 rm off).
rewrite (@set_rhnr _ f m p.1 p.2 rm off) in hge.
have hRs : #|[set e in rCr f m p.1 p.2 a rm off | @rhnr _ f m p.1 p.2 rm off e]|
           <= #|rCr f m p.1 p.2 a rm off|.
  by apply: subset_leq_card; apply/subsetP => e; rewrite memsetP => /andP[].
have hsz0 := @r_count_size _ f m W bipf p.1 p.2 hmp1 hmp2 a gty rm off hgp.
have hPs := @r_Pk_cuts _ f m bipf p.1 p.2 hmp1 hmp2 a rm off hszp.
have hkp := @r_keep_count _ f m bipf p.1 p.2 hmp1 hmp2 a rm off.
have hnu := @r_nonunan_int _ f m p.1 p.2 a off.
have hrd := @r_rmd_count _ f m p.1 p.2 rm off.
have hspl := @r_cuts_split _ f m p.1 p.2 a off hszp.
rewrite -[size (bl f p.1 p.2) * m.+1]/(plen p) in hPs hnu hrd hspl.
set I := #|p.1 :&: p.2|.
set SI := \sum_(j <- ps) #|j.1 :&: j.2|.
set Zf := rYc f p.1 p.2 a gty off false ord0.
set Zt := rYc f p.1 p.2 a gty off true ord0.
set Zf' := Ycnt a gty false ord0 (off + plen p) (\sum_(j <- ps) plen j).
set Zt' := Ycnt a gty true ord0 (off + plen p) (\sum_(j <- ps) plen j).
set R := #|rCr f m p.1 p.2 a rm off|.
set R' := #|[set e in rCr f m p.1 p.2 a rm off | @rhnr _ f m p.1 p.2 rm off e]|.
set SC := \sum_(j <- rmatch a rm (off + plen p) ps) #|j|.
set cp := cuts_seq (take (plen p) (drop off a)).
set ct := cuts_seq (take (\sum_(j <- ps) plen j) (drop (off + plen p) a)).
set ca := cuts_seq (take (plen p + \sum_(j <- ps) plen j) (drop off a)).
set rp := count (fun q : nat => rm (off + q) && (q %% m.+1 != 0)) (iota 0 (plen p)).
set rt := count (fun q : nat => rm (off + plen p + q) && (q %% m.+1 != 0))
                (iota 0 (\sum_(j <- ps) plen j)).
set ra := count (fun q : nat => rm (off + q) && (q %% m.+1 != 0))
                (iota 0 (plen p + \sum_(j <- ps) plen j)).
set P := #|rPk f m p.1 p.2 a rm off|.
set qb := count (rQbnd f m p.1 p.2 a off) (iota 0 (plen p)).
set qi := count (rQint f m p.1 p.2 a off) (iota 0 (plen p)).
set K := count (fun e : {set G} => @rhnr _ f m p.1 p.2 rm off e
                                  && ~~ rkeepE f m p.1 p.2 a rm off e) (bl f p.1 p.2).
set CS := count (fun e : {set G} => sel f p.1 p.2 m (drop off a) e
                                    && @rhnr _ f m p.1 p.2 rm off e) (bl f p.1 p.2).
set nu := count (fun j : nat => ~~ runan m a off j) (iota 0 (size (bl f p.1 p.2))).
set rd := count [eta rrmdc m rm off] (iota 0 (size (bl f p.1 p.2))).
have hge' : I + CS <= R' + P + K by exact: hge.
have hRs' : R' <= R by exact: hRs.
have hsz0' : Zf + Zt <= CS by exact: hsz0.
have hPs' : P <= qb + cp by exact: hPs.
have hspl' : qb + qi = cp by exact: hspl.
have hkp' : K <= nu + rd by exact: hkp.
have hnu' : nu <= qi by exact: hnu.
have hrd' : rd <= rp by exact: hrd.
have hs4' : SI + Zf' + Zt' <= SC + (2 * ct + rt) by exact: hs4.
have hcut' : cp + ct <= ca by exact: hcut.
have hrm' : ra = rp + rt by exact: hrm.
move/leP: hge' => hge'; move/leP: hsz0' => hsz0'; move/leP: hPs' => hPs';
  move/leP: hkp' => hkp'; move/leP: hnu' => hnu'; move/leP: hrd' => hrd';
  move/leP: hs4' => hs4'; move/leP: hcut' => hcut'; move/leP: hRs' => hRs';
  apply/leP.
rewrite -!plusE -!multE in hge' hsz0' hPs' hkp' hnu' hrd' hs4' hcut' hrm' hspl'
  hRs' *.
lia.
Qed.

(** *** instantiating [gok] and the type counts on the concatenation *)

Lemma gok_gtys (rm : pred nat) (gty : nat -> TY) (ps : seq (MM * MM)) (r0 : seq TY) :
  (forall q, q < size (r0 ++ gtys ps) ->
     gty q = (if rm q then nul else nth nul (r0 ++ gtys ps) q)) ->
  gok gty rm (size r0) ps.
Proof.
elim: ps r0 => [|p ps IH] r0 //= hg; split.
  move=> q hq.
  have hlt : size r0 + q < size (r0 ++ (creal f p.1 p.2 W ++ gtys ps)).
    rewrite size_cat size_cat size_creal ltn_add2l.
    by apply: leq_trans hq _; exact: leq_addr.
  rewrite (hg _ hlt) nth_cat ltnNge leq_addr /= addKn nth_cat size_creal hq.
  by rewrite nth_creal.
have -> : size r0 + plen p = size (r0 ++ creal f p.1 p.2 W).
  by rewrite size_cat size_creal.
apply: IH => q hq.
by rewrite -catA; apply: hg; move: hq; rewrite -catA.
Qed.

Lemma count_gtys (k : TY) (ps : seq (MM * MM)) :
  count_mem k (gtys ps) = \sum_(p <- ps) count_mem k (creal f p.1 p.2 W).
Proof.
by elim: ps => [|p ps IH]; [rewrite big_nil | rewrite /= count_cat IH big_cons].
Qed.

(** In [gtys ps] a *size* type [tix s ord0] can only sit at the head bead of a
    group: each [plen p] is a multiple of [m.+1], and inside a group the bead at
    offset [l] carries the statistic [inord l]. *)
Lemma gtys_class (ps : seq (MM * MM)) (q : nat) (s : bool) :
  q %% m.+1 != 0 -> nth nul (gtys ps) q != tix s ord0.
Proof.
elim: ps q => [|p ps IH] q hq; first by rewrite nth_nil eq_sym tix_null.
rewrite /= nth_cat size_creal.
case: ltnP => hlt; last first.
  apply: IH; move: hq.
  by rewrite -{1}(subnKC hlt) modnMDl.
rewrite nth_creal // /beadty.
case: ifP => hw; last by rewrite eq_sym tix_null.
rewrite tixE; apply/negP => /andP[_ /eqP hl].
have := congr1 (@nat_of_ord m.+1) hl.
by rewrite inordK ?ltn_pmod // => h0; rewrite h0 eqxx in hq.
Qed.

Lemma card_splitW (A B : {set {set G}}) :
  matching A -> matching B -> forall P : pred {set G},
  #|[set e in A | P e]| + #|[set e in B | P e]|
  = 2 * #|[set e in A :&: B | P e]| + count P (bl f A B).
Proof.
move=> mA mB P.
exact: (@card_split _ f A B m W bipf mA mB (nseq (size (cs f A B W)) ord0)
                    (size_nseq _ _) P).
Qed.

(** *** one round *)

Theorem round_exists (ps : seq (MM * MM)) :
  (forall p, p \in ps -> matching p.1) -> (forall p, p \in ps -> matching p.2) ->
  exists cs : seq MM,
    [/\ size cs = size ps,
        (forall C, C \in cs -> matching C),
        (forall l : 'I_m.+1,
           2 * \sum_(C <- cs) #|[set e in C | wpred W l e]|
           <= \sum_(p <- ps) (#|[set e in p.1 | wpred W l e]|
                              + #|[set e in p.2 | wpred W l e]|)) &
        \sum_(p <- ps) (#|p.1| + #|p.2|) <= 2 * \sum_(C <- cs) #|C| + (12 * m + 14)].
Proof.
move=> hmA hmB.
pose raw := gtys ps.
pose CS := csq raw.
have [a [hsza hcuts hshare]] := splitting_necklace_seq (ltn0Sn 1) (fun k => csq_even raw k).
have hszraw : size raw = \sum_(p <- ps) plen p by exact: size_gtys.
have hsz1 : 0 + \sum_(p <- ps) plen p <= size a.
  by rewrite add0n -hszraw hsza; exact: size_csq.
have hgok : gok (nth nul CS) (rmvp raw) 0 ps.
  have hh := @gok_gtys (rmvp raw) (nth nul CS) ps [::].
  rewrite /= in hh.
  by apply: hh => q hq; rewrite nth_csq.
have [h1 h2 h3 h4] := round_ind hmA hmB hsz1 hgok.
have hpad : forall i, nth nul CS (size raw + i) = nul.
  move=> i; rewrite /CS /csq nth_cat size_retys ltnNge leq_addr /= addKn nth_nseq.
  by case: ifP.
have hszCS : size CS = size raw + (odd (count_mem nul (retys raw)) : nat).
  by rewrite /CS /csq size_cat size_retys size_nseq.
have hYc : forall (s : bool) (l : 'I_m.+1),
    Ycnt a (nth nul CS) s l 0 (\sum_(p <- ps) plen p) = count_mem (tix s l) CS %/ 2.
  move=> s l.
  rewrite -(hshare (tix s l) (gd s)) (count_pair_pos nul ord0 (tix s l) (gd s) hsza).
  rewrite -/CS hszCS count_iota_split.
  have hz : count (fun i : nat => (nth nul CS (size raw + i) == tix s l)
                                  && (nth ord0 a (size raw + i) == gd s))
                  (iota 0 (odd (count_mem nul (retys raw)) : nat)) = 0.
    case: (odd (count_mem nul (retys raw))) => //=.
    by rewrite hpad eq_sym tix_null.
  rewrite hz addn0 /Ycnt hszraw.
  by apply: eq_in_count => q _; rewrite !add0n.
have hCSc : forall (s : bool) (l : 'I_m.+1),
    count_mem (tix s l) CS
    = count_mem (tix s l) raw - (odd (count_mem (tix s l) raw) : nat).
  move=> s l; rewrite /CS /csq count_cat count_nseq.
  rewrite /= eq_sym tix_null mul0n addn0 count_retys //.
  by rewrite tix_null.
have hsplitc : forall l : 'I_m.+1,
    \sum_(p <- ps) count (wpred W l) (bl f p.1 p.2)
    = count_mem (tix false l) raw + count_mem (tix true l) raw.
  move=> l; rewrite /raw !count_gtys -big_split /=.
  apply: eq_big_seq => p _.
  rewrite !count_creal_tix.
  rewrite (count_split (bl f p.1 p.2) (wpred W l) (fun e => sd p.2 e == false)).
  by congr (_ + _); apply: eq_count => e /=; case: (sd p.2 e).
exists (rmatch a (rmvp raw) 0 ps); split => //.
  move=> l.
  have hRHS : \sum_(p <- ps) (#|[set e in p.1 | wpred W l e]|
                              + #|[set e in p.2 | wpred W l e]|)
            = 2 * \sum_(p <- ps) #|[set e in p.1 :&: p.2 | wpred W l e]|
              + \sum_(p <- ps) count (wpred W l) (bl f p.1 p.2).
    rewrite big_distrr -big_split /=; apply: eq_big_seq => p hp.
    exact: (card_splitW (hmA p hp) (hmB p hp) (wpred W l)).
  rewrite hRHS hsplitc.
  have h2f : 2 * Ycnt a (nth nul CS) false l 0 (\sum_(p <- ps) plen p)
             <= count_mem (tix false l) raw.
    rewrite hYc mulnC divnK; last exact: csq_even.
    by rewrite hCSc; exact: leq_subr.
  have h2t : 2 * Ycnt a (nth nul CS) true l 0 (\sum_(p <- ps) plen p)
             <= count_mem (tix true l) raw.
    rewrite hYc mulnC divnK; last exact: csq_even.
    by rewrite hCSc; exact: leq_subr.
  apply: (leq_trans (_ : _ <= 2 * (\sum_(p <- ps) #|[set e in p.1 :&: p.2 | wpred W l e]|
                                   + Ycnt a (nth nul CS) false l 0 (\sum_(p <- ps) plen p)
                                   + Ycnt a (nth nul CS) true l 0 (\sum_(p <- ps) plen p)))).
    by rewrite leq_mul2l; apply/orP; right; exact: h3.
  rewrite !mulnDr addnA.
  by apply: leq_add; [rewrite leq_add2l | ].
have hRHS0 : \sum_(p <- ps) (#|p.1| + #|p.2|)
           = 2 * \sum_(p <- ps) #|p.1 :&: p.2|
             + \sum_(p <- ps) count (wpred W ord0) (bl f p.1 p.2).
  rewrite big_distrr -big_split /=; apply: eq_big_seq => p hp.
  have hh := card_splitW (hmA p hp) (hmB p hp) (wpred W ord0).
  by rewrite !set_wpred0 in hh.
rewrite hRHS0 hsplitc.
have hcf : forall s : bool,
    count_mem (tix s ord0) raw
    <= 2 * Ycnt a (nth nul CS) s ord0 0 (\sum_(p <- ps) plen p) + 1.
  move=> s; rewrite hYc mulnC divnK; last exact: csq_even.
  rewrite hCSc; case: (odd (count_mem (tix s ord0) raw)) => /=.
    by case: (count_mem (tix s ord0) raw) => [|n] //=; rewrite subn1 /= addn1.
  by rewrite subn0 addn1.
have herr : 2 * cuts_seq (take (\sum_(p <- ps) plen p) (drop 0 a))
          + count (fun q : nat => rmvp raw (0 + q) && (q %% m.+1 != 0))
                  (iota 0 (\sum_(p <- ps) plen p))
          <= 6 * m + 6.
  have hc1 : cuts_seq (take (\sum_(p <- ps) plen p) (drop 0 a)) <= 2 * m + 3.
    apply: (leq_trans (_ : _ <= cuts_seq a)).
      by rewrite drop0; apply: cuts_seq_subseq; exact: take_subseq.
    apply: (leq_trans hcuts).
    rewrite card_TT muln1.
    by rewrite -!plusE -!multE; apply/leP; lia.
  have hc2 : count (fun q : nat => rmvp raw (0 + q) && (q %% m.+1 != 0))
                   (iota 0 (\sum_(p <- ps) plen p)) <= 2 * m.
    rewrite (@eq_in_count _ _ (fun q => rmvp raw q && (q %% m.+1 != 0)));
      last by move=> q _ /=; rewrite add0n.
    rewrite -hszraw; apply: count_rmvp_class => q s hq.
    exact: gtys_class.
  move/leP: hc1 => hc1; move/leP: hc2 => hc2; apply/leP.
  by rewrite -!plusE -!multE in hc1 hc2 *; lia.
set SI := \sum_(p <- ps) #|p.1 :&: p.2|.
set SC := \sum_(C <- rmatch a (rmvp raw) 0 ps) #|C|.
set Zf := Ycnt a (nth nul CS) false ord0 0 (\sum_(p <- ps) plen p).
set Zt := Ycnt a (nth nul CS) true ord0 0 (\sum_(p <- ps) plen p).
set cf := count_mem (tix false ord0) raw.
set ct := count_mem (tix true ord0) raw.
set E := 2 * cuts_seq (take (\sum_(p <- ps) plen p) (drop 0 a))
       + count (fun q : nat => rmvp raw (0 + q) && (q %% m.+1 != 0))
               (iota 0 (\sum_(p <- ps) plen p)).
have h4' : SI + Zf + Zt <= SC + E by exact: h4.
have hcf' : cf <= 2 * Zf + 1 by exact: (hcf false).
have hct' : ct <= 2 * Zt + 1 by exact: (hcf true).
have herr' : E <= 6 * m + 6 by exact: herr.
move/leP: h4' => h4'; move/leP: hcf' => hcf'; move/leP: hct' => hct';
  move/leP: herr' => herr'; apply/leP.
rewrite -!plusE -!multE in h4' hcf' hct' herr' *.
lia.
Qed.

(** *** the rounds *)

Fixpoint pairup (s : seq MM) : seq (MM * MM) :=
  if s is x :: y :: s' then (x, y) :: pairup s' else [::].

Lemma size_pairup (n : nat) (s : seq MM) : size s = n.*2 -> size (pairup s) = n.
Proof.
elim: n s => [|n IH] s hs.
  by move/eqP: hs; rewrite size_eq0 => /eqP ->.
case: s hs => [|x [|y s']]; rewrite ?doubleS //= => -[] hs.
by rewrite (IH _ hs).
Qed.

Lemma pairup_sum (g : MM -> nat) (n : nat) (s : seq MM) : size s = n.*2 ->
  \sum_(p <- pairup s) (g p.1 + g p.2) = \sum_(M <- s) g M.
Proof.
elim: n s => [|n IH] s hs.
  by move/eqP: hs; rewrite size_eq0 => /eqP ->; rewrite !big_nil.
case: s hs => [|x [|y s']]; rewrite ?doubleS //= => -[] hs.
by rewrite !big_cons (IH _ hs) addnA.
Qed.

Lemma pairup_mem (n : nat) (s : seq MM) (p : MM * MM) :
  size s = n.*2 -> p \in pairup s -> (p.1 \in s) && (p.2 \in s).
Proof.
elim: n s => [|n IH] s hs.
  by move/eqP: hs; rewrite size_eq0 => /eqP ->.
case: s hs => [|x [|y s']]; rewrite ?doubleS //= => -[] hs.
rewrite in_cons => /orP[/eqP ->|hp].
  by rewrite /= !in_cons !eqxx orbT.
have /andP[h1 h2] := IH s' hs hp.
by rewrite !in_cons h1 h2 !orbT.
Qed.

Theorem rounds_exists (L : nat) (s : seq MM) :
  size s = 2 ^ L -> (forall M, M \in s -> matching M) ->
  exists C, [/\ matching C,
      \sum_(M <- s) #|M| <= 2 ^ L * #|C| + (2 ^ L - 1) * (12 * m + 14) &
      forall l : 'I_m.+1,
        2 ^ L * #|[set e in C | wpred W l e]|
        <= \sum_(M <- s) #|[set e in M | wpred W l e]|].
Proof.
elim: L s => [|L IH] s hs hm.
  move: hs; rewrite expn0 => hs.
  case: s hs hm => [|x [|y s']] //= _ hm.
  exists x; split; first by apply: hm; rewrite in_cons eqxx.
    by rewrite big_cons big_nil mul1n subnn mul0n !addn0.
  by move=> l; rewrite mul1n big_cons big_nil addn0.
have hsz2 : size s = (2 ^ L).*2 by rewrite hs expnS mul2n.
have hmp1 : forall p, p \in pairup s -> matching p.1.
  by move=> p hp; apply: hm; case/andP: (pairup_mem hsz2 hp).
have hmp2 : forall p, p \in pairup s -> matching p.2.
  by move=> p hp; apply: hm; case/andP: (pairup_mem hsz2 hp).
have [cs [hc1 hc2 hc3 hc4]] := round_exists hmp1 hmp2.
have hcs : size cs = 2 ^ L by rewrite hc1 (size_pairup hsz2).
have [C [hC1 hC2 hC3]] := IH cs hcs hc2.
exists C; split => //.
  apply: (leq_trans (_ : _ <= 2 * \sum_(C0 <- cs) #|C0| + (12 * m + 14))).
    by rewrite -(pairup_sum (fun M => #|M|) hsz2).
  have hpos : 1 <= 2 ^ L by rewrite expn_gt0.
  set E := 2 ^ L.
  set K := 12 * m + 14.
  set X := #|C|.
  set SC := \sum_(C0 <- cs) #|C0|.
  have hC2' : SC <= E * X + (E - 1) * K by exact: hC2.
  have hpos' : 1 <= E by exact: hpos.
  rewrite expnS -/E.
  move/leP: hC2' => hC2'; move/leP: hpos' => hpos'; apply/leP.
  rewrite -!plusE -!multE -!minusE in hC2' hpos' *.
  nia.
move=> l.
apply: (leq_trans (_ : _ <= 2 * \sum_(C0 <- cs) #|[set e in C0 | wpred W l e]|)).
  by rewrite expnS -mulnA leq_mul2l hC3 orbT.
by rewrite -(pairup_sum (fun M => #|[set e in M | wpred W l e]|) hsz2).
Qed.

End Round.

(** ** Assembly: the colour classes as the leaves of the mixing tree *)

Lemma matching0 (G : sgraph) : matching (set0 : {set {set G}}).
Proof. by split => [e|e1 e2]; rewrite ?in_set0. Qed.

Lemma big_nseq_sum (T : Type) (q : nat) (u : T) (F : T -> nat) :
  \sum_(x <- nseq q u) F x = q * F u.
Proof. by elim: q => [|q IH]; rewrite ?big_nil // /= big_cons IH mulSn. Qed.

Lemma size_flatten_nseq (T : Type) (q : nat) (u : seq T) :
  size (flatten (nseq q u)) = q * size u.
Proof. by elim: q => [|q IH] //=; rewrite size_cat IH mulSn. Qed.

Theorem approx_fair_rounds (G : sgraph) (f : G -> bool) (m : nat)
    (E : 'I_m -> {set {set G}}) :
  (forall x y : G, x -- y -> f x != f y) ->
  (forall i : 'I_m, E i \subset E(G)) ->
  forall D : nat, 0 < D ->
  forall col : {set G} -> nat,
  (forall e : {set G}, e \in E(G) -> col e < D) ->
  (forall j : nat, matching [set e in E(G) | col e == j]) ->
  exists C : {set {set G}},
    [/\ matching C,
        #|E(G)| %/ D <= #|C| + (12 * m + 14) &
        forall i : 'I_m, #|C :&: E i| <= ceil_div #|E i| D].
Proof.
move=> bipf subE D D_gt0 col col_lt col_match.
pose K := 12 * m + 14.
pose ee := #|E(G)|.
pose L := D * (ee + K + 1).
pose P := 2 ^ L.
pose q := P %/ D.
pose lv := flatten (nseq q [seq cls col j | j <- enum 'I_D]) ++ nseq (P - q * D) set0.
have hqD : q * D <= P by rewrite /q leq_divM.
have hsize : size lv = P.
  rewrite /lv size_cat size_flatten_nseq size_map size_enum_ord size_nseq.
  by rewrite subnKC.
have hsubl : forall M, M \in lv -> M \subset E(G).
  move=> M; rewrite /lv mem_cat => /orP[].
    move=> /flattenP[u hu hM].
    move: hu; rewrite mem_nseq => /andP[_ /eqP hu].
    by move: hM; rewrite hu => /mapP[j _ ->]; exact: cls_sub.
  by rewrite mem_nseq => /andP[_ /eqP ->]; exact: sub0set.
have hmatch : forall M, M \in lv -> matching M.
  move=> M; rewrite /lv mem_cat => /orP[].
    move=> /flattenP[u hu hM].
    move: hu; rewrite mem_nseq => /andP[_ /eqP hu].
    by move: hM; rewrite hu => /mapP[j _ ->]; exact: (cls_matching col_match).
  by rewrite mem_nseq => /andP[_ /eqP ->]; exact: matching0.
have hsum : forall X : {set {set G}}, X \subset E(G) ->
    \sum_(M <- lv) #|M :&: X| = q * #|X|.
  move=> X hX.
  rewrite /lv big_cat /= big_flatten /= big_nseq_sum big_nseq_sum.
  have -> : #|(set0 : {set {set G}}) :&: X| = 0 by rewrite set0I cards0.
  rewrite muln0 addn0 big_map -(cls_partition col_lt hX).
  congr (q * _); rewrite big_enum; apply: eq_bigr => j _.
  by rewrite setIC.
have [C [hC1 hC2 hC3]] := rounds_exists E bipf hsize hmatch.
rewrite -/P -/K in hC2.
have hCsz : #|C| <= ee.
  case: hC1 => hsub _; apply: subset_leq_card; apply/subsetP => e he.
  exact: hsub.
have hPL : L < P by rewrite /P; exact: ltn_expl.
have hq1 : ee + K + 1 <= q.
  rewrite /q -(mulKn (ee + K + 1) D_gt0).
  by apply: leq_div2r; rewrite -/L; exact: ltnW.
have hq : ee + K < q by rewrite -addn1.
have hq0 : 0 < q by apply: leq_trans hq.
have hPub : P < (q + 1) * D.
  rewrite mulnDl mul1n {1}(divn_eq P D) -/q ltn_add2l.
  exact: ltn_pmod.
exists C; split => //.
  have hszsum : \sum_(M <- lv) #|M| = q * ee.
    rewrite -(hsum E(G) (subxx _)); apply: eq_big_seq => M hM.
    by rewrite (setIidPl (hsubl M hM)).
  rewrite hszsum in hC2.
  have hkey : q * (ee %/ D) <= (q + 1) * (#|C| + K).
    have h1 : q * (ee %/ D) * D <= q * ee.
      by rewrite -mulnA leq_mul2l; apply/orP; right; exact: leq_divM.
    have h2 : q * ee <= P * (#|C| + K).
      apply: (leq_trans hC2); rewrite mulnDr leq_add2l.
      by rewrite leq_mul2r; apply/orP; right; exact: leq_subr.
    have h3 : P * (#|C| + K) <= (q + 1) * D * (#|C| + K).
      by rewrite leq_mul2r; apply/orP; right; exact: ltnW.
    have h4 : q * (ee %/ D) * D <= (q + 1) * D * (#|C| + K).
      by apply: leq_trans h3; apply: leq_trans h2.
    rewrite -(leq_pmul2r D_gt0); apply: leq_trans h4 _.
    by rewrite -!mulnA [D * _]mulnC !mulnA.
  rewrite leqNgt; apply/negP => hgt.
  move: hkey; rewrite leqNgt => /negP; apply.
  have hge : #|C| + K + 1 <= ee %/ D by rewrite addn1.
  have hXq : #|C| + K < q by apply: leq_ltn_trans hq; rewrite leq_add2r.
  rewrite mulnDl mul1n.
  apply: (@leq_trans (q * (#|C| + K) + q)); last first.
    by rewrite -[q in _ + q]muln1 -mulnDr leq_mul2l hge orbT.
  by rewrite ltn_add2l.
move=> i.
have hWset : forall X : {set {set G}},
    [set e in X | wpred E (lift ord0 i) e] = X :&: E i.
  by move=> X; apply/setP => e; rewrite !inE /wpred liftK.
have := hC3 (lift ord0 i).
rewrite hWset.
have -> : \sum_(M <- lv) #|[set e in M | wpred E (lift ord0 i) e]|
        = \sum_(M <- lv) #|M :&: E i|.
  by apply: eq_big_seq => M _; rewrite hWset.
rewrite (hsum (E i) (subE i)) => hkey.
have hDx : D * #|C :&: E i| <= #|E i|.
  rewrite -(leq_pmul2l hq0) [q * (D * _)]mulnA.
  apply: (leq_trans (_ : _ <= P * #|C :&: E i|)); last exact: hkey.
  by rewrite leq_mul2r; apply/orP; right.
apply: (leq_trans (_ : _ <= #|E i| %/ D)).
  by rewrite leq_divRL // mulnC.
rewrite /ceil_div; apply: leq_div2r.
by rewrite -addnBA // leq_addr.
Qed.

(** ** The linear-constant fair matching, in the vocabulary of [X15] *)

Theorem x15_rounds_instance (m : nat) (G : sgraph) (E : 'I_m -> {set {set G}}) :
  bipartite G -> 0 < Delta G -> x15_edge_family E ->
  exists S : {set {set G}},
    x15_matching S /\
    (#|sg_edge_set G| %/ Delta G <= #|S| + (12 * m + 14))%N /\
    forall i : 'I_m, #|S :&: E i| <= ceil_div #|E i| (Delta G).
Proof.
move=> [f fP] dpos famE.
have D_deg (v : G) : #|N(v)| <= Delta G by exact: leq_bigmax.
have [col [col_lt col_match]] := line_colouring_E fP D_deg.
have subE (i : 'I_m) : E i \subset E(G).
  exact: famE i.
have [C [mC hsz hcl]] := approx_fair_rounds fP subE dpos col_lt col_match.
by exists C; split; [exact: matching_x15 | split].
Qed.

Theorem x15_llm3_proof : bipartite_matching_underrepresentation_llm3_statement.
Proof.
move=> m; exists (12 * m + 14); split; first by [].
exact: x15_rounds_instance.
Qed.

Theorem x15_llm2_proof : bipartite_matching_underrepresentation_llm2_statement.
Proof.
move=> m; exists (12 * m + 14); split.
  have h1 : 12 * m + 14 <= 16 * m + 29 by rewrite -!plusE -!multE; apply/leP; lia.
  by apply: leq_trans h1 _; apply: leq_pmull; rewrite expn_gt0 addn1.
move=> G E bipG dpos famE; exact: x15_rounds_instance.
Qed.

Theorem x15_llm_proof : bipartite_matching_underrepresentation_llm_statement.
Proof.
move=> m; exists (12 * m + 14); split.
  have h1 : 12 * m + 14 <= 32 * (m + 1).
    by rewrite mulnDr muln1 -!plusE -!multE; apply/leP; lia.
  apply: leq_trans h1 _; rewrite leq_pmul2l // -{1}(expn1 (m + 1)).
  by apply: leq_pexp2l; rewrite ?addn1.
move=> G E bipG dpos famE; rewrite x15_edge_setE.
exact: x15_rounds_instance.
Qed.

Corollary bipartite_matching_underrepresentation :
  bipartite_matching_underrepresentation_statement.
Proof. by move=> m; have [c [_ hc]] := x15_llm_proof m; exists c. Qed.

Print Assumptions x15_big_matching.
Print Assumptions round_exists.
Print Assumptions rounds_exists.
Print Assumptions approx_fair_rounds.
Print Assumptions x15_rounds_instance.
Print Assumptions x15_llm3_proof.
Print Assumptions x15_llm2_proof.
Print Assumptions x15_llm_proof.
Print Assumptions bipartite_matching_underrepresentation.
