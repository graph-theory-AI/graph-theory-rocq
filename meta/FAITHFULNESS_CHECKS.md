# Checking faithfulness of the statements

**Formal-resolution update (2026-09-05):** the corpus still records statement
formalization separately from proof status. Complete local proofs and disproofs
are now recorded in [FORMAL_RESOLUTIONS.md](FORMAL_RESOLUTIONS.md) and checked by
`meta/formal_resolutions.py`. An exact, freshly compiled and assumption-free
`(statement, theorem, direction)` entry is accepted without changing the source
status. All other exact-type faithfulness probes remain active. The baseline
statement-only sweep described below is historical.

For a **statement-first** corpus, *faithfulness is the whole game*. Nothing here is proven; every
row is an axiom-free `Definition <name>_statement : Prop`. So the only thing separating "we
formalized 227 OpenProblemGarden conjectures" from "we wrote 227 Props that don't mean what we
think" is whether each `Prop` faithfully encodes its source proposition.

Faithfulness can **never be fully machine-guaranteed** — there is an irreducible gap between an
informal OPG sentence and a formal `Prop`. The goal is therefore to **drive the residual risk
down** with layered, mostly-mechanical checks. The external audit that found the U4 blocker
(`partial_list_coloring_statement` was `done` while the repo *itself proved* `~ …`, sitting in a
green release) is the standing reminder of why this matters.

## The failure modes we are checking against

| # | mode | example |
|---|---|---|
| 1 | **Vacuously true** — axiom-free provable (degenerate/constant witness, empty quantifier domain) | the old abstract complexity model (`alg := exact-answer`, `cost := 0`) |
| 2 | **Refutable** — axiom-free disprovable (a missing guard) | U4 `t = 0` empty-palette corner (fixed) |
| 3 | **Too strong** — encoding ⟹ source, not conversely (a *proof* transfers, a *disproof* does not) | `general_position` in `small_universal` (removed); `realFieldType` vs `rcfType` |
| 4 | **Too weak / proxy** — source ⟹ encoding, not conversely (a *disproof* transfers, a *proof* does not) | reading-2 for χ=∞; `euler_genus` disconnected-understatement |
| 5 | **Wrong object** — a load-bearing definition has an edge-case bug | `list_colourable_on` total-vs-partial; `seg_meet` completeness |

## What is already in place (keep + scale)

- **Gates** (`make gate` / `check_milestone.py`): compiles, axiom-free, `Print Assumptions`
  clean, and exact-type faithfulness probes for the two cheap signatures below. Rules out hidden
  axioms and blatant committed proof/refutation regressions — **not** deeper meaning.
- **Grounding lemmas** (Qed'd, per milestone `grounding_<phase>.v`): the machine-checked faithfulness
  anchors —
  - *inhabitation / non-vacuity*: a real witness exists (`iRay_proper_self_minor`, `is_crossing_genus_inhab`);
  - *guard-has-teeth*: the trivial witness provably **fails** (`identity_not_proper`, `Komega_const_not_unfriendly`, `not_1_colorable`);
  - *primitive-has-content*: (`orient_unit ≠ 0`);
  - *structural laws the notion must satisfy* (`is_crossing_genus_nonincreasing`, `crossing_number0`).
- **Adversarial red-team audits** (multi-agent, per milestone): independent skeptics try to (a) prove
  the statement axiom-free, (b) refute it axiom-free, (c) find a degenerate witness, (d) compare to the
  source — with distinct lenses (oracle-attack / mathematician / Rocq-semantics) and a synthesizer.
  These caught the Track-B vacuity, the crossing-number `euler_genus` proxy, and forced several
  over-claimed `done`s down to `partial`. Recorded in each package's `docs/*_AUDIT_NOTES.md`.
- **Prospective X211 policy**: hard suspicion lint, an independent wave verdict, and named
  grounding certificates are acceptance requirements. The same lint is warning-only on the
  X1-X210 legacy baseline so old risk stays visible without falsifying its historical gate.
- **Foundation fidelity registry**: audited primitives carry FAITHFUL/LIGHTWEIGHT/BROKEN verdicts;
  statement lint follows local helper definitions and flags use of risky primitives.

## Baseline mechanical sweep (current state)

Two blatant modes are cheap to check corpus-wide by static scan of every `theories/**/*.v`:

- **Committed refutations** — any committed *unconditional* `Lemma/Theorem _ : ~ <name>_statement`
  (or `… : <name>_statement -> False`) on a non-`disproved` row (this is exactly the U4 skeleton).
  The *unconditional* qualifier is load-bearing: a **conditional** refutation edge is legitimate and
  must not trip the check — e.g. `clique_cluster.v` proves
  `conjecture_5_10_statement -> ~ question_5_9_statement` (a stated A ⟹ ¬B implication, not a
  standalone disproof of B). The one `disproved` row (Shitov / Hedetniemi) is *also* exempt: there a
  `~ <name>_statement` is the *correct* artifact, not a bug. **Result: 0** across the corpus.
- **Directly-proven undecided conjectures** — any committed `Lemma _ : <name>_statement.` on a row
  whose **manifest `status` is `open` or `partial`** (⇒ the statement is vacuously/trivially true).
  Keyed off `status`, *not* the OPG proposition kind: the corpus has 3 `solved` + 1 `disproved` rows
  where a proof / refutation is *valid* optional `applications/` work (plan §3), so only `open`/`partial`
  rows may not be directly provable. **Result: 0.**

So the two most blatant unfaithfulness signatures are absent today. The remaining risk lives in the
subtler modes (#3/#4/#5), which need the stronger techniques below.

## Techniques, by leverage

### 1. Refutation-scan gate check *(cheap — do first)*
The gate verifies each statement compiles + is axiom-free, but **never checks that
`~ <name>_statement` is not provable** — the precise hole U4 fell through. This is now implemented in
`check_milestone.py`: **fail any `done`/`partial` row (manifest `status` ≠ `disproved`) that has a
committed *unconditional* theorem of type exactly `~ <name>_statement` / `<name>_statement -> False`.**
Auto-catches mode #2 forever.

Implement it as a **declaration scanner + Rocq `Check` probe, not a raw regex.** A regex on
`<name>_statement -> False` / `~ <name>_statement` false-positives on legitimate conditional edges
(`A_statement -> ~ B_statement`), on comments, and on multi-line declarations. Instead: scan
`Theorem/Lemma` headers that mention a row name, then for each candidate emit
`Check (lemma_name : ~ <name>_statement).` and fail **only if Rocq accepts that exact (hypothesis-free)
type** — and skip the `disproved` row. This decides "is this an *unconditional* refutation of the row?"
at the type level, immune to the syntactic false positives. The implemented gate also rejects direct
proofs of manifest `open`/`partial` rows by the same exact-type `Fail Check` mechanism. (The sweep
above was the one-shot form; the baseline is clean, and the invariant is now locked into `make gate`.)

### 2. Settled-case proof applications *(strongest forcing function — follow-up issue #4)*
For every row whose manifest `status` is **solved** or **disproved** (`status` field; free-text
rationale in `status_semantics`), actually **prove `<name>_statement`** (solved-true) or
**`~ <name>_statement`** (disproved) in Rocq. A faithful encoding of a *decided* conjecture must be
provable/refutable with the right polarity; if it is not, the encoding is wrong. This forces the
correct **truth value** on every decided case, and is the strongest truth-value-forcing check —
catching many instances of modes #1–#5. (It does not by itself prove semantic *equivalence*: a
wrong/proxy encoding that happens to share the row's truth value would still pass, so pair it with #3.)
Almost none of this exists yet (corpus is statement-only) — the biggest untapped signal.

### 3. Independent equivalent re-encoding + `<->` proof
For the load-bearing / complex statements (the infinite-minor relation, combinatorial ends, the genus
crossing number, the `orient`/`seg_meet` geometry), write a **second, structurally different**
encoding and prove `stmt₁ <-> stmt₂` (Qed). Agreement between two independent formalizations is strong
evidence: a bug in either almost always breaks the equivalence. Best ROI on the definitions whose
faithfulness is a documented judgement call.

### 4. Mutation testing *(validates the checks themselves)*
Systematically mutate each statement — drop a guard, weaken `<`→`≤`, flip `exists`/`forall`, empty a
hypothesis — and confirm that **some** check catches it (grounding fails to compile, or the statement
becomes axiom-free provable/refutable, or an audit flags it). A mutation that survives every check is a
hole in that row's faithfulness net. This is how one would have *predicted* the U4 gap.

Standing seed harness: `meta/faithfulness_mutation.py` (also exposed as `make mutation`) runs isolated
temporary-workspace mutants, then requires `check_milestone.py` to reject each mutant for the expected
signature. The current suite covers both exact-type gate failures and semantic drift in load-bearing
definitions:

- U4 open row mutated to `True` plus a direct proof (`direct-proof-undecided`);
- U4 open row mutated to `False` plus an unconditional refutation (`unconditional-refutation`);
- `list_colourable_on` changed back to total colouring instead of partial-on-`W`;
- `girth_geq` with the genuine-cycle guard `2 < size c` removed;
- `wagner_planar` weakened to `True`;
- `has_girth` weakened by dropping the witnessed cycle of length `g`;
- `strongly_colorable` weakened from "all partitions" to "some partition".
- X138's class-uniform clustering constant moved inside `forall G`;
- X125's ratio-to-one `fg_whp` replaced by a fixed 9/10 event threshold.

Current baseline: **9/9 mutants killed**. This is now a standing mutation smoke test for the checks
themselves. It is not an exhaustive mutation campaign; add a targeted mutant whenever a new
load-bearing definition, guard, inequality, or quantifier choice becomes part of a faithfulness claim.

### 5. Blind readback / the `audit_page` (correspondence) leg
The five-leg model reserves a 5th leg (`audit_page` / correspondence), mostly `todo` today. Fill it: an
agent reads **only the Rocq `Definition`** (blind to the source), reconstructs the conjecture in prose,
and a second agent diffs it against the OPG statement. Divergence flags modes #3/#4/#5 — the systematic
version of "does it say what the paper says."

Pilot run: `meta/FAITHFULNESS_READBACK_REVIEW_2026-07-07.md` records a targeted readback/review over
high-risk load-bearing definitions. It repaired three local statement bugs and triggered a downgrade
of the four D3cr crossing-number rows to `partial`; a drawing/rotation layer is still needed to move
them back to `done`.

### 6. External expert / peer review *(highest signal-per-effort)*
The audit that found U4 was exactly this and it beat the internal audits. Recurring domain-expert
review of the statements is the most cost-effective single technique; schedule it.

## Recommended order

1. **#1 refutation/direct-proof exact-type gate check** — now in `check_milestone.py`; keep it green
   as pure regression protection.
2. **#2 settled-case proofs** — the deepest track; maps onto follow-up issue #4. Forces the right truth
   value on every decided row.
3. **#3 equivalent re-encodings** + keep extending **#4 mutation testing** on the load-bearing
   definitions (minor relation, ends, crossing number, geometry) — where modes #3/#4/#5 are most likely.
4. **#5 readback leg** + **#6 recurring external review** — the systematic and human layers.

## What faithfulness checking can and cannot deliver

- **Can** rule out (mechanically): hidden axioms, committed refutations, vacuous proofs of open rows,
  quantifier/guard mutations that flip provability, disagreement between two independent encodings, and
  wrong truth values on decided cases.
- **Cannot** rule out (fully): a subtle proxy that is genuinely equivalent on all *reachable* witnesses
  but diverges on an object nobody constructed — i.e. the last mile between an informal sentence and a
  formal `Prop`. That gap is narrowed by the layers above and by honest `partial` labelling of every
  known proxy (see `CORPUS_STATUS.md`), never fully closed. Report proxies; do not hide them.
