# graph-theory-rocq — expansion plan & faithfulness programme

> Written 2026-07-17 from a systematic 5-axis review (shared foundations, area packages, meta
> infrastructure, coverage statistics, defect taxonomy mined from the repo's own audit history).
> Companion documents: `meta/V2_FULL_CORPUS_PLAN.md` (the original v2 programme),
> `meta/BLOCKED_RETARGETING_AUDIT.md` (the 2026-07-17 audit that overturned the bulk-unblocking
> pass and supplies most of the empirical defect data below).

---

## 1. Where the repo stands

**Architecture** — a math-comp-style monorepo: 14 area packages + `base`, each area stating open
conjectures as axiom-free `Definition <name>_statement : Prop` over MathComp 2.5 +
coq-graph-theory 0.9.7 (Rocq 9.1.1, opam switch `digraph`). Two tracked corpora:
the frozen OPG v1 (227 rows, 208 done · 12 partial · 7 blocked) and the growing v2
(1745 rows, 332 done · 10 partial · 36 blocked · 1251 todo as of the 2026-07-18 audits;
live numbers in `meta/CORPUS_STATUS.md`). Tracking is deterministic:
committed overlay JSONs → generator scripts → manifests → `CORPUS_STATUS.md`, gated by
`make audit` (metadata-level, CI-safe) and `make gate` (261 milestone acceptance checks:
compiles, axiom-free, `Print Assumptions` clean, legs justified).

**Scale** — 379 conjecture `.v` files (~674 statements), 8 shared GTBase foundation modules
(~1,036 lines), ~2.5k lines of meta tooling, 57 grounding + 36 implications files, a 46-edge
conjecture-implication graph (3 Qed-verified edges).

**Strengths**
- Uniform, high-quality statement idiom across all waves (GTBase import, `xN_` local vocabulary,
  named `_statement : Prop`, axiom-free, per-row provenance).
- Real, audit-verified foundations where it matters: a genuinely cost-coupled computation model
  (`complexity.v` — output *and* step count from one interpreter, no zero-cost escape), a genuine
  rotation-system surface layer, a genuine `fg_whp` (ratio→1) probability threshold, faithful nat
  asymptotics (`little_o`, `n^{o(1)}` via rational cross-multiplication).
- A working two-tier gate + drift-detection pipeline, and — decisively — an *audit culture* with
  written per-wave faithfulness verdicts (226 `faithfulness_result` fields).

**Weaknesses (each becomes a plan track below)**
1. **Faithfulness is the binding constraint, not compilation.** The audit history shows ~90 defect
   instances in 10 classes; every one compiled axiom-free and passed `make gate`. Escape rates by
   authoring mode: single-author readback ≈ **14%**, bulk retargeting without per-row audit ≈
   **74%**, author + independent adversarial audit + re-verify ≈ **0%** (measured across ~350
   statements). The gates are blind to semantics by design; the human/agent audit layer is the
   real gate and is not yet enforced by tooling.
2. **Validation infrastructure froze at the OPG era.** All 57 grounding and 36 implications files
   attach to U/D milestones; the 227 X/XE-wave files have **zero** grounding lemmas and zero edges.
3. **Foundational gaps block 43 rows** (36 v2 blocked + 7 OPG blocked; 65 counting the 22
   partial legs, which are proxies awaiting the same layers): no
   drawing/crossing layer, no expectation/mixing probability, no sparsity (scol/wcol, shallow
   minors, bounded expansion), no distributed/randomized complexity classes, no merge-width, no
   extension complexity, thin infinite-graph support, no real-valued invariants.
4. **Coverage is lopsided**: chromatic (73 files) and digraph (77) are heavy; reconstruction (4),
   hamiltonicity (4), homomorphism (5), spectral (5) are starved; infinite-graph-theory received
   **no** v2 wave at all.
5. **Remaining infra debt**: changed-path CI now builds Rocq reverse dependencies, checks complete
   `LANDED` coverage, runs mutation/migration controls, and validates the pinned OPG input. A full
   v2 regeneration still needs the separately pinned upstream checkout, and the vacuity probe
   remains dependent on a small curated-hint set.

---

## 2. Expansion programme

### Track A — Statement coverage (the 698 truly-owing rows)

Of the 1251 v2 todo rows, only **698 owe statements** (466 parked by documented disposition,
87 edge-anchor, alias rest): **330 arXiv** (sequential `axv_*` track, next after `axv_1803_10962`),
**133 derived** (attack-engine rows, all `topic=None` — need triage first), **120 erdős**
(post-XE1/XE2 remainder), **115 studies `std_*`** (alphabetical track paused at X150
`gimbel_thomassen`; next: `gishboliner…`, `gowers…`, `grünbaum…`, `graham…`).

- **Cadence** (proven this campaign): batches of ~20, area-grouped author subagents working from a
  written spec, then the mandatory independent audit (§4). Sustained defect-free throughput was
  ~20 rows/session.
- **Recovery-first**: 47 of the 698 owing rows have missing/short/internal-reference source text
  (`recovery: needed`; 102 todo rows carry the flag overall, but 55 of those are parked and owe no
  statement). Build the REC stage (fetch + normalize source statements from the arXiv HTML/upstream
  repo) before those 47 reach their waves; authoring from a bad source is the one defect class no
  audit can fix.
- **Repair backlog (46 rows)**: 36 blocked + 10 partial (v2) from the overturned retargeting +
  audits. Each has a written defect diagnosis in `BLOCKED_RETARGETING_AUDIT.md`; many are fixable
  on *existing* foundations, and the first repair wave is instructive: of the four 2026-07-17
  self-verified repairs, adversarial re-verification (2026-07-18) confirmed **X138**, caught new
  machine-refutable degenerate-parameter holes in **X194/X198** (fixed with `2≤k` / `1≤t` guards),
  and **re-blocked X125** (the `fg_whp` repair introduced a multiplicity-skew collapse; needs a
  canonical *labelled* lift model). Remaining examples: X139 by restoring the scol distance
  constraint; X141 needs a zombie-game primitive. Fold into themed repair waves, one
  foundation-family at a time — and every repair re-enters adversarial verification (3 of 4
  self-verified repairs were still broken).
- **Followup debts** (from `v2_reconciliation.json`): 12 proxy constants (non-faithful existing
  definitions — must stay todo, never marked done), 14 unmatched constants (decide: mint rows or
  retire), 2 rcfType reals rows, 1 OPG duplicate.

### Track B — Foundation investments (ranked by rows-unblocked per unit effort)

| # | Layer | Unblocks / de-risks | Difficulty |
|---|---|---|---|
| B1 | **Sparsity**: shallow minors at depth r, `scol_r`/`wcol_r`, bounded expansion as first-class GTBase primitives | X139, X190, X199 blocked; de-risks X128/X145/X147/X198 which hand-roll these | Medium — all finite combinatorics over sgraph |
| B2 | **Probability, level 2**: expectation over weighted finite spaces, two-sided whp equality, uniformly-random rotation systems (surface × finite_graph), Glauber/Markov-chain ergodicity on finite state graphs | X140, X143, X162 blocked; X181 partial | Medium |
| B3 | **Drawing/crossing layer**: drawings with local rotation + crossing-alternation data, validated against the `xsplit` planarization proxy | 4 OPG partial crossing rows → done; 2 OPG blocked; X202 | High — multi-week; the single largest honesty payoff for OPG |
| B4 | **Computation model, level 2**: NP as a *coupled* verifier class in GTBase (replacing GTMisc's decoupled D7 layer), randomized/distributed (LOCAL) cost classes | X205; retro-hardens X114 and the D7 rows | Medium-high |
| B5 | **Width parameters**: merge-width (Dreier–Toruńczyk), extension complexity of polytopes | X124; X167/X168 | High (paper-local, low row yield — keep blocked unless a wave arrives) |
| B6 | **Infinite-graph layer 2**: ends, rays, automorphism actions; cardinal arithmetic | 2 OPG blocked; opens infinite-graph v2 waves (area currently skipped) | High |
| B7 | **Reals (`rcfType`) re-encodings** | 2 reconciliation rows; future real-valued invariants (fractional, spectral) | Medium |

Rule learned the hard way (74% defect rate): **a foundation must be audited for fidelity before
any row builds on it**, and every new foundation ships with grounding lemmas that machine-check
its non-vacuity (`no_zero_cost_program`-style) — see §4.6.

### Track C — Depth: grounding, edges, correspondence for the X-waves

The v2 corpus is statement-rich and validation-poor (grounding/edges/correspondence/audit legs:
0/1629). Statements alone are cheap to doubt; grounding is what makes the corpus *trustworthy*.

- **C1. Grounding waves for X-files** (highest value): per statement, a `grounding_Xn.v` proving
  (i) hypotheses satisfiable (∃ a graph meeting the antecedent), (ii) conclusion non-trivial
  (∃ a graph failing the conclusion absent the hypothesis), (iii) helper-definition sanity
  (e.g. `x115_odd_induced_cycle` holds exactly on odd induced cycles of small witnesses). Target
  the ~332 done v2 rows in batches; make it a leg-gate for *future* waves (§4.4).
- **C2. Edge-graph expansion**: 46 edges is far below the known implication structure (e.g.
  X71 ⇒ X123 was proved in prose during audit — turn such audit facts into Qed `_implies_`
  theorems). Systematically mine the audits + source papers for implications between formalized
  rows; target ~200 edges with a growing Qed-verified core.
- **C3. Correspondence + audit pages**: per-row documentation linking formal name ↔ source text ↔
  encoding decisions ↔ audit verdict. Much of this content already exists scattered in wave notes;
  a generator can assemble it.
- **C4. Proof campaigns** (long-term): for rows with `status: solved/disproved`, formalize the
  known proof or the refutation certificate; for open rows, prove relative theorems (more Qed
  edges) and small-case instances.

### Track D — Rebalance starved areas

Reconstruction (4 files), hamiltonicity (4), homomorphism (5), spectral (5, which *has* real
spectral foundations lying idle) and infinite (0 X-waves) each get a dedicated themed wave pulled
from the 698 owing rows by topic, rather than letting the alphabetical tracks starve them.
Also: give chromatic-theory (73 files, the largest area, zero area foundations) a
`foundations/` module extracting its recurring local vocabulary (colouring variants,
criticality, recolouring graphs).

### Track E — Infrastructure & CI hardening

1. **CI**: the container job builds changed packages and reverse dependencies, runs milestone
   gates, mutation canaries, migration assumptions checks, and prospective vacuity probes. The OPG
   source checkout is pinned and content-validated; the growing v2 source still requires its
   separately pinned upstream checkout for a full regeneration.
2. **Close the LANDED gap**: assert `Makefile LANDED` ⊇ every wave in `v2_statement_waves.json`
   and every `(phase, repo)` manifest cell (a 20-line check in `report_corpus_status --check`).
3. **Wire `build_v2_manifest --check` into `make audit`** (v2 drift is currently ungated).
4. **Hygiene**: purge committed `.vo`/scratch artifacts (spectral has `scratch_*.vok` etc.);
   gitignore audit.
5. **Edge-graph validation**: re-typecheck verified edges against their annotations instead of
   regex/name matching.

### Track F — Release & community

Tagged releases per milestone-complete state (the `opg-v1.0.1` pattern), opam packaging of `base`
+ mature areas, a generated website from the correspondence/audit legs, and outreach to source
authors for statement readback (the cheapest independent auditors available — see §4.8).

---

## 3. The empirical threat model (why faithfulness needs a programme)

Mined from this repo's own audits (~350 audited statements, ~90 defect instances, 10 classes).
**Every defect compiled axiom-free and passed every mechanical gate.**

| # | Defect class | ≈count | Canonical examples | What caught it |
|---|---|---|---|---|
| 1 | Missing degenerate guards (empty graph, `n≥n₀`, positivity) | 18 | X4-wave (10× `0<#|G|`), X50, X55 | independent readers; `~statement` probes |
| 2 | Vacuous / trivially-satisfiable witness or antecedent | 15 | X89 quartet record, X90 cost, X124 merge-width, X167 xc | machine component-triviality proofs |
| 3 | Wrong object entirely / wrong statement for the row | 13 | X100 (not χ′ₖ, refuted on K₄), X127 (Conj-3 vs DJMNW), X185 | machine refutation; source pull |
| 4 | Missing defining constraint on a quantified object | 8 | X83 (properness), X139 (scol distance), X179 | `~statement` refutation; re-read |
| 5 | Strength mismatch (constant vs function bound; weaker form) | 7 | **X71** (χ⃗-finite vs χ⃗-bounded), X176, X182-risk | **cross-audit against sibling rows** |
| 6 | Discretization defects (`logn` vs `trunc_log`, nat-subtraction truncation) | 7 | X4-wave (4× floor-log2), X174, X210 | 28-reader adversarial audit |
| 7 | Quantifier order (per-instance ∃ vs uniform ∃-before-∀) | 6 | X138/X194 clustering constant; chi-bounded family | reader + machine collapse proof |
| 8 | One-sided/Θ-collapsed rendering of two-sided asymptotics | 5 | X181, X202, X115 (literal vs Θ) | K₆-style machine refutation |
| 9 | Mis-quantified "almost all"/whp (family-∀ collapse) | 4 | **X125** (`∀L ∃good ratio≥9/10` ⇒ "all") | **foundation audit** of the primitive |
| 10 | Faithful-to-refuted source (curation, not encoding) | 5 | X14, X92, X73, X127-final | source re-read during audit |

**Escape rates by process** (the single most important table in this document):

| Authoring process | Defect escape rate |
|---|---|
| Single-author + own readback | ≈ 14% (X10–X110: 16/115 escaped the readback) |
| Bulk mechanical pass, no per-row audit | ≈ **74%** (retargeting: 53/72 not faithful) |
| Author + independent adversarial audit + re-verify-until-dry | ≈ 0% detected residual (X4–XE2: 17/109 caught then fixed; X111–X130: 1/20 caught then fixed) |

---

## 4. Faithfulness programme — defence in depth

Eight layers, ordered from cheapest/earliest to deepest. Layers 1–4 are tooling (automatable);
layers 5–8 are process (enforceable by convention + gate hooks).

### 4.1 Authoring discipline: spec + anti-pattern catalog
Every wave starts from a written author spec (the `AUTHOR_SPEC.md` pattern) which now must embed
the **anti-pattern catalog** distilled from §3 — each entry with its repo-historical example:
- `∃ witness` satisfiable by `0 / ∅ / constant` (X89) → tighten or add a non-triviality clause.
- `∀ G, ∃ c` where the source means `∃ c, ∀ G` (X138) — uniform bounds *always* quantify first.
- `∀ (P : … -> Prop), …` over an unconstrained predicate — refutable by `P := False`-style
  instantiation (pre-fix X125/X128); placeholders must be *concrete* definitions.
- "almost all / whp" must be `fg_whp` (n-indexed, ratio→1), never a fixed-ratio threshold under a
  family quantifier (X125 collapse).
- Constant vs function bound: χ⃗-finite ≠ χ⃗-bounded (X71); check which the source asserts.
- `has_girth` = girth *exactly* g; "girth ≥ g" is `girth_geq` (X129).
- `logn` is the 2-adic valuation, not floor-log2 (`trunc_log`); guard every nat subtraction.
- Two-sided asymptotics need both bounds; `= f(n)^{1+o(1)}` needs the ∀ε ∃n₀ two-sided form.
- Empty/small-graph guards wherever the source implicitly assumes non-degeneracy.
- Complexity claims only on the cost-coupled model (`GTBase.complexity`), never on free
  `cost : _ -> nat` fields.

### 4.2 Static lint (`meta/faithfulness_lint.py` — to build)
A syntactic pass over conjecture files flagging, with a whitelist mechanism:
top-level `forall` over `-> Prop`-typed variables in a `_statement`; `exists f` *after* an outer
`forall G : sgraph`; `fg_event_at_least_ratio` inside a `_statement` (should be `fg_whp`);
`has_girth` in hypothesis position; `logn`; `-` on `nat` without an adjacent guard comment;
`x*_cost`/`cert_size` free function fields. Low precision is fine — the lint routes *suspicion* to
auditors, it does not judge. Wire into `make audit` as a warning tier, `make gate` as a hard tier
for new waves.

### 4.3 Active probes (extend `meta/vacuity_probe.py`)
The probe's measured recall: curated hints 5/5, auto-ladder ≈0 on subtle rows. Therefore:
- **Per-wave hint debt**: every audit that machine-refutes a statement (or proves a component
  trivial) must deposit its probe as a `probe_hints/<name>.v` — the hint corpus is the regression
  suite (stale-FIX-OK semantics already implemented).
- Add **instantiation probes** to the auto layer: try `∅`/`0`/singleton/`K_n (n≤6)` instantiations
  of leading quantifiers and run the tactic ladder on the specialized goal — this mechanizes the
  K₆-style refutations that caught X100/X115.
- Add a **small-model evaluator**: for statements whose predicates are boolean-reflectable,
  brute-force check the claim on all graphs up to 5–6 vertices against known invariant values
  (χ, ω, α, girth computed by the library) — catches wrong-object defects (class 3) cheaply.
- Run the probe on **every new wave** in CI (auto layer) with hints required for any row the
  audit flagged.

### 4.4 Grounding certificates as a statement-leg gate (the biggest single upgrade)
Promote grounding from "optional later leg" to **part of statement acceptance for new waves**:
a wave's `check_milestone` acceptance additionally requires, per statement, a grounding file with:
1. `..._hyp_inhabited` : the hypotheses are satisfiable (Qed, small witness);
2. `..._not_trivially_true` : the conclusion fails for some structure when the load-bearing
   hypothesis is dropped (Qed) — this is exactly the lemma that would have caught the vacuous
   classes 2 and 7 at authoring time;
3. helper-sanity lemmas pinning each `xN_` definition to a textbook characterization on a small
   instance (e.g. `x115_odd_induced_cycle` ↔ the 5-cycle of C₅).
Wave metadata records each obligation as `{theorem, claim, references}`. The claim must be an
explicit `Prop` definition anchored to the row/classified helpers, while the theorem must have
exactly that claim as its type and be closed under `Print Assumptions`; a declaration name alone is
not a certificate.
Cost: ~30–60 lines of Qed per row (measured from the D-milestone grounding files). This converts
the two highest-frequency defect classes from "found by audit" to "impossible to author".

### 4.5 Independent adversarial audit — the mandatory human/agent layer
Codify what the escape-rate table proves: **no statement leg reaches `done` without a
faithfulness verdict from a reader distinct from the author**, recorded in the wave's
`faithfulness_verified_by/result`. Process rules (all already exercised this campaign):
- Reader gets the *source text* and the *unfolded* formal statement; their job list is the §3
  taxonomy, and any suspicion must be resolved by a **machine-checked probe** (refutation or
  collapse proof), not prose.
- **Sibling cross-audit**: audit related rows together (X71 was caught only via X123). The wave
  planner should group same-family rows to one reader.
- **Fix → re-verify until dry**: fixes re-enter audit; two clean consecutive rounds close the wave
  (the X4-wave protocol — its two rounds caught 2 defective first-round fixes).
- **Overturn discipline**: when an audit overturns a prior verdict, `source_verified_by` must be
  superseded (the X71 provenance rule now in the generator).
- **Bulk passes are forbidden**: any change flipping >5 legs in one pass requires the same
  per-row audit before merge — the 2026-07-16 event (74% defect) is the standing counterexample.

### 4.6 Foundation fidelity registry
Every GTBase/area foundation module explicitly enrols each audited primitive and carries its verdict
(FAITHFUL / LIGHTWEIGHT / BROKEN + misuse watch-list), stored as
`meta/foundation_fidelity.json` and printed into `CORPUS_STATUS.md`. Rows inherit trust from the
primitives they use; the lint (§4.2) flags any `_statement` using a LIGHTWEIGHT/BROKEN primitive.
New foundations ship with machine-checked non-vacuity lemmas in-file
(`no_zero_cost_program`-style) before any row may import them. The 2026-07-17 audit's verdicts
seed this registry. Module defaults are shorthand only for the committed `audited_primitives` list;
new declarations remain unaudited until explicitly enrolled.

### 4.7 Dual encodings & mutation testing
- For high-stakes rows (famous conjectures), author **two independent encodings** (different
  reader/author pairs, different primitive choices) and prove `encoding_A <-> encoding_B` (or at
  least one implication) — disagreement is a defect detector with near-perfect precision.
- Extend `meta/faithfulness_mutation.py` beyond its 7 OPG canaries with **v2-wave mutants**: for
  each defect class in §3, keep one deliberately-broken variant (a guard dropped, a quantifier
  swapped, a ratio-for-whp substitution) and assert the check-stack (lint + probe + grounding
  gate) flags it. The mutation suite measures the *recall of the checks themselves* and must grow
  with every new defect class discovered.

### 4.8 External readback
For each formalized named conjecture, generate a one-page correspondence sheet (source text ↔
formal statement ↔ encoding notes) and, where feasible, send it to the conjecture's authors or
post it with the corpus release. Source authors are the highest-precision faithfulness oracles
available; even a low response rate catches wrong-object defects nothing else can.

---

## 5. Sequencing

| Phase | Contents | Exit criterion |
|---|---|---|
| **P0 — stabilize** | ✅ COMPLETE 2026-07-18. Honest reclassification + X131–X210 waves committed (`8800958`); fresh-rows audit done (20 rows: 16 faithful, 2 defects fixed, 1 re-blocked, 1 partial); the 4 self-verified repairs adversarially re-verified (X138 confirmed; X194/X198 guard-fixed; X125 re-blocked). Remaining hygiene: purge scratch artifacts (folded into P1/Track E). | ✅ every done leg has an independent audit verdict |
| **P1 — harden the loop (1–2 weeks)** | **IN PROGRESS 2026-07-18:** first implementation tranche in `meta/P1_HARDENING.md` (prospective X211 policy, lint, small-model probes, grounding contract, seeded registry, changed-wave CI, LANDED/v2 drift assertions, first v2 mutants). Remaining: broaden mutation coverage and exercise the first real X211 grounding wave. | mutation suite green incl. new v2 mutants |
| **P2 — repair + foundations round 1** | Track A repair backlog (44 rows) in foundation-family batches; B1 sparsity + B2 probability-level-2 (unblocks ~8 rows honestly) | v2 blocked count reduced with audit verdicts, not reclassification |
| **P3 — coverage engine** | Resume std/axv/erdős waves at ~20 rows/batch under the hardened loop; REC stage for the 102 recovery rows; themed waves for starved areas (Track D) | +200 done rows, all with grounding certificates |
| **P4 — depth** | C1 grounding backfill for existing X-rows; C2 edge-graph growth (audit-mined implications → Qed edges); B3 drawing/crossing layer | OPG crossing rows honestly done; ≥150 edges |
| **P5 — outward** | Track F: releases, opam, correspondence site, author readback | first external readback round completed |

---

## 6. The one-line summary

The repo's mechanical pipeline is sound and its statement idiom is mature; the entire expansion
risk is *semantic*. Every future increment should ride the loop that measurably produces
zero-escape output — **recovered source → spec'd author → lint → probe → grounding certificate →
independent adversarial audit with machine-checked refutations → re-verify until dry → provenance
recorded** — and never again accept a leg flip that skipped it.
