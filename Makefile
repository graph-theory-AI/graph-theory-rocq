# graph-theory-rocq root build. Each package has a _CoqProject; we generate its Makefile.coq
# and build, in dependency order (base first; area packages depend on base).
PACKAGES := base classical-lemmas chromatic-theory hamiltonicity-theory homomorphism-theory cycle-theory minor-theory packing-theory reconstruction-theory hypergraph-theory topological-graph-theory graph-theory-misc spectral-graph-theory extremal-graph-theory infinite-graph-theory
LANDED := U1 chromatic-theory U2 hamiltonicity-theory U3 homomorphism-theory U4 chromatic-theory U5 chromatic-theory U6 cycle-theory U7 minor-theory U8 chromatic-theory U9 packing-theory U10 cycle-theory D1 cycle-theory D7 graph-theory-misc D5 spectral-graph-theory D2chr extremal-graph-theory D2ram extremal-graph-theory D2tur extremal-graph-theory D2pr extremal-graph-theory D2str extremal-graph-theory D3cr topological-graph-theory D3geo topological-graph-theory D3xseq topological-graph-theory D4doa infinite-graph-theory D4inf1 infinite-graph-theory D4inf2 infinite-graph-theory D4inf3 infinite-graph-theory D4inf4 infinite-graph-theory D4inf5 infinite-graph-theory D6emb topological-graph-theory U11 reconstruction-theory U12 hypergraph-theory U13 topological-graph-theory U13 packing-theory U13 graph-theory-misc P9 digraph-theory X1 digraph-theory X2 digraph-theory X3 chromatic-theory X4 extremal-graph-theory X5 minor-theory X5 cycle-theory X5 packing-theory X5 hamiltonicity-theory X6 hypergraph-theory X6 spectral-graph-theory X6 topological-graph-theory X7 chromatic-theory X8 minor-theory X9 cycle-theory X10 cycle-theory X11 minor-theory X12 chromatic-theory X13 extremal-graph-theory X14 graph-theory-misc X15 packing-theory X16 digraph-theory X17 digraph-theory X18 packing-theory X19 digraph-theory X20 graph-theory-misc X21 reconstruction-theory X22 homomorphism-theory X23 topological-graph-theory X24 cycle-theory X25 packing-theory X26 packing-theory X27 minor-theory X28 chromatic-theory X29 graph-theory-misc X30 extremal-graph-theory X31 chromatic-theory X32 chromatic-theory X33 chromatic-theory X34 chromatic-theory X35 chromatic-theory X36 extremal-graph-theory X37 graph-theory-misc X38 graph-theory-misc X39 graph-theory-misc X40 graph-theory-misc X41 graph-theory-misc X42 minor-theory X43 chromatic-theory X44 digraph-theory X45 digraph-theory X46 digraph-theory X47 packing-theory X48 packing-theory X49 extremal-graph-theory X50 chromatic-theory X51 digraph-theory X52 digraph-theory X53 digraph-theory X54 digraph-theory X55 graph-theory-misc X56 extremal-graph-theory X57 extremal-graph-theory X58 extremal-graph-theory X59 extremal-graph-theory X60 extremal-graph-theory X61 extremal-graph-theory X62 graph-theory-misc X63 chromatic-theory X64 chromatic-theory X65 chromatic-theory X66 chromatic-theory X67 minor-theory X68 chromatic-theory X69 chromatic-theory X70 chromatic-theory X71 digraph-theory X72 hypergraph-theory X73 hypergraph-theory X74 graph-theory-misc X75 chromatic-theory X76 extremal-graph-theory X77 graph-theory-misc X78 extremal-graph-theory X79 digraph-theory X80 graph-theory-misc X81 chromatic-theory X82 graph-theory-misc X83 chromatic-theory X84 extremal-graph-theory X85 extremal-graph-theory X86 digraph-theory X87 graph-theory-misc X88 extremal-graph-theory X89 graph-theory-misc X90 digraph-theory X91 graph-theory-misc X92 digraph-theory X93 digraph-theory X94 graph-theory-misc X95 minor-theory X96 extremal-graph-theory X97 extremal-graph-theory X98 extremal-graph-theory X99 graph-theory-misc X100 chromatic-theory X101 graph-theory-misc X102 graph-theory-misc X103 topological-graph-theory X104 hypergraph-theory X105 extremal-graph-theory X106 extremal-graph-theory X107 digraph-theory X108 hypergraph-theory X109 chromatic-theory X110 graph-theory-misc XE1 chromatic-theory XE2 chromatic-theory XE1 cycle-theory XE2 cycle-theory XE1 graph-theory-misc XE2 graph-theory-misc XE1 hypergraph-theory XE2 hypergraph-theory XE1 packing-theory XE2 digraph-theory XE1 extremal-graph-theory XE2 extremal-graph-theory X111 packing-theory X112 chromatic-theory X113 graph-theory-misc X114 graph-theory-misc X115 extremal-graph-theory X116 graph-theory-misc X117 hypergraph-theory X118 extremal-graph-theory X119 hypergraph-theory X120 extremal-graph-theory X121 minor-theory X122 digraph-theory X123 digraph-theory X124 chromatic-theory X125 extremal-graph-theory X126 chromatic-theory X127 minor-theory X128 graph-theory-misc X129 chromatic-theory X130 chromatic-theory X131 chromatic-theory X132 chromatic-theory X133 minor-theory X134 spectral-graph-theory X135 homomorphism-theory X136 digraph-theory X137 hypergraph-theory X138 topological-graph-theory X139 graph-theory-misc X140 topological-graph-theory X141 graph-theory-misc X142 chromatic-theory X143 extremal-graph-theory X144 graph-theory-misc X145 graph-theory-misc X146 graph-theory-misc X147 minor-theory X148 hypergraph-theory X149 chromatic-theory X150 chromatic-theory X151 chromatic-theory X152 chromatic-theory X153 chromatic-theory X154 chromatic-theory X155 packing-theory X156 graph-theory-misc X157 chromatic-theory X158 topological-graph-theory X159 chromatic-theory X160 chromatic-theory X161 chromatic-theory X162 chromatic-theory X163 graph-theory-misc X164 chromatic-theory X165 graph-theory-misc X166 digraph-theory X167 graph-theory-misc X168 graph-theory-misc X169 graph-theory-misc X170 chromatic-theory X171 graph-theory-misc X172 graph-theory-misc X173 chromatic-theory X174 minor-theory X175 minor-theory X176 topological-graph-theory X177 chromatic-theory X178 packing-theory X179 digraph-theory X180 extremal-graph-theory X181 chromatic-theory X182 graph-theory-misc X183 chromatic-theory X184 cycle-theory X185 chromatic-theory X186 chromatic-theory X187 chromatic-theory X188 chromatic-theory X189 chromatic-theory X190 minor-theory X191 extremal-graph-theory X192 chromatic-theory X193 digraph-theory X194 chromatic-theory X195 extremal-graph-theory X196 extremal-graph-theory X197 graph-theory-misc X198 minor-theory X199 minor-theory X200 minor-theory X201 minor-theory X202 topological-graph-theory X203 chromatic-theory X204 chromatic-theory X205 graph-theory-misc X206 chromatic-theory X207 extremal-graph-theory X208 graph-theory-misc X209 hypergraph-theory X210 chromatic-theory X211 hamiltonicity-theory X212 cycle-theory X213 chromatic-theory X214 minor-theory X214 packing-theory X215 extremal-graph-theory X216 digraph-theory X216 graph-theory-misc X216 infinite-graph-theory X217 graph-theory-misc X217 hypergraph-theory X218 chromatic-theory X219 chromatic-theory X220 minor-theory X221 digraph-theory X223 extremal-graph-theory X225 hypergraph-theory X226 packing-theory X227 graph-theory-misc X227 homomorphism-theory X228 cycle-theory X228 minor-theory X228 topological-graph-theory X228 infinite-graph-theory X229 extremal-graph-theory
.PHONY: all clean gate audit mutation probe resolutions gap-repairs digraph-theory atlas $(PACKAGES)
all: $(PACKAGES)

chromatic-theory hamiltonicity-theory homomorphism-theory cycle-theory minor-theory packing-theory reconstruction-theory hypergraph-theory topological-graph-theory graph-theory-misc spectral-graph-theory extremal-graph-theory infinite-graph-theory: base   # area packages depend on base (G3-core)

hamiltonicity-theory packing-theory: topological-graph-theory   # Wave-1: use the embedding foundation
packing-theory: classical-lemmas   # X15: Alon's splitting necklace theorem
graph-theory-misc: topological-graph-theory minor-theory   # X80/X102 reuse embedding + tree-decomposition foundations

# CI gate (G1 + acceptance): manifest reproduces, edge-graph has no drift, every landed
# milestone passes check_milestone (compiles, axiom-free, Print-Assumptions-clean, legs justified).
gate:
	python3 meta/build_opg_manifest.py
	python3 meta/build_v2_manifest.py --check
	python3 meta/build_corpus_relations.py --check
	$(MAKE) atlas
	python3 meta/build_edge_graph.py --check
	python3 meta/check_edges.py --assumptions --registry
	python3 meta/sync_edge_legs.py --check
	python3 meta/report_corpus_status.py --check --edge-legs
	python3 meta/check_statement_docs.py
	@set -e; set -- $(LANDED); while [ $$# -ge 2 ]; do python3 meta/check_milestone.py $$1 $$2; shift 2; done
	python3 meta/formal_resolutions.py
	python3 meta/check_gap_repairs.py

# Toolchain-free status audit (no Coq build, no external OPG source) — backs the
# "statement-complete" claim in CI. Only VERIFIES the committed manifest/overlay/report/edge-graph
# are mutually consistent (drift + invariants); it does NOT regenerate the manifest, since
# build_opg_manifest.py reads the external OpenProblemGarden clone (data/problems.json) which is
# not in the repo. Manifest regeneration lives in `gate`, run in the full dev environment.
# check_statement_docs.py verifies the doc block (corpus row, site + review links, English
# statement, recalled definitions) that must precede every conjecture statement.
audit:
	python3 meta/formal_resolutions.py --metadata-only
	python3 meta/build_edge_graph.py --check
	python3 meta/check_edges.py --registry
	python3 meta/sync_edge_legs.py --check
	python3 meta/report_corpus_status.py --check --edge-legs
	python3 meta/check_statement_docs.py

mutation:
	python3 meta/test_formal_resolutions.py
	python3 meta/test_statement_docs.py
	python3 meta/test_check_edges.py
	python3 meta/faithfulness_mutation.py --timeout 900

# Active vacuity/refutability probe: try to close each `_statement` and its negation with a
# bounded automation ladder + curated witnesses (meta/probe_hints/). Any statement that is
# settleable is FLAGGED — a faithfully-encoded open conjecture should be settleable by neither.
# Usage: make probe                    (whole v2 conjecture corpus; slow)
#        make probe PROBE_ARGS="--wave X35"   (one wave)
#        python3 meta/vacuity_probe.py --validate   (self-test recall on known-broken + control)
PROBE_ARGS ?= --all

# Source statuses are preserved; local proof status lives in a separate checked registry.
# Select a compatible toolchain explicitly, e.g. ROCQ_OPAM_SWITCH=rocq-tools make resolutions.
resolutions:
	python3 meta/formal_resolutions.py

# Partial proof artifacts have exact checks but grant no source-resolution status.
gap-repairs:
	python3 meta/check_gap_repairs.py

probe:
	python3 meta/vacuity_probe.py $(PROBE_ARGS)

$(PACKAGES):
	cd $@ && rocq makefile -f _CoqProject -o Makefile.coq && $(MAKE) -f Makefile.coq

# `digraph-theory/` stays out of PACKAGES (heaviest proofs in the repo) but must still be
# buildable by name: without an explicit rule, `make digraph-theory` matches the directory,
# reports success and does nothing. Its P9 milestone is gated by `make gate` either way.
digraph-theory: base
	cd $@ && rocq makefile -f _CoqProject -o Makefile.coq && $(MAKE) -f Makefile.coq

# `atlas/` hosts the cross-package implication edges (theorems A -> B whose endpoints live in
# two area packages that cannot import each other). It imports every area package and
# digraph-theory, so it stays out of PACKAGES / `make all` like digraph-theory; `make gate`
# builds it and build_edge_graph.py picks its @EDGE annotations up like any package.
atlas: $(filter-out base classical-lemmas,$(PACKAGES)) digraph-theory
	cd $@ && rocq makefile -f _CoqProject -o Makefile.coq && $(MAKE) -f Makefile.coq

clean:
	@for p in $(PACKAGES) digraph-theory atlas; do (cd $$p && rocq makefile -f _CoqProject -o Makefile.coq >/dev/null 2>&1 && $(MAKE) -f Makefile.coq clean) 2>/dev/null || true; done

# NOTE: `base/` (G3-core) + `chromatic-theory/` (U1) build today; add each area package to
# PACKAGES (with `<pkg>: base`) as its milestone lands. The absorbed `digraph-theory/` (heavy
# proofs) is kept out of the default `all`/`PACKAGES` to keep `make all` light — but its P9
# milestone IS gated: `make gate` runs `check_milestone P9 digraph-theory` (it builds the package
# itself, verifies all 32 formal_names Defined + axiom-free + Print Assumptions clean). The
# already-formalized P9 rows live in sibling conjecture files (classic_core.v/packing.v/sad.v/
# colouring_variants.v/long_dipath.v) which check_milestone now scans + imports.
