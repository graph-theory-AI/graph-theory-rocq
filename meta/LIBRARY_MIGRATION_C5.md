# C5: supplied proper vertex colourings

Eight local helpers in Chromatic, Spectral and Infinite now adapt the single
public predicate `GTBase.colourings.proper_colouring`. It is upstream `coloring`
of the supplied map's `preim_partition` of all vertices. The pointwise reflection
and Boolean equality lemmas establish unconditional correspondence with the old
adjacent-colours-differ bodies. No `hom_s` shortcut, surjectivity, positive palette
size or inhabited graph assumption is used.

The five Prop interfaces remain Prop-valued; the three Boolean interfaces keep
their finite-function carriers. Recolouring walks still test every supplied
state, and D5 coefficients/D4doa counts still enumerate the same labelled finite
functions, including unused labels. Empty graphs and empty palettes retain their
original behaviour. The public client grounds the empty/empty case, K1 with
unused labels, K2 identity and constant maps, and injective relabellings.

The private prerequisite baseline is `a6db537386d7092db506526fbcfd2dbe9760ed5e`,
which combines reviewed C4, A3 `dde0199033f6e3299360ed5ae1a7c1eb7e0cda02`
and B3 `49ddc033ec6be3372ba6813f044fd26922fad16d`. The regeneration spec records
all eight original sources, eight dependent local chains and ten complete row
bodies, with source hashes and explicit substitutions. X64's combined Original
uses A3's pre-M1 frozen bridgeless chain; X83's uses B3's frozen rainbow induced
path. The existing M1/A3/B3 snapshots are unchanged and their remaining live
colouring references are documented in the compact report.

All ten statement texts, documentation blocks, quantifier orders, guards and
manifest states stay unchanged. In particular X162's unrelated defective Kempe
step remains blocked; D5 keeps its existential affirmative reading; D4doa keeps
its documented Cauchy-existence reading over arbitrary real-closed fields. Edge
colourings, hypergraph colourings and other stronger predicates are separate
families. B4's later raw-cycle migration must compose its X3 hole history with
this frozen colouring chain.

`chi_le_palette` retains its exact public type and now uses the shared API.
The existing D5 and D4doa grounding proofs use the public views and retain their
types and exact count values. Aliases remain for their tracked consumers.

Focused validation: the base package/public client and all three certificate
modules compile; D5/D4doa grounding and `chi_le_palette` rebuild. Fresh probes
check ten exact statement iff types, Boolean/count interfaces and 55 named
assumption closures. All 26 frozen-object headers and the changed proof-consumer
headers retain their baseline types; all three imported historical modules are
byte-identical. The source report passes all 236 checks. Broader gate results
are recorded with the pinned commit in the coordination evidence.

Regenerate the compact report with
`python3 meta/migration_report.py proper_colouring --write`; request full details
with `--details PATH`. Kernel, exact-type and dependency evidence is recorded
under `coordination/evidence/C5-proper_colouring/`. Independent review and final
integration gates are coordinator responsibilities, never inferred from this
implementation record.
