# D3: images of supplied hyperedges

D3 is implemented on the fixed D2 pin `aa1f6f38d309d50725f98b5e1b42dff6414af30b`. It is the new
`image-edge` shard.

The canonical is MathComp's `f @: e` (`mathcomp.boot.finset.imset`, HB-locked): the image of a
supplied set under any map between finite types. It has no injectivity, nonempty or no-isolated
guard. X108's `x108_image_edge` and the ordinal-codomain X117/X119 adapters are now aliases of it.
The corpus bounded-existential body equals it by `GTBase.set_images.imset_existsE`, a proved set
equality and not a conversion. MathComp's API is reused, including `card_imset` with its
injectivity premise. The three aliases are the same term, so the vocabulary_hypergraph equalities,
including the equality of Props `x117_monochromatic_copyE`, stay conversions.

Frozen at D2 are 3 sources, 8 chains (same-colour injective copies, two-colour and q-colour
forcing, Ramsey numbers with forcing and minimality) and 3 complete current rows. There are also
2 complete A10+D1+D3 Originals bound at the complete-history source `9e03072`:
- X108: D1's raw uniformity and A10's actual `X108Legacy.d_degenerate`.
- X119: D1's raw uniformity, with no-isolated and the opaque `x119_sqrt_ex` square root unchanged.

That gives 5 whole-statement iffs. The four certified support objects are listed in the historical
role; the four older snapshots stay byte-exact with notes, and reciprocal A10/D1 notes are added.
Copy, forcing and Ramsey ownership is not migrated; statuses, legs and docs are unchanged. The
client is `base/theories/examples/set_images.v`. Regenerate with
`python3 meta/migration_report.py image_edge --write`. Evidence: coordination `evidence/D3-by-lancelot/`.
