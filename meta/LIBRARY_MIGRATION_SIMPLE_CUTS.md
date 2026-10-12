# Simple cuts and cut lower bounds

This family is based on accepted parent a69e27fedb17b9a509dc794b45f6e2aa5c8f4e9e.

`GTBase.simple_cuts` owns edges meeting both sides of a vertex cut and the exact X47 cut lower bound. Packing's intersection formula and Cycle's count-one formula are proved equal for simple edges. The cardinality is the existing `GTBase.common.cut_size`. No order guard is added: the cut bound is vacuous at orders zero and one and remains distinct from guarded edge-deletion connectivity.

The X47, X48 and X212 Bondy rows keep their complete meanings and guards. New certificates preserve the current raw formulas and compose deeper Originals with the unchanged M1 edge-set, A11 degree and B10 cycle certificates. The copy/list-decomposition representations, repeated-part conventions, cyclic-side premises and all documented defects are preserved. Atlas's complete public boundary requires the separate copy/decomposition family.

The public client tests empty/full cuts, complement, threshold zero, orders zero/one, the failure of deletion connectivity at K1 and the exact K2 cut bound. Three existing proofs in two files use the public API: the grounding empty-cut theorem, Atlas's deletion-to-cut theorem and its minimum-degree lemma. Their complete types are preserved. Atlas's short names are retained; the new module is required with qualified uses to avoid shadowing them.

The registry records18 frozen objects,12 public API theorems and15 compatibility theorems, including the three complete current rows and their complete Original counterparts. Reciprocal notes explain the preserved A11 and B10 snapshots. The cut-size registry's historical reference to a nonexistent Hypergraph X212 helper is corrected to Cycle's actual declaration; no frozen body or mathematical statement changes.

Validation covers the measured31-file reverse closure,16 affected migration families, all559 existing declared types in29 old reverse files, and their implicit argument positions. One Print Implicit display unfolds the new transparent cut alias; an explicit ascription to the former expanded type checks its conversion. Original failed diagnostic attempts and subsequent recovery evidence are retained in coordination. Final source/history/provider checks, prescribed gates and independent compiled review are recorded by path in the acceptance receipt under `coordination/evidence/resume-2026-10-06/`; this record alone does not establish acceptance.
