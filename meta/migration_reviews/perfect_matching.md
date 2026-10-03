# Independent review: perfect matching (C2)

Implementer: lancelot, completed by coordinator helper family_scope during the
worker's quota pause. Reviewer: arthur. Reviewed commit:
`99e3132092cb7020c7d09a41ee629c4af067f127`. Date: 2026-10-02.
Verdict: approved; no semantic finding. Coordinator independently approved the
three final statement equivalence types and proofs at the same commit.

The existing canonical is unchanged: matching plus full vertex coverage. Its
unconditional equivalence with exactly-one incidence preserves all three helper
contracts, including empty graphs, invalid members and odd order. Grounding and
the public-only client cover K0, K2, K3 and a two-edge perfect matching of K4.
The separate U10 multigraph concepts remain untouched.

Arthur independently built the affected packages and checked 36 closed theorem
assumptions, the three exact row types, four helper types and six frozen/live
dependency closures. X24's verbatim frozen chain includes its pre-M1 edge set;
the existing C1 X18 and M1 X25 frozen bodies are unchanged. The thin Packing
entry point reuses those certificates. X24's parity and size bounds, X18's
partial status and X25's open status are preserved.

Independent report/kernel checks passed 92/92. Fidelity, registry tests and
statement docs passed. The sole all-report failure was the C1 summary count
193-to-191 after removing two migrated consumers; integration regenerates that
summary, and all six reports plus audit pass on the combined B2/C2 tree.
Implementer targeted gates separately passed 219 theorem assumptions in 24
modules and X24/X18/X25 milestones, each 11/11.

Integration resolves equivalent-C1 ancestry while retaining coordinator review
records, A2/B2 additions and both families' project registrations. All C2 Rocq
and specification changes preserve the reviewed bytes. Root integration gates
and full unscoped acceptance are recorded separately in the coordination log.
Detailed independent evidence is kept outside the repository under
`coordination/evidence/C2-perfect_matching-review-arthur/`.
