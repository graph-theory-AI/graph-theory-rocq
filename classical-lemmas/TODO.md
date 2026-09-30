# classical-lemmas — TODO: external theorems to formalize

The implication programme (2026-09-24) proved 13 relations between conjectures only
*conditionally*: each is a Qed theorem `external_T_statement -> A -> B`, where `T` is a
published theorem stated in the repository's vocabulary but not formalized. The ten
statements below are registered in `meta/external_theorems.json` (citation, claim, users,
second-reader verdict) and defined next to the edge that uses them. Formalizing one of them
here, and proving the registered `external_*_statement` from it, turns the corresponding
edges from `conditional` into `verified` (`python3 meta/check_edges.py --assumptions`
re-checks the exact type; `python3 meta/build_edge_graph.py` re-tags the graph).

Rules for a port: state the theorem on MathComp / coq-graph-theory notions (this package
imports nothing else of the repository), keep it axiom-free (`Print Assumptions` closed
under the global context), and add the bridge lemma `external_T_statement` ⇐ the theorem in
the package that owns the edge (a package may import `classical-lemmas`; see `packing-theory`).

| # | external statement (where defined) | theorem to formalize | source | edges unblocked | difficulty |
|---|---|---|---|---|---|
| 1 | `external_circular_5_flow_statement` (`cycle-theory/theories/conjectures/implications_X228.v`) | A circular 5-flow (real Kirchhoff flow with 1 ≤ \|φ(e)\| ≤ 4, stated denominator-free with 2 ≤ \|φ\| ≤ 8) yields a nowhere-zero integer 5-flow. | Goddyn, Tarsi, Zhang, *On (k,d)-colorings and fractional nowhere-zero flows*, J. Graph Theory 28 (1998) 155–161 | half-flow pair ⇒ 5-flow (gc:e174) | medium: rounding argument on the cycle space |
| 2 | `external_five_even_cover_cubic_reduction_statement` (`implications_U6.v`) | Cycle double covers and k-even-subgraph double covers reduce to cubic bridgeless multigraphs (suppress degree-2 vertices, split vertices of degree ≥ 4 preserving bridgelessness — Fleischner's splitting lemma). | Jaeger, *A survey of the cycle double cover conjecture*, Ann. Discrete Math. 27 (1985) 1–12 §2; Zhang, *Integer Flows and Cycle Covers of Graphs* (1997) Ch. 3 | strong 5-CDC ⇒ CDC, ⇒ (5,2)-covers; Petersen colouring ⇒ CDC, ⇒ (5,2)-covers (e085, e086, e090, e091) | hard: vertex splitting + Fleischner's lemma on `mgraph` |
| 3 | `external_cdc_simple_reduction_statement` (`implications_U6.v`) | CDC for simple bridgeless graphs implies CDC for all bridgeless multigraphs (subdivide every edge twice, transport the cover back; loops covered twice by themselves). | Jaeger 1985 §2 | small CDC ⇒ CDC (e209) | medium: subdivision and transport of covers |
| 4 | `external_cdc_cubic_2connected_reduction_statement` (`implications_U6.v`) | CDC for cubic 2-connected multigraphs implies CDC for all bridgeless multigraphs (block decomposition + item 2). Weaker than the cited 3-connected form. | Jaeger 1985 §2; Zhang 1997 Ch. 3 | CDC with predefined 2-regular subgraph ⇒ CDC (e098) | hard: block decomposition + item 2 |
| 5 | `external_steffen_3flow_5graphs_statement` (`implications_D1.v`) | If every 5-graph has circular flow number ≤ 3 then every 4-edge-connected graph has a nowhere-zero 3-flow (the direction used of Steffen's equivalence; via Kochol's 5-edge-connected reduction and attainment of the circular flow number). | Steffen, J. Graph Theory 79 (2015) 1–7 end of §3; Kochol, *An equivalent version of the 3-flow conjecture*, JCTB 83 (2001) 258–261; Goddyn–Tarsi–Zhang 1998 | circular flow numbers of r-graphs ⇒ 3-flow (e184) | hard: Kochol's reduction |
| 6 | `external_tutte_class1_cubic_statement` (`implications_D1.v`) | A loopless cubic multigraph is 3-edge-colourable iff it has a nowhere-zero 4-flow; hence a class-1 cubic multigraph has circular flow number ≤ 4. | Tutte, Proc. London Math. Soc. 51 (1949) 474–483; Canad. J. Math. 6 (1954) 80–91 | circular flow numbers of r-graphs ⇒ regular class-1 graphs, t = 1 case (e096) | medium: explicit Z₂×Z₂ flow from a 3-edge-colouring |
| 7 | `external_modular_orientation_to_flow_statement` (`implications_D1.v`) | For k ≥ 1, an orientation whose imbalance is a multiple of 2k+1 at every vertex yields a nowhere-zero integer (2k+1)-flow (Tutte's Z_m-flow ⇒ integer m-flow). Guard k > 0 is essential (k = 0 is refutable). | Tutte, Canad. J. Math. 6 (1954) 80–91 | Jaeger's modular orientation ⇒ 3-flow (e093) | medium: Tutte's flow lifting |
| 8 | `external_petersen_BF_cover_statement` (`implications_U10.v`) | The six perfect matchings of the Petersen graph cover every edge exactly twice (a Berge–Fulkerson cover). | Holton, Sheehan, *The Petersen Graph*, CUP 1993 | Petersen colouring ⇒ Berge–Fulkerson (e089) | easy: finite, decidable on the `Pedge` encoding (bit-code checks as in `implications_U6.v`) |
| 9 | `external_whitney_line_inversion_statement` (`reconstruction-theory/theories/conjectures/implications_U11.v`) | Two graphs with ≥ 4 edges, the same edge deck and isomorphic line graphs are isomorphic (Whitney componentwise; K₃/K₁,₃ swaps excluded by Kelly's lemma on the edge deck; isolated vertices fixed by the deck). The naive premise without the edge deck is false (K₃+K₁+K₂ vs K₁,₃+K₂). | Whitney, Amer. J. Math. 54 (1932) 150–168; Hemminger, Proc. AMS 20 (1969) 185–187; Greenwell, Proc. AMS 30 (1971) 431–433 | reconstruction ⇒ edge reconstruction (e055) | hard: Whitney's theorem |
| 10 | `external_layered_treewidth_planar_statement` (`atlas/theories/conjectures/implications_A1.v`) | Every planar graph (no K₅, K₃,₃ minor) has layered treewidth ≤ 3. | Dujmović, Morin, Wood, JCTB 127 (2017) 111–147; Wagner, Math. Ann. 114 (1937) 570–590 | bounded layered treewidth ⇒ planar queue number (e126) | hard: needs a planar-embedding layer |

Second-reader notes on each statement: `meta/E1-A1_edge_audit.md`, sections B and E.
