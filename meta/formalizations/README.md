# Checked graph-theory resolutions

Four source records now have exact, assumption-free Rocq proofs in this repository. Three are new formalizations; Question 5.9 reuses an existing construction through a new statement bridge.

| Source record | Checked result | Final module |
|---|---|---|
| `2103.15175__00` | List Ramsey least forcing order `s^k+1`, for all `s>=2`, `k>=1` | [list_ramsey_graph.v](../../extremal-graph-theory/theories/applications/list_ramsey_graph.v) |
| `2408.02400__00` | For every `k>=5`, a graph with clique number 4, cochromatic number `k`, and chromatic number `k+3` | [cochromatic_gap.v](../../chromatic-theory/theories/applications/cochromatic_gap/cochromatic_gap.v) |
| `2512.10438__00` | Six-color, nine-vertex nontransitive tournament with longest avoiding path 7 vertices, below the exact transitive benchmark 8 | [color_avoiding_tournament.v](../../digraph-theory/theories/applications/color_avoiding_tournament.v) |
| `2310.04265__09` | Negation of the existing Question 5.9 statement | [question_5_9_resolution.v](../../digraph-theory/theories/applications/question_5_9_resolution.v) |

From the repository root, using an installed compatible switch:

```sh
ROCQ_OPAM_SWITCH=rocq-tools make resolutions
ROCQ_OPAM_SWITCH=rocq-tools python3 meta/test_formal_resolutions.py
ROCQ_OPAM_SWITCH=rocq-tools python3 meta/formal_resolutions.py \
  --report meta/formalizations/ASSUMPTIONS.txt
```

The development environment used Rocq 9.1.1, OCaml 5.3.0 and the installed MathComp/GraphTheory libraries in `rocq-tools`. The live checker builds the required local dependencies and rejects nonclosed assumptions and mismatched statements. It preserves historical source statuses.

Read the [development journal](JOURNAL.md) for the proof attempts, MCP workflow, certificate optimizations and integration decisions. The [assumptions transcript](ASSUMPTIONS.txt) records the successful four-entry check. The [registry documentation](../FORMAL_RESOLUTIONS.md) explains source correspondence and the validation contract.

Validation on 2026-09-05: all four resolutions and a separate `rocqchk` validation passed, all 14 checker tests passed, and the X7 milestone passed all 11 checks. The full repository `make audit` remains blocked by pre-existing drift in `meta/dependency_graph.json`; it was not changed by this work. Source correspondence was independently reviewed by other agents and remains open to human mathematical review.
