# Directed-path cases k = 4, 5, 6

This directory extends the Cheng--Keevash directed-path development from
`applications/ck3`.  Its public end products prove that every nonempty
oriented graph of minimum out-degree at least `k` has a simple directed path
with `2*k` arcs, for `k = 4, 5, 6`.

## Proof structure

- `ckpath_shapes.v`, `ckpath_kernel_cases.v`, and the strengthened kernel in
  `ck3/lemma7.v` reduce a shortest counterexample to a finite list of exact
  path/cycle shapes.
- `ckpath_cycle_tools.v`, `ckpath_tight_cycles.v`,
  `ckpath_odd_gateway.v`, and `ckpath_even_gateway.v` discharge the uniform
  structural and counting arguments.  The `k=4` branch is entirely in this
  hand-checked layer.
- `ckpath_c10_hand.v` and `ckpath_kernel_c10_adapter.v` isolate the new
  two-prefix argument used by the `k=6`, ten-cycle shape.
- `ckpath_rotation_paths.v` proves that every numeric rotation used by the
  finite endgames is a Hamilton ordering when its chord variables are
  realized by graph arcs.
- `ckpath_cnf.v`, `ckpath_cardinality.v`, and `ckpath_drup.v` define the
  transparent Boolean semantics and the verified hinted-RUP/DRUP checker.
  `ckpath_cert_base.v` defines the exact C9/C10/C11 formulas; the generated
  `ckpath_cert_*` modules replay their contradiction traces inside Rocq.
- `ckpath_cert_valuation.v`, `ckpath_cert_clause_tools.v`, and
  `ckpath_graph_count.v` form the audited semantic boundary between an
  oriented graph and those finite formulas.
- `ckpath_cert_graph_{common,odd,c10}.v` proves that the remaining graph
  configurations satisfy the certified formulas.  `ckpath_k4.v`,
  `ckpath_k5.v`, and `ckpath_k6.v` assemble the exact kernel cases.

## Public results

- `ck_conj1_delta4`, `ck_conj1_delta5`, `ck_conj1_delta6` prove
  `2*k <= ell D` from minimum out-degree at least `k` for `k = 4,5,6`.
- `ck_conj1_delta4_path`, `ck_conj1_delta5_path`, and
  `ck_conj1_delta6_path` return explicit simple directed paths with exactly
  8, 10, and 12 arcs.
- `ck_conj1_at_4`, `ck_conj1_at_5`, and `ck_conj1_at_6` expose the same
  results in the notation of Cheng--Keevash Conjecture 1.

## Certificate trust boundary

`scripts/generate_ckpath_certificates.py` and the external SAT solver are
untrusted generators.  Their output consists only of data.  Each hinted RUP
step is recomputed by transparent Rocq functions, the database is threaded
through proved soundness lemmas, and the exported contradiction theorem
requires a checked final empty clause.  The large C11 traces are split into
bounded modules solely to keep replay memory and elaboration time stable.

No theorem in this directory is intended to rely on `Admitted`, a custom
axiom, or an opaque native-code oracle.  The final audit compiles every module,
runs `rocqchk`, and checks `Print Assumptions` for the public results.

From `digraph-theory/`, the integrated build is:

```sh
opam exec --switch=rocq-tools -- make
```

The certificate generator can reconstruct DIMACS instances and hinted proof
data, but it is outside the trusted base: only the Rocq definitions and the
kernel-checked replay theorems are trusted.
