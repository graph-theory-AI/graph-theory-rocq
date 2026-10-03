# Migration source-closure gate review

Implementer: `matching_scope`. Independent reviewer: `path_review`.
Coordinator final review: `root`. Both reviewers approved the combined change
on 2026-10-02, including the follow-up ownership fix:

- `8336d9a10727e3467e4d51324bcd5c31770ea49b`: fresh source closure and forced builds.
- `2c9668886464e5618a748e6c31e017d1ffe76ec5`: reject object aliases before ownership resolution.

Fresh pinned `rocq dep` rules determine every local dependency of all registered
API/certificate roots. Generated project Makefiles force every required source,
including unregistered transitive helpers, once in dependency order. They retain
project compiler flags and reread `Load` inputs. No empty-target package build is
used. Missing ownership, unresolved imports, cycles, unsupported compiler/project
overrides, and non-pinned external dependencies fail closed.

Review specifically covered stale clean objects with preserved source timestamps,
changed `Require`/`Load` imports with stale dependency files, local and external
object aliases, symlinked directories, compiler query/proof-skipping modes, and
inherited Make/compiler overrides. Numeric parallelism and OCaml GC controls are
retained; only the pinned runtime's exact numeric GC counters are exempted from
strict dependency-warning rejection. Rollback tests reproduced unsafe acceptance
for the environment, query-mode, and three alias cases.

Validation through the pinned proof-shell:

- Independent focused tests: 25/25 at `8336d9a`; 29/29 at `2c96688`.
- Full `make mutation`, separately at each pin: exit 0; all 12/12 canaries killed
  with every baseline accepted. The final pin also passed registry 14, build 29,
  resolution 15, documentation 22, edge 43, lint/inventory self-tests, and report
  18 tests with kernel probes. The first run is not evidence for the alias fix.
- Integration on `72f29c624c37e505a49e0105f5932731e4d3dace` was conflict-free.
  The four tooling files remain byte-identical to `2c96688`; all Rocq/project
  files and the newer compact-report guards remain byte-identical to the base.
- Combined integration tests: registry 15/15, build 29/29, report 20/20 with
  kernel probes. Fresh expanded plan: 35 roots, 124 local sources, 10 packages.
- All generated manifests, inventory, status, dependency graph and eight compact
  reports were regenerated with no byte drift; `make audit` passed in the
  prepared integration snapshot.

Every reached project is parsed by coqdep, so unresolved imports in an unrelated
source can still reject the plan; unrelated ill-typed proofs are not compiled.
Unsupported custom configuration is rejected explicitly. Corpus package builds
and statement-family gates remain coordinator-owned integration checks; the
fresh-plan counts above do not claim those proof builds have completed.
