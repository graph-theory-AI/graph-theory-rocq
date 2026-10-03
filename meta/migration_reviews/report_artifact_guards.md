# Review: compact report storage guards

Reviewed source: `1db2e8698ebc7485e8ff9628b56b4861dda6e179`.
Implementer: matching_scope. Independent reviewer: path_review.
Coordinator read and approved the complete three-file change on 2026-10-02.

The generator rejects detailed output inside the committed report directory,
including descendants and symlink aliases, before writing anything. The all-family
check rejects non-specification JSON there while retaining valid specifications
and documentation. A separate regression verifies that mutation workspaces copy
a newly enrolled fidelity owner's package, even when it is neither the mutant
target nor one of its dependencies, and exclude compiled artifacts.

Independent review found no blocker. All three regressions detect the previous
behavior. Focused suites passed: 15 registry and 20 report tests, including real
kernel probes; the repository audit passed. Full mutation at the reviewed SHA
exited successfully: all 12 canaries detected, baselines accepted, inventory
self-test and final report suite passed. No statement or compiler behavior
changes are included.

This tooling change is integrated separately from A2's family migration.
