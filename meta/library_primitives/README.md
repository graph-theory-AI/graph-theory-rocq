# Family registry ownership

Each migration family owns `meta/library_primitives/<family>.json`. There is no
aggregate registry or manually maintained family index. Readers use
`family_registry.load_library_registry(root)` and receive the former logical
`{"schema_version": 1, "primitives": {...}}` shape.

Each file contains exactly `schema_version: 1`, `family` (matching its filename),
and `primitive` (the existing family record: canonical name, ownership, status,
sources, consumer count, upstream audit and theorem lists). Adding or updating a
family does not require editing another family's document. The inventory checks
the sources and consumer counts; the migration gate checks registered theorems.

Optional `migration_report`, `migration_spec`, `independent_review` and
`foundation_fidelity` fields name repository-relative documents. Referenced files
must exist. A report writer can explicitly set `allow_missing_reports=True` to
create a missing generated `migration_report`; checking commands remain strict,
and other document references never receive that exception.

Malformed JSON, duplicate keys, wrong filenames, missing/empty registry
directories and coexistence with the obsolete `meta/library_primitives.json`
are errors. A linked document cannot disappear silently. Completeness of active
migrations is also checked against report specifications. Deleting an entirely
unreferenced proposed family is a reviewable git deletion; directory discovery
alone cannot distinguish it from an intentional removal without a second index.

## Public repository source definitions

`source_definitions` remains the sole source list. To enroll a same-contract
public Definition outside the conjecture-only helper inventory, add its name
to that list and an entry in optional `repository_sources`:

```json
"repository_sources": {
  "Namespace.foundations.module.definition": {
    "path": "area/theories/foundations/module.v",
    "commit": "<full 40-character lowercase commit hash>",
    "blob": "<full 40-character lowercase blob hash>",
    "declaration_hash": "<64-character normalized declaration SHA256>"
  }
}
```

The descriptor pins the original regular Git blob and parsed declaration. The
current declaration may become a compatibility alias; it must still exist with
the same name, source path and build-listed project namespace. Both original
and current ownership are checked independently. Supported public paths are
flat `base/theories/*.v`, area `theories/foundations/**/*.v`, and build-listed
`classical-lemmas/theories/**/*.v` library modules. Classical conjecture,
migration and example directories, probes and path aliases cannot use this
mechanism. Definitions
inside Sections are supported; local or nested-module declarations, absolute
project load paths and hidden ownership overrides fail closed. Every source has
one family owner.

These records are parsed on demand by
`library_inventory.repository_source_records(root, primitive)`, with an explicit
repository root. They do not expand the generated helper inventory or its debt
counts. Missing conjecture inventory entries never fall back to descriptors.
`consumers_remaining` retains its existing same-file direct-consumer meaning.

The report uses ordinary `kind: source` objects, whose original commit/path must
match the descriptor. Frozen text, aliases, certificate registration, exact
statement iff types, assumptions and corpus status checks remain unchanged.
Independent baseline reachability includes public base/foundation intermediates
and ClassicalLemmas sibling modules;
omitting a reached corpus statement or an intermediate on its path fails.
Lexical discovery still requires the usual independent Section/dependency review.
Record intermediate objects as `kind: chain`, using registered earlier-family
certificates when reusing an existing freeze. Never refresh a pin to silence a
failure or label an existing corpus row `non_corpus`.

An explicitly reviewed complete non-corpus proposition whose name lacks
`_statement` can be listed in its report specification's optional
`additional_statements` array of qualified names. Each must be reached from the
migrated sources at both baseline and current source, outside both manifests,
and have exactly one `kind: statement`, `non_corpus: true` frozen mapping and a
complete iff certificate. Its source and project must be regular, build-listed
and owned by the recorded namespace at the immutable full baseline commit and
in the current tree. The initial format accepts only top-level
`Definition NAME : Prop := ...` outside Modules and Sections; parameterized or
inferred signatures fail closed. Source helpers cannot be enrolled this way.
The complete intermediary path must also be frozen. Kernel checks require the
unapplied frozen/live constants to have type `Prop`, the exact complete iff,
and zero assumptions for every certificate. This field grants no axiom
exception and cannot remove an ordinarily discovered statement. Independent
review supplies the semantic classification as a statement; a nullary `Prop`
type alone cannot distinguish a statement from a proposition used as a helper.

The registered theorem gate recognizes `ClassicalLemmas` as owned by
`classical-lemmas`; it forces the same fresh local source closure as other
packages. Classical source/project changes rebuild that package and its Packing
consumer, and run the migration and report gates. Any new cross-package import
must also be declared in `_CoqProject` and the root build dependencies when the
family introduces it; source enrollment alone does not establish that dependency.

## Family fidelity fragments

Historical module contracts remain in `meta/foundation_fidelity.json`. A family
can own `meta/foundation_fidelity/<family>.json`, referenced by its primitive's
`foundation_fidelity` field. A fragment has exactly `schema_version: 1`, `family`
and `modules`. Each module entry has `path`, `overrides` and `machine_evidence`:

```json
{
  "schema_version": 1,
  "family": "example-family",
  "modules": {
    "GTBase.common": {
      "path": "base/theories/common.v",
      "overrides": {
        "example_primitive": {"verdict": "FAITHFUL", "note": "The precise audited contract."}
      },
      "machine_evidence": ["example_primitive_grounding"]
    }
  }
}
```

Families explicitly enroll their own primitives through `overrides`; they cannot
change a module's default, reuse another entry's primitive ownership or change
its source path. The fidelity gate merges disjoint entries and checks the actual
declarations and evidence. Unlisted declarations receive no inherited trust.
Existing module-wide audits are not divided into artificial families.

Run `python3 meta/test_family_registry.py`, `make audit`, and the usual migration
gates through `environment/proof-shell.sh`. Registry and loader changes also
route to `make mutation`.
