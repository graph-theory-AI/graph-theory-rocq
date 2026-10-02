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
