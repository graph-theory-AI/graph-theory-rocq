#!/usr/bin/env python3
"""Check separately recorded formal resolutions without changing source statuses.

Every accepted entry binds an upstream source snapshot to a named statement and
an exact proof (or refutation). Rocq recompiles both source files, checks the exact
type, and reports the transitive assumptions of both constants. This cannot
verify that mathematical prose and its formal encoding mean the same thing;
the explicit correspondence review remains a separate obligation.

A v2 entry names its source row by row_id and copies the row's pinned hash,
text and locator. An OPG entry is keyed opg:<slug> and copies the pinned OPG
manifest row's identity (node id, URL, both upstream commits, text and selected
proposition); its statement is the row's formal_name, defined at top level (outside
every Module) in exactly one file of the owning package. --record and --package
restrict a run to part of the registry; a selection that matches nothing fails.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import shlex
import subprocess
import sys
import tempfile

import gate_contracts as CONTRACTS
import library_inventory as INV
import rocq_toolchain as ROCQ

ROOT = Path(__file__).resolve().parent.parent
QUALIFIED = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)+")
SHA256 = re.compile(r"[0-9a-f]{64}")
COMMON_FIELDS = {
    "record_key", "corpus", "package", "statement", "statement_file",
    "statement_sha256", "theorem", "theorem_file", "direction", "correspondence",
}
# Fields copied verbatim from the pinned manifest row; the v2 record_key is copied too.
SOURCE_IDENTITY = {
    "v2": ("record_key", "source_hash", "source_text", "source_locator"),
    "opg": ("node_id", "canonical_url", "source_commit_repo",
            "source_commit_problems_json", "source_text", "selected_proposition"),
}
ENTRY_FIELDS = {
    "v2": COMMON_FIELDS | {"row_id", *SOURCE_IDENTITY["v2"]},
    "opg": COMMON_FIELDS | set(SOURCE_IDENTITY["opg"]),
}
OPG_KEY = re.compile(r"opg:([a-z0-9_]+)")
# A compiler warning: its location line, a line starting "Warning:", further message lines,
# then its own [category,...] line (categories may contain dots, as in deprecated-since-9.2).
WARNING_LOCATION = re.compile(r'File "[^"\n]*", line \d+, characters \d+-\d+:')
WARNING_CATEGORY = re.compile(r"\[[^\]\n]+\]")


class ResolutionError(ValueError):
    pass


@dataclass(frozen=True)
class VerifiedResolution:
    record_key: str
    statement: str
    theorem: str
    direction: str
    assumptions: str

    @property
    def exact_type_key(self) -> tuple[str, str, str]:
        return self.statement, self.theorem, self.direction


def declaration_hash(command: str) -> str:
    """Hash declaration syntax, ignoring comments and whitespace formatting."""
    normalized = " ".join(CONTRACTS.strip_comments(command).split())
    return hashlib.sha256(normalized.encode("utf-8")).hexdigest()


def read_json(path: Path) -> object:
    try:
        return json.loads(path.read_text())
    except (OSError, ValueError) as exc:
        raise ResolutionError(f"cannot read {path}: {exc}") from exc


def local_file(root: Path, relative: object) -> Path:
    if not isinstance(relative, str) or not re.fullmatch(r"[A-Za-z0-9_./-]+", relative):
        raise ResolutionError(f"invalid repository path: {relative!r}")
    path = PurePosixPath(relative)
    if path.is_absolute() or ".." in path.parts or str(path) != relative:
        raise ResolutionError(f"path must be canonical and repository-relative: {relative}")
    resolved = (root / relative).resolve()
    if not resolved.is_relative_to(root.resolve()) or not resolved.is_file():
        raise ResolutionError(f"missing file or path escapes repository: {relative}")
    return resolved


def project(root: Path, package: str) -> tuple[list[str], set[str]]:
    """Read only load-path flags and listed sources; never evaluate shell text."""
    path = local_file(root, f"{package}/_CoqProject")
    words = shlex.split(path.read_text(), comments=True)
    flags: list[str] = []
    files: set[str] = set()
    index = 0
    while index < len(words):
        token = words[index]
        if token in ("-Q", "-R"):
            if index + 2 >= len(words):
                raise ResolutionError(f"incomplete load-path flag in {path}")
            flags.extend(words[index:index + 3])
            index += 3
        elif token.endswith(".v"):
            files.add(f"{package}/{token}")
            index += 1
        else:
            index += 1
    if not flags:
        raise ResolutionError(f"no Rocq load-path flags in {path}")
    return flags, files


def module_name(root: Path, package: str, file: Path, flags: list[str]) -> str:
    candidates: list[tuple[int, str]] = []
    for index in range(0, len(flags), 3):
        physical = (root / package / flags[index + 1]).resolve()
        logical = flags[index + 2]
        if file.is_relative_to(physical):
            suffix = file.relative_to(physical).with_suffix("").parts
            candidates.append((len(physical.parts), ".".join((logical, *suffix))))
    if not candidates:
        raise ResolutionError(f"file has no project load-path mapping: {file}")
    return max(candidates)[1]


def registry_entries(root: Path) -> list[dict]:
    raw = read_json(root / "meta/formal_resolutions.json")
    if not isinstance(raw, dict) or raw.get("schema_version") != 1:
        raise ResolutionError("formal_resolutions.json requires schema_version=1")
    entries = raw.get("resolutions")
    if not isinstance(entries, list) or not all(isinstance(entry, dict) for entry in entries):
        raise ResolutionError("resolutions must be a list of objects")
    keys: set[str] = set()
    for entry in entries:
        key = entry.get("record_key")
        if not isinstance(key, str) or not key or key in keys:
            raise ResolutionError(f"missing or duplicate record_key: {key!r}")
        keys.add(key)
    return entries


def top_level_definitions(source: str, what: str) -> set[str]:
    """Definition/Let names of a source outside every Module.

    A Section leaves its definitions public under the file's module, so they
    count; a Module (such as a migration certificate's frozen Legacy copy) does
    not. Comments and strings are masked; unsupported scope structure fails.
    """
    try:
        masked = INV.scope_mask(source, what)
        modules = [o for o in INV.scope_openers(masked) if o["kind"] == "Module"]
    except ValueError as exc:
        raise ResolutionError(f"{what}: unsupported Module/Section structure: {exc}") from None
    return {match.group(1) for match in CONTRACTS.DEFINITION_DECL_RE.finditer(masked)
            if not any(o["body_start"] <= match.start(1) < o["close_start"] for o in modules)}


def statement_location(root: Path, listed: set[str], name: str) -> str:
    """The one project file of a package that defines `name` at top level."""
    owners = []
    for relative in sorted(listed):
        source = local_file(root, relative).read_text()
        # The substring test only skips files that cannot define the name.
        if name in source and name in top_level_definitions(source, relative):
            owners.append(relative)
    if len(owners) != 1:
        raise ResolutionError(f"formal_name {name} needs exactly one top-level definition "
                              f"in its package, found {owners or 'none'}")
    return owners[0]


def validate_entry(root: Path, entry: dict) -> tuple[list[str], list[Path]]:
    corpus = entry.get("corpus")
    if not isinstance(corpus, str) or corpus not in ENTRY_FIELDS:
        raise ResolutionError("corpus must be v2 or opg")
    if missing := ENTRY_FIELDS[corpus] - entry.keys():
        raise ResolutionError(f"missing fields: {sorted(missing)}")
    if extra := entry.keys() - ENTRY_FIELDS[corpus]:
        raise ResolutionError(f"fields not used by {corpus} entries: {sorted(extra)}")
    if entry["direction"] not in ("prove", "disprove"):
        raise ResolutionError("direction must be prove or disprove")
    for field in ("statement", "theorem"):
        if not isinstance(entry[field], str) or not QUALIFIED.fullmatch(entry[field]):
            raise ResolutionError(f"{field} must be a fully qualified Rocq constant")
    if entry["statement"] == entry["theorem"]:
        raise ResolutionError("statement and theorem must be distinct constants")
    for field in ("source_hash", "statement_sha256") if corpus == "v2" else ("statement_sha256",):
        if not isinstance(entry[field], str) or not SHA256.fullmatch(entry[field]):
            raise ResolutionError(f"{field} must be a SHA-256 hexadecimal digest")
    package = entry["package"]
    if not isinstance(package, str) or not re.fullmatch(r"[A-Za-z0-9_-]+", package):
        raise ResolutionError("invalid package")
    manifest = read_json(root / "meta" / f"{corpus}_corpus_manifest.json")
    if corpus == "opg":
        key = OPG_KEY.fullmatch(entry["record_key"]) if isinstance(entry["record_key"], str) else None
        if key is None:
            raise ResolutionError("an OPG record_key must be opg:<slug>")
        source = f"OPG slug {key.group(1)}"
        matches = [row for row in manifest["rows"] if row.get("slug") == key.group(1)]
    else:
        source = entry["row_id"]
        matches = [row for row in manifest["rows"] if row.get("row_id") == entry["row_id"]]
    if len(matches) != 1:
        raise ResolutionError(f"source row must occur exactly once: {source}")
    row = matches[0]
    for field in SOURCE_IDENTITY[corpus]:
        if entry[field] != row.get(field):
            raise ResolutionError(f"{field} differs from the pinned source row")
    if row.get("repo") != package:
        raise ResolutionError("package differs from source row ownership")
    if corpus == "opg" and not row.get("formal_name"):
        raise ResolutionError("an OPG resolution needs the source row's formal_name")
    if row.get("formal_name") and entry["statement"].rsplit(".", 1)[1] != row["formal_name"]:
        raise ResolutionError("statement differs from the corpus formal_name")
    flags, listed = project(root, package)
    if corpus == "opg":
        if entry["statement_file"] != statement_location(root, listed, row["formal_name"]):
            raise ResolutionError("statement_file differs from the corpus statement location")
    elif row.get("formal_name"):
        locator = re.search(r"\| Rocq: ([^#\s]+)#([A-Za-z0-9_']+)", row["source_locator"])
        if locator:
            expected_file = locator.group(1)
        elif row.get("phase") and not row.get("already_formalized"):
            expected_file = f"{package}/theories/conjectures/{row['phase']}.v"
        else:
            raise ResolutionError("existing formal_name has no unambiguous defining file in source metadata")
        if entry["statement_file"] != expected_file:
            raise ResolutionError("statement_file differs from the corpus statement location")
    review = entry["correspondence"]
    if not isinstance(review, dict) or any(
        not isinstance(review.get(field), str) or not review[field].strip()
        for field in ("explanation", "implemented_by", "reviewed_by", "reviewed_at")
    ):
        raise ResolutionError("correspondence requires explanation and author/reviewer/date")
    if review["implemented_by"] == review["reviewed_by"]:
        raise ResolutionError("correspondence reviewer must differ from implementer")
    if not re.fullmatch(r"\d{4}-\d{2}-\d{2}", review["reviewed_at"]):
        raise ResolutionError("correspondence reviewed_at must use YYYY-MM-DD")
    paths: list[Path] = []
    for role, pattern in (("statement", CONTRACTS.DEFINITION_DECL_RE),
                          ("theorem", CONTRACTS.PROOF_DECL_RE)):
        relative = entry[f"{role}_file"]
        file = local_file(root, relative)
        if relative not in listed:
            raise ResolutionError(f"{role}_file is absent from package _CoqProject")
        logical = module_name(root, package, file, flags)
        name = entry[role].rsplit(".", 1)[1]
        if entry[role] != f"{logical}.{name}":
            raise ResolutionError(f"{role} does not match its file's logical module")
        declarations = CONTRACTS.declaration_commands(file.read_text(), pattern)
        if name not in declarations:
            raise ResolutionError(f"{role} has no matching declaration in {relative}")
        if role == "statement" and declaration_hash(declarations[name]) != entry["statement_sha256"]:
            raise ResolutionError("statement declaration changed; correspondence must be reviewed again")
        clean = CONTRACTS.strip_comments(file.read_text())
        if re.search(r"\b(?:Admitted|Axiom|Axioms|Parameter|Parameters|Conjecture|admit)\b", clean):
            raise ResolutionError(f"forbidden admission/axiom declaration in {relative}")
        if file not in paths:
            paths.append(file)
    return flags, paths


def run(command: list[str], cwd: Path, env: dict[str, str]) -> str:
    try:
        proc = subprocess.run(command, cwd=cwd, env=env, text=True, capture_output=True)
    except OSError as exc:
        raise ResolutionError(f"could not execute {command[0]}: {exc}") from exc
    output = proc.stdout + proc.stderr
    if proc.returncode:
        raise ResolutionError(f"{' '.join(command)} failed:\n{output[-6000:]}")
    return output


def build_dependencies(root: Path, package: str, env: dict[str, str], seen: set[str]) -> None:
    """Build local package dependencies named by the project's load-path flags."""
    if package in seen:
        return
    seen.add(package)
    flags, _files = project(root, package)
    dependencies = set()
    for index in range(0, len(flags), 3):
        physical = (root / package / flags[index + 1]).resolve()
        if physical.is_relative_to(root):
            parts = physical.relative_to(root).parts
            if parts and parts[0] != package and (root / parts[0] / "_CoqProject").is_file():
                dependencies.add(parts[0])
    for dependency in sorted(dependencies):
        if dependency in seen:
            continue
        build_dependencies(root, dependency, env, seen)
        directory = root / dependency
        run(["rocq", "makefile", "-f", "_CoqProject", "-o", "Makefile.coq"], directory, env)
        run(["make", "-f", "Makefile.coq"], directory, env)


def verify_entry(root: Path, entry: dict, *, build: bool = True) -> VerifiedResolution:
    root = root.resolve()
    flags, sources = validate_entry(root, entry)
    package = root / entry["package"]
    env = ROCQ.environment()
    if build:
        build_dependencies(root, entry["package"], env, set())
    # Recompile the actual registered sources even when the caller already built
    # the package. A fresh exact-type probe alone could otherwise trust a stale .vo.
    # Use the package's compiler options and load-path ordering: compiling with
    # only the raw project load paths can invalidate already-built dependents.
    run(["rocq", "makefile", "-f", "_CoqProject", "-o", "Makefile.coq"], package, env)
    relative_sources = [source.relative_to(package) for source in sources]
    targets = [str(source.with_suffix(".vo")) for source in relative_sources]
    # Force recompilation even if a source edit preserved its original timestamp.
    force_sources = [arg for source in relative_sources for arg in ("-W", str(source))]
    run(["make", "-f", "Makefile.coq", *force_sources, *targets], package, env)
    statement, theorem = entry["statement"], entry["theorem"]
    target = f"~ {statement}" if entry["direction"] == "disprove" else statement
    modules = sorted({name.rsplit(".", 1)[0] for name in (statement, theorem)})
    body = "".join(f"Require Import {module}.\n" for module in modules)
    body += f"Check ({statement} : Prop).\nCheck ({theorem} : {target}).\n"
    body += f"Print Assumptions {statement}.\nPrint Assumptions {theorem}.\n"
    # Probe and products stay out of the source tree and do not collide across runs.
    with tempfile.TemporaryDirectory(prefix="rocq-resolution-") as temporary:
        probe = Path(temporary) / "ResolutionCheck.v"
        probe.write_text(body)
        output = run(["rocq", "compile", *flags, str(probe)], package, env)
    # The decision reads the whole compiler output; only the recorded transcript drops warnings.
    if "Axioms:" in output or output.count("Closed under the global context") != 2:
        raise ResolutionError(f"statement/proof assumptions are not closed:\n{output}")
    return VerifiedResolution(entry["record_key"], statement, theorem, entry["direction"],
                              transcript(output, temporary))


def transcript(output: str, temporary: str) -> str:
    """The probe output without compiler warning blocks.

    A warning block names the run's temporary probe file, so keeping it would
    make the --report differ on every run. Any other mention of that directory
    is an unrecognised message and fails rather than being recorded. A block
    must end with its category line before the next location line or the end
    of the output, so a malformed block can never swallow real output.
    """
    def unrecognised() -> ResolutionError:
        return ResolutionError(f"unrecognised compiler message in the probe output:\n{output}")

    lines = output.splitlines(keepends=True)
    kept: list[str] = []
    index = 0
    while index < len(lines):
        if (WARNING_LOCATION.fullmatch(lines[index].rstrip("\n"))
                and index + 1 < len(lines) and lines[index + 1].startswith("Warning:")):
            end = index + 1
            while not WARNING_CATEGORY.fullmatch(lines[end].rstrip("\n")):
                end += 1
                if end == len(lines) or WARNING_LOCATION.fullmatch(lines[end].rstrip("\n")):
                    raise unrecognised()
            index = end + 1
        else:
            kept.append(lines[index])
            index += 1
    text = "".join(kept)
    if temporary in text or "Warning:" in text:
        raise unrecognised()
    return text


def selected_entries(root: Path, *, package: str | None = None,
                     record_keys: set[str] | None = None) -> list[dict]:
    """Registry entries of `package` and/or named by `record_keys` (None: no restriction)."""
    entries = registry_entries(root)
    if record_keys is not None and (
            unknown := sorted(record_keys - {entry["record_key"] for entry in entries})):
        raise ResolutionError(f"unknown record_key: {', '.join(unknown)}")
    return [entry for entry in entries
            if (package is None or entry.get("package") == package)
            and (record_keys is None or entry["record_key"] in record_keys)]


def verify_resolutions(root: Path = ROOT, *, package: str | None = None,
                       statement_names: set[str] | None = None,
                       record_keys: set[str] | None = None,
                       build: bool = True) -> list[VerifiedResolution]:
    verified: list[VerifiedResolution] = []
    for entry in selected_entries(root, package=package, record_keys=record_keys):
        if statement_names is None or entry.get("statement") in statement_names:
            try:
                verified.append(verify_entry(root, entry, build=build))
            except ResolutionError as exc:
                raise ResolutionError(f"{entry.get('record_key')}: {exc}") from exc
    return verified


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--metadata-only", action="store_true",
                        help="validate registry metadata only; never grants a faithfulness exemption")
    parser.add_argument("--report", type=Path, help="write the successful compiler assumptions output")
    parser.add_argument("--package", help="check only the entries of this package")
    parser.add_argument("--record", action="append", metavar="KEY",
                        help="check only this record_key (repeatable)")
    args = parser.parse_args(argv)
    records = None if args.record is None else set(args.record)
    scope = "" if args.package is None and records is None else "; selected entries only"
    try:
        selection = selected_entries(args.root, package=args.package, record_keys=records)
        if scope and not selection:
            raise ResolutionError("the --package / --record selection matches no registry entry")
        if args.metadata_only:
            for entry in selection:
                validate_entry(args.root, entry)
            print(f"formal resolution metadata OK ({len(selection)} entries; proofs not checked{scope})")
        else:
            entries = verify_resolutions(args.root, package=args.package, record_keys=records)
            for entry in entries:
                print(f"OK {entry.record_key}: {entry.direction} {entry.statement}")
            print(f"formal resolutions OK ({len(entries)} exact, assumption-free proofs{scope})")
            if args.report:
                args.report.write_text("\n".join(
                    f"{entry.record_key}\n{entry.assumptions}" for entry in entries))
    except (ResolutionError, RuntimeError) as exc:
        print(f"formal resolutions FAILED: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
