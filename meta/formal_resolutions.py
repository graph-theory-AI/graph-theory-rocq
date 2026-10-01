#!/usr/bin/env python3
"""Check separately recorded formal resolutions without changing source statuses.

Every accepted entry binds an upstream source snapshot to a named statement and
an exact proof (or refutation). Rocq recompiles both source files, checks the exact
type, and reports the transitive assumptions of both constants. This cannot
verify that mathematical prose and its formal encoding mean the same thing;
the explicit correspondence review remains a separate obligation.
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
import rocq_toolchain as ROCQ

ROOT = Path(__file__).resolve().parent.parent
QUALIFIED = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)+")
SHA256 = re.compile(r"[0-9a-f]{64}")


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


def validate_entry(root: Path, entry: dict) -> tuple[list[str], list[Path]]:
    required = {
        "record_key", "corpus", "row_id", "source_hash", "source_text",
        "source_locator", "package", "statement", "statement_file",
        "statement_sha256", "theorem", "theorem_file", "direction",
        "correspondence",
    }
    if missing := required - entry.keys():
        raise ResolutionError(f"missing fields: {sorted(missing)}")
    if entry["corpus"] not in ("v2", "opg"):
        raise ResolutionError("corpus must be v2 or opg")
    if entry["direction"] not in ("prove", "disprove"):
        raise ResolutionError("direction must be prove or disprove")
    for field in ("statement", "theorem"):
        if not isinstance(entry[field], str) or not QUALIFIED.fullmatch(entry[field]):
            raise ResolutionError(f"{field} must be a fully qualified Rocq constant")
    if entry["statement"] == entry["theorem"]:
        raise ResolutionError("statement and theorem must be distinct constants")
    for field in ("source_hash", "statement_sha256"):
        if not isinstance(entry[field], str) or not SHA256.fullmatch(entry[field]):
            raise ResolutionError(f"{field} must be a SHA-256 hexadecimal digest")
    package = entry["package"]
    if not isinstance(package, str) or not re.fullmatch(r"[A-Za-z0-9_-]+", package):
        raise ResolutionError("invalid package")
    manifest = read_json(root / "meta" / f"{entry['corpus']}_corpus_manifest.json")
    matches = [row for row in manifest["rows"] if row.get("row_id") == entry["row_id"]]
    if len(matches) != 1:
        raise ResolutionError(f"source row must occur exactly once: {entry['row_id']}")
    row = matches[0]
    for field in ("record_key", "source_hash", "source_text", "source_locator"):
        if entry[field] != row.get(field):
            raise ResolutionError(f"{field} differs from the pinned source row")
    if row.get("repo") != package:
        raise ResolutionError("package differs from source row ownership")
    if row.get("formal_name") and entry["statement"].rsplit(".", 1)[1] != row["formal_name"]:
        raise ResolutionError("statement differs from the corpus formal_name")
    if row.get("formal_name"):
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
    flags, listed = project(root, package)
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
        run(["rocq", "makefile", "-f", "_CoqProject", "-o", "Makefile.coq"], package, env)
        targets = [str(source.relative_to(package).with_suffix(".vo")) for source in sources]
        run(["make", "-f", "Makefile.coq", *targets], package, env)
    # Recompile the actual registered sources even when the caller already built
    # the package. A fresh exact-type probe alone could otherwise trust a stale .vo.
    for source in sources:
        run(["rocq", "compile", *flags, str(source.relative_to(package))], package, env)
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
    if "Axioms:" in output or output.count("Closed under the global context") != 2:
        raise ResolutionError(f"statement/proof assumptions are not closed:\n{output}")
    return VerifiedResolution(entry["record_key"], statement, theorem, entry["direction"], output)


def verify_resolutions(root: Path = ROOT, *, package: str | None = None,
                       statement_names: set[str] | None = None,
                       build: bool = True) -> list[VerifiedResolution]:
    entries = registry_entries(root)
    verified: list[VerifiedResolution] = []
    for entry in entries:
        if (package is None or entry.get("package") == package) and (
            statement_names is None or entry.get("statement") in statement_names
        ):
            try:
                verified.append(verify_entry(root, entry, build=build))
            except ResolutionError as exc:
                raise ResolutionError(f"{entry.get('record_key')}: {exc}") from exc
    return verified


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--metadata-only", action="store_true",
                        help="validate registry metadata only; never grants a faithfulness exemption")
    parser.add_argument("--report", type=Path, help="write the successful compiler assumptions output")
    args = parser.parse_args()
    try:
        if args.metadata_only:
            entries = registry_entries(args.root)
            for entry in entries:
                validate_entry(args.root, entry)
            print(f"formal resolution metadata OK ({len(entries)} entries; proofs not checked)")
        else:
            entries = verify_resolutions(args.root)
            for entry in entries:
                print(f"OK {entry.record_key}: {entry.direction} {entry.statement}")
            print(f"formal resolutions OK ({len(entries)} exact, assumption-free proofs)")
            if args.report:
                args.report.write_text("\n".join(
                    f"{entry.record_key}\n{entry.assumptions}" for entry in entries))
    except (ResolutionError, RuntimeError) as exc:
        print(f"formal resolutions FAILED: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
