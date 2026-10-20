#!/usr/bin/env python3
"""install_gate.py: the metadata contract, the import table, the inputs digest and the verdicts
(N1-N14, the planted client, CTL); no Rocq, opam or opam-installer needed (a fake runner
stands in for them, and the real library_package.py stages the fixture)."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import sys
import tempfile
import unittest
from unittest.mock import patch

import install_gate as G

COMMIT, TREE = "a" * 40, "b" * 40
GT_COMMIT = "322e352b72c4ca3f153e5f80123c5020a0d40620"
PIN = f'pin-depends: [["{G.GRAPH_THEORY_PIN}" "{G.GRAPH_THEORY_URL}{GT_COMMIT}"]]\n'
EXTERNALS = '  "rocq-core" {= "9.2.0"}\n  "coq-graph-theory" {= "dev"}\n  "conf-python-3" {build}\n'
INSTALLED = {"rocq-core": "9.2.0", "coq-graph-theory": "dev"}
PACKAGES = {"base": "base", "chromatic-theory": "chromatic"}


def build_block(directory: str) -> str:
    stage = f"_build/library/{directory}"
    return ("build: [\n"
            f'  ["python3" "-c" "{G.GUARD}"]\n'
            f'  ["python3" "-B" "meta/library_package.py" "{directory}"]\n'
            f'  ["sh" "-c" "cd {stage} && rocq makefile -f _CoqProject -o Makefile.coq"]\n'
            f'  [make "-C" "{stage}" "-f" "Makefile.coq" "-j%{{jobs}}%"]\n'
            "]\n")


def canonical_text(directory: str, depends: str = EXTERNALS, extra: str = PIN, build: str | None = None) -> str:
    # The comment holds what the contract refuses; the gate must never read it (O-d).
    return ("# never read: %{prefix}% [make] {with-test} x-unknown: \"y\"\n"
            'opam-version: "2.0"\n'
            'synopsis: "A fixture package"\n'
            'description: """\nA fixture.\nIt installs public modules only.\n"""\n'
            'maintainer: "Fixture <fixture@example.org>"\n'
            f"depends: [\n{depends}]\n"
            + (build_block(directory) if build is None else build) + extra)


def wrapper_text(canonical: str) -> str:
    return ('# Compatibility wrapper.\nopam-version: "2.0"\nsynopsis: "A wrapper"\n'
            f'depends: [\n  "{canonical}" {{= version}}\n]\n')


def fields_and_entries(name: str, text: str):
    fields = G.parse_opam(text)
    entries, problems = G.depends_of(name, fields)
    return fields, entries, problems


class OpamContract(unittest.TestCase):
    def test_ctl_canonical_file_keeps_the_contract(self):
        fields, entries, problems = fields_and_entries("rocq-graph-theory-base", canonical_text("base"))
        self.assertEqual(problems, [])
        self.assertEqual(G.canonical_problems("rocq-graph-theory-base", fields, "base", entries), [])
        self.assertEqual(fields["build"], G.expected_build("base"))
        self.assertIn("It installs public modules only.", fields["description"][1])
        self.assertEqual(G.pin_depends_commit("rocq-graph-theory-base", fields), (GT_COMMIT, []))

    def test_comments_are_never_read(self):
        tokens = G.opam_tokens(canonical_text("base"))
        self.assertFalse([t for t in tokens if "prefix" in t[1] or t[1] in ("with-test", "x-unknown")])

    def test_jobs_expands_to_the_explicit_value(self):
        build = G.parse_opam(canonical_text("base"))["build"]
        for jobs in (1, 2):
            commands = G.expand(build, jobs)
            self.assertEqual(len(commands), 4)
            self.assertEqual(commands[0], ["python3", "-c", G.GUARD])
            self.assertEqual(commands[1], ["python3", "-B", "meta/library_package.py", "base"])
            self.assertEqual(commands[3], ["make", "-C", "_build/library/base", "-f", "Makefile.coq", f"-j{jobs}"])
            self.assertNotIn("%{", " ".join(" ".join(c) for c in commands))

    def contract(self, text: str, directory: str = "base") -> list[str]:
        fields, entries, problems = fields_and_entries("rocq-graph-theory-base", text)
        return problems + G.canonical_problems("rocq-graph-theory-base", fields, directory, entries)

    def test_n11_another_variable_is_refused(self):
        in_build = canonical_text("base").replace('"Makefile.coq" "-j%{jobs}%"]', '"Makefile.coq" "-j%{jobs}%" "%{prefix}%"]')
        in_text = canonical_text("base").replace('"A fixture package"', '"A fixture %{name}% package"')
        for text in (in_build, in_text):
            self.assertTrue([p for p in self.contract(text) if "opam variables" in p], text)

    def test_n12_a_filtered_command_is_refused(self):
        text = canonical_text("base").replace('"-j%{jobs}%"]\n', '"-j%{jobs}%"] {with-test}\n')
        problems = self.contract(text)
        self.assertTrue([p for p in problems if "4-command contract" in p])
        self.assertTrue([p for p in problems if "build: carries a filter" in p])

    def test_n13_a_fifth_command_or_another_directory_is_refused(self):
        fifth = canonical_text("base").replace('"-j%{jobs}%"]\n', '"-j%{jobs}%"]\n  ["true"]\n')
        other_dir = canonical_text("base").replace("cd _build/library/base", "cd _build/library/atlas")
        for text in (fifth, other_dir):
            self.assertTrue([p for p in self.contract(text) if "4-command contract" in p], text)

    def test_n14_an_unknown_field_is_refused(self):
        problems = self.contract(canonical_text("base") + 'x-ci-accept: "yes"\n')
        self.assertIn("rocq-graph-theory-base: unknown field x-ci-accept", problems)

    def test_constraints_outside_the_contract_are_refused(self):
        lower_bound = self.contract(canonical_text("base", depends='  "rocq-core" {>= "9.2"}\n'))
        internal_pin = self.contract(canonical_text("base", depends=EXTERNALS + '  "rocq-graph-theory-base" {= "1.0"}\n'))
        unpinned = self.contract(canonical_text("base", depends='  "rocq-core"\n'))
        self.assertTrue([p for p in lower_bound if "unsupported constraint" in p])
        self.assertTrue([p for p in internal_pin if "must be {= version}" in p])
        self.assertTrue([p for p in unpinned if "exact pin" in p])
        with self.assertRaises(G.OpamSyntax):
            G.parse_opam('opam-version: "2.0"\ndepends: [ ("a" | "b") ]\n')

    def test_wrappers(self):
        name = "coq-graph-theory-base"
        fields, entries, problems = fields_and_entries(name, wrapper_text("rocq-graph-theory-base"))
        self.assertEqual(problems + G.wrapper_problems(name, fields, entries), [])
        built = wrapper_text("rocq-graph-theory-base") + build_block("base")
        fields, entries, _ = fields_and_entries(name, built)
        self.assertIn(f"{name}: a wrapper has no build:", G.wrapper_problems(name, fields, entries))
        other = wrapper_text("rocq-graph-theory-digraph")
        fields, entries, _ = fields_and_entries(name, other)
        self.assertTrue(G.wrapper_problems(name, fields, entries))

    def test_n7_lint_output(self):
        self.assertEqual(G.lint_output_problems("opam/x.opam", 0, "opam/x.opam: Passed.\n"), [])
        warned = "opam/x.opam: Warnings.\n             warning 25: Missing field 'authors'\n"
        for rc, output in ((0, warned), (1, "opam/x.opam: Errors.\n"), (0, ""), (127, "opam: not found\n")):
            self.assertTrue(G.lint_output_problems("opam/x.opam", rc, output), output)

    def test_repository_opam_files_parse_and_keep_the_build_contract(self):
        opam = G.ROOT / "opam"
        if not opam.is_dir():
            self.skipTest("no opam/ in this tree")
        packages = {G.CANONICAL_PREFIX + s: d for d, s in G.PKG.PACKAGES.items()}
        for path in sorted(opam.glob("*.opam")):
            fields = G.parse_opam(path.read_text(encoding="utf-8"))
            entries, problems = G.depends_of(path.stem, fields)
            _, more = G.pin_depends_commit(path.stem, fields)
            if path.stem in G.WRAPPERS:
                more += G.wrapper_problems(path.stem, fields, entries)
            else:
                more += G.canonical_problems(path.stem, fields, packages[path.stem], entries)
            self.assertEqual(problems + more, [], path.name)


class Pins(unittest.TestCase):
    def files(self, depends: str = EXTERNALS, extra: str = PIN) -> dict:
        fields, entries, _ = fields_and_entries("rocq-graph-theory-base", canonical_text("base", depends, extra))
        pin, _ = G.pin_depends_commit("rocq-graph-theory-base", fields)
        return {"rocq-graph-theory-base": {"depends": entries, "pin": pin}}

    def test_ctl_pins_equal_the_installed_toolchain(self):
        self.assertEqual(G.pin_problems(self.files(), INSTALLED, GT_COMMIT), [])

    def test_n8_pins_unequal_to_the_toolchain_are_refused(self):
        old = EXTERNALS.replace('"9.2.0"', '"9.1.1"').replace('{= "dev"}', '{= "0.9.7"}')
        cases = [
            (self.files(old), INSTALLED, GT_COMMIT),
            (self.files(extra=""), INSTALLED, GT_COMMIT),
            (self.files(), INSTALLED, "c" * 40),
            (self.files(), INSTALLED, None),
            (self.files(), {"rocq-core": "9.2.0", "coq-graph-theory": "0.9.7"}, GT_COMMIT),
        ]
        for files, installed, commit in cases:
            self.assertTrue(G.pin_problems(files, installed, commit), (files, installed, commit))

    def test_pin_depends_shape(self):
        for extra in (f'pin-depends: [["{G.GRAPH_THEORY_PIN}" "{G.GRAPH_THEORY_URL}322e352b"]]\n',
                      f'pin-depends: [["coq-graph-theory.0.9.7" "{G.GRAPH_THEORY_URL}{GT_COMMIT}"]]\n',
                      f'pin-depends: ["{G.GRAPH_THEORY_PIN}" "{G.GRAPH_THEORY_URL}{GT_COMMIT}"]\n'):
            fields = G.parse_opam(canonical_text("base", extra=extra))
            self.assertEqual(G.pin_depends_commit("x", fields)[0], None, extra)
            self.assertTrue(G.pin_depends_commit("x", fields)[1], extra)

    def test_commit_of_record(self):
        with tempfile.TemporaryDirectory(prefix="install-gate-pins-") as name:
            root = Path(name)
            self.assertIsNone(G.graph_theory_commit(root))
            (root / "environment/rocq92").mkdir(parents=True)
            (root / G.PINS).write_text(
                f"path-pin\tcoq-graph-theory\tdev\tUNRELEASED: commit {GT_COMMIT} tree {'d' * 40}; archive\tsrc\n")
            self.assertEqual(G.graph_theory_commit(root), GT_COMMIT)


class SourceIdentity(unittest.TestCase):
    def test_n9_ids_are_required_and_exact(self):
        self.assertEqual(G.source_identity(COMMIT, TREE), {"commit": COMMIT, "tree": TREE, "declared_by": "caller"})
        for bad in (None, "", "HEAD", "a" * 39, "a" * 41, "A" * 40, "a" * 64):
            with self.assertRaises(G.Refused):
                G.source_identity(bad, TREE)
            with self.assertRaises(G.Refused):
                G.source_identity(COMMIT, bad)

    def test_o1_row_paths_normalise_or_refuse(self):
        self.assertEqual(G.normal_row_path("./a/b.v"), "a/b.v")
        self.assertEqual(G.normal_row_path("a/b.v"), "a/b.v")
        for bad in ("/a/b.v", "a/../b.v", "a//b.v", "", "./", "a/./b"):
            self.assertIsNone(G.normal_row_path(bad), bad)

    def test_n10_the_tree_manifest(self):
        with tempfile.TemporaryDirectory(prefix="install-gate-manifest-") as name:
            path = Path(name) / "TREE.sha256"
            path.write_text(f"{'1' * 64}  ./a.v\n{'2' * 64} *b/c.v\n")
            rows = G.tree_manifest(path)
            self.assertEqual(rows, {"a.v": "1" * 64, "b/c.v": "2" * 64})
            self.assertEqual(G.manifest_problems({"a.v": "1" * 64}, rows), [])
            self.assertTrue(G.manifest_problems({"a.v": "3" * 64}, rows))
            self.assertTrue(G.manifest_problems({"d.v": "1" * 64}, rows))
            for text in (f"{'1' * 64}  ./a.v\n{'1' * 64}  a.v\n", f"{'1' * 64}  /abs.v\n", "not a row\n"):
                path.write_text(text)
                with self.assertRaises(G.Refused):
                    G.tree_manifest(path)


class Requires(unittest.TestCase):
    def test_first_sentence_and_comments(self):
        source = ('From GTBase Require Import base common.\n'
                  '(* Require Import Hidden. (* nested *) still hidden *)\n'
                  'Definition s := "(* not a comment".\n'
                  'Require Export Chromatic.foundations.colour.\n'
                  'From mathcomp Require Import (notations) ssreflect.\n')
        self.assertEqual(G.required_modules(source), [
            ("GTBase", "base"), ("GTBase", "common"), (None, "Chromatic.foundations.colour"),
            ("mathcomp", "ssreflect")])

    def test_excluded_copy_paths(self):
        for rel in ("chromatic-theory/theories/conjectures/X1.v", "base/theories/migration/a.v",
                    "digraph-theory/theories/applications/a.v", "base/theories/examples/a.v",
                    "extremal-graph-theory/theories/grounding_D2chr.v", "meta/library_primitives.json"):
            self.assertTrue(G.excluded(rel), rel)
        self.assertFalse(G.excluded("base/theories/base.v"))
        self.assertFalse(G.excluded("meta/library_package.py"))


class Verdicts(unittest.TestCase):
    def test_n2_a_non_public_manifest_entry(self):
        top, stage = "coq/user-contrib/GTBase/", "_build/library/base/theories/"
        entries = [(stage + m + x, top + m + x) for m in ("base", "graphs") for x in (".v", ".vo", ".glob")]
        self.assertEqual(G.entry_problems("p", "base", "GTBase", entries, ["GTBase.base", "GTBase.graphs"]), [])
        leaked = entries + [(stage + "migration/edge_count" + x, top + "migration/edge_count" + x)
                            for x in (".v", ".vo", ".glob")]
        self.assertTrue(G.entry_problems("p", "base", "GTBase", leaked, ["GTBase.base", "GTBase.graphs"]))
        self.assertTrue(G.entry_problems("p", "base", "GTBase", entries[:-1], ["GTBase.base", "GTBase.graphs"]))

    def test_n5_a_stray_prefix_file(self):
        with tempfile.TemporaryDirectory(prefix="install-gate-prefix-") as name:
            prefix = Path(name)
            (prefix / "lib/coq/user-contrib/GTBase").mkdir(parents=True)
            (prefix / "lib/coq/user-contrib/GTBase/base.vo").write_bytes(b"vo")
            self.assertEqual(G.prefix_problems(prefix, {"lib/coq/user-contrib/GTBase/base.vo"}), [])
            (prefix / "lib/coq/user-contrib/GTBase/stray.vo").write_bytes(b"vo")
            self.assertTrue(G.prefix_problems(prefix, {"lib/coq/user-contrib/GTBase/base.vo"}))

    def test_n3_a_repository_load_path_or_environment(self):
        with tempfile.TemporaryDirectory(prefix="install-gate-client-") as name:
            base = Path(name).resolve()
            repo, copy, downstream, prefix_uc = base / "repo", base / "copy", base / "down", base / "prefix/lib"
            for d in (repo, copy, downstream, prefix_uc):
                d.mkdir(parents=True)
            env = {"ROCQPATH": str(prefix_uc), "PATH": "/usr/bin"}
            good = ["rocq", "compile", "-R", ".", "Downstream", "a.v"]
            self.assertEqual(G.client_path_problems(good, env, downstream, prefix_uc, [repo, copy]), [])
            bad = ["rocq", "compile", "-R", ".", "Downstream", "-Q", str(repo / "base/theories"), "GTBase", "a.v"]
            self.assertTrue(G.client_path_problems(bad, env, downstream, prefix_uc, [repo, copy]))
            self.assertTrue(G.client_path_problems(good, dict(env, COQPATH=str(repo)), downstream, prefix_uc, [repo]))
            self.assertTrue(G.client_path_problems(good, dict(env, ROCQPATH=str(repo)), downstream, prefix_uc, [repo]))
            nested = downstream / "uc"  # the prefix inside the client's -R dir: Rocq would remap it (V-a r2 probe)
            nested.mkdir()
            problems = G.client_path_problems(good, dict(env, ROCQPATH=str(nested)), downstream, nested, [repo, copy])
            self.assertEqual(problems, [f"the prefix {nested} is inside the client load path ."])

    def test_c1_the_planted_client_passes_only_by_failing_on_its_module(self):
        error = ('File "./neg__nonpublic.v", line 1, characters 0-48:\n'
                 "Error: Cannot find a physical path bound to logical path\nmigration.edge_count with prefix GTBase.\n")
        self.assertTrue(G.neg_verdict(1, error)[0])
        for rc, output in ((0, ""), (0, error), (1, "Error: Unable to locate library GTBase.\n"),
                           (127, "rocq: No such file or directory\n"), (1, "migration.edge_count was not found\n")):
            self.assertFalse(G.neg_verdict(rc, output)[0], (rc, output))

    def test_c1_planted_client_preconditions(self):
        with tempfile.TemporaryDirectory(prefix="install-gate-neg-") as name:
            root, prefix_uc = Path(name) / "repo", Path(name) / "prefix"
            (prefix_uc / "GTBase/migration").mkdir(parents=True)
            self.assertTrue(G.neg_preconditions(root, prefix_uc, lambda rel: False))
            (root / "base/theories/migration").mkdir(parents=True)
            (root / G.NEG_SOURCE).write_text("Definition x := 0.\n")
            self.assertEqual(G.neg_preconditions(root, prefix_uc, lambda rel: False), [])
            self.assertTrue(G.neg_preconditions(root, prefix_uc, lambda rel: True))
            (prefix_uc / "GTBase/migration/edge_count.vo").write_bytes(b"vo")
            self.assertTrue(G.neg_preconditions(root, prefix_uc, lambda rel: False))

    def test_locate(self):
        prefix_uc = Path("/out/prefix/lib/coq/user-contrib")
        output = ("GTBase.base has been loaded from file\n /out/prefix/lib/coq/user-contrib/GTBase/base.vo\n"
                  "Library GTBase.graphs is bound to file /elsewhere/GTBase/graphs.vo\n")
        found = G.located_files(output, ["GTBase.base", "GTBase.graphs", "GTBase.missing"])
        self.assertEqual(found["GTBase.base"], "/out/prefix/lib/coq/user-contrib/GTBase/base.vo")
        problems = G.locate_problems(found, prefix_uc)
        self.assertEqual(len(problems), 2, problems)

    def test_o3_builds_and_clients_inherit_no_make_or_load_path_overrides(self):
        hostile = {"MAKEFLAGS": "-n -j7", "MAKEOVERRIDES": "COQBIN=/x", "MFLAGS": "-n", "GNUMAKEFLAGS": "-t",
                   "COQFLAGS": "-q", "COQPATH": "/repo", "ROCQPATH": "/repo", "PYTHONPATH": "/elsewhere", "PATH": "/usr/bin"}
        with patch.dict(G.os.environ, hostile, clear=True):
            env = G.client_env(Path("/out/prefix/lib/coq/user-contrib"))
        self.assertEqual((env["ROCQPATH"], env["PATH"], env.get("MAKEFLAGS")),
                         ("/out/prefix/lib/coq/user-contrib", "/usr/bin", "-j7"))
        for key in ("MAKEOVERRIDES", "MFLAGS", "GNUMAKEFLAGS", "COQFLAGS", "COQPATH", "PYTHONPATH"):
            self.assertNotIn(key, env)


# ── the fixture tree, with a fake runner for the tools ──

FIXTURE_SOURCES = {
    "base/_CoqProject": "-R theories GTBase\n-arg -w -arg -notation-overridden\n\ntheories/base.v\n"
                        "theories/graphs.v\ntheories/migration/edge_count.v\ntheories/examples/demo.v\n",
    "base/theories/base.v": "From mathcomp Require Import ssreflect.\nDefinition b := 0.\n",
    "base/theories/graphs.v": "From GTBase Require Import base.\nDefinition g := b.\n",
    "base/theories/migration/edge_count.v": "From GTBase Require Import base.\n",
    "base/theories/examples/demo.v": "From GTBase Require Import graphs.\n",
    "chromatic-theory/_CoqProject": "-R theories Chromatic\n-Q ../base/theories GTBase\n\n"
                                    "theories/foundations/colour.v\ntheories/conjectures/X1.v\ntheories/examples/ex.v\n",
    "chromatic-theory/theories/foundations/colour.v": "From GTBase Require Import base.\n",
    "chromatic-theory/theories/conjectures/X1.v": "From Chromatic Require Import foundations.colour.\n",
    "chromatic-theory/theories/examples/ex.v": "From Chromatic Require Import foundations.colour.\n"
                                               "From GTBase Require Import base.\n",
    G.PINS: f"path-pin\tcoq-graph-theory\tdev\tUNRELEASED: commit {GT_COMMIT} tree {'d' * 40}\tsrc\n",
}


def make_fixture(root: Path) -> None:
    (root / "meta").mkdir(parents=True)
    for reader in G.READERS:
        shutil.copyfile(G.META / reader, root / "meta" / reader)
    for rel, text in FIXTURE_SOURCES.items():
        (root / rel).parent.mkdir(parents=True, exist_ok=True)
        (root / rel).write_text(text)
    (root / "opam").mkdir()
    (root / "opam/rocq-graph-theory-base.opam").write_text(canonical_text("base"))
    (root / "opam/rocq-graph-theory-chromatic.opam").write_text(
        canonical_text("chromatic-theory", '  "rocq-graph-theory-base" {= version}\n' + EXTERNALS))
    for wrapper, canonical in G.WRAPPERS.items():
        (root / f"opam/{wrapper}.opam").write_text(wrapper_text(canonical))
    for old, new in G.LEGACY_COPIES.items():
        (root / old).parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(root / new, root / old)


class FakeTools:
    """opam, opam-installer and rocq as the gate calls them; library_package.py runs for real."""

    def __init__(self, neg_rc: int = 1):
        self.calls: list[list[str]] = []
        self.neg_rc = neg_rc

    def __call__(self, argv, *, cwd, env, log=None):
        self.calls.append(list(argv))
        rc, output = self.result(list(argv), Path(cwd), env)
        if log is not None:
            log.write_text(f"$ {' '.join(argv)}\n{output}# rc {rc}\n")
        return rc, output

    def result(self, argv, cwd, env):
        if argv[:2] == ["opam", "lint"]:
            return 0, f"{argv[2]}: Passed.\n"
        if argv == G.OPAM_LIST:
            return 0, "".join(f"{k}   {v}\n" for k, v in INSTALLED.items())
        if argv[1:] == ["--version"]:
            return 0, f"{argv[0]} fake\n"
        if argv[:2] == ["python3", "-c"]:
            return 0, ""
        if argv[:3] == ["python3", "-B", "meta/library_package.py"]:
            return ORIGINAL_RUN([sys.executable, *argv[1:]], cwd=cwd, env=env)
        if argv[:2] == ["sh", "-c"]:
            return 0, ""
        if argv[0] == "make":
            for source in (cwd / argv[2] / "theories").rglob("*.v"):
                source.with_suffix(".vo").write_bytes(b"vo " + source.read_bytes())
                source.with_suffix(".glob").write_bytes(b"glob")
            return 0, ""
        if argv[0] == "opam-installer":
            prefix = Path(argv[1].split("=", 1)[1])
            for source, destination in G.install_entries((cwd / argv[2]).read_text()):
                (prefix / "lib" / destination).parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(cwd / source, prefix / "lib" / destination)
            return 0, ""
        if argv[:2] == ["rocq", "compile"]:
            if argv[-1] == G.LOCATE_PROBE:
                modules = [line.split()[2].rstrip(".") for line in (cwd / argv[-1]).read_text().splitlines()]
                return 0, "".join(f"{m} has been loaded from file {env['ROCQPATH']}/{m.replace('.', '/')}.vo\n"
                                  for m in modules)
            if argv[-1] == G.NEG_CLIENT:
                if self.neg_rc == 0:
                    return 0, ""
                return 1, ('File "./neg__nonpublic.v", line 1, characters 0-48:\nError: Cannot find a physical '
                           "path bound to logical path\nmigration.edge_count with prefix GTBase.\n")
            return 0, ""
        return 127, f"unexpected command {argv}\n"


ORIGINAL_RUN = G.run_command


class GateFixture(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="install-gate-fixture-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve() / "repo"
        self.out = Path(temporary.name).resolve() / "out"
        make_fixture(self.root)
        patcher = patch.object(G.PKG, "PACKAGES", PACKAGES)
        patcher.start()
        self.addCleanup(patcher.stop)

    def run_gate(self, tools: FakeTools, tree_sha256: Path | None = None) -> tuple[int, dict]:
        args = argparse.Namespace(out=self.out, source_commit=COMMIT, source_tree=TREE, tree_sha256=tree_sha256,
                                  jobs=1, expect_examples=2, lint_only=False)
        with patch.object(G, "run_command", tools):
            rc = G.gate(self.root, args)
        return rc, json.loads((self.out / "install-gate.json").read_text())

    def test_ctl_the_fixture_passes_with_the_declared_identity(self):
        tools = FakeTools()
        rc, receipt = self.run_gate(tools)
        self.assertEqual((rc, receipt["verdict"]), (0, "PASS"), receipt["problems"])
        self.assertEqual(receipt["source"], {"commit": COMMIT, "tree": TREE, "declared_by": "caller"})
        rows = (self.out / "inputs.sha256").read_text()
        self.assertEqual(receipt["inputs"]["sha256"], hashlib.sha256(rows.encode()).hexdigest())
        self.assertIsNone(receipt["tree_sha256"])  # O-2
        # C-2: the digest covers the examples and the gate itself, not only the copied files.
        for rel in ("base/theories/examples/demo.v", "chromatic-theory/theories/examples/ex.v",
                    "meta/install_gate.py", "meta/library_package.py", "opam/rocq-graph-theory-base.opam"):
            self.assertIn(f"  ./{rel}\n", rows, rel)
        self.assertNotIn("conjectures", rows)
        self.assertEqual(receipt["order"], ["rocq-graph-theory-base", "rocq-graph-theory-chromatic"])
        self.assertEqual(receipt["prefix_files"], 9)
        self.assertTrue(receipt["planted_client"]["passed"])
        self.assertEqual(sorted(receipt["locate"]), ["Chromatic.foundations.colour", "GTBase.base", "GTBase.graphs"])
        self.assertTrue(receipt["final"].startswith("INSTALL_GATE PASS: 2 packages, 3 public modules, 9 prefix files, "
                                                    "2 examples, 0 failed"), receipt["final"])
        self.assertFalse((self.out / "copy/chromatic-theory/theories/conjectures").exists())
        # C-1: the planted client compiles only after every positive client.
        compiles = [c[-1] for c in tools.calls if c[:2] == ["rocq", "compile"]]
        self.assertEqual(compiles[-1], G.NEG_CLIENT)
        self.assertEqual(sorted(compiles[:2]), ["Chromatic__ex.v", "GTBase__demo.v"])
        # Every make call is either tool_versions' one `make --version` (which V-a r2's filter caught) or a package build at -j1.
        makes = [c for c in tools.calls if c[:1] == ["make"]]
        self.assertEqual(makes.count(["make", "--version"]), 1)
        self.assertEqual([c for c in makes if c != ["make", "--version"]],
                         [["make", "-C", f"_build/library/{d}", "-f", "Makefile.coq", "-j1"] for d in ("base", "chromatic-theory")])

    def test_a_planted_client_that_compiles_fails_the_gate(self):
        rc, receipt = self.run_gate(FakeTools(neg_rc=0))
        self.assertEqual(rc, 1)
        self.assertTrue([p for p in receipt["problems"] if "planted client" in p], receipt["problems"])

    def test_the_tree_manifest_binds_every_input(self):
        rows = "".join(f"{hashlib.sha256(p.read_bytes()).hexdigest()}  ./{p.relative_to(self.root).as_posix()}\n"
                       for p in sorted(self.root.rglob("*")) if p.is_file())
        rows += f"{hashlib.sha256((G.META / 'install_gate.py').read_bytes()).hexdigest()}  ./meta/install_gate.py\n"
        manifest = self.root.parent / "TREE.sha256"
        manifest.write_text(rows)
        rc, receipt = self.run_gate(FakeTools(), manifest)
        self.assertEqual(rc, 0, receipt["problems"])
        self.assertEqual(receipt["tree_sha256"], hashlib.sha256(rows.encode()).hexdigest())

    def test_a_changed_input_fails_the_manifest(self):
        manifest = self.root.parent / "TREE.sha256"
        manifest.write_text(f"{'0' * 64}  ./base/theories/base.v\n")
        rc, receipt = self.run_gate(FakeTools(), manifest)
        self.assertEqual(rc, 1)
        self.assertTrue([p for p in receipt["problems"] if p.startswith("copy: base/theories/base.v: sha256")])

    def static_problems(self) -> list[str]:
        return G.metadata(self.root)[1]

    def test_ctl_static(self):
        self.assertEqual(self.static_problems(), [])

    def test_n1_an_example_importing_a_corpus_module(self):
        (self.root / "chromatic-theory/theories/examples/ex.v").write_text("From Chromatic Require Import conjectures.X1.\n")
        self.assertTrue([p for p in self.static_problems() if p.startswith("LEAK ")])

    def test_n4_a_barrier(self):
        (self.root / "chromatic-theory/theories/foundations/colour.v").write_text(
            "From Chromatic Require Import conjectures.X1.\n")
        self.assertTrue([p for p in self.static_problems() if p.startswith("BARRIER ")])

    def test_n6_an_example_importing_an_example(self):
        (self.root / "chromatic-theory/theories/examples/ex.v").write_text("From GTBase Require Import examples.demo.\n")
        self.assertTrue([p for p in self.static_problems() if p.startswith("EXAMPLE ")])

    def test_internal_depends_must_equal_the_imports(self):
        (self.root / "opam/rocq-graph-theory-chromatic.opam").write_text(canonical_text("chromatic-theory"))
        self.assertTrue([p for p in self.static_problems() if "internal depends" in p])

    def test_legacy_copies_must_stay_byte_equal(self):
        (self.root / "base/coq-graph-theory-base.opam").write_text(wrapper_text("rocq-graph-theory-base") + "# edit\n")
        self.assertIn("base/coq-graph-theory-base.opam: not byte-equal to opam/coq-graph-theory-base.opam",
                      self.static_problems())

    def test_refusals_before_anything_runs(self):
        tools = FakeTools()
        cases = [dict(source_commit=None), dict(source_tree="HEAD"), dict(out=self.root / "inside")]
        for case in cases:
            args = argparse.Namespace(**{**dict(out=self.out, source_commit=COMMIT, source_tree=TREE, tree_sha256=None,
                                                jobs=1, expect_examples=None, lint_only=False), **case})
            with patch.object(G, "run_command", tools), self.assertRaises(G.Refused):
                G.gate(self.root, args)
        self.assertEqual(tools.calls, [])
        self.assertFalse(self.out.exists())
        self.assertFalse((self.root / "inside").exists())


if __name__ == "__main__":
    unittest.main(verbosity=2)
