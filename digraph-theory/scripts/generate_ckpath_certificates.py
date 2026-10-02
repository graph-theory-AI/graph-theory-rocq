#!/usr/bin/env python3
"""Generate and validate the finite CK-path endgame certificates.

The generated CNFs use the same deterministic variable and clause order as
``ckpath_cert_base.v``.  Given a Z3 DRAT trace, this script removes deletion
records and annotates every retained RUP addition with the exact zero-based
clause identifiers used for unit propagation.  Those identifiers are consumed
by the transparent checker in ``ckpath_drup.v``.

This is an untrusted build-time tool: Rocq recomputes every hinted propagation.
"""

from __future__ import annotations

import argparse
from collections import defaultdict, deque
from dataclasses import dataclass
from itertools import combinations, product
from pathlib import Path
from typing import Iterable, Iterator, Sequence


Clause = tuple[int, ...]


class CNF:
    def __init__(self, truth_table: bool = False) -> None:
        self.ids: dict[tuple[object, ...], int] = {}
        self.clauses: list[Clause] = []
        self.truth_table = truth_table

    def var(self, key: tuple[object, ...]) -> int:
        if key not in self.ids:
            self.ids[key] = len(self.ids) + 1
        return self.ids[key]

    def add(self, *literals: int) -> None:
        self.clauses.append(tuple(literals))

    def at_least(self, variables: Sequence[int], k: int,
                 guard: Clause = ()) -> None:
        if self.truth_table:
            for row in product((False, True), repeat=len(variables)):
                if sum(row) < k:
                    self.add(*guard,
                             *(variable if not bit else -variable
                               for variable, bit in zip(variables, row)))
            return
        for subset in combinations(variables, len(variables) - k + 1):
            self.add(*guard, *subset)

    def at_most(self, variables: Sequence[int], k: int,
                guard: Clause = ()) -> None:
        if self.truth_table:
            for row in product((False, True), repeat=len(variables)):
                if sum(row) > k:
                    self.add(*guard,
                             *(variable if not bit else -variable
                               for variable, bit in zip(variables, row)))
            return
        for subset in combinations(variables, k + 1):
            self.add(*guard, *(-x for x in subset))

    def exactly(self, variables: Sequence[int], k: int,
                guard: Clause = ()) -> None:
        self.at_least(variables, k, guard)
        self.at_most(variables, k, guard)

    def write_dimacs(self, path: Path) -> None:
        with path.open("w", encoding="ascii") as stream:
            stream.write(f"p cnf {len(self.ids)} {len(self.clauses)}\n")
            for clause in self.clauses:
                stream.write(" ".join(map(str, clause)) + " 0\n")


def cyclic_order(endpoint: int, n: int) -> tuple[int, ...]:
    return tuple((endpoint + 1 + offset) % n for offset in range(n))


def two_chord_rotation(endpoint: int, i: int, j: int,
                       n: int) -> tuple[int, ...]:
    word = cyclic_order(endpoint, n)
    return word[i:j + 1] + word[:i] + word[j + 1:]


def three_chord_rotation(endpoint: int, cut: int) -> tuple[int, ...]:
    word = cyclic_order(endpoint, 11)
    return word[cut + 1:10] + (word[cut],) + word[:cut] + (word[10],)


def reverse_three_block_rotation(endpoint: int, a: int, b: int, c: int,
                                 n: int) -> tuple[int, ...]:
    """Read four nonempty consecutive blocks ``A|B|C|D`` as ``C|B|A|D``."""
    word = cyclic_order(endpoint, n)
    return word[b:c] + word[a:b] + word[:a] + word[c:]


def noncycle_chords(path: Sequence[int], n: int) -> tuple[tuple[int, int], ...]:
    return tuple((u, v) for u, v in zip(path, path[1:])
                 if v != (u + 1) % n)


def add_cycle_arcs(cnf: CNF, n: int) -> dict[tuple[int, int], int]:
    arcs = {(u, v): cnf.var(("e", u, v))
            for u in range(n) for v in range(n) if u != v}
    for u in range(n):
        for v in range(u + 1, n):
            cnf.add(-arcs[u, v], -arcs[v, u])
    for u in range(n):
        cnf.add(arcs[u, (u + 1) % n])
    return arcs


def internal_row(arcs: dict[tuple[int, int], int], n: int,
                 endpoint: int) -> list[int]:
    """Arc variables other than loop, cycle successor, and cycle predecessor."""
    return [arcs[endpoint, v] for v in range(n)
            if v not in (endpoint, (endpoint + 1) % n,
                         (endpoint - 1) % n)]


def two_chord_rotations(endpoint: int, n: int) -> Iterator[tuple[int, ...]]:
    for i in range(1, n - 1):
        for j in range(i, n - 1):
            yield two_chord_rotation(endpoint, i, j, n)


def reverse_three_block_rotations(endpoint: int,
                                  n: int) -> Iterator[tuple[int, ...]]:
    for a in range(1, n - 2):
        for b in range(a + 1, n - 1):
            for c in range(b + 1, n):
                yield reverse_three_block_rotation(endpoint, a, b, c, n)


def c9_instance(normalized: bool = False, truth_table: bool = False) -> CNF:
    """Negation of the C9 rotation-union lemma used in the k=5 proof."""
    n = 9
    cnf = CNF(truth_table)
    arcs = add_cycle_arcs(cnf, n)
    active = [cnf.var(("a", v)) for v in range(n)]
    covered = [cnf.var(("m", v)) for v in range(n)]
    cnf.exactly(active, 3)
    cnf.at_most(covered, 5)
    if normalized:
        cnf.add(active[0])
    for endpoint in range(n):
        # The original directed Hamilton path starts at successor(endpoint).
        cnf.add(-active[endpoint], covered[(endpoint + 1) % n])
        # Vertices outside the active set have internal outdegree exactly five.
        row = [arcs[endpoint, v] for v in range(n)
               if v not in (endpoint, (endpoint + 1) % n,
                            (endpoint - 1) % n)]
        cnf.exactly(row, 4, guard=(active[endpoint],))
        # Every available two-chord rotation contributes its starting vertex.
        for i in range(1, n - 1):
            for j in range(i, n - 1):
                path = two_chord_rotation(endpoint, i, j, n)
                chords = noncycle_chords(path, n)
                assert len(chords) == 2
                cnf.add(-active[endpoint], covered[path[0]],
                        *(-arcs[arc] for arc in chords))
    return cnf


def c10_instance(normalized: bool = False, truth_table: bool = False) -> CNF:
    """Negation of the C10 'at most one bad endpoint' lemma for k=6."""
    n = 10
    cnf = CNF(truth_table)
    arcs = add_cycle_arcs(cnf, n)
    selected = [cnf.var(("s", v)) for v in range(n)]
    bad = [cnf.var(("b", v)) for v in range(n)]
    cnf.exactly(selected, 6)
    if normalized:
        cnf.add(bad[0])
    for endpoint in range(n):
        row = [arcs[endpoint, v] for v in range(n)
               if v not in (endpoint, (endpoint + 1) % n,
                            (endpoint - 1) % n)]
        cnf.exactly(row, 5, guard=(-selected[endpoint],))
        cnf.add(-bad[endpoint], -selected[endpoint])
        for i in range(1, n - 1):
            for j in range(i, n - 1):
                path = two_chord_rotation(endpoint, i, j, n)
                chords = noncycle_chords(path, n)
                assert len(chords) == 2
                start = path[0]
                predecessor = (start - 1) % n
                cnf.add(-bad[endpoint], -selected[predecessor],
                        *(-arcs[arc] for arc in chords))
    cnf.at_least(bad, 2)
    return cnf


def c11_instance(active_size: int, normalized: bool = False,
                 truth_table: bool = False) -> CNF:
    """Negation of the C11 rotation-cover lemma for active size 3 or 4."""
    assert active_size in (3, 4)
    n = 11
    cnf = CNF(truth_table)
    arcs = add_cycle_arcs(cnf, n)
    active = [cnf.var(("a", v)) for v in range(n)]
    covered = [cnf.var(("m", v)) for v in range(n)]
    cnf.exactly(active, active_size)
    # We need only prove that at least six starts are covered.
    cnf.at_most(covered, 5)
    if normalized:
        cnf.add(active[0])
    for endpoint in range(n):
        cnf.add(-active[endpoint], covered[(endpoint + 1) % n])
        row = [arcs[endpoint, v] for v in range(n)
               if v not in (endpoint, (endpoint + 1) % n,
                            (endpoint - 1) % n)]
        cnf.exactly(row, 5, guard=(active[endpoint],))
        paths = [two_chord_rotation(endpoint, i, j, n)
                 for i in range(1, n - 1)
                 for j in range(i, n - 1)]
        if active_size == 3:
            paths.extend(three_chord_rotation(endpoint, cut)
                         for cut in range(1, 9))
        for path in paths:
            chords = noncycle_chords(path, n)
            assert len(chords) in (2, 3)
            cnf.add(-active[endpoint], covered[path[0]],
                    *(-arcs[arc] for arc in chords))
    return cnf


def c11_k7_bad_instance(normalized: bool = False,
                        truth_table: bool = False) -> CNF:
    """Negation of the k=7 C11 at-most-one-bad-endpoint lemma."""
    n = 11
    cnf = CNF(truth_table)
    arcs = add_cycle_arcs(cnf, n)
    selected = [cnf.var(("s", v)) for v in range(n)]
    bad = [cnf.var(("b", v)) for v in range(n)]
    cnf.exactly(selected, 6)
    if normalized:
        cnf.add(bad[0])
    for endpoint in range(n):
        cnf.exactly(internal_row(arcs, n, endpoint), 6,
                    guard=(-selected[endpoint],))
        cnf.add(-bad[endpoint], -selected[endpoint])
        for path in two_chord_rotations(endpoint, n):
            chords = noncycle_chords(path, n)
            assert len(chords) == 2
            predecessor = (path[0] - 1) % n
            cnf.add(-bad[endpoint], -selected[predecessor],
                    *(-arcs[arc] for arc in chords))
    cnf.at_least(bad, 2)
    return cnf


def c12_k7_cover_instance(active_size: int, normalized: bool = False,
                          truth_table: bool = False) -> CNF:
    """Negation of the k=7 C12 five-cover lemma."""
    assert active_size in (3, 4)
    n = 12
    cnf = CNF(truth_table)
    arcs = add_cycle_arcs(cnf, n)
    active = [cnf.var(("a", v)) for v in range(n)]
    covered = [cnf.var(("m", v)) for v in range(n)]
    cnf.exactly(active, active_size)
    cnf.at_most(covered, 5)
    if normalized:
        cnf.add(active[0])
    for endpoint in range(n):
        cnf.add(-active[endpoint], covered[(endpoint + 1) % n])
        row = internal_row(arcs, n, endpoint)
        cnf.exactly(row, 6, guard=(active[endpoint],))
        cnf.at_most(row, 5, guard=(-active[endpoint],))
        for path in two_chord_rotations(endpoint, n):
            chords = noncycle_chords(path, n)
            assert len(chords) == 2
            cnf.add(-active[endpoint], covered[path[0]],
                    *(-arcs[arc] for arc in chords))
    return cnf


def c12_k7_low_bad_instance(normalized: bool = False,
                            truth_table: bool = False) -> CNF:
    """Negation of the k=7 C12 aggregate low-endpoint lemma."""
    n = 12
    cnf = CNF(truth_table)
    arcs = add_cycle_arcs(cnf, n)
    selected = [cnf.var(("s", v)) for v in range(n)]
    low = [cnf.var(("l", v)) for v in range(n)]
    cnf.exactly(selected, 7)
    if normalized:
        cnf.add(selected[0])
    for endpoint in range(n):
        row = internal_row(arcs, n, endpoint)
        cnf.exactly(row, 6, guard=(-selected[endpoint],))
        cnf.at_most(row, 6, guard=(selected[endpoint],))
        cnf.at_least(row, 4, guard=(selected[endpoint], low[endpoint]))
        for path in two_chord_rotations(endpoint, n):
            chords = noncycle_chords(path, n)
            assert len(chords) == 2
            predecessor = (path[0] - 1) % n
            cnf.add(selected[endpoint], -low[endpoint],
                    -selected[predecessor],
                    *(-arcs[arc] for arc in chords))
    return cnf


def c13_k7_cover_instance(active_size: int, normalized: bool = False,
                          truth_table: bool = False) -> CNF:
    """Negation of the k=7 C13 six-cover block-rotation lemma."""
    assert active_size in (3, 4, 5)
    n = 13
    cnf = CNF(truth_table)
    arcs = add_cycle_arcs(cnf, n)
    active = [cnf.var(("a", v)) for v in range(n)]
    covered = [cnf.var(("m", v)) for v in range(n)]
    cnf.exactly(active, active_size)
    cnf.at_most(covered, 6)
    if normalized:
        cnf.add(active[0])
    for endpoint in range(n):
        cnf.add(-active[endpoint], covered[(endpoint + 1) % n])
        row = internal_row(arcs, n, endpoint)
        cnf.exactly(row, 6, guard=(active[endpoint],))
        cnf.at_most(row, 5, guard=(-active[endpoint],))
        paths = list(two_chord_rotations(endpoint, n))
        paths.extend(reverse_three_block_rotations(endpoint, n))
        for path in paths:
            chords = noncycle_chords(path, n)
            assert len(chords) in (2, 3)
            cnf.add(-active[endpoint], covered[path[0]],
                    *(-arcs[arc] for arc in chords))
    return cnf


def checked_fixed_set_assignment(
        cnf: CNF, instance_name: str,
        encoded_mask: str) -> list[tuple[int, bool]]:
    """Validate a fixed mask and return its already allocated variables."""
    specifications = {
        "c12_low_bad": ("s", 12, 7),
        "c13_cover_3": ("a", 13, 3),
        "c13_cover_4": ("a", 13, 4),
        "c13_cover_5": ("a", 13, 5),
    }
    if instance_name not in specifications:
        raise ValueError(
            f"fixed masks are not supported for instance {instance_name}")
    set_key, length, weight = specifications[instance_name]
    if len(encoded_mask) != length or any(bit not in "01"
                                           for bit in encoded_mask):
        raise ValueError(
            f"fixed mask for {instance_name} must contain exactly "
            f"{length} zero/one digits")
    bits = [bit == "1" for bit in encoded_mask]
    if sum(bits) != weight:
        raise ValueError(
            f"fixed mask for {instance_name} must have weight {weight}")
    if not bits[0]:
        raise ValueError("fixed mask must be rooted at vertex zero")
    return [(cnf.ids[(set_key, vertex)], bit)
            for vertex, bit in enumerate(bits)]


def append_fixed_set_units(cnf: CNF, instance_name: str,
                           encoded_mask: str) -> None:
    """Append the exact unit-clause suffix used by [fixed_set_instance].

    The normalized k=7 Rocq bases already contain the distinguished
    vertex-zero unit before their endpoint clauses.  These units are appended
    afterwards, matching [base ++ fixed_set_units n mask] literally (including
    the harmless repeated positive unit at vertex zero).
    """
    for variable, bit in checked_fixed_set_assignment(
            cnf, instance_name, encoded_mask):
        cnf.add(variable if bit else -variable)


def specialize_variables(cnf: CNF,
                         assignment_items: Sequence[tuple[int, bool]]) -> None:
    """Substitute variables, preserving residual literal and clause order."""
    assignment = dict(assignment_items)
    residual: list[Clause] = []
    for clause in cnf.clauses:
        specialized: list[int] = []
        satisfied = False
        for literal in clause:
            variable = abs(literal)
            if variable not in assignment:
                specialized.append(literal)
                continue
            literal_value = (literal > 0) == assignment[variable]
            if literal_value:
                satisfied = True
                break
        if not satisfied:
            residual.append(tuple(specialized))
    cnf.clauses = residual


def specialize_fixed_set(cnf: CNF, instance_name: str,
                         encoded_mask: str) -> None:
    """Substitute fixed set variables, preserving residual clause order."""
    specialize_variables(
        cnf, checked_fixed_set_assignment(cnf, instance_name, encoded_mask))


def specialize_true_marks(cnf: CNF, instance_name: str,
                          encoded_vertices: str) -> None:
    """Set selected mark variables true for a bounded split subproblem."""
    if instance_name != "c12_low_bad":
        raise ValueError("--true-marks currently supports only c12_low_bad")
    try:
        vertices = [int(value) for value in encoded_vertices.split(",")
                    if value != ""]
    except ValueError as error:
        raise ValueError("true-mark vertices must be comma-separated naturals") \
            from error
    if not vertices or len(vertices) != len(set(vertices)):
        raise ValueError("true-mark vertices must be nonempty and distinct")
    if any(vertex < 0 or vertex >= 12 for vertex in vertices):
        raise ValueError("true-mark vertices must lie in [0,12)")
    specialize_variables(
        cnf, [(cnf.ids[("l", vertex)], True) for vertex in vertices])


def specialize_low_vertices(cnf: CNF, instance_name: str,
                            encoded_vertices: str) -> None:
    """Substitute vertices as both outside the set and marked low."""
    if instance_name != "c12_low_bad":
        raise ValueError("--low-vertices currently supports only c12_low_bad")
    try:
        vertices = [int(value) for value in encoded_vertices.split(",")
                    if value != ""]
    except ValueError as error:
        raise ValueError("low vertices must be comma-separated naturals") \
            from error
    if not vertices or len(vertices) != len(set(vertices)):
        raise ValueError("low vertices must be nonempty and distinct")
    if any(vertex < 0 or vertex >= 12 for vertex in vertices):
        raise ValueError("low vertices must lie in [0,12)")
    specialize_variables(
        cnf,
        [(cnf.ids[("s", vertex)], False) for vertex in vertices] +
        [(cnf.ids[("l", vertex)], True) for vertex in vertices])


def specialize_low_mask(cnf: CNF, instance_name: str,
                        encoded_mask: str) -> None:
    """Assert each true mask position is an outside, marked-low vertex."""
    if len(encoded_mask) != 12 or any(bit not in "01"
                                      for bit in encoded_mask):
        raise ValueError("low mask must contain exactly 12 zero/one digits")
    vertices = [vertex for vertex, bit in enumerate(encoded_mask)
                if bit == "1"]
    specialize_low_vertices(
        cnf, instance_name, ",".join(str(vertex) for vertex in vertices))


def append_c12_low_cardinality_strengthening(cnf: CNF, lower: int) -> None:
    """Append [Low subset complement S] and a cardinality lower bound."""
    if not 0 <= lower <= 12:
        raise ValueError("the C12 low-cardinality bound must lie in [0,12]")
    selected = [cnf.ids[("s", vertex)] for vertex in range(12)]
    low = [cnf.ids[("l", vertex)] for vertex in range(12)]
    for selected_variable, low_variable in zip(selected, low):
        cnf.add(-low_variable, -selected_variable)
    cnf.at_least(low, lower)


def append_c12_low_mark_degree_strengthening(cnf: CNF) -> None:
    """Make every true low mark certify internal outdegree at most three."""
    arcs = {(u, v): cnf.ids[("e", u, v)]
            for u in range(12) for v in range(12) if u != v}
    for endpoint in range(12):
        low_variable = cnf.ids[("l", endpoint)]
        cnf.at_most(internal_row(arcs, 12, endpoint), 3,
                    guard=(-low_variable,))


def append_c13_low_root_strengthening(cnf: CNF,
                                      instance_name: str) -> None:
    """Bound the internal row of a minimum-degree active root.

    In the graph argument the 13-cycle is rooted at an active gateway whose
    cycle outdegree is at most ``active_size - 1``.  Its cycle successor is
    always an out-neighbour and the cycle predecessor never is, so the ten
    non-cycle-neighbour variables in row zero contain at most
    ``active_size - 2`` true entries.  Choosing the outside vertex witnessed
    by that active root also forces covered/mark vertex zero true by
    orientedness.
    """
    active_sizes = {
        "c13_cover_3": 3,
        "c13_cover_4": 4,
        "c13_cover_5": 5,
    }
    if instance_name not in active_sizes:
        raise ValueError(
            "--c13-low-root requires a c13_cover_3/4/5 instance")
    cnf.add(cnf.ids[("m", 0)])
    arcs = {(u, v): cnf.ids[("e", u, v)]
            for u in range(13) for v in range(13) if u != v}
    cnf.at_most(internal_row(arcs, 13, 0),
                active_sizes[instance_name] - 2)


def append_c13_orbit_union_strengthening(cnf: CNF,
                                         instance_name: str) -> None:
    """Keep all canonical active-set necklaces in one rooted formula.

    The normalized base already fixes active vertex zero.  Among the rooted
    fixed-weight masks, block exactly those which are not the canonical
    representative of a cyclic orbit.  This preserves one mask per orbit
    without generating a separate certificate for every representative.
    Choosing the outside witness of the canonical active root also forces
    mark vertex zero.
    """
    active_sizes = {
        "c13_cover_3": 3,
        "c13_cover_4": 4,
        "c13_cover_5": 5,
    }
    if instance_name not in active_sizes:
        raise ValueError(
            "--c13-orbit-union requires a c13_cover_3/4/5 instance")
    active_size = active_sizes[instance_name]
    active = [cnf.ids[("a", vertex)] for vertex in range(13)]
    representatives = set(orbit_representative_masks(13, active_size))
    if len(representatives) not in (22, 55, 99):
        raise AssertionError("unexpected C13 orbit-representative count")
    if any(mask[0] != "1" for mask in representatives):
        raise AssertionError("C13 orbit representatives must be rooted")

    cnf.add(cnf.ids[("m", 0)])
    for bits in product((False, True), repeat=13):
        if not bits[0] or sum(bits) != active_size:
            continue
        encoded = "".join("1" if bit else "0" for bit in bits)
        if encoded in representatives:
            continue
        cnf.add(*( -variable if bit else variable
                   for variable, bit in zip(active, bits)))


def orbit_representative_masks(length: int, weight: int) -> list[str]:
    """Mirror [orbit_representatives] from [ckpath_k7_orbits.v].

    Enumeration is false-prefix first, canonical comparison orders true before
    false, and newly discovered representatives are prepended.  Keeping the
    otherwise slightly unusual final order identical lets a generated Rocq
    coverage theorem close by computation.
    """
    if not 0 <= weight <= length:
        raise ValueError("orbit weight must lie between zero and the length")

    def rotations(word: tuple[bool, ...]) -> Iterator[tuple[bool, ...]]:
        for offset in range(length):
            yield word[offset:] + word[:offset]

    def comparison_key(word: tuple[bool, ...]) -> tuple[int, ...]:
        return tuple(0 if bit else 1 for bit in word)

    representatives: list[tuple[bool, ...]] = []
    for word in product((False, True), repeat=length):
        if sum(word) != weight:
            continue
        representative = min(rotations(word), key=comparison_key)
        if representative not in representatives:
            representatives.insert(0, representative)
    return ["".join("1" if bit else "0" for bit in word)
            for word in representatives]


def read_dimacs(path: Path) -> tuple[int, list[Clause]]:
    variable_count = 0
    clauses: list[Clause] = []
    with path.open(encoding="ascii") as stream:
        for line in stream:
            if line.startswith("p "):
                variable_count = int(line.split()[2])
            elif line and line[0] not in "c%0\n":
                clauses.append(tuple(map(int, line.split()[:-1])))
    return variable_count, clauses


def read_drat_additions(path: Path) -> Iterator[Clause]:
    with path.open(encoding="ascii") as stream:
        for line in stream:
            if line.strip() and not line.startswith("d "):
                yield tuple(map(int, line.split()[:-1]))


@dataclass
class HintedAddition:
    clause: Clause
    hints: list[int]


class WatchedDatabase:
    """Fast RUP checker which also returns a checker-valid propagation chain."""

    def __init__(self, variable_count: int, clauses: Iterable[Clause]) -> None:
        self.variable_count = variable_count
        self.clauses: list[Clause] = []
        self.watches: list[tuple[int, int]] = []
        self.watch_lists: defaultdict[int, list[int]] = defaultdict(list)
        self.units: list[tuple[int, int]] = []
        self.has_empty = False
        for clause in clauses:
            self.add(clause)

    def add(self, clause: Clause) -> None:
        identifier = len(self.clauses)
        self.clauses.append(clause)
        if not clause:
            self.has_empty = True
            self.watches.append((0, 0))
        elif len(clause) == 1:
            self.units.append((identifier, clause[0]))
            self.watches.append((0, 0))
        else:
            self.watches.append((0, 1))
            self.watch_lists[clause[0]].append(identifier)
            self.watch_lists[clause[1]].append(identifier)

    def hinted_rup(self, target: Clause) -> list[int] | None:
        if self.has_empty:
            # The first retained empty clause is an immediate conflict.
            return [next(i for i, clause in enumerate(self.clauses)
                         if not clause)]
        values = [0] * (self.variable_count + 1)
        queue: deque[int] = deque()
        hints: list[int] = []

        def assign(literal: int) -> int:
            """Return 1 for new, 0 for already equal, -1 for conflict."""
            variable = abs(literal)
            value = 1 if literal > 0 else -1
            if values[variable] == -value:
                return -1
            if values[variable] == value:
                return 0
            values[variable] = value
            queue.append(literal)
            return 1

        # Target literals are assumed false in their listed order.  A
        # complementary pair makes the target tautological, accepted by Rocq
        # without consulting hints.
        for literal in target:
            if assign(-literal) == -1:
                return []

        # Persistent unit clauses are visited in identifier order.
        for identifier, literal in self.units:
            outcome = assign(literal)
            if outcome == -1:
                hints.append(identifier)
                return hints
            if outcome == 1:
                hints.append(identifier)

        while queue:
            literal = queue.popleft()
            falsified = -literal
            old = self.watch_lists[falsified]
            self.watch_lists[falsified] = []
            for position, identifier in enumerate(old):
                clause = self.clauses[identifier]
                first, second = self.watches[identifier]
                if clause[first] == falsified:
                    watched, other_index = first, second
                elif clause[second] == falsified:
                    watched, other_index = second, first
                else:
                    # The identifier is stale after a prior watch move.
                    continue
                other = clause[other_index]
                other_value = values[abs(other)] * (1 if other > 0 else -1)
                if other_value == 1:
                    self.watch_lists[falsified].append(identifier)
                    continue
                replacement = None
                for index, candidate in enumerate(clause):
                    if index in (watched, other_index):
                        continue
                    candidate_value = (values[abs(candidate)] *
                                       (1 if candidate > 0 else -1))
                    if candidate_value != -1:
                        replacement = index
                        break
                if replacement is not None:
                    if watched == first:
                        self.watches[identifier] = (replacement, second)
                    else:
                        self.watches[identifier] = (first, replacement)
                    self.watch_lists[clause[replacement]].append(identifier)
                    continue
                self.watch_lists[falsified].append(identifier)
                if other_value == -1:
                    self.watch_lists[falsified].extend(old[position + 1:])
                    hints.append(identifier)
                    return hints
                outcome = assign(other)
                if outcome == -1:
                    self.watch_lists[falsified].extend(old[position + 1:])
                    hints.append(identifier)
                    return hints
                if outcome == 1:
                    hints.append(identifier)
        return None


def produce_hints(variable_count: int, base: Sequence[Clause],
                  proof: Iterable[Clause]) -> list[HintedAddition]:
    database = WatchedDatabase(variable_count, base)
    result: list[HintedAddition] = []
    for addition_number, clause in enumerate(proof, start=1):
        hints = database.hinted_rup(clause)
        if hints is None:
            raise ValueError(f"non-RUP addition {addition_number}: {clause[:12]}")
        result.append(HintedAddition(clause, hints))
        database.add(clause)
        if addition_number % 10_000 == 0:
            print(f"hinted {addition_number} additions", flush=True)
    if not result or result[-1].clause:
        raise ValueError("the retained proof does not end with the empty clause")
    return result


def check_hints(variable_count: int, base: Sequence[Clause],
                proof: Sequence[HintedAddition]) -> None:
    """Reference implementation of the Rocq checker's sequential semantics."""
    database = list(base)
    for addition_number, addition in enumerate(proof, start=1):
        values = [0] * (variable_count + 1)

        def assign(literal: int) -> bool:
            variable = abs(literal)
            value = 1 if literal > 0 else -1
            if values[variable] == -value:
                return False
            if values[variable] == 0:
                values[variable] = value
            return True

        tautology = False
        for literal in addition.clause:
            if not assign(-literal):
                tautology = True
                break
        if not tautology:
            conflicted = False
            for hint in addition.hints:
                if hint >= len(database):
                    raise ValueError(f"future hint {hint} at addition {addition_number}")
                unresolved: list[int] = []
                satisfied = False
                for literal in database[hint]:
                    value = values[abs(literal)] * (1 if literal > 0 else -1)
                    if value == 1:
                        satisfied = True
                        break
                    if value == 0:
                        unresolved.append(literal)
                if satisfied or len(unresolved) > 1:
                    raise ValueError(
                        f"non-unit hint {hint} at addition {addition_number}")
                if not unresolved:
                    conflicted = True
                    break
                if not assign(unresolved[0]):
                    raise ValueError(
                        f"assignment conflict, not clause conflict, at {addition_number}")
            if not conflicted:
                raise ValueError(f"hint chain has no conflict at addition {addition_number}")
        database.append(addition.clause)


def trim_hinted_proof(base_count: int,
                      proof: Sequence[HintedAddition]) -> list[HintedAddition]:
    """Keep the backward dependency cone of the final empty clause.

    Hints are already complete derivations, so an added clause not occurring in
    this cone cannot contribute to the contradiction.  Identifiers are then
    remapped to the shorter persistent database.  This proof-producing slice is
    independently rechecked by ``check_hints`` after trimming.
    """
    if not proof or proof[-1].clause:
        raise ValueError("cannot trim a proof without a final empty clause")
    needed = {len(proof) - 1}
    work = [len(proof) - 1]
    while work:
        addition_index = work.pop()
        for identifier in proof[addition_index].hints:
            if identifier < base_count:
                continue
            dependency = identifier - base_count
            if dependency >= addition_index:
                raise ValueError(
                    f"non-earlier dependency {identifier} in addition {addition_index}")
            if dependency not in needed:
                needed.add(dependency)
                work.append(dependency)

    kept = sorted(needed)
    remap = {base_count + old: base_count + new
             for new, old in enumerate(kept)}
    trimmed = [
        HintedAddition(
            proof[old].clause,
            [identifier if identifier < base_count else remap[identifier]
             for identifier in proof[old].hints])
        for old in kept
    ]
    return trimmed


def encode_literal(literal: int) -> int:
    """Odd means positive, even means negative; variable zero is unused."""
    return 2 * (abs(literal) - 1) + (1 if literal > 0 else 0)


def write_hinted_text(path: Path, proof: Sequence[HintedAddition]) -> None:
    """Compact, deterministic intermediate format: literals ; hint IDs."""
    with path.open("w", encoding="ascii") as stream:
        for addition in proof:
            stream.write(" ".join(str(encode_literal(x)) for x in addition.clause))
            stream.write(" ; ")
            stream.write(" ".join(map(str, addition.hints)))
            stream.write("\n")


def decode_literal_code(code: int) -> int:
    """Inverse of ``encode_literal`` for the retained hinted-text format."""
    if code < 0:
        raise ValueError(f"negative encoded literal {code}")
    variable = code // 2 + 1
    return variable if code % 2 else -variable


def read_hinted_text(path: Path) -> list[HintedAddition]:
    """Read the checked, stable-ID intermediate format written above.

    This deliberately does not regenerate hints.  Microblock generation only
    projects and renumbers an already retained hinted proof.
    """
    proof: list[HintedAddition] = []
    with path.open(encoding="ascii") as stream:
        for line_number, line in enumerate(stream, start=1):
            stripped = line.rstrip("\n")
            if not stripped.strip():
                continue
            literals_text, separator, hints_text = stripped.partition(";")
            if not separator or ";" in hints_text:
                raise ValueError(
                    f"malformed hinted-text record at line {line_number}")
            codes = [int(value) for value in literals_text.split()]
            hints = [int(value) for value in hints_text.split()]
            if any(identifier < 0 for identifier in hints):
                raise ValueError(f"negative hint at line {line_number}")
            proof.append(HintedAddition(
                tuple(decode_literal_code(code) for code in codes), hints))
    return proof


def rocq_nat_list(values: Iterable[int]) -> str:
    return "[" + ";".join(map(str, values)) + "]"


def rocq_clause(clause: Clause) -> str:
    literals = (f"({abs(literal)},"
                f"{'true' if literal > 0 else 'false'})"
                for literal in clause)
    return "[" + ";".join(literals) + "]"


def write_rocq_cnf(stream, formula: Sequence[Clause], indent: str = "  ") -> None:
    stream.write("[")
    if formula:
        stream.write("\n")
        for index, clause in enumerate(formula):
            separator = ";" if index + 1 < len(formula) else ""
            stream.write(f"{indent}{rocq_clause(clause)}{separator}\n")
    stream.write("]")


def write_rocq_explicit_base(
        output_prefix: Path, name: str, semantic_base: str,
        semantic_module: str, formula: Sequence[Clause], chunk_size: int = 0
) -> tuple[list[Path], Path, Path]:
    """Emit an explicit CNF module and its computational semantic bridge.

    Generated files follow the repository convention that files on the
    ``Digraph`` load path are imported by their basename.  A zero chunk size
    preserves the original monolithic data module.  A positive chunk size
    emits bounded data modules and makes the original data module a small,
    ordered aggregator, while leaving the bridge interface unchanged.
    """
    if chunk_size < 0:
        raise ValueError("Rocq base chunk size must be zero or positive")

    prefix = (output_prefix.with_suffix("")
              if output_prefix.suffix == ".v" else output_prefix)
    prefix.parent.mkdir(parents=True, exist_ok=True)
    data_path = prefix.with_name(f"{prefix.name}_data.v")
    bridge_path = prefix.with_name(f"{prefix.name}_bridge.v")
    data_module = data_path.stem
    chunk_paths: list[Path] = []

    if chunk_size == 0:
        with data_path.open("w", encoding="ascii") as stream:
            stream.write(
                "(** Generated by [scripts/generate_ckpath_certificates.py]. *)\n\n"
                "From Stdlib Require Import List.\n"
                "From Digraph Require Import ckpath_cnf.\n"
                "Import ListNotations.\n"
                "Set Warnings \"-abstract-large-number\".\n\n"
                f"Definition {name} : cnf :=\n  ")
            write_rocq_cnf(stream, formula, indent="  ")
            stream.write(".\n")
    else:
        chunks = [formula[start:start + chunk_size]
                  for start in range(0, len(formula), chunk_size)]
        width = max(2, len(str(len(chunks) - 1)))
        chunk_paths = [
            prefix.with_name(
                f"{prefix.name}_data_chunk{index:0{width}d}.v")
            for index in range(len(chunks))
        ]
        chunk_names = [f"{name}_chunk{index:0{width}d}"
                       for index in range(len(chunks))]

        for path, chunk_name, chunk in zip(
                chunk_paths, chunk_names, chunks, strict=True):
            with path.open("w", encoding="ascii") as stream:
                stream.write(
                    "(** Generated by "
                    "[scripts/generate_ckpath_certificates.py]. *)\n\n"
                    "From Stdlib Require Import List.\n"
                    "From Digraph Require Import ckpath_cnf.\n"
                    "Import ListNotations.\n"
                    "Set Warnings \"-abstract-large-number\".\n\n"
                    f"Definition {chunk_name} : cnf :=\n  ")
                write_rocq_cnf(stream, chunk, indent="  ")
                stream.write(".\n")

        with data_path.open("w", encoding="ascii") as stream:
            stream.write(
                "(** Generated by [scripts/generate_ckpath_certificates.py].\n"
                "    This ordered aggregator preserves the DIMACS clause "
                "order. *)\n\n"
                "From Stdlib Require Import List.\n"
                "From Digraph Require Import ckpath_cnf.\n")
            for chunk_path in chunk_paths:
                stream.write(
                    f"From Digraph Require Import {chunk_path.stem}.\n")
            stream.write(
                "Import ListNotations.\n\n"
                f"Definition {name} : cnf :=\n"
                "  concat [")
            if chunk_names:
                stream.write("\n")
                for index, chunk_name in enumerate(chunk_names):
                    separator = ";" if index + 1 < len(chunk_names) else ""
                    stream.write(f"    {chunk_name}{separator}\n")
                stream.write("  ")
            stream.write("].\n")

    with bridge_path.open("w", encoding="ascii") as stream:
        stream.write(
            "(** Generated by [scripts/generate_ckpath_certificates.py]. *)\n\n"
            f"From Digraph Require Import {data_module} {semantic_module}.\n\n"
            f"Lemma {name}_eq : {name} = ({semantic_base}).\n"
            "Proof. vm_compute; reflexivity. Qed.\n")

    return chunk_paths, data_path, bridge_path


@dataclass
class ImportGroup:
    """Earlier additions imported from one producer microblock."""

    producer_block: int
    original_ids: list[int]
    output_indices: list[int]


@dataclass
class Microblock:
    """A dense replay block projected from a stable-ID hinted proof.

    ``imported_ids`` deliberately retains the stable identifiers from the
    original proof.  They are the auditable provenance used to construct the
    producer-grouped selections in generated Rocq modules.
    """

    start: int
    base_ids: list[int]
    imported_ids: list[int]
    import_groups: list[ImportGroup]
    proof: list[HintedAddition]


MAX_MICROBLOCK_SIZE = 100


def project_microblock(base_count: int, proof: Sequence[HintedAddition],
                       start: int, count: int,
                       block_size: int = 25) -> Microblock:
    """Project ``proof[start:start+count]`` to a fresh dense database.

    The local database is, in order, the distinct referenced base clauses,
    the distinct referenced pre-block additions, and then earlier additions
    of this block.  Every hint is remapped to that dense numbering.  No proof
    search or hint regeneration occurs here.
    """
    if start < 0:
        raise ValueError("microblock start must be nonnegative")
    if count <= 0:
        raise ValueError("microblock count must be positive")
    if block_size <= 0 or block_size > MAX_MICROBLOCK_SIZE:
        raise ValueError(
            f"microblock size must be between 1 and {MAX_MICROBLOCK_SIZE}")
    if count > block_size:
        raise ValueError("microblock count exceeds its partition size")
    if start % block_size:
        raise ValueError("microblock start is not a partition boundary")
    stop = start + count
    if stop > len(proof):
        raise ValueError(
            f"microblock [{start}, {stop}) exceeds {len(proof)} additions")

    base_ids: list[int] = []
    imported_by_producer: dict[int, list[int]] = defaultdict(list)
    seen_base: set[int] = set()
    seen_imported: set[int] = set()
    for addition_index in range(start, stop):
        current_identifier = base_count + addition_index
        for identifier in proof[addition_index].hints:
            if identifier >= current_identifier:
                raise ValueError(
                    f"non-earlier hint {identifier} in addition "
                    f"{addition_index}")
            if identifier < base_count:
                if identifier not in seen_base:
                    seen_base.add(identifier)
                    base_ids.append(identifier)
            elif identifier < base_count + start:
                if identifier not in seen_imported:
                    seen_imported.add(identifier)
                    addition_identifier = identifier - base_count
                    producer = addition_identifier // block_size
                    imported_by_producer[producer].append(identifier)

    # The explicit-base checker verifies these clauses with one left-to-right
    # scan of the semantic CNF.  Sorting preserves stable provenance while
    # making the selected clauses a genuine subsequence; the local hint IDs
    # are rebuilt below against this order.
    base_ids.sort()

    import_groups = [
        ImportGroup(
            producer,
            imported_by_producer[producer],
            [identifier - base_count - producer * block_size
             for identifier in imported_by_producer[producer]])
        for producer in sorted(imported_by_producer)
    ]
    imported_ids = [identifier
                    for group in import_groups
                    for identifier in group.original_ids]

    local_identifier: dict[int, int] = {}
    for local, identifier in enumerate(base_ids):
        local_identifier[identifier] = local
    for offset, identifier in enumerate(imported_ids, start=len(base_ids)):
        local_identifier[identifier] = offset
    local_prefix = len(base_ids) + len(imported_ids)
    for addition_index in range(start, stop):
        local_identifier[base_count + addition_index] = (
            local_prefix + addition_index - start)

    local_proof = [
        HintedAddition(
            proof[addition_index].clause,
            [local_identifier[identifier]
             for identifier in proof[addition_index].hints])
        for addition_index in range(start, stop)
    ]
    return Microblock(start, base_ids, imported_ids, import_groups,
                      local_proof)


def block_label(index: int, width: int) -> str:
    return f"block{index:0{width}d}"


def block_output_name(name: str, index: int, width: int) -> str:
    return f"{name}_{block_label(index, width)}_output"


def block_sound_name(name: str, index: int, width: int) -> str:
    return f"{name}_{block_label(index, width)}_sound"


def write_rocq_chain_block(path: Path, module_names: Sequence[str],
                           name: str, base: str, base_module: str,
                           selected_base: Sequence[Clause],
                           block: Microblock, block_index: int,
                           width: int) -> None:
    """Emit one bounded block with only its output kept transparent."""
    producer_modules = [module_names[group.producer_block]
                        for group in block.import_groups]
    imports = ["ckpath_cnf", "ckpath_drup_explicit_microblock",
               base_module] + producer_modules
    output_name = block_output_name(name, block_index, width)
    sound_name = block_sound_name(name, block_index, width)
    output = [addition.clause for addition in block.proof]
    with path.open("w", encoding="ascii") as stream:
        stream.write(
            "(** Generated by [scripts/generate_ckpath_certificates.py].\n"
            "    Only the block output is transparent.  Selected base clauses,\n"
            "    producer imports, replay records, and the transient database\n"
            "    all remain underneath the opaque soundness theorem. *)\n\n"
            "From Stdlib Require Import List.\n"
            f"From Digraph Require Import {' '.join(imports)}.\n"
            "Import ListNotations.\n"
            "Set Warnings \"-abstract-large-number\".\n\n"
            f"(** Original retained additions [{block.start}, "
            f"{block.start + len(block.proof)}); "
            f"{len(block.base_ids)} selected base clauses and "
            f"{len(block.imported_ids)} imported consequences from "
            f"{len(block.import_groups)} producer blocks.\n"
            f"    Original selected base identifiers: "
            f"{rocq_nat_list(block.base_ids)}. *)\n"
            "Definition selected_base : cnf :=\n  ")
        write_rocq_cnf(stream, selected_base, indent="  ")
        stream.write(
            ".\n\n"
            f"Definition {output_name} : cnf :=\n  ")
        write_rocq_cnf(stream, output, indent="  ")
        stream.write(
            ".\n\n"
            f"Theorem {sound_name} :\n"
            f"  forall rho, satisfies_cnf rho ({base}) ->\n"
            f"    satisfies_cnf rho {output_name}.\n"
            "Proof.\n"
            "intros rho Hbase.\n")

        selected_names: list[str] = []
        for group in block.import_groups:
            producer = group.producer_block
            producer_label = block_label(producer, width)
            producer_output = block_output_name(name, producer, width)
            producer_sound = block_sound_name(name, producer, width)
            selected_name = f"imported_from_{producer_label}"
            selected_hypothesis = f"H{selected_name}"
            selected_names.append(selected_name)
            indices = rocq_nat_list(group.output_indices)
            stream.write(
                f"pose (select_cnf {producer_output} {indices} : cnf)\n"
                f"  as {selected_name}.\n"
                f"assert ({selected_hypothesis} :\n"
                f"  satisfies_cnf rho {selected_name}).\n"
                "{\n"
                f"  unfold {selected_name}.\n"
                f"  apply (satisfies_cnf_select rho {producer_output} "
                f"{indices}).\n"
                f"  - exact ({producer_sound} rho Hbase).\n"
                "  - vm_compute. reflexivity.\n"
                "}\n")

        selected_list = "[" + ";".join(selected_names) + "]"
        stream.write(
            f"pose (concat {selected_list} : cnf) as imported.\n"
            "assert (Himported : satisfies_cnf rho imported).\n"
            "{\n"
            "  unfold imported.\n"
            "  apply satisfies_cnf_concat_intro.\n")
        for selected_name in selected_names:
            stream.write(
                "  constructor.\n"
                f"  {{ exact H{selected_name}. }}\n")
        stream.write(
            "  constructor.\n"
            "}\n"
            "pose ([\n")
        for index, addition in enumerate(block.proof):
            separator = ";" if index + 1 < len(block.proof) else ""
            stream.write(
                f"  ({rocq_nat_list(encode_literal(x) for x in addition.clause)},"
                f"{rocq_nat_list(addition.hints)}){separator}\n")
        stream.write(
            "] : list (list nat * list nat)) as records.\n"
            "assert (Hcheck :\n"
            f"  check_explicit_microblock ({base}) selected_base\n"
            f"    imported records {output_name} = true).\n"
            "{ vm_compute. reflexivity. }\n"
            "exact (check_explicit_microblock_sound\n"
            f"  ({base}) selected_base imported records {output_name}\n"
            "  Hcheck rho Hbase Himported).\n"
            "Qed.\n")


def write_rocq_chain_final(path: Path, name: str, base: str,
                           base_module: str, last_module: str, last_block: int,
                           last_block_length: int, width: int) -> None:
    """Emit the tiny final theorem extracting the retained empty clause."""
    output_name = block_output_name(name, last_block, width)
    sound_name = block_sound_name(name, last_block, width)
    with path.open("w", encoding="ascii") as stream:
        stream.write(
            "(** Generated by [scripts/generate_ckpath_certificates.py].\n"
            "    The complete microblock chain ends in the empty clause. *)\n\n"
            "From Stdlib Require Import List.\n"
            f"From Digraph Require Import ckpath_cnf {base_module} "
            f"{last_module}.\n"
            "Import ListNotations.\n\n"
            f"Theorem {name}_base_unsatisfiable :\n"
            f"  forall rho, ~ satisfies_cnf rho ({base}).\n"
            "Proof.\n"
            "intros rho Hbase.\n"
            f"pose proof ({sound_name} rho Hbase) as Hlast.\n"
            f"assert (Hin : In [] {output_name}).\n"
            "{\n"
            f"  unfold {output_name}.\n")
        for _ in range(last_block_length - 1):
            stream.write("  right.\n")
        stream.write(
            "  left. reflexivity.\n"
            "}\n"
            f"pose proof (eval_cnf_member rho {output_name} [] Hlast Hin) "
            "as Hfalse.\n"
            "unfold eval_clause in Hfalse. discriminate.\n"
            "Qed.\n")


def write_rocq_microblock_chain(
        output_prefix: Path, name: str, base: str, base_module: str,
        variable_count: int, base_clauses: Sequence[Clause],
        proof: Sequence[HintedAddition], block_size: int = 25
) -> tuple[list[Path], Path, list[Microblock]]:
    """Validate and emit a complete gap-free bounded-memory replay chain."""
    if block_size <= 0 or block_size > MAX_MICROBLOCK_SIZE:
        raise ValueError(
            f"microblock size must be between 1 and {MAX_MICROBLOCK_SIZE}")
    if not proof:
        raise ValueError("cannot emit an empty retained proof")
    if proof[-1].clause:
        raise ValueError("the complete retained proof does not end in []")

    # Validate the entire retained stable-ID proof before any projection.
    check_hints(variable_count, base_clauses, proof)
    ranges = [(start, min(start + block_size, len(proof)))
              for start in range(0, len(proof), block_size)]
    cursor = 0
    for start, stop in ranges:
        if start != cursor or not start < stop or stop - start > block_size:
            raise ValueError("microblock partition is not gap-free and bounded")
        cursor = stop
    if cursor != len(proof):
        raise ValueError("microblock partition does not cover the whole proof")

    prefix = (output_prefix.with_suffix("")
              if output_prefix.suffix == ".v" else output_prefix)
    prefix.parent.mkdir(parents=True, exist_ok=True)
    width = max(2, len(str(len(ranges) - 1)))
    block_paths = [
        prefix.with_name(
            f"{prefix.name}_{block_label(index, width)}.v")
        for index in range(len(ranges))
    ]
    module_names = [path.stem for path in block_paths]
    blocks: list[Microblock] = []
    for block_index, (start, stop) in enumerate(ranges):
        block = project_microblock(
            len(base_clauses), proof, start, stop - start, block_size)
        selected_base = [base_clauses[identifier]
                         for identifier in block.base_ids]
        imported_clauses = [proof[identifier - len(base_clauses)].clause
                            for identifier in block.imported_ids]
        local_input = selected_base + imported_clauses
        check_hints(variable_count, local_input, block.proof)
        write_rocq_chain_block(
            block_paths[block_index], module_names, name, base, base_module,
            selected_base, block, block_index, width)
        blocks.append(block)

    final_path = prefix.with_name(f"{prefix.name}_final.v")
    write_rocq_chain_final(
        final_path, name, base, base_module, module_names[-1], len(blocks) - 1,
        len(blocks[-1].proof), width)
    return block_paths, final_path, blocks


def write_rocq_certificate(path: Path, name: str, base: str,
                           proof: Sequence[HintedAddition],
                           base_count: int) -> None:
    """Emit bounded incremental modules and the final checked theorem."""

    def header(stream, extra_modules: Sequence[str] = ()) -> None:
        imports = "ckpath_cnf ckpath_drup ckpath_cert_base"
        if "_k7_" in base:
            imports += " ckpath_cert_k7_base"
        if extra_modules:
            imports += " " + " ".join(extra_modules)
        stream.write(
            "(** Generated by [scripts/generate_ckpath_certificates.py].\n"
            "    The data is untrusted: [vm_compute] replays every hinted RUP\n"
            "    step.  Do not edit this file by hand. *)\n\n"
            "From Stdlib Require Import List.\n"
            f"From Digraph Require Import {imports}.\n"
            "Import ListNotations.\n"
            "Set Warnings \"-abstract-large-number\".\n\n")

    chunk_size = 500
    chunks = [proof[start:start + chunk_size]
              for start in range(0, len(proof), chunk_size)]
    # At most two replay chunks per source keeps both evolve and physical
    # compilation comfortably below their per-call limits.
    if name == "c11_m3" and len(chunks) > 8:
        groups = [list(range(start, start + 2)) for start in range(0, 8, 2)]
        groups.extend([[index] for index in range(8, len(chunks))])
    else:
        groups = [list(range(start, min(start + 2, len(chunks))))
                  for start in range(0, len(chunks), 2)]
    split = len(groups) > 1
    part_paths = [path.with_name(f"{path.stem}_part{index:02d}.v")
                  for index in range(len(groups))] if split else [path]
    part_modules = [part.stem for part in part_paths]

    for part_number, (part_path, chunk_numbers) in enumerate(
            zip(part_paths, groups)):
        previous = [part_modules[part_number - 1]] if part_number else []
        with part_path.open("w", encoding="ascii") as stream:
            header(stream, previous)
            if part_number == 0:
                stream.write(
                    f"Definition {name}_db_0 : clause_database :=\n"
                    f"  initial_database ({base}).\n\n")
            for chunk_number in chunk_numbers:
                chunk = chunks[chunk_number]
                records = f"{name}_records_{chunk_number}"
                trace = f"{name}_trace_{chunk_number}"
                before = f"{name}_db_{chunk_number}"
                after = f"{name}_db_{chunk_number + 1}"
                stream.write(
                    f"Definition {records} : list (list nat * list nat) := [\n")
                for index, addition in enumerate(chunk):
                    separator = ";" if index + 1 < len(chunk) else ""
                    stream.write(
                        f"({rocq_nat_list(encode_literal(x) for x in addition.clause)},"
                        f"{rocq_nat_list(addition.hints)}){separator}\n")
                stream.write(
                    "].\n\n"
                    f"Definition {trace} : list drup_step :=\n"
                    f"  decode_trace {records}.\n\n"
                    f"Definition {after} : clause_database :=\n"
                    f"  Eval vm_compute in (add_drup_steps {before} {trace}).\n\n"
                    f"Lemma {name}_chunk_{chunk_number}_checks :\n"
                    f"  check_drup_chunk {before} {trace} = true.\n"
                    "Proof. vm_compute. reflexivity. Qed.\n\n")

    # For split certificates, the requested output is a small aggregator.  For
    # small certificates it is the sole data module and is extended in place.
    mode = "w" if split else "a"
    with path.open(mode, encoding="ascii") as stream:
        if split:
            header(stream, part_modules)
        final_db = f"{name}_db_{len(chunks)}"
        # Base identifiers occupy [0, base_count); every retained addition adds
        # one stable identifier.  The final retained addition is empty.
        final_identifier = base_count + len(proof) - 1
        stream.write(
            f"Lemma {name}_final_empty :\n"
            f"  database_lookup {final_db} {final_identifier} = Some [].\n"
            "Proof. vm_compute. reflexivity. Qed.\n\n"
            f"Theorem {name}_base_unsatisfiable :\n"
            f"  forall rho, ~ satisfies_cnf rho ({base}).\n"
            "Proof.\n"
            "intros rho Hbase.\n"
            f"pose proof (initial_database_sound rho ({base}) Hbase) as Hdb0.\n")
        for chunk_number in range(len(chunks)):
            stream.write(
                f"pose proof (check_drup_chunk_sound {name}_db_{chunk_number} "
                f"{name}_trace_{chunk_number} {name}_chunk_{chunk_number}_checks "
                f"rho Hdb{chunk_number}) as Hdb{chunk_number + 1}.\n"
                f"change (satisfies_database rho {name}_db_{chunk_number + 1}) "
                f"in Hdb{chunk_number + 1}.\n")
        stream.write(
            f"pose proof (Hdb{len(chunks)} {final_identifier} [] "
            f"{name}_final_empty) as Hfalse.\n"
            "unfold eval_clause in Hfalse. discriminate.\n"
            "Qed.\n")


def instance(name: str, normalized: bool = False,
             truth_table: bool = False) -> CNF:
    return {"c9": c9_instance,
            "c10": c10_instance,
            "c11_m3": lambda flag, truth: c11_instance(3, flag, truth),
            "c11_m4": lambda flag, truth: c11_instance(4, flag, truth),
            "c11_bad": c11_k7_bad_instance,
            "c12_cover_3":
                lambda flag, truth: c12_k7_cover_instance(3, flag, truth),
            "c12_cover_4":
                lambda flag, truth: c12_k7_cover_instance(4, flag, truth),
            "c12_low_bad": c12_k7_low_bad_instance,
            "c13_cover_3":
                lambda flag, truth: c13_k7_cover_instance(3, flag, truth),
            "c13_cover_4":
                lambda flag, truth: c13_k7_cover_instance(4, flag, truth),
            "c13_cover_5":
                lambda flag, truth: c13_k7_cover_instance(5, flag, truth)}[name](
                normalized, truth_table)


def main() -> None:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)
    cnf_parser = subparsers.add_parser("cnf")
    cnf_parser.add_argument(
        "instance",
        choices=("c9", "c10", "c11_m3", "c11_m4",
                 "c11_bad", "c12_cover_3", "c12_cover_4", "c12_low_bad",
                 "c13_cover_3", "c13_cover_4", "c13_cover_5"))
    cnf_parser.add_argument("output", type=Path)
    cnf_parser.add_argument("--normalized", action="store_true",
                            help="fix one nonempty distinguished set at vertex zero")
    cnf_parser.add_argument("--truth-table", action="store_true",
                            help="use ckpath_cardinality's direct row encoding")
    cnf_parser.add_argument(
        "--fixed-mask",
        help=("append a rooted zero/one set mask after the normalized k=7 "
              "base, in the exact order of fixed_set_units"))
    cnf_parser.add_argument(
        "--specialize-fixed-mask", action="store_true",
        help=("substitute --fixed-mask into the base instead of appending "
              "units; matches the Rocq fixed-set specializer"))
    cnf_parser.add_argument(
        "--true-marks",
        help=("comma-separated mark vertices to substitute true after fixed-"
              "set specialization (currently c12_low_bad only)"))
    cnf_parser.add_argument(
        "--low-vertices",
        help=("comma-separated vertices to substitute outside the set and "
              "marked low (currently c12_low_bad only)"))
    cnf_parser.add_argument(
        "--low-mask",
        help=("12-bit partial low-set mask: true positions are substituted "
              "outside the set and marked low; false positions stay free"))
    cnf_parser.add_argument(
        "--c12-low-at-least", type=int,
        help=("append Low subset complement(S) and an at-least-k constraint "
              "for c12_low_bad"))
    cnf_parser.add_argument(
        "--c12-low-root-mark", action="store_true",
        help="append the c12_low_bad unit fixing mark vertex zero true")
    cnf_parser.add_argument(
        "--c12-low-mark-degree", action="store_true",
        help="append mark(i) -> internal-outdegree(i) <= 3")
    cnf_parser.add_argument(
        "--c13-low-root", action="store_true",
        help=("append the minimum-active-root internal-row bound for "
              "c13_cover_3/4/5"))
    cnf_parser.add_argument(
        "--c13-orbit-union", action="store_true",
        help=("append mark0 and block noncanonical rooted active-set masks "
              "for c13_cover_3/4/5"))
    rocq_base_parser = subparsers.add_parser(
        "rocq-base",
        help="emit an explicit Rocq CNF and a computational semantic bridge")
    rocq_base_parser.add_argument("cnf", type=Path)
    rocq_base_parser.add_argument("output_prefix", type=Path)
    rocq_base_parser.add_argument("--rocq-name", required=True)
    rocq_base_parser.add_argument("--semantic-base", required=True)
    rocq_base_parser.add_argument("--semantic-module", required=True)
    rocq_base_parser.add_argument(
        "--chunk-size", type=int, default=0,
        help=("maximum clauses per explicit data chunk; zero preserves the "
              "monolithic data module"))
    hint_parser = subparsers.add_parser("hint")
    hint_parser.add_argument("cnf", type=Path)
    hint_parser.add_argument("drat", type=Path)
    hint_parser.add_argument("output", type=Path)
    hint_parser.add_argument("--rocq-output", type=Path)
    hint_parser.add_argument("--rocq-name")
    hint_parser.add_argument("--rocq-base")
    chain_parser = subparsers.add_parser(
        "microblock-chain",
        help=("validate and emit a complete bounded Rocq replay chain "
              f"(at most {MAX_MICROBLOCK_SIZE} additions per block)"))
    chain_parser.add_argument("cnf", type=Path)
    chain_parser.add_argument("hints", type=Path)
    chain_parser.add_argument("output_prefix", type=Path)
    chain_parser.add_argument("--block-size", type=int, default=25)
    chain_parser.add_argument("--rocq-name", required=True)
    chain_parser.add_argument("--rocq-base", required=True)
    chain_parser.add_argument("--rocq-base-module", required=True)
    orbit_parser = subparsers.add_parser(
        "orbit-masks",
        help="emit masks in the exact order of Rocq orbit_representatives")
    orbit_parser.add_argument("length", type=int)
    orbit_parser.add_argument("weight", type=int)
    orbit_parser.add_argument("output", type=Path)
    args = parser.parse_args()

    if args.command == "cnf":
        formula = instance(args.instance, args.normalized, args.truth_table)
        # These clauses are part of the strengthened base.  Add them before
        # any requested specialization so the residual formula is literally
        # the Rocq reduction of the complete strengthened base.
        if args.c12_low_root_mark:
            if args.instance != "c12_low_bad":
                parser.error("--c12-low-root-mark requires c12_low_bad")
            formula.add(formula.ids[("l", 0)])
        if args.c12_low_at_least is not None:
            if args.instance != "c12_low_bad":
                parser.error("--c12-low-at-least requires c12_low_bad")
            try:
                append_c12_low_cardinality_strengthening(
                    formula, args.c12_low_at_least)
            except ValueError as error:
                parser.error(str(error))
        if args.c12_low_mark_degree:
            if args.instance != "c12_low_bad":
                parser.error("--c12-low-mark-degree requires c12_low_bad")
            append_c12_low_mark_degree_strengthening(formula)
        if args.c13_low_root:
            try:
                append_c13_low_root_strengthening(formula, args.instance)
            except ValueError as error:
                parser.error(str(error))
        if args.c13_orbit_union:
            if not args.normalized:
                parser.error("--c13-orbit-union requires --normalized")
            if args.c13_low_root:
                parser.error(
                    "--c13-orbit-union and --c13-low-root are alternative "
                    "normalizations")
            try:
                append_c13_orbit_union_strengthening(
                    formula, args.instance)
            except ValueError as error:
                parser.error(str(error))
        if args.fixed_mask is not None:
            if not args.normalized:
                parser.error("--fixed-mask requires --normalized")
            try:
                if args.specialize_fixed_mask:
                    specialize_fixed_set(formula, args.instance,
                                         args.fixed_mask)
                else:
                    append_fixed_set_units(formula, args.instance,
                                           args.fixed_mask)
            except ValueError as error:
                parser.error(str(error))
        elif args.specialize_fixed_mask:
            parser.error("--specialize-fixed-mask requires --fixed-mask")
        if args.true_marks is not None:
            try:
                specialize_true_marks(formula, args.instance, args.true_marks)
            except ValueError as error:
                parser.error(str(error))
        if args.low_vertices is not None:
            try:
                specialize_low_vertices(formula, args.instance,
                                        args.low_vertices)
            except ValueError as error:
                parser.error(str(error))
        if args.low_mask is not None:
            try:
                specialize_low_mask(formula, args.instance, args.low_mask)
            except ValueError as error:
                parser.error(str(error))
        formula.write_dimacs(args.output)
        print(len(formula.ids), len(formula.clauses))
    elif args.command == "rocq-base":
        variable_count, base = read_dimacs(args.cnf)
        if args.chunk_size < 0:
            parser.error("--chunk-size must be zero or positive")
        chunk_paths, data_path, bridge_path = write_rocq_explicit_base(
            args.output_prefix, args.rocq_name, args.semantic_base,
            args.semantic_module, base, args.chunk_size)
        chunk_summary = (f"{len(chunk_paths)} data chunks, "
                         if chunk_paths else "")
        print(f"{variable_count} variables, {len(base)} clauses; wrote "
              f"{chunk_summary}{data_path} and {bridge_path}")
    elif args.command == "hint":
        variable_count, base = read_dimacs(args.cnf)
        proof = produce_hints(variable_count, base,
                              read_drat_additions(args.drat))
        check_hints(variable_count, base, proof)
        untrimmed_count = len(proof)
        untrimmed_hints = sum(len(x.hints) for x in proof)
        proof = trim_hinted_proof(len(base), proof)
        check_hints(variable_count, base, proof)
        write_hinted_text(args.output, proof)
        if args.rocq_output:
            if not args.rocq_name or not args.rocq_base:
                parser.error("--rocq-output requires --rocq-name and --rocq-base")
            write_rocq_certificate(args.rocq_output, args.rocq_name,
                                   args.rocq_base, proof, len(base))
        print(f"{len(base)} base clauses, "
              f"{untrimmed_count} -> {len(proof)} additions, "
              f"{untrimmed_hints} -> "
              f"{sum(len(x.hints) for x in proof)} hints")
    elif args.command == "microblock-chain":
        variable_count, base = read_dimacs(args.cnf)
        proof = read_hinted_text(args.hints)
        block_paths, final_path, blocks = write_rocq_microblock_chain(
            args.output_prefix, args.rocq_name, args.rocq_base,
            args.rocq_base_module, variable_count, base, proof,
            args.block_size)
        print(f"{len(proof)} additions -> {len(blocks)} gap-free blocks; "
              f"max {max(len(block.base_ids) for block in blocks)} selected "
              f"base clauses, max "
              f"{max(len(block.imported_ids) for block in blocks)} imported "
              f"consequences; wrote {len(block_paths)} block modules and "
              f"{final_path}")
    else:
        try:
            masks = orbit_representative_masks(args.length, args.weight)
        except ValueError as error:
            parser.error(str(error))
        args.output.write_text("\n".join(masks) + "\n", encoding="ascii")
        print(f"wrote {len(masks)} orbit representatives")


if __name__ == "__main__":
    main()
