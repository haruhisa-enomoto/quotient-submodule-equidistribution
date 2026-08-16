#!/usr/bin/env python3
"""Independent reconstruction of the frozen paper's four-vertex census."""

from itertools import combinations, permutations, product

V = range(4)
PERMS = tuple(permutations(V))


def edge(edges, x, y):
    return x != y and bool(edges & (1 << (4 * x + y)))


def neighbors_in(edges, x):
    return frozenset(y for y in V if edge(edges, y, x))


def neighbors_out(edges, x):
    return frozenset(y for y in V if edge(edges, x, y))


def rooted(edges, pi):
    reached = set(pi)
    while True:
        more = reached | {y for x in reached for y in V if edge(edges, x, y)}
        if more == reached:
            return len(reached) == 4
        reached = more


def no_transitive_triangle(edges):
    return all(
        not (edge(edges, x, y) and edge(edges, y, z) and edge(edges, x, z))
        for x in V for y in V for z in V
    )


def ladder_status(edges, pi, tau, start):
    prev = (0, 0, 0, 0)
    nxt = tuple(int(i == start) for i in V)
    seen = set()
    while True:
        if any(nxt[p] for p in pi):
            return "boundary", len(seen), max(max(v) for pair in seen for v in pair) if seen else 1
        if not any(nxt):
            return "zero", len(seen), max(max(v) for pair in seen for v in pair) if seen else 1
        pair = (prev, nxt)
        if pair in seen:
            return "repeat", len(seen), max(max(v) for pair in seen for v in pair)
        seen.add(pair)
        theta = tuple(sum(nxt[x] for x in V if edge(edges, y, x)) for y in V)
        tau_prev = tuple(sum(prev[x] for x in V if tau.get(x) == y) for y in V)
        prev, nxt = nxt, tuple(max(theta[y] - tau_prev[y], 0) for y in V)


def hooks(edges, pi, tau):
    return tuple(
        (a, u, b)
        for a in V for u in V for b in V
        if u not in pi
        and edge(edges, a, u) and edge(edges, u, b)
        and tau.get(b) == a
        and neighbors_in(edges, u) == {a}
        and neighbors_in(edges, b) == {u}
    )


def is_fixed(edges, pi, tau):
    if len(pi) != 1:
        return False
    p = next(iter(pi))
    for a, c, z in permutations([x for x in V if x != p], 3):
        if (
            edge(edges, p, a)
            and edge(edges, a, c) and edge(edges, c, a)
            and edge(edges, c, z) and edge(edges, z, c)
            and tau.get(z) == a and tau.get(c) == c
            and not edge(edges, p, z)
            and neighbors_in(edges, z) == {c}
            and neighbors_in(edges, c) == {a, z}
            and tau.get(a) in (z, 4)
        ):
            return True
    return False


def is_triangle(edges, pi, tau):
    if len(pi) != 1:
        return False
    p = next(iter(pi))
    for a1, a2, x in permutations([y for y in V if y != p], 3):
        if (
            neighbors_in(edges, a1) == {a2}
            and neighbors_in(edges, a2) == {p, x}
            and neighbors_in(edges, x) == {a1}
            and tau.get(a1) == p
            and tau.get(a2) == a1
            and tau.get(x) == 4
        ):
            return True
    return False


def is_double(edges, pi, tau, hs):
    if len(hs) != 2:
        return False
    for p in pi:
        for u1, u2, u3 in permutations([x for x in V if x != p], 3):
            if set(hs) == {(p, u1, u2), (u1, u2, u3)}:
                return True
    return False


def admissible(edges, pi, tau):
    if not rooted(edges, pi) or not no_transitive_triangle(edges):
        return None
    internal = [y for x, y in tau.items() if y != 4]
    if len(internal) != len(set(internal)):
        return None
    for w, t in tau.items():
        if t != 4:
            if neighbors_in(edges, w) != neighbors_out(edges, t):
                return None
            if edge(edges, t, w):
                return None
    image = set(internal)
    for x, y in combinations(V, 2):
        if edge(edges, x, y) and edge(edges, y, x):
            if tau.get(x) != x and tau.get(y) != y:
                return None
            if (x in pi and x in image) or (y in pi and y in image):
                return None
    runs = tuple(ladder_status(edges, pi, tau, x) for x in V)
    statuses = tuple(run[0] for run in runs)
    return statuses, max(run[1] for run in runs), max(run[2] for run in runs)


def transform(edges, pi, tau, perm):
    new_edges = 0
    for x in V:
        for y in V:
            if edge(edges, x, y):
                new_edges |= 1 << (4 * perm[x] + perm[y])
    new_pi = sum(1 << perm[x] for x in pi)
    new_tau = [4] * 4
    for x, y in enumerate(tau):
        if x in pi:
            continue
        new_tau[perm[x]] = 4 if y == 4 else perm[y]
    return new_edges, new_pi, tuple(new_tau)


def canonical(pattern):
    edges, pi, tau = pattern
    return min(transform(edges, pi, tau, p) for p in PERMS)


def main():
    categories = {name: [] for name in ("all", "killed", "hookless_killed", "fixed", "triangle", "double")}
    blocker_counts = [0, 0, 0, 0]
    blocker_total = 0
    max_steps = 0
    max_coeff = 0
    max_structural_steps = 0
    max_structural_coeff = 0
    for compact_edges in range(1 << 12):
        edges = 0
        k = 0
        for x in V:
            for y in V:
                if x != y:
                    if compact_edges & (1 << k):
                        edges |= 1 << (4 * x + y)
                    k += 1
        if not no_transitive_triangle(edges):
            continue
        pred = tuple(neighbors_in(edges, x) for x in V)
        succ = tuple(neighbors_out(edges, x) for x in V)
        for pi_mask in range(1, 16):
            pi = frozenset(x for x in V if pi_mask & (1 << x))
            nonpi = tuple(x for x in V if x not in pi)
            if not rooted(edges, pi):
                continue
            for values in product(range(5), repeat=len(nonpi)):
                tau = dict(zip(nonpi, values))
                admitted = admissible(edges, pi, tau)
                if admitted is None:
                    continue
                statuses, steps, coeff = admitted
                max_structural_steps = max(max_structural_steps, steps)
                max_structural_coeff = max(max_structural_coeff, coeff)
                if "repeat" in statuses:
                    continue
                max_steps = max(max_steps, steps)
                max_coeff = max(max_coeff, coeff)
                tau_tuple = tuple(tau.get(x, 4) for x in V)
                pattern = (edges, pi, tau_tuple)
                categories["all"].append(pattern)
                hs = hooks(edges, pi, tau)
                killed = "zero" in statuses
                fixed = is_fixed(edges, pi, tau)
                triangle = is_triangle(edges, pi, tau)
                double = is_double(edges, pi, tau, hs)
                if killed:
                    categories["killed"].append(pattern)
                if killed and not hs:
                    categories["hookless_killed"].append(pattern)
                if fixed:
                    categories["fixed"].append(pattern)
                if triangle:
                    categories["triangle"].append(pattern)
                if double:
                    categories["double"].append(pattern)
                assert len(hs) <= 2
                assert (len(hs) == 2) == double
                assert killed == (bool(hs) or fixed or triangle)
                assert not (fixed and triangle)
                # Mark the blocker lemma's induced projective-end triples.
                for p in pi:
                    for u, b, z in permutations([x for x in V if x != p], 3):
                        if u in pi or b in pi or z in pi:
                            continue
                        if not (edge(edges, p, u) and edge(edges, u, b)
                                and tau.get(b) == p):
                            continue
                        triple = {p, u, b}
                        if ({x for x in triple if edge(edges, x, u)} != {p}
                                or {x for x in triple if edge(edges, x, b)} != {u}):
                            continue
                        if not (edge(edges, u, z) or edge(edges, b, z)):
                            continue
                        blocker_total += 1
                        cases = (
                            not edge(edges, z, u) and not edge(edges, z, b),
                            edge(edges, u, z) and edge(edges, z, u) and
                                (tau.get(u) == u or tau.get(z) == z),
                            edge(edges, b, z) and edge(edges, z, u) and tau.get(z) == u,
                            triangle,
                        )
                        assert sum(cases) == 1
                        blocker_counts[cases.index(True)] += 1
    for name, rows in categories.items():
        print(name, len(rows), len({canonical(row) for row in rows}))
    print("blockers", blocker_total, blocker_counts)
    print("max_steps", max_steps, "max_coeff", max_coeff)
    print("max_structural_steps", max_structural_steps,
          "max_structural_coeff", max_structural_coeff)


if __name__ == "__main__":
    main()
