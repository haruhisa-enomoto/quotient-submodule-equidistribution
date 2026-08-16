# Verification

## Four-vertex translation-quiver census

An admissible four-vertex pattern is a tuple `(V, E, Pi, t)` consisting of:

- a loop-free arrow relation on four labeled vertices;
- a nonempty set of projective vertices;
- a partial translation, with a separate value for translates outside the
  four-vertex set; and
- the factor-ladder recurrence determined by these data.

The admissibility conditions tested by the program are:

1. every vertex is reachable from `Pi` by a directed path;
2. the values of `t` that lie in `V` are distinct;
3. if `t(w) = v` lies in `V`, then the predecessors of `w` equal the
   successors of `v`, and there is no arrow from `v` to `w`;
4. the arrow relation contains no transitive triangle;
5. in every two-cycle, one vertex is fixed by `t`, and a projective vertex in
   the two-cycle is not in the image of `t`; and
6. the factor-ladder recurrence from each vertex reaches a projective summand
   or zero before repeating a nonzero pair of consecutive terms.

A pattern is *killed* when one of its four recurrences reaches zero before it
meets a projective vertex.

[`four_vertex_patterns.py`](four_vertex_patterns.py) enumerates every such
tuple, tests the manuscript's six admissibility conditions, and evaluates the
recurrence from each vertex.  It uses the Python standard library.  From the
repository root, run:

```text
python3 verification/four_vertex_patterns.py
```

The complete expected output is:

```text
all 6933 329
killed 1272 53
hookless_killed 96 4
fixed 72 3
triangle 24 1
double 96 4
blockers 528 [384, 48, 72, 24]
max_steps 4 max_coeff 1
max_structural_steps 4 max_structural_coeff 1
```

The first number on each of the first six lines is the number of labeled
patterns and the second is the number of isomorphism classes.  The output
labels `fixed` and `triangle` denote types F and T in the manuscript,
respectively; `double` denotes the double-hook patterns.  Assertions in the
enumeration check that every pattern has at most two hooks, that two hooks are
equivalent to a double hook, and that a pattern is killed exactly when it has
a hook or has type F or T.

The `blockers` line counts extensions of a projective-end hook
`p -> u -> b` with `t(b) = p` by a fourth vertex `z`.  Its four entries count,
in order: no arrow from `z` to `u` or `b`; a two-cycle between `u` and `z`
with `u` or `z` fixed by `t`; arrows `b -> z -> u` with `t(z) = u`; and type
T.  The two final lines report the maximum recurrence length and coefficient,
first for admissible patterns and then before the nonrepetition condition is
imposed.  CI reruns the program on every push.

## Comparison of Lean target statements

This nested Lake project gives Comparator its own dependency environment.
Each challenge module states one public theorem type in an environment formed
from the theorem's common dependencies.  The solution module is loaded in a
separate environment.  For the Nakayama, radical-square-zero, and
representation-directed declarations, the corresponding JSON asks Comparator
to check equality of the environment-level types and to require the axiom set
`propext`, `Classical.choice`, and `Quot.sound`.

The challenge declarations use `sorry` as statement specifications.  They
belong to the nested verification project; the root production project has
`sorry_count: 0`.

After installing the external prerequisites documented by Comparator, run
from this directory:

```text
lake update
lake build ComparatorChallenges
lake build Comparator:comparator Comparator:lean4export
COMPARATOR_LEAN4EXPORT=../.lake/packages/Comparator/.lake/packages/lean4export/.lake/build/bin/lean4export \
  lake env ../.lake/packages/Comparator/.lake/build/bin/comparator \
  ComparatorChallenges/MainTheorem.json
```

Repeat the last command for each of the three JSON configurations.  CI
compiles the challenge and solution environments and records `#print axioms`.
The Comparator command above additionally requires the external `landrun`
executable.

`MainTheorem.lean` and `FirstLastFour.lean` are also compilable statement
specifications.  The corresponding solutions use Lean 4.32's generated
native `bv_decide` certificate-checking axioms, whose names and consequences
are recorded in `../TRUST.md`.
