# Verification

## Four-vertex translation-quiver census

[`four_vertex_patterns.py`](four_vertex_patterns.py) is the exhaustive finite
checker used in the manuscript's classification of admissible four-vertex
patterns. It encodes only:

- a loop-free arrow relation on four labeled vertices;
- a nonempty set of projective vertices;
- a partial translation, with a separate value for translates outside the
  four-vertex set; and
- the factor-ladder recurrence and the six admissibility conditions stated in
  the paper.

It is therefore a pure translation-quiver calculation, not a QPA calculation
and not an enumeration of finite-dimensional algebras. The program uses only
the Python standard library. From the repository root, run:

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
patterns and the second is the number of isomorphism classes. Assertions in
the enumeration check the hook bound, the double-hook characterization, the
classification of killed patterns by hooks or the two hookless types, their
disjointness, and the four blocker cases. CI reruns the program on every push.

## Exact Lean target verification

This nested Lake project isolates the optional `Comparator` dependency from
the production theorem library. Each challenge module restates an advertised
target independently, with an intentional `sorry`, without importing the
solution module. For the Nakayama, radical-square-zero, and
representation-directed endpoints, the corresponding JSON asks Comparator to
check that the challenge and solution declarations have the same
environment-level type and that the solution uses only the three standard
axioms.

The challenge `sorry`s are specification placeholders.  They are excluded from
the production `sorry_count: 0` claim.

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

Repeat the last command for each of the three JSON configurations. CI compiles both the
challenge and solution environments and records `#print axioms`; a fully
sandboxed Comparator run additionally requires `landrun`, so it remains an
explicit release/auditor command rather than being simulated in CI.

`MainTheorem.lean` and `FirstLastFour.lean` remain independently compilable
statement specifications. They have no strict Comparator JSON because their
solutions use Lean 4.32's generated native `bv_decide` certificate-checking
axioms. See `../TRUST.md`.
