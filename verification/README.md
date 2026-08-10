# Exact-target verification

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
