# Trust boundary

The production source contains no `sorry`, `admit`, or source-level `axiom`.
`Audit.lean` reports `propext`, `Classical.choice`, and `Quot.sound` for every
listed result except the first/last-four theorem and the results that use it.

The first/last-four coefficient theorem uses `bv_decide` in
`QuotientSubmoduleEquidistribution/Combinatorics/NormalizedFourVertexLadderClassification.lean`
to check finite bit-vector classifiers.  In Lean 4.32, `bv_decide` asks a SAT
solver for an LRAT certificate and then checks the certificate by native
evaluation.  Lean records each such native evaluation as a generated axiom
with a name containing `_native.bv_decide.ax_`.  This makes the Lean compiler
and interpreter part of the trusted base for that branch, in addition to the
kernel.  The generated names are printed exactly by `Audit.lean` and may be
regenerated when proof scripts or the Lean version change.

Consequently this additional trust boundary affects:

- `FirstLastFourEndpoint.bottom_top_four`;
- `FirstLastFourEndpoint.equidistribution_of_card_le_nine`; and
- the four-case aggregation theorem, through its at-most-nine branch.

The axiom report separates the results as follows:

| Results | Compiler-visible axioms |
| --- | --- |
| Nakayama, radical-square-zero, and representation-directed theorems | `propext`, `Classical.choice`, `Quot.sound` |
| First/last-four theorem, at-most-nine theorem, and four-case theorem | the three axioms above and generated native `bv_decide` axioms |

The nested verification project supplies strict Comparator configurations for
the Nakayama, radical-square-zero, and representation-directed declarations.
Its main-theorem and first/last-four challenge modules compile as separate
statement specifications.  Their solutions have the larger axiom set recorded
in the second row of the table.
