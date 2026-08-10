# Trust boundary

The production source contains no `sorry`, `admit`, or source-level `axiom`.
Most advertised results depend, as reported by Lean, only on `propext`,
`Classical.choice`, and `Quot.sound`.

The first/last-four coefficient theorem uses `bv_decide` in
`OpConjecture/Combinatorics/NormalizedFourVertexLadderClassification.lean`
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

The standalone Nakayama, radical-square-zero, and representation-directed
equidistribution endpoints report only the three standard axioms above.

The optional Comparator configurations are therefore supplied only for those
three endpoints.  The main and first/last-four challenge modules still compile
as independent statement specifications, but this release does not claim that
their solutions pass Comparator's strict standard-axiom policy.  Replacing the
native certificate checks by fully kernel-reduced proof terms would be a
separate proof-engineering project, not a documentation-only change.

