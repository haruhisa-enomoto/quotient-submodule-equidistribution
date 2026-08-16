# Source versions and attribution

The Lean source corresponds to formalization commit
`175e0ee7e78e04efe9a39a78c49d77032c67a282`, dated 2026-08-16, which matches
the manuscript at repository commit
`3ba2c24b0e537139461b80052e8813936feb38c0`, whose
`paper/op_conjecture/` tree is
`1b2a5e5f34dfa7ed9aa4fef447f866e9208747d3`.

This repository publishes the Lean source for the four-case main theorem and
the structural results listed in `MainResults.lean`.  The manuscript and
research records are maintained in their respective source repositories.

For the representation-directed case, the Lean declaration
`selectedWordMixedMultiplicityFor_eq_factorHomDimension_of_reduced` formalizes
the equality between a mixed coordinate and a Hom-space dimension in an ideal
quotient.  The declarations `finiteIndependentEquivCompactClosedSet`,
`finiteIntervalDeletionChain`, and
`qClosed_finiteIntervalDeletionChain_of_finiteDimensional` formalize the
corresponding convex-geometric statements.  The first/last-four endpoint uses
Lean's finite classifiers to prove the coefficient equalities; the manuscript
presents an exhaustive enumeration of the associated four-vertex patterns.

The accompanying finite translation-quiver verifier
`verification/four_vertex_patterns.py` is copied byte-for-byte from
`experiments/op-conjecture-formalization/verify_paper_four_vertex_patterns.py`
at internal repository commit
`778470bcb87fa23f336cb8cbaad08daad4f56dbf`. Its SHA-256 digest at export is
`8b7669c87d4d9470532dd4fd3ce0b98b74e4cd87e7c3a5e03889c18eac4d6424`.

## Dependencies

The root Lake project directly requires Mathlib at commit
`28313485bc624fcd16dcb162dd2e2c3c813aa8fe` (Lean 4.32.0).  Eleven foundational
modules were adapted from TauCeti commit
`eeb5b4e20c16d302fab0930c4b589c1e0bdd7241`; their file headers preserve exact
attribution, and they are maintained here as ordinary local source.

Comparator and doc-gen4 are configured in the nested `verification/` and
`docbuild/` Lake projects, each with its own manifest.
