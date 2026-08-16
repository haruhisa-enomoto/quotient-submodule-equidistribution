# Provenance and release boundary

This standalone repository was exported from, and synchronized through, the
Mathlib-only formalization checkpoint
`175e0ee7e78e04efe9a39a78c49d77032c67a282`, frozen internally on 2026-08-16.
That checkpoint matches the manuscript at repository commit
`3ba2c24b0e537139461b80052e8813936feb38c0`, whose
`paper/op_conjecture/` tree is
`1b2a5e5f34dfa7ed9aa4fef447f866e9208747d3`.

The public artifact is intentionally narrower than the surrounding research
workspace.  It contains the Lean source required for the manuscript's main
four-case theorem and supporting structural results, but no paper drafts,
research ledgers, experimental computations, or TauCeti-dependent package.
After release, this repository is the source of truth for the public Lean
artifact; manuscript and research records remain maintained separately.

The 2026-08-16 synchronization adds the manuscript's literal ideal-quotient
tau-category route for representation-directed principal positivity and the
exact finite-independent/compact-closed and finite-interval interfaces. The
accepted stronger Lean proof of the first/last-four result is retained instead
of duplicating the manuscript's reader-facing exhaustive enumeration.

The accompanying finite translation-quiver verifier
`verification/four_vertex_patterns.py` is copied byte-for-byte from
`experiments/op-conjecture-formalization/verify_paper_four_vertex_patterns.py`
at internal repository commit
`778470bcb87fa23f336cb8cbaad08daad4f56dbf`. Its SHA-256 digest at export is
`8b7669c87d4d9470532dd4fd3ce0b98b74e4cd87e7c3a5e03889c18eac4d6424`.

## Dependency boundary

The production Lake project directly requires only Mathlib, pinned at commit
`28313485bc624fcd16dcb162dd2e2c3c813aa8fe` (Lean 4.32.0).  It has no TauCeti
package, import, API reference, or effective search path.  Eleven foundational
modules were adapted into this repository from TauCeti commit
`eeb5b4e20c16d302fab0930c4b589c1e0bdd7241`; their file headers preserve exact
attribution, and they are maintained here as ordinary local source.

Documentation and target-comparison tools live in nested Lake projects.  They
do not alter the dependency graph of the production theorem library.
