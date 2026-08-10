# Provenance and release boundary

This standalone repository was exported from the Mathlib-only formalization
checkpoint
`19395b97eb53e81370949d6c120a3475786bcc4d`, frozen internally on
2026-08-10 under the tag
`op-conjecture-mathlib-only-main-theorems-2026-08-10`.

The public artifact is intentionally narrower than the surrounding research
workspace.  It contains the Lean source required for the manuscript's main
four-case theorem and supporting structural results, but no paper drafts,
research ledgers, experimental computations, or TauCeti-dependent package.
After release, this repository is the source of truth for the public Lean
artifact; manuscript and research records remain maintained separately.

## Dependency boundary

The production Lake project directly requires only Mathlib, pinned at commit
`28313485bc624fcd16dcb162dd2e2c3c813aa8fe` (Lean 4.32.0).  It has no TauCeti
package, import, API reference, or effective search path.  Eleven foundational
modules were adapted into this repository from TauCeti commit
`eeb5b4e20c16d302fab0930c4b589c1e0bdd7241`; their file headers preserve exact
attribution, and they are maintained here as ordinary local source.

Documentation and target-comparison tools live in nested Lake projects.  They
do not alter the dependency graph of the production theorem library.

