# Quotient-submodule equidistribution in Lean

This repository contains a Lean 4 formalization accompanying Haruhisa
Enomoto's manuscript *An equidistribution conjecture for quotient-closed and
submodule-closed subcategories*.  It is a standalone Mathlib project: the
production build has exactly one direct dependency, a fixed revision of
Mathlib.

The universal quotient-submodule equidistribution conjecture is **stated but remains open**.  The checked main
theorem proves it for each representation-finite algebra in any of these four
classes:

1. the algebra has at most nine indecomposable right modules up to isomorphism;
2. it is a Nakayama algebra;
3. its Jacobson radical has square zero;
4. it is representation-directed.

No Dynkin classification, ORT parametrization, or separate Poincaré-polynomial
theorem is part of the release target.

## Where to look

[`MainResults.lean`](MainResults.lean) is the short, stable map of the
advertised declarations.  The paper-facing aggregation theorem is
[`QuotientSubmoduleEquidistribution.MainTheoremEndpoint.rightQuotientSubmoduleEquidistribution`](QuotientSubmoduleEquidistribution/RepresentationTheory/MainTheoremEndpoint.lean).
Its four branches are exposed by
`QuotientSubmoduleEquidistribution.MainTheoremEndpoint.MainTheoremWitness` in the same file.

| Result | Lean declaration | Source |
| --- | --- | --- |
| Main four-case theorem | `QuotientSubmoduleEquidistribution.MainTheoremEndpoint.rightQuotientSubmoduleEquidistribution` | [`MainTheoremEndpoint.lean`](QuotientSubmoduleEquidistribution/RepresentationTheory/MainTheoremEndpoint.lean) |
| First and last four coefficients | `QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence.FirstLastFourEndpoint.bottom_top_four` | [`FirstLastFourEndpoint.lean`](QuotientSubmoduleEquidistribution/RepresentationTheory/FirstLastFourEndpoint.lean) |
| At most nine indecomposables | `QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence.FirstLastFourEndpoint.equidistribution_of_card_le_nine` | [`FirstLastFourEndpoint.lean`](QuotientSubmoduleEquidistribution/RepresentationTheory/FirstLastFourEndpoint.lean) |
| Nakayama case | `QuotientSubmoduleEquidistribution.NakayamaAlgebraProductFormula.rightQuotientSubmoduleEquidistribution` | [`NakayamaAlgebraProductFormula.lean`](QuotientSubmoduleEquidistribution/RepresentationTheory/NakayamaAlgebraProductFormula.lean) |
| Radical-square-zero case | `QuotientSubmoduleEquidistribution.RadicalSquareZero.rightQuotientSubmoduleEquidistribution_of_squareZero` | [`SeparatedDirectedInterface.lean`](QuotientSubmoduleEquidistribution/RadicalSquareZero/SeparatedDirectedInterface.lean) |
| Representation-directed case | `QuotientSubmoduleEquidistribution.rightRepresentationDirected_quotientSubmoduleEquidistribution` | [`AlgebraEndpoint.lean`](QuotientSubmoduleEquidistribution/RepresentationDirected/AlgebraEndpoint.lean) |
| Universal conjecture (statement only) | `QuotientSubmoduleEquidistribution.RightQuotientSubmoduleEquidistribution` | [`FiniteDimensionalAlgebra.lean`](QuotientSubmoduleEquidistribution/RepresentationTheory/FiniteDimensionalAlgebra.lean) |

The representation-directed branch is synchronized with the manuscript's
literal quotient-category proof. Its load-bearing strengthened identity is

```text
QuotientSubmoduleEquidistribution.RepresentationDirected.FactorARWord.
  selectedWordMixedMultiplicityFor_eq_factorHomDimension_of_reduced
```

It identifies the selected mixed coordinate with the dimension of the actual
ideal-quotient Hom space and proves its nonnegativity. The public reduced-word,
profile, equidistribution, and Bruhat-polynomial endpoints construct this
factor-category realization for both the source and opposite algebra; they do
not accept a supplied mesh-exactness package.

The exact convex-geometry interfaces added by the same frozen-paper audit are
`SetClosure.finiteIndependentEquivCompactClosedSet`,
`SetClosure.finiteIntervalDeletionChain`, and
`IndecomposableSkeleton.qClosed_finiteIntervalDeletionChain_of_finiteDimensional`.

## Finite translation-quiver verification

The paper's four-vertex pattern classification is supported by the
standard-library Python program
[`verification/four_vertex_patterns.py`](verification/four_vertex_patterns.py).
This is an exhaustive calculation on finite arrow relations, projective
subsets, and partial translations. It does not construct algebras or use QPA.
The program checks all classification assertions while enumerating the
patterns and reproduces the paper's counts: 6,933 labeled admissible patterns
in 329 isomorphism classes. See
[`verification/README.md`](verification/README.md) for the precise scope,
command, and complete expected output.

[`formalization.yaml`](formalization.yaml) gives the same map in a
machine-readable form, following the target-oriented convention used by
OpenAI's `ten-proofs` repository.  [`Audit.lean`](Audit.lean) checks every
public target and prints its axiom dependencies.  The nested
[`verification`](verification/) project contains concise independent target
statements; strict Comparator configurations are supplied for the three
standard-axiom class endpoints. Its intentional `sorry`s are not part of the
production library.

## Build and verify

The pinned toolchain is Lean 4.32.0.  From the repository root:

```text
lake update
lake exe cache get
lake build MainResults
lake env lean Audit.lean
python3 verification/four_vertex_patterns.py
python3 tools/check_release.py
```

`lake build QuotientSubmoduleEquidistribution` checks the full retained library.  The release check
also rejects production `sorry`/`admit`, project-local axioms, TauCeti imports
or package dependencies, missing targets, and broken static-site links.

## Scope and audit status

Lean has checked the declaration bodies against the pinned Mathlib revision;
the production source contains no `sorry`, `admit`, or project-local `axiom`.
The finite first/last-four classifiers use Lean 4.32's `bv_decide`, whose
native LRAT-certificate checks appear as generated axioms and add the compiler
and interpreter to the trusted base for that branch.  [`TRUST.md`](TRUST.md)
records the exact scope; `Audit.lean` prints the generated names. The
advertised theorem signatures and the frozen manuscript's load-bearing proof
path have undergone a paper-interface audit. This is not a claim that an
independent human has line-by-line audited every proof body. The website does
not advertise the unused two-sided strictness packaging of the paper's general
tau-category corollary; it exposes the exact right-sequence strictness and
representable-Hom expansion consumed by the main theorem. In particular, the
first/last-four development is exposed separately to make the most technical
branch easy to inspect.

Right modules are represented as finitely generated modules over `Aᵐᵒᵖ`.
The main theorem assumes a field `K`, `IsAlgClosed K`, a finite-dimensional
`K`-algebra `A`, and a right-representation-finiteness witness.  The Nakayama
case itself is formalized over an arbitrary field where algebraic closedness
is unnecessary.

Readers need only basic representation theory of finite-dimensional algebras
to understand the mathematical overview.  Lean familiarity is useful for
reading declarations but is not assumed by the website.

## Documentation

The hand-written site lives in [`website`](website/) and is ready for GitHub
Pages. It contains direct theorem/source links and source-derived interactive
import graphs, including dedicated views of the factor-category proof and the
finite convex-interval interfaces. API documentation is generated with
doc-gen4 from the isolated [`docbuild`](docbuild/) project, so documentation
tooling does not become a production dependency. The site also links
source-derived, project-only interactive import graphs for the main theorem
and each principal branch.
Automatic Pages deployment is skipped while the repository is private; after
making it public, run the `Pages` workflow once from the Actions tab.  Later
pushes to `main` deploy automatically.

## Provenance and license

See [`PROVENANCE.md`](PROVENANCE.md) for the frozen source checkpoint and
dependency boundary.  A small foundational layer was adapted from TauCeti;
those source headers and [`NOTICE`](NOTICE) record the attribution.  The
repository is licensed under Apache-2.0.
