import QuotientSubmoduleEquidistribution.RepresentationTheory.SeparatedQuiverArrowExtraction
import QuotientSubmoduleEquidistribution.RepresentationTheory.SeparatedTriangularAlgebraEquivalence

/-!
# Separated-quiver representations as triangular-algebra modules

Combining literal separated-quiver coordinates, the finite arrow-bimodule
equivalence, and the triangular realization identifies representations of the
separated quiver with modules over its basis-free triangular algebra.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.SeparatedQuiverTriangularEquivalence

open QuotientSubmoduleEquidistribution.SeparatedQuiver
open QuotientSubmoduleEquidistribution.SeparatedQuiverArrowBimodule
open QuotientSubmoduleEquidistribution.SeparatedQuiverArrowExtraction

universe uK uV v

variable (K : Type uK) (V : Type uV)
variable [Field K] [Fintype V] [DecidableEq V] [Quiver.{v} V]
variable [∀ i j : V, Fintype (i ⟶ j)] [∀ i j : V, DecidableEq (i ⟶ j)]

/-- Representations of the literal separated quiver are categorically
equivalent to modules over the triangular algebra built from the vertex ring
and the arrow bimodule. -/
def moduleEquivalence :
    CategoryTheory.Equivalence
      (QuotientSubmoduleEquidistribution.Foundation.QuiverRep K (Vertex V))
      (ModuleCat.{uV}
        (SeparatedTriangularAlgebra.Algebra (V → K) (ArrowBimodule K V))) :=
  (RepresentationData.quiverRepEquivalence
      (K := K) (V := V)).symm.trans
    ((arrowActionEquivalence K V).trans
      (SeparatedTriangularAlgebra.moduleEquivalence
        (S := V → K) (J := ArrowBimodule K V)))

end QuotientSubmoduleEquidistribution.SeparatedQuiverTriangularEquivalence
