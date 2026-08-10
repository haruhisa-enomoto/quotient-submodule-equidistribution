import QuotientSubmoduleEquidistribution.RepresentationTheory.AuslanderEquivalence
import QuotientSubmoduleEquidistribution.RepresentationTheory.FiniteDimensionalAlgebra

/-!
# The canonical right-module Auslander equivalence

This is the paper-facing specialization of the generic additive-generator
equivalence to a representation-finite finite-dimensional algebra.
-/

noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.AuslanderEquivalence

universe v u w

section CanonicalRightModules

variable (K : Type u) (A : Type v)
  [Field K] [Ring A] [Algebra K A]
  [FiniteDimensional K A]

/-- The exact paper-facing specialization: under conventional
representation-finiteness, take the direct sum of the canonical
indecomposable right-module representatives and apply the finite-skeleton
Auslander equivalence. -/
noncomputable def canonicalRightModuleAuslanderEquivalence
    (hrep : IsRightRepresentationFinite.{u, v, w} K A) :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    letI : Finite
        (CanonicalIndecomposableIndex.{v, w} Aᵐᵒᵖ) :=
      hrep
    let σ :=
      rightIndecomposableSkeleton.{u, v, w} K A
    FGModuleCat.{w} Aᵐᵒᵖ ≌
      (finiteProjectiveModules
        (End
          (FiniteTypeGenerator.additiveGenerator σ))ᵐᵒᵖ).FullSubcategory := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  letI : Finite
      (CanonicalIndecomposableIndex.{v, w} Aᵐᵒᵖ) :=
    hrep
  dsimp only
  exact
    FiniteTypeGenerator.auslanderEquivalence
      (rightIndecomposableSkeleton.{u, v, w} K A)

end CanonicalRightModules

end QuotientSubmoduleEquidistribution.AuslanderEquivalence
