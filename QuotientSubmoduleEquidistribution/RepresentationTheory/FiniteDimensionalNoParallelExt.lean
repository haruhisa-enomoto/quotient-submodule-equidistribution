import QuotientSubmoduleEquidistribution.RepresentationTheory.GabrielArrowBridge

/-!
# No parallel Ext arrows for finite complete skeletons

This is the left-module form of the finite-isomorphism-class argument.  It is
kept upstream of all hereditary and small-core classifications because it is
a general finite-dimensional statement.
-/

noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.FiniteDimensionalNoParallelExt

universe u v

variable {K R : Type u}
  [Field K] [IsAlgClosed K]
  [Ring R] [Small.{u} R] [Algebra K R]
  [FiniteDimensional K R] [IsNoetherianRing R]
  {iota : Type v} [Finite iota]
  (sigma : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, v, u} R iota)

/-- A finite complete skeleton over a finite-dimensional algebra over an
algebraically closed field has no parallel degree-one Ext arrows. -/
theorem noParallelExtSupport :
    QuotientSubmoduleEquidistribution.GabrielArrowBridge.NoParallelExtSupport
      (K := K) sigma := by
  intro s t
  letI : IsArtinianRing R := IsArtinianRing.of_finite K R
  letI : IsSimpleModule R (sigma.obj s.1) :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).mp
      s.2
  letI : IsSimpleModule R (sigma.obj t.1) :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).mp
      t.2
  letI : Module K (sigma.obj s.1) :=
    Module.restrictScalars K R _
  letI : Module K (sigma.obj t.1) :=
    Module.restrictScalars K R _
  letI : IsScalarTower K R (sigma.obj s.1) :=
    IsScalarTower.restrictScalars K R _
  letI : IsScalarTower K R (sigma.obj t.1) :=
    IsScalarTower.restrictScalars K R _
  letI : FiniteDimensional K (sigma.obj s.1) :=
    Module.Finite.trans R _
  letI : FiniteDimensional K (sigma.obj t.1) :=
    Module.Finite.trans R _
  letI : FiniteDimensional K
      (CategoryTheory.End
        (ModuleCat.of R (sigma.obj t.1))) :=
    QuotientSubmoduleEquidistribution.NoParallelExtOne.moduleFinite_moduleCatHom_of_finiteDimensional
      (K := K) (R := R)
  letI : FiniteDimensional K
      (CategoryTheory.End
        (ModuleCat.of R (sigma.obj s.1))) :=
    QuotientSubmoduleEquidistribution.NoParallelExtOne.moduleFinite_moduleCatHom_of_finiteDimensional
      (K := K) (R := R)
  letI : FiniteDimensional K
      (CategoryTheory.Abelian.Ext
        (ModuleCat.of R (sigma.obj s.1))
        (ModuleCat.of R (sigma.obj t.1)) 1) :=
    QuotientSubmoduleEquidistribution.NoParallelExtOne.moduleFinite_ext_one_of_finiteDimensional
      (K := K) (R := R)
  exact ⟨inferInstance,
    QuotientSubmoduleEquidistribution.NoParallelExtOne.finrank_ext_one_le_one_of_finite_skeleton
      sigma⟩

end QuotientSubmoduleEquidistribution.FiniteDimensionalNoParallelExt
