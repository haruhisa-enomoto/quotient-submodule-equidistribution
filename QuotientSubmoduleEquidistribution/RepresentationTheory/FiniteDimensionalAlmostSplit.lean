import QuotientSubmoduleEquidistribution.RepresentationTheory.FiniteDimensionalStableHomExt
import QuotientSubmoduleEquidistribution.RepresentationTheory.StableEndResidueLinear
import QuotientSubmoduleEquidistribution.RepresentationTheory.FGExtRealization

/-!
# Right almost-split maps over finite-dimensional algebras

For a nonprojective chosen indecomposable, the field-valued stable Hom--Ext
duality and the canonical projective-stable residue select a nonzero socle
class.  Finite realization of that `Ext¹` class then produces a right
almost-split morphism.

The result applies to an arbitrary indecomposable skeleton; neither
representation-finiteness nor a concrete algebra or module classification is
used.  The construction is one-sided: no left almost-split map or
presentation-independent identification of the starting term is asserted.
-/

noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

open QuotientSubmoduleEquidistribution.RingelStable
open QuotientSubmoduleEquidistribution.AuslanderTranspose
open QuotientSubmoduleEquidistribution.AuslanderTranspose.TwoStepProjectivePresentation

universe u uIota

section FixedHomologicalData

variable (K R : Type u) [Field K] [Ring R] [Algebra K R]
  [FiniteDimensional K R]
  [IsNoetherianRing R] [IsNoetherianRing Rᵐᵒᵖ]
  [HasExt.{u} (FGModuleCat.{u} R)]
  (sigma : IndecomposableSkeleton.{u, uIota, u} R Iota)

local instance : Linear K (ProjectiveStableCategory (R := R)) :=
  ProjectiveStableScalar.linear K R

local instance : Functor.Linear K
    (projectiveStableFunctor (R := R)) :=
  ProjectiveStableScalar.functorLinear K R

/-- A field-valued stable Hom--Ext socle pairing constructed from the
canonical stable residue and attached to a two-step presentation of a
nonprojective chosen indecomposable. -/
def finiteDimensionalProjectiveStableHomExtSoclePairing
    (x : Iota) (hx : ¬ Projective (sigma.obj x))
    (P : TwoStepProjectivePresentation (sigma.obj x)) :
    StableHomExtSoclePairing
      (projectiveStableFunctor (R := R)) (sigma.obj x)
      (P.dTranspose (ArtinDuality.ofFiniteDimensional K)) K :=
  sigma.projectiveStableHomExtSoclePairing (K := K) x hx
    (finiteDimensionalStableHomExtLinearDuality K R P)

/-- Every chosen presentation of a nonprojective indecomposable supplies a
short exact sequence whose quotient map is right almost split. -/
theorem exists_rightAlmostSplitSequence_of_finiteDimensional
    (x : Iota) (hx : ¬ Projective (sigma.obj x))
    (P : TwoStepProjectivePresentation (sigma.obj x)) :
    ∃ (E : FGModuleCat.{u} R)
      (i : P.dTranspose (ArtinDuality.ofFiniteDimensional K) ⟶ E)
      (q : E ⟶ sigma.obj x) (zero : i ≫ q = 0)
      (hS : (ShortComplex.mk i q zero).ShortExact),
      hS.extClass =
          (sigma.finiteDimensionalProjectiveStableHomExtSoclePairing
            K R x hx P).socleClass ∧
        IsRightAlmostSplit q :=
  (sigma.finiteDimensionalProjectiveStableHomExtSoclePairing
    K R x hx P).exists_rightAlmostSplit

end FixedHomologicalData

section AutomaticData

variable (K R : Type u) [Field K] [Ring R] [Algebra K R]
  [FiniteDimensional K R] [IsNoetherianRing R]
  (sigma : IndecomposableSkeleton.{u, uIota, u} R Iota)

include K in
/-- Every nonprojective chosen indecomposable over a finite-dimensional
algebra admits a right almost-split morphism.  The right-Noetherian and
`HasExt` data used by the construction are selected from the
finite-dimensional hypotheses. -/
theorem exists_rightAlmostSplit_of_finiteDimensional
    (x : Iota) (hx : ¬ Projective (sigma.obj x)) :
    ∃ (E : FGModuleCat.{u} R) (q : E ⟶ sigma.obj x),
      IsRightAlmostSplit q := by
  letI : IsNoetherianRing Rᵐᵒᵖ :=
    IsNoetherianRing.of_finite K Rᵐᵒᵖ
  letI : HasExt.{u} (FGModuleCat.{u} R) :=
    hasExt_of_enoughProjectives.{u} (FGModuleCat.{u} R)
  letI : Linear K (ProjectiveStableCategory (R := R)) :=
    ProjectiveStableScalar.linear K R
  letI : Functor.Linear K (projectiveStableFunctor (R := R)) :=
    ProjectiveStableScalar.functorLinear K R
  let P := Classical.choice
    (twoStepProjectivePresentation_nonempty (X := sigma.obj x))
  obtain ⟨E, i, q, zero, hS, hclass, hq⟩ :=
    sigma.exists_rightAlmostSplitSequence_of_finiteDimensional K R x hx P
  exact ⟨E, q, hq⟩

include K in
omit [IsNoetherianRing R] in
/-- Every finitely generated module over a finite-dimensional algebra has
finite length. -/
theorem fgModule_isFiniteLength_of_finiteDimensional
    (E : FGModuleCat.{u} R) : IsFiniteLength R E := by
  letI : IsArtinianRing R := IsArtinianRing.of_finite K R
  exact
    ((IsArtinianRing.tfae R E).out 0 3).mp
      (inferInstance : Module.Finite R E)

include K in
/-- Stable Hom--Ext duality constructs a finite-length right almost-split
middle term without any finiteness assumption on the indecomposable
skeleton. -/
theorem exists_finiteLength_rightAlmostSplit_of_finiteDimensional_of_not_projective
    (x : Iota) (hx : ¬ Projective (sigma.obj x)) :
    ∃ (E : FGModuleCat.{u} R) (q : E ⟶ sigma.obj x),
      IsFiniteLength R E ∧ IsRightAlmostSplit q := by
  obtain ⟨E, q, hq⟩ :=
    sigma.exists_rightAlmostSplit_of_finiteDimensional K R x hx
  exact ⟨E, q, fgModule_isFiniteLength_of_finiteDimensional K R E, hq⟩

include K in
/-- The finite-length minimalization theorem turns the right almost-split
map obtained from stable Hom--Ext duality into a minimal right almost-split
decomposition.  No finite skeleton or minimal projective presentation is
required. -/
theorem minimalRightAlmostSplitDecomposition_nonempty_of_finiteDimensional_of_not_projective
    (x : Iota) (hx : ¬ Projective (sigma.obj x)) :
    Nonempty (sigma.MinimalRightAlmostSplitDecomposition x) := by
  obtain ⟨E, q, hE, hq⟩ :=
    sigma.exists_finiteLength_rightAlmostSplit_of_finiteDimensional_of_not_projective
      K R x hx
  exact
    MinimalRightAlmostSplitDecomposition.exists_of_rightAlmostSplit_of_finiteLength
      sigma q hq hE

end AutomaticData

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
