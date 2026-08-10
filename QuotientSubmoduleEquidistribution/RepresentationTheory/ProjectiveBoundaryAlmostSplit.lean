import QuotientSubmoduleEquidistribution.RepresentationTheory.AlmostSplitCofinite
import QuotientSubmoduleEquidistribution.RepresentationTheory.ProjectiveSimpleRank

/-!
# The projective boundary right almost-split morphism

For an indecomposable projective finite-length module `P`, the inclusion
`rad P ⟶ P` of its module Jacobson radical is minimal right almost split.
This file proves that statement for an arbitrary complete indecomposable
skeleton and packages the inclusion with the skeleton's finite decomposition
of `rad P`.

No field, finite ambient skeleton, algebra presentation, or module
classification is used.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe u v

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v}
  (σ : IndecomposableSkeleton.{u, v, u} R ι)

/-- The module Jacobson radical of a chosen representative, bundled as a
finitely generated module. -/
abbrev projectiveBoundaryRadical (p : ι) : FGModuleCat.{u} R :=
  FGModuleCat.of R (Module.jacobson R (σ.obj p))

/-- The canonical inclusion `rad P ⟶ P` at a chosen label. -/
def projectiveBoundaryRadicalInclusion (p : ι) :
    σ.projectiveBoundaryRadical p ⟶ σ.obj p :=
  FGModuleCat.ofHom (Module.jacobson R (σ.obj p)).subtype

private theorem projectiveBoundary_jacobson_isCoatom
    (p : ι) (hp : Projective (σ.obj p)) :
    IsCoatom (Module.jacobson R (σ.obj p)) := by
  letI : Projective (σ.obj p) := hp
  letI : Module.Projective R (σ.obj p) :=
    ProjectiveSimpleRank.moduleProjective_of_fgProjective (σ.obj p) hp
  letI : Nontrivial (σ.obj p) := (σ.indecomposable p).nontrivial
  letI : IsLocalRing (Module.End R (σ.obj p)) :=
    QuotientSubmoduleEquidistribution.Foundation.isLocalRing_end_of_isIndecomposable
      (σ.finiteLength p) (σ.indecomposable p)
  exact
    QuotientSubmoduleEquidistribution.ProjectiveSimpleTop.jacobson_isCoatom_of_local_end

/-- The inclusion of the Jacobson radical of an indecomposable projective
is right almost split.  A nonsplit map into the projective has proper range;
the unique maximal submodule property forces that range into the radical. -/
theorem projectiveBoundaryRadicalInclusion_isRightAlmostSplit
    (p : ι) (hp : Projective (σ.obj p)) :
    IsRightAlmostSplit (σ.projectiveBoundaryRadicalInclusion p) := by
  classical
  letI : Projective (σ.obj p) := hp
  have hradCoatom :=
    projectiveBoundary_jacobson_isCoatom σ p hp
  constructor
  · intro hsplit
    letI : IsSplitEpi (σ.projectiveBoundaryRadicalInclusion p) := hsplit
    have hsurjective : Function.Surjective
        (σ.projectiveBoundaryRadicalInclusion p).hom.hom :=
      (fg_epi_iff_surjective
        (σ.projectiveBoundaryRadicalInclusion p)).1 inferInstance
    apply hradCoatom.ne_top
    apply top_unique
    intro x _
    obtain ⟨y, hy⟩ := hsurjective x
    rw [← hy]
    exact y.2
  · intro X g hg
    have hrangeProper : LinearMap.range g.hom.hom ≠ ⊤ := by
      intro hrange
      have hsurjective : Function.Surjective g.hom.hom :=
        LinearMap.range_eq_top.mp hrange
      letI : Epi g := (fg_epi_iff_surjective g).2 hsurjective
      apply hg
      obtain ⟨s, hs⟩ := Projective.factors (𝟙 (σ.obj p)) g
      exact IsSplitEpi.mk'
        { section_ := s
          id := hs }
    obtain ⟨M, hMCoatom, hrangeM⟩ :=
      (eq_top_or_exists_le_coatom
        (LinearMap.range g.hom.hom)).resolve_left hrangeProper
    have hradM : Module.jacobson R (σ.obj p) ≤ M := by
      rw [Module.jacobson]
      exact sInf_le hMCoatom
    have hMrad : M = Module.jacobson R (σ.obj p) :=
      (hradCoatom.le_iff_eq hMCoatom.ne_top).1 hradM
    have hrangeRadical :
        LinearMap.range g.hom.hom ≤
          Module.jacobson R (σ.obj p) := by
      simpa only [hMrad] using hrangeM
    let lift : X ⟶ σ.projectiveBoundaryRadical p :=
      FGModuleCat.ofHom
        (LinearMap.codRestrict
          (Module.jacobson R (σ.obj p)) g.hom.hom
          (fun x ↦ hrangeRadical (LinearMap.mem_range_self g.hom.hom x)))
    refine ⟨lift, ?_⟩
    apply FGModuleCat.hom_ext
    ext x
    rfl

/-- The projective-boundary radical inclusion is right minimal. -/
theorem projectiveBoundaryRadicalInclusion_isRightMinimal (p : ι) :
    IsRightMinimal (σ.projectiveBoundaryRadicalInclusion p) := by
  letI : Mono (σ.projectiveBoundaryRadicalInclusion p) :=
    (fg_mono_iff_injective
      (σ.projectiveBoundaryRadicalInclusion p)).2
        (Module.jacobson R (σ.obj p)).subtype_injective
  intro e he
  have heq : e = 𝟙 (σ.projectiveBoundaryRadical p) := by
    exact (cancel_mono (σ.projectiveBoundaryRadicalInclusion p)).1
      (by simpa only [Category.id_comp] using he)
  rw [heq]
  infer_instance

/-- The radical of a chosen representative has finite length. -/
theorem projectiveBoundaryRadical_isFiniteLength (p : ι) :
    IsFiniteLength R (σ.projectiveBoundaryRadical p) :=
  (σ.finiteLength p).of_injective
    (Module.jacobson R (σ.obj p)).subtype_injective

/-- The canonical minimal right almost-split decomposition ending at an
indecomposable projective.  Its middle term is literally `rad P`, and its
finite indecomposable decomposition comes from completeness of the supplied
skeleton. -/
def projectiveBoundaryMinimalRightAlmostSplitDecomposition
    (p : ι) (hp : Projective (σ.obj p)) :
    σ.MinimalRightAlmostSplitDecomposition p :=
  MinimalRightAlmostSplitDecomposition.ofMap σ
    (σ.projectiveBoundaryRadicalInclusion p)
    (σ.projectiveBoundaryRadical_isFiniteLength p)
    (σ.projectiveBoundaryRadicalInclusion_isRightAlmostSplit p hp)
    (σ.projectiveBoundaryRadicalInclusion_isRightMinimal p)

/-- At a projective endpoint, an indecomposable occurs as a direct summand
of `rad P` exactly when it is the source of an irreducible morphism to `P`.
This is the intrinsic, multiplicity-blind projective boundary dictionary. -/
theorem indecomposableRetract_projectiveBoundaryRadical_iff_irreducible
    (p : ι) (hp : Projective (σ.obj p)) (x : ι) :
    Nonempty (Retract (σ.obj x) (σ.projectiveBoundaryRadical p)) ↔
      HasIrreducibleMorphism (σ.obj x) (σ.obj p) := by
  exact MinimalRightAlmostSplitDecomposition.indecomposableRetract_middle_iff_irreducible
    (σ.projectiveBoundaryMinimalRightAlmostSplitDecomposition p hp) x

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
