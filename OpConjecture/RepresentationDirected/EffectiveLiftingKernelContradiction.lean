import OpConjecture.RepresentationDirected.EffectiveLiftingKernel
import OpConjecture.RepresentationDirected.EffectiveLiftingCoordinates
import OpConjecture.RepresentationDirected.EffectiveLiftingComplement

/-!
# Kernel orthogonality in directed effective lifting

This file packages the central contradiction in the induction: after
representing all labels above the least retained label, no nonzero map from
that least object can enter the kernel.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace OpConjecture.RepresentationDirected

universe u uIota

variable (K R : Type u) [Field K] [IsAlgClosed K]
  [Ring R] [Algebra K R] [FiniteDimensional K R] [IsNoetherianRing R]
  {Iota : Type uIota} [Fintype Iota]
  (sigma : IndecomposableSkeleton.{u, uIota, u} R Iota)

/-- A recursive Hom-isomorphism above the least retained label, whose source
has zero old coordinate at that label, has no nonzero map from the least
object into its kernel under retained-coordinate nonnegativity. -/
theorem hom_kernel_eq_zero_of_recursive_bijective_of_nonnegative
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : Finset Iota) {i : Iota} (hi : i ∉ D)
    (hleast : IsLeastRetained R sigma H D i)
    {T Y : FGModuleCat.{u} R} (f : T ⟶ Y)
    (hf : ∀ a, a ∉ D.cons i hi →
      Function.Bijective (postcompose (U := sigma.obj a) f))
    (hTi : mixedMultiplicity K R sigma H D T i = 0)
    (hnonnegative : ∀ (M : FGModuleCat.{u} R) a, a ∉ D →
      0 ≤ mixedMultiplicity K R sigma H D M a)
    (g : sigma.obj i ⟶ kernel f) :
    g = 0 := by
  by_contra hg
  let W : KernelSummandWitness sigma (sigma.obj i) (kernel f) :=
    Classical.choice (exists_kernelSummandWitness sigma f g hg)
  letI : IsSplitMono W.inclusion := W.inclusion_isSplitMono sigma
  let V : FGModuleCat.{u} R := deletedQuotient f W.inclusion
  let q : T ⟶ V := deletedProjection f W.inclusion
  let j : sigma.obj W.label ⟶ T := deletedInclusion f W.inclusion
  have hq_bijective : ∀ a, a ∉ D.cons i hi →
      Function.Bijective (postcompose (U := sigma.obj a) q) := by
    intro a ha
    exact (quotient_preserves_postcompose_bijective
      f W.inclusion (hf a ha)).1
  have hHom : ∀ a, a ∉ D.cons i hi →
      homFinrankVector K R sigma V a =
        homFinrankVector K R sigma T a := by
    intro a ha
    letI : FiniteDimensional K (sigma.obj a ⟶ T) :=
      finiteDimensional_hom_from_obj K R sigma a T
    letI : FiniteDimensional K (sigma.obj a ⟶ V) :=
      finiteDimensional_hom_from_obj K R sigma a V
    have hq_linear : Function.Bijective
        (postcompLinearMap (K := K) (X := sigma.obj a) q) := by
      have hb := hq_bijective a ha
      constructor
      · intro x y hxy
        apply hb.1
        exact hxy
      · intro y
        obtain ⟨x, hx⟩ := hb.2 y
        exact ⟨x, hx⟩
    have hfinrank :=
      (LinearEquiv.ofBijective
        (postcompLinearMap (K := K) (X := sigma.obj a) q)
        hq_linear).finrank_eq
    change (Module.finrank K (sigma.obj a ⟶ V) : ℤ) =
      (Module.finrank K (sigma.obj a ⟶ T) : ℤ)
    exact_mod_cast hfinrank.symm
  have hrow := H.homFinrankVector_eq_add_mixedMultiplicity
    K R sigma D hi hleast T V hHom hTi
  have hmu : 0 ≤ mixedMultiplicity K R sigma H D V i :=
    hnonnegative V i hi
  have hleInt : homFinrankVector K R sigma T i ≤
      homFinrankVector K R sigma V i := by
    omega
  have hle : Module.finrank K (sigma.obj i ⟶ T) ≤
      Module.finrank K (sigma.obj i ⟶ V) := by
    change (Module.finrank K (sigma.obj i ⟶ T) : ℤ) ≤
      (Module.finrank K (sigma.obj i ⟶ V) : ℤ) at hleInt
    exact_mod_cast hleInt
  letI : FiniteDimensional K (sigma.obj i ⟶ T) :=
    finiteDimensional_hom_from_obj K R sigma i T
  letI : FiniteDimensional K (sigma.obj i ⟶ V) :=
    finiteDimensional_hom_from_obj K R sigma i V
  haveI : Mono j := by
    dsimp only [j, deletedInclusion]
    infer_instance
  have hjq : j ≫ q = 0 := by
    simpa only [j, q, deletedInclusion, deletedProjection] using
      cokernel.condition (deletedInclusion f W.inclusion)
  let S := ShortComplex.mk j q hjq
  have hS : S.ShortExact := by
    refine { exact := ?_ }
    simpa only [S, j, q, deletedInclusion, deletedProjection, hjq] using
      ShortComplex.exact_cokernel (deletedInclusion f W.inclusion)
  by_cases hprojective : Projective (sigma.obj i)
  · letI : Projective (sigma.obj i) := hprojective
    have hzero := hom_left_eq_zero_of_projective_of_finrank_le
      (K := K) j q hjq hle W.component
    exact W.component_ne_zero hzero
  · let x : sigma.NonprojectiveLabel := ⟨i, hprojective⟩
    have hzero := hom_left_eq_zero_of_nonprojective_of_finrank_le
      K R sigma H x W.label hS hle W.component
    exact W.component_ne_zero hzero

end OpConjecture.RepresentationDirected
