import Mathlib.Algebra.Category.ModuleCat.Algebra
import Mathlib.Algebra.Category.ModuleCat.Ext.DimensionShifting
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# An upper-radical Ext obstruction

For a projective presentation `0 → W → P → S → 0`, if there are no
maps `P → W`, the connecting map identifies `End(W)` with `Ext¹(S,W)`.
Thus a length-two uniserial `W` with two-dimensional endomorphism ring
obstructs a universal upper-radical rank-one bound.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace QuotientSubmoduleEquidistribution.UniserialUpperExtObstruction

universe u

variable {K R : Type u}
  [Field K] [Ring R] [Algebra K R] [Small.{u} R]

/-- In a projective presentation `0 → W → P → S → 0`, the connecting
map `Ext⁰(W,W) → Ext¹(S,W)` is bijective if `Hom(P,W)=0`. -/
theorem extClass_precomp_bijective_of_projective_middle_of_hom_eq_zero
    {S : ShortComplex (ModuleCat.{u} R)}
    (hS : S.ShortExact) [Projective S.X₂]
    (hHom : ∀ f : S.X₂ ⟶ S.X₁, f = 0) :
    Function.Bijective
      (hS.extClass.precompOfLinear K S.X₁ (add_zero 1)) := by
  constructor
  · intro x y hxy
    apply sub_eq_zero.mp
    have hker :
        hS.extClass.comp (x - y) (add_zero 1) = 0 := by
      change
        (hS.extClass.precompOfLinear K S.X₁ (add_zero 1)) (x - y) = 0
      rw [map_sub, hxy, sub_self]
    obtain ⟨z, hz⟩ :=
      Ext.contravariant_sequence_exact₁
        hS S.X₁ (x - y) (add_zero 1) hker
    have hzZero : z = 0 := by
      apply (Ext.linearEquiv₀ (R := K)).injective
      simpa using hHom (Ext.linearEquiv₀ (R := K) z)
    rw [hzZero] at hz
    simpa using hz.symm
  · intro x
    obtain ⟨z, hz⟩ :=
      Ext.contravariant_sequence_exact₃ hS S.X₁ x
        (Ext.eq_zero_of_projective _) (add_zero 1)
    exact ⟨z, hz⟩

/-- Under the same hypotheses, dimension shifting gives a `K`-linear
equivalence `End(W) ≃ Ext¹(S,W)`. -/
def endLinearEquivExtOne_of_projective_middle_of_hom_eq_zero
    {S : ShortComplex (ModuleCat.{u} R)}
    (hS : S.ShortExact) [Projective S.X₂]
    (hHom : ∀ f : S.X₂ ⟶ S.X₁, f = 0) :
    (S.X₁ ⟶ S.X₁) ≃ₗ[K] Ext S.X₃ S.X₁ 1 :=
  (Ext.linearEquiv₀ (R := K)).symm.trans
    (LinearEquiv.ofBijective
      (hS.extClass.precompOfLinear K S.X₁ (add_zero 1))
      (extClass_precomp_bijective_of_projective_middle_of_hom_eq_zero
        hS hHom))

/-- Consequently, the upper `Ext¹` space and the endomorphism ring of the
kernel have equal finite dimension. -/
theorem finrank_extOne_eq_finrank_end_of_projective_middle_of_hom_eq_zero
    {S : ShortComplex (ModuleCat.{u} R)}
    (hS : S.ShortExact) [Projective S.X₂]
    (hHom : ∀ f : S.X₂ ⟶ S.X₁, f = 0)
    [FiniteDimensional K (S.X₁ ⟶ S.X₁)]
    [FiniteDimensional K (Ext S.X₃ S.X₁ 1)] :
    Module.finrank K (Ext S.X₃ S.X₁ 1) =
      Module.finrank K (S.X₁ ⟶ S.X₁) := by
  exact LinearEquiv.finrank_eq
    (endLinearEquivExtOne_of_projective_middle_of_hom_eq_zero hS hHom).symm

/-- If the kernel endomorphism ring has dimension two, so does the upper
`Ext¹` space. -/
theorem finrank_extOne_eq_two_of_finrank_end_eq_two
    {S : ShortComplex (ModuleCat.{u} R)}
    (hS : S.ShortExact) [Projective S.X₂]
    (hHom : ∀ f : S.X₂ ⟶ S.X₁, f = 0)
    [FiniteDimensional K (S.X₁ ⟶ S.X₁)]
    [FiniteDimensional K (Ext S.X₃ S.X₁ 1)]
    (hEnd : Module.finrank K (S.X₁ ⟶ S.X₁) = 2) :
    Module.finrank K (Ext S.X₃ S.X₁ 1) = 2 :=
  (finrank_extOne_eq_finrank_end_of_projective_middle_of_hom_eq_zero
    hS hHom).trans hEnd

/-- A two-dimensional endomorphism ring therefore refutes the corresponding
rank-one upper-radical bound. -/
theorem not_finrank_extOne_le_one_of_finrank_end_eq_two
    {S : ShortComplex (ModuleCat.{u} R)}
    (hS : S.ShortExact) [Projective S.X₂]
    (hHom : ∀ f : S.X₂ ⟶ S.X₁, f = 0)
    [FiniteDimensional K (S.X₁ ⟶ S.X₁)]
    [FiniteDimensional K (Ext S.X₃ S.X₁ 1)]
    (hEnd : Module.finrank K (S.X₁ ⟶ S.X₁) = 2) :
    ¬ Module.finrank K (Ext S.X₃ S.X₁ 1) ≤ 1 := by
  rw [finrank_extOne_eq_two_of_finrank_end_eq_two hS hHom hEnd]
  omega

end QuotientSubmoduleEquidistribution.UniserialUpperExtObstruction
