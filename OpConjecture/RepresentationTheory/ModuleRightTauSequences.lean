import OpConjecture.CategoryTheory.CategoricalRadicalIdeal
import OpConjecture.CategoryTheory.IyamaTauSequence
import OpConjecture.RepresentationTheory.FactorLadderARData
import OpConjecture.RepresentationTheory.IrreducibleRadicalQuotient

/-!
# Right tau-sequences from module Auslander--Reiten data

The chosen minimal right almost-split map at a nonprojective indecomposable,
together with its kernel inclusion, is a right tau-sequence.  At a projective
indecomposable the boundary sequence is `0 ⟶ rad P ⟶ P`.  This supplies the
ambient module-category tau meshes needed before passing to an ideal
quotient; it uses no classification of modules or concrete algebra.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace OpConjecture.IndecomposableSkeleton

open CategoricalRadical

universe u v

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v}
  (σ : IndecomposableSkeleton.{u, v, u} R ι)
  (D : σ.FiniteARTranslationData)

namespace FiniteARTranslationData

/-- The kernel--middle--endpoint complex of the chosen AR map at a
nonprojective indecomposable. -/
def nonprojectiveRightMesh
    (x : {x : ι // ¬ Projective (σ.obj x)}) :
    ShortComplex (FGModuleCat.{u} R) :=
  ShortComplex.mk (arKernelMap σ D x) (chosenRightAR σ D x).map (by
    dsimp only [arKernelMap]
    rw [Category.assoc, kernel.condition, comp_zero])

/-- The chosen nonprojective AR complex is a right tau-sequence. -/
theorem nonprojectiveRightTau
    (x : {x : ι // ¬ Projective (σ.obj x)}) :
    Iyama.RightTauSequence (nonprojectiveRightMesh σ D x) := by
  have hfmono : Mono (arKernelMap σ D x) := by
    dsimp only [arKernelMap]
    infer_instance
  letI : Mono (arKernelMap σ D x) := hfmono
  have hfRad : IsRadicalMorphism (arKernelMap σ D x) :=
    (σ.isRadicalMorphism_iff_not_isSplitMono_from_obj
      (arKernelMap σ D x)).2
      (arKernelMap_leftAlmostSplit σ D x).not_isSplitMono
  have hgRad : IsRadicalMorphism (chosenRightAR σ D x).map :=
    (σ.isRadicalMorphism_iff_not_isSplitEpi_to_obj
      (chosenRightAR σ D x).map).2
      (chosenRightAR σ D x).rightAlmostSplit.not_isSplitEpi
  refine
    { f_radical := hfRad
      g_radical := hgRad
      factors_from_left := ?_
      factors_into_right := ?_
      minimalWeakKernel := ?_ }
  · intro W a ha
    exact (arKernelMap_leftAlmostSplit σ D x).factors a
      ((σ.isRadicalMorphism_iff_not_isSplitMono_from_obj a).1 ha)
  · intro W a ha
    exact (chosenRightAR σ D x).rightAlmostSplit.factors a
      ((σ.isRadicalMorphism_iff_not_isSplitEpi_to_obj a).1 ha)
  · constructor
    · rw [Iyama.ShortComplex.isWeakKernel_iff]
      intro W k hk
      let l : W ⟶ kernel (chosenRightAR σ D x).map :=
        kernel.lift (chosenRightAR σ D x).map k hk
      refine ⟨l ≫ (arTranslationKernelIso σ D x).hom, ?_⟩
      dsimp only [nonprojectiveRightMesh, arKernelMap]
      simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
        kernel.lift_ι (chosenRightAR σ D x).map k hk
    · intro e he
      have heq : e = 𝟙 _ := by
        apply (cancel_mono (arKernelMap σ D x)).1
        change e ≫ arKernelMap σ D x =
          𝟙 _ ≫ arKernelMap σ D x
        change e ≫ arKernelMap σ D x = arKernelMap σ D x at he
        simpa only [Category.id_comp] using he
      rw [heq]
      infer_instance

/-- The projective boundary complex `0 ⟶ rad P ⟶ P`. -/
def projectiveRightMesh (p : ι) (_hp : Projective (σ.obj p)) :
    ShortComplex (FGModuleCat.{u} R) :=
  ShortComplex.mk (0 : (0 : FGModuleCat.{u} R) ⟶
      σ.projectiveBoundaryRadical p)
    (σ.projectiveBoundaryRadicalInclusion p) (by simp)

/-- The projective boundary complex is a right tau-sequence. -/
theorem projectiveRightTau (p : ι) (hp : Projective (σ.obj p)) :
    Iyama.RightTauSequence (projectiveRightMesh σ p hp) := by
  let g := σ.projectiveBoundaryRadicalInclusion p
  have hgmono : Mono g := by
    dsimp only [g, projectiveBoundaryRadicalInclusion]
    exact (fg_mono_iff_injective _).2
      (Module.jacobson R (σ.obj p)).subtype_injective
  letI : Mono g := hgmono
  have hgRad : IsRadicalMorphism g :=
    (σ.isRadicalMorphism_iff_not_isSplitEpi_to_obj g).2
      (σ.projectiveBoundaryRadicalInclusion_isRightAlmostSplit p hp).not_isSplitEpi
  refine
    { f_radical := isRadicalMorphism_zero
      g_radical := hgRad
      factors_from_left := ?_
      factors_into_right := ?_
      minimalWeakKernel := ?_ }
  · intro W a _ha
    refine ⟨0, ?_⟩
    have ha : a = 0 := (isZero_zero (FGModuleCat.{u} R)).eq_of_src a 0
    change (0 : (0 : FGModuleCat.{u} R) ⟶
      σ.projectiveBoundaryRadical p) ≫ 0 = a
    rw [zero_comp]
    exact ha.symm
  · intro W a ha
    exact (σ.projectiveBoundaryRadicalInclusion_isRightAlmostSplit p hp).factors a
      ((σ.isRadicalMorphism_iff_not_isSplitEpi_to_obj a).1 ha)
  · constructor
    · rw [Iyama.ShortComplex.isWeakKernel_iff]
      intro W k hk
      change k ≫ g = 0 at hk
      have hk0 : k = 0 := by
        apply (cancel_mono g).1
        change k ≫ g = (0 : W ⟶ σ.projectiveBoundaryRadical p) ≫ g
        rw [zero_comp]
        exact hk
      refine ⟨0, ?_⟩
      change (0 : W ⟶ (0 : FGModuleCat.{u} R)) ≫ 0 = k
      rw [hk0]
      simp
    · intro e _he
      have heq : e = 𝟙 _ :=
        (isZero_zero (FGModuleCat.{u} R)).eq_of_src e (𝟙 _)
      rw [heq]
      infer_instance

/-- The unified ambient right mesh at a skeleton label. -/
def moduleRightMesh (x : ι) : ShortComplex (FGModuleCat.{u} R) := by
  classical
  by_cases hx : Projective (σ.obj x)
  · exact projectiveRightMesh σ x hx
  · exact nonprojectiveRightMesh σ D ⟨x, hx⟩

/-- Every unified ambient right mesh is a right tau-sequence. -/
theorem moduleRightTau (x : ι) :
    Iyama.RightTauSequence (moduleRightMesh σ D x) := by
  classical
  by_cases hx : Projective (σ.obj x)
  · simpa [moduleRightMesh, hx] using projectiveRightTau σ x hx
  · simpa [moduleRightMesh, hx] using
      nonprojectiveRightTau σ D ⟨x, hx⟩

/-- The right endpoint of the unified mesh is literally the selected
indecomposable. -/
theorem moduleRightMesh_X₃ (x : ι) :
    (moduleRightMesh σ D x).X₃ = σ.obj x := by
  classical
  by_cases hx : Projective (σ.obj x) <;>
    simp [moduleRightMesh, hx, projectiveRightMesh,
      nonprojectiveRightMesh]

/-- At a projective label the unified mesh starts at zero. -/
theorem moduleRightMesh_X₁_of_projective
    (x : ι) (hx : Projective (σ.obj x)) :
    (moduleRightMesh σ D x).X₁ = (0 : FGModuleCat.{u} R) := by
  simp [moduleRightMesh, hx, projectiveRightMesh]

/-- At a nonprojective label the unified mesh starts at its chosen
Auslander--Reiten translate. -/
theorem moduleRightMesh_X₁_of_not_projective
    (x : ι) (hx : ¬ Projective (σ.obj x)) :
    (moduleRightMesh σ D x).X₁ =
      σ.obj (arTranslation σ D ⟨x, hx⟩).1 := by
  simp [moduleRightMesh, hx, nonprojectiveRightMesh]

/-- Its middle term is the unified minimal right almost-split middle term
used by the factor-ladder operator. -/
theorem moduleRightMesh_X₂ (x : ι) :
    (moduleRightMesh σ D x).X₂ =
      (factorLadderRightARAt σ D x).middle := by
  classical
  by_cases hx : Projective (σ.obj x)
  · simp only [moduleRightMesh, hx, ↓reduceDIte,
      factorLadderRightARAt, projectiveRightMesh]
    rfl
  · simp only [moduleRightMesh, hx, ↓reduceDIte,
      factorLadderRightARAt, nonprojectiveRightMesh]

end FiniteARTranslationData

end OpConjecture.IndecomposableSkeleton
