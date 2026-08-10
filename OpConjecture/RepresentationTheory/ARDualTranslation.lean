import OpConjecture.RepresentationTheory.AlmostSplitDuality
import OpConjecture.RepresentationTheory.FiniteARTranslationData
import OpConjecture.RepresentationTheory.ProjectiveInjectiveMiddleARBridge

/-!
# AR translation under aligned duality

An aligned anti-equivalence reverses almost-split sequences.  Consequently
AR translation on the target skeleton is inverse AR translation on the
source skeleton.  The proof below compares the contravariant image of the
chosen target right almost-split map with the chosen source left
almost-split map and uses uniqueness of their cokernels.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace OpConjecture.IndecomposableSkeleton

universe u v w

variable {R S : Type u}
  [Ring R] [IsNoetherianRing R]
  [Ring S] [IsNoetherianRing S]
  {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)
  (τ : IndecomposableSkeleton.{u, w, u} S κ)

namespace AlignedBiduality

variable (D : AlignedBiduality σ τ)

/-- A nonprojective target label pulls back to a noninjective source label. -/
def backwardNoninjectiveLabel (q : τ.NonprojectiveLabel) :
    σ.NoninjectiveLabel :=
  ⟨D.backward.labelEquiv q.1, by
    intro hinj
    apply q.2
    exact (D.backward.projective_iff_injective_image τ σ q.1).2 hinj⟩

omit [Fintype κ] in
/-- The backward label of target AR translation is inverse source AR
translation. -/
theorem backward_arTranslation_eq_inverse
    (ARσ : σ.FiniteARTranslationData)
    (ARτ : τ.FiniteARTranslationData)
    (q : τ.NonprojectiveLabel) :
    D.backward.labelEquiv (ARτ.arTranslation τ q).1 =
      ((ARσ.arTranslationEquiv σ).symm
        (D.backwardNoninjectiveLabel σ τ q)).1 := by
  let A := ARτ.chosenRightAR τ q
  let x := D.backwardNoninjectiveLabel σ τ q
  let L := ARσ.chosenLeftAR σ x
  let g := (D.backward.objIso q.1).inv ≫
    D.backward.categoryEquiv.functor.map A.map.op
  have hgAS : OpConjecture.IsLeftAlmostSplit g := by
    apply OpConjecture.IsLeftAlmostSplit.precomp_iso
      (D.backward.objIso q.1).symm
    exact A.rightAlmostSplit.map_op_equivalence
      D.backward.categoryEquiv
  have hgMin : OpConjecture.IsLeftMinimal g := by
    apply OpConjecture.IsLeftMinimal.precomp_iso
      (D.backward.objIso q.1).symm
    exact A.rightMinimal.map_op_equivalence
      D.backward.categoryEquiv
  have hL_AS : OpConjecture.IsLeftAlmostSplit L.map := L.leftAlmostSplit
  have hL_Min : OpConjecture.IsLeftMinimal L.map := L.leftMinimal
  let cokernelComparison : cokernel g ≅ cokernel L.map :=
    Classical.choice
      (OpConjecture.nonempty_cokernelIso_of_leftAlmostSplit
        hgAS hgMin hL_AS hL_Min)
  let mappedKernelIso :
      cokernel g ≅
        D.backward.categoryEquiv.functor.obj
          (Opposite.op (kernel A.map)) :=
    OpConjecture.cokernelPrecompMapOpIsoKernel
      D.backward.categoryEquiv A.map (D.backward.objIso q.1).symm
  let translatedKernelIso :
      D.backward.categoryEquiv.functor.obj
          (Opposite.op (kernel A.map)) ≅
        σ.obj (D.backward.labelEquiv (ARτ.arTranslation τ q).1) :=
    D.backward.categoryEquiv.functor.mapIso
        (ARτ.arTranslationKernelIso τ q).symm.op ≪≫
      D.backward.objIso (ARτ.arTranslation τ q).1
  let sourceCokernelIso :
      cokernel L.map ≅
        σ.obj ((ARσ.arTranslationEquiv σ).symm x).1 :=
    ARσ.chosenLeftARCokernelIso σ x
  apply σ.eq_of_iso
  exact ⟨translatedKernelIso.symm ≪≫ mappedKernelIso.symm ≪≫
    cokernelComparison ≪≫ sourceCokernelIso⟩

omit [Fintype κ] in
/-- Forward dual labels turn target AR translation into inverse source AR
translation in the more convenient source-coordinate form. -/
theorem forward_symm_arTranslation_eq_inverse
    (ARσ : σ.FiniteARTranslationData)
    (ARτ : τ.FiniteARTranslationData)
    (q : τ.NonprojectiveLabel) :
    D.forward.labelEquiv.symm (ARτ.arTranslation τ q).1 =
      ((ARσ.arTranslationEquiv σ).symm
        ⟨D.forward.labelEquiv.symm q.1, by
          intro hinj
          apply q.2
          simpa using
            ((D.forward.injective_iff_projective_image σ τ
              (D.forward.labelEquiv.symm q.1)).1 hinj)⟩).1 := by
  simpa [D.backward_label, backwardNoninjectiveLabel] using
    D.backward_arTranslation_eq_inverse σ τ ARσ ARτ q

end AlignedBiduality

end OpConjecture.IndecomposableSkeleton
