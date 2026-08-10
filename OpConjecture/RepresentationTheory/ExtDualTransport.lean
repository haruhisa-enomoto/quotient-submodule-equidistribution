import OpConjecture.RepresentationTheory.LengthTwoContragredient
import OpConjecture.RepresentationTheory.ExtDegreeNakayamaReduction

/-!
# Ext-arrow endpoint transport under an aligned anti-equivalence

This file isolates general length-two transport under an aligned
anti-equivalence and then passes to multiplicity-bearing Ext--Gabriel arrows
through the maintained no-parallel equivalence.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace OpConjecture.ExtDualTransport

universe u v w

variable
    {K R S : Type u}
    [Field K] [IsAlgClosed K]
    [Ring R] [Small.{u} R] [IsNoetherianRing R] [IsArtinianRing R]
    [Ring S] [Small.{u} S] [IsNoetherianRing S] [IsArtinianRing S]
    [Algebra K R] [Algebra K S]
    {ι κ : Type v} [Finite ι] [Finite κ]
    (σ : IndecomposableSkeleton.{u, v, u} R ι)
    (τ : IndecomposableSkeleton.{u, v, u} S κ)
    (D : IndecomposableSkeleton.AlignedAntiEquivalence σ τ)

open GabrielArrowBridge
open GabrielArrowBridge.LengthTwo

namespace AlignedAntiEquivalence

/-- A simple quotient becomes a simple submodule under an aligned
anti-equivalence. -/
def simpleSubmoduleOfSimpleQuotient
    {x : ι} (Q : σ.SimpleQuotient x) :
    τ.SimpleSubmodule (D.labelEquiv x) where
  index := D.labelEquiv Q.index
  simple := by
    rw [← τ.compositionLength_eq_one_iff_simple]
    rw [LengthTwoGabrielBridge.IndecomposableSkeleton.AlignedAntiEquivalence.compositionLength_eq
      σ τ D]
    exact (σ.compositionLength_eq_one_iff_simple Q.index).2 Q.simple
  map :=
    (D.objIso Q.index).inv ≫
      D.categoryEquiv.functor.map Q.map.op ≫
      (D.objIso x).hom
  mono := by
    letI : Epi Q.map := Q.epi
    infer_instance

/-- The aligned label equivalence restricts to simple representatives. -/
def simpleIndexEquiv : σ.SimpleIndex ≃ τ.SimpleIndex where
  toFun i := ⟨D.labelEquiv i.1, by
    rw [← τ.compositionLength_eq_one_iff_simple]
    rw [LengthTwoGabrielBridge.IndecomposableSkeleton.AlignedAntiEquivalence.compositionLength_eq
      σ τ D]
    exact (σ.compositionLength_eq_one_iff_simple i.1).2 i.2⟩
  invFun j := ⟨D.labelEquiv.symm j.1, by
    rw [← σ.compositionLength_eq_one_iff_simple]
    rw [← LengthTwoGabrielBridge.IndecomposableSkeleton.AlignedAntiEquivalence.compositionLength_eq
      σ τ D]
    simp only [Equiv.apply_symm_apply]
    exact (τ.compositionLength_eq_one_iff_simple j.1).2 j.2⟩
  left_inv i := by
    apply Subtype.ext
    simp
  right_inv j := by
    apply Subtype.ext
    simp

/-- An aligned anti-equivalence bijects length-two representatives. -/
def lengthTwoEquiv : σ.LengthTwoIndex ≃ τ.LengthTwoIndex where
  toFun x := ⟨D.labelEquiv x.1, by
    rw [LengthTwoGabrielBridge.IndecomposableSkeleton.AlignedAntiEquivalence.compositionLength_eq
      σ τ D]
    exact x.2⟩
  invFun y := ⟨D.labelEquiv.symm y.1, by
    rw [← LengthTwoGabrielBridge.IndecomposableSkeleton.AlignedAntiEquivalence.compositionLength_eq
      σ τ D]
    simpa using y.2⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv y := by
    apply Subtype.ext
    simp

omit [Small.{u} R] [IsArtinianRing R] [Small.{u} S] [IsArtinianRing S]
  [Finite ι] [Finite κ] in
/-- Contragredient transport exchanges the top of a length-two object with
the socle of its image. -/
theorem target_lengthTwoEquiv (x : σ.LengthTwoIndex) :
    target τ (lengthTwoEquiv σ τ D x) =
      simpleIndexEquiv σ τ D (source σ x) := by
  apply Subtype.ext
  exact
    IndecomposableSkeleton.SimpleSubmodule.index_eq_of_compositionLength_eq_two
      τ (lengthTwoEquiv σ τ D x).2
      (submodule τ (lengthTwoEquiv σ τ D x))
      (simpleSubmoduleOfSimpleQuotient σ τ D (quotient σ x))

omit [Small.{u} R] [IsArtinianRing R] [Small.{u} S] [IsArtinianRing S]
  [Finite ι] [Finite κ] in
/-- Contragredient transport exchanges the socle of a length-two object with
the top of its image. -/
theorem source_lengthTwoEquiv (x : σ.LengthTwoIndex) :
    source τ (lengthTwoEquiv σ τ D x) =
      simpleIndexEquiv σ τ D (target σ x) := by
  apply Subtype.ext
  exact
    IndecomposableSkeleton.SimpleQuotient.index_eq_of_compositionLength_eq_two
      τ (lengthTwoEquiv σ τ D x).2
      (quotient τ (lengthTwoEquiv σ τ D x))
      (LengthTwoGabrielBridge.IndecomposableSkeleton.AlignedAntiEquivalence.simpleQuotientOfSimpleSubmodule
        σ τ D (submodule σ x))

omit [Small.{u} R] [IsArtinianRing R] [Small.{u} S] [IsArtinianRing S]
  [Finite ι] [Finite κ] in
/-- Target-injectivity on the dual skeleton gives source-injectivity on the
original length-two skeleton. -/
theorem lengthTwoSource_injective_of_dualTarget_injective
    (D : IndecomposableSkeleton.AlignedAntiEquivalence σ τ)
    (hTarget : Function.Injective (target τ)) :
    Function.Injective (source σ) := by
  intro x y hxy
  apply (lengthTwoEquiv σ τ D).injective
  apply hTarget
  rw [target_lengthTwoEquiv σ τ D, target_lengthTwoEquiv σ τ D, hxy]

omit [Small.{u} R] [IsArtinianRing R] [Small.{u} S] [IsArtinianRing S]
  [Finite ι] [Finite κ] in
/-- Source-injectivity on the dual skeleton gives target-injectivity on the
original length-two skeleton. -/
theorem lengthTwoTarget_injective_of_dualSource_injective
    (D : IndecomposableSkeleton.AlignedAntiEquivalence σ τ)
    (hSource : Function.Injective (source τ)) :
    Function.Injective (target σ) := by
  intro x y hxy
  apply (lengthTwoEquiv σ τ D).injective
  apply hSource
  rw [source_lengthTwoEquiv σ τ D, source_lengthTwoEquiv σ τ D, hxy]

omit [Small.{u} R] [IsArtinianRing R] [Small.{u} S] [IsArtinianRing S]
  [Finite ι] [Finite κ] in
/-- Target-injectivity on the original skeleton gives source-injectivity on
its aligned dual length-two skeleton. -/
theorem dualLengthTwoSource_injective_of_target_injective
    (D : IndecomposableSkeleton.AlignedAntiEquivalence σ τ)
    (hTarget : Function.Injective (target σ)) :
    Function.Injective (source τ) := by
  let e := lengthTwoEquiv σ τ D
  intro a b hab
  apply e.symm.injective
  apply hTarget
  apply (simpleIndexEquiv σ τ D).injective
  calc
    simpleIndexEquiv σ τ D (target σ (e.symm a)) =
        source τ (e (e.symm a)) :=
      (source_lengthTwoEquiv σ τ D (e.symm a)).symm
    _ = source τ a := by rw [e.apply_symm_apply]
    _ = source τ b := hab
    _ = source τ (e (e.symm b)) := by rw [e.apply_symm_apply]
    _ = simpleIndexEquiv σ τ D (target σ (e.symm b)) :=
      source_lengthTwoEquiv σ τ D (e.symm b)

omit [Small.{u} R] [IsArtinianRing R] [Small.{u} S] [IsArtinianRing S]
  [Finite ι] [Finite κ] in
/-- Source-injectivity on the original skeleton gives target-injectivity on
its aligned dual length-two skeleton. -/
theorem dualLengthTwoTarget_injective_of_source_injective
    (D : IndecomposableSkeleton.AlignedAntiEquivalence σ τ)
    (hSource : Function.Injective (source σ)) :
    Function.Injective (target τ) := by
  let e := lengthTwoEquiv σ τ D
  intro a b hab
  apply e.symm.injective
  apply hSource
  apply (simpleIndexEquiv σ τ D).injective
  calc
    simpleIndexEquiv σ τ D (source σ (e.symm a)) =
        target τ (e (e.symm a)) :=
      (target_lengthTwoEquiv σ τ D (e.symm a)).symm
    _ = target τ a := by rw [e.apply_symm_apply]
    _ = target τ b := hab
    _ = target τ (e (e.symm b)) := by rw [e.apply_symm_apply]
    _ = simpleIndexEquiv σ τ D (source σ (e.symm b)) :=
      target_lengthTwoEquiv σ τ D (e.symm b)

end AlignedAntiEquivalence

namespace LengthTwo

omit [IsAlgClosed K] [Finite ι] in
/-- The maintained length-two/Ext-arrow equivalence preserves its source
endpoint. -/
theorem source_lengthTwoEquivExtGabrielArrow
    (hNoParallel : NoParallelExtSupport (K := K) σ)
    (x : σ.LengthTwoIndex) :
    ExtGabrielArrowIndex.source σ
        (lengthTwoEquivExtGabrielArrow σ hNoParallel x) =
      source σ x := by
  rfl

omit [IsAlgClosed K] [Finite ι] in
/-- The maintained length-two/Ext-arrow equivalence preserves its target
endpoint. -/
theorem target_lengthTwoEquivExtGabrielArrow
    (hNoParallel : NoParallelExtSupport (K := K) σ)
    (x : σ.LengthTwoIndex) :
    ExtGabrielArrowIndex.target σ
        (lengthTwoEquivExtGabrielArrow σ hNoParallel x) =
      target σ x := by
  rfl

omit [IsAlgClosed K] [Finite ι] in
/-- Source-injectivity may be transported back from length-two objects to
the multiplicity-bearing Ext-arrow type. -/
theorem extSource_injective_of_lengthTwoSource_injective
    (hNoParallel : NoParallelExtSupport (K := K) σ)
    (hSource : Function.Injective (source σ)) :
    Function.Injective
      (ExtGabrielArrowIndex.source (K := K) σ) := by
  let e := lengthTwoEquivExtGabrielArrow σ hNoParallel
  intro a b hab
  apply e.symm.injective
  apply hSource
  calc
    source σ (e.symm a) =
        ExtGabrielArrowIndex.source σ (e (e.symm a)) :=
      (source_lengthTwoEquivExtGabrielArrow σ hNoParallel (e.symm a)).symm
    _ = ExtGabrielArrowIndex.source σ a := by rw [e.apply_symm_apply]
    _ = ExtGabrielArrowIndex.source σ b := hab
    _ = ExtGabrielArrowIndex.source σ (e (e.symm b)) := by
      rw [e.apply_symm_apply]
    _ = source σ (e.symm b) :=
      source_lengthTwoEquivExtGabrielArrow σ hNoParallel (e.symm b)

omit [IsAlgClosed K] [Finite ι] in
/-- Target-injectivity may be transported back from length-two objects to
the multiplicity-bearing Ext-arrow type. -/
theorem extTarget_injective_of_lengthTwoTarget_injective
    (hNoParallel : NoParallelExtSupport (K := K) σ)
    (hTarget : Function.Injective (target σ)) :
    Function.Injective
      (ExtGabrielArrowIndex.target (K := K) σ) := by
  let e := lengthTwoEquivExtGabrielArrow σ hNoParallel
  intro a b hab
  apply e.symm.injective
  apply hTarget
  calc
    target σ (e.symm a) =
        ExtGabrielArrowIndex.target σ (e (e.symm a)) :=
      (target_lengthTwoEquivExtGabrielArrow σ hNoParallel (e.symm a)).symm
    _ = ExtGabrielArrowIndex.target σ a := by rw [e.apply_symm_apply]
    _ = ExtGabrielArrowIndex.target σ b := hab
    _ = ExtGabrielArrowIndex.target σ (e (e.symm b)) := by
      rw [e.apply_symm_apply]
    _ = target σ (e.symm b) :=
      target_lengthTwoEquivExtGabrielArrow σ hNoParallel (e.symm b)

end LengthTwo

namespace AlignedAntiEquivalence

omit [IsAlgClosed K] [Finite ι] [Finite κ] in
/-- Exact Ext--Gabriel endpoint transport: target-injectivity on an aligned
dual skeleton implies source-injectivity on the original skeleton. -/
theorem extSource_injective_of_dualExtTarget_injective
    (D : IndecomposableSkeleton.AlignedAntiEquivalence σ τ)
    (hNoParallelσ : NoParallelExtSupport (K := K) σ)
    (hNoParallelτ : NoParallelExtSupport (K := K) τ)
    (hTarget : Function.Injective
      (ExtGabrielArrowIndex.target (K := K) τ)) :
    Function.Injective
      (ExtGabrielArrowIndex.source (K := K) σ) := by
  apply LengthTwo.extSource_injective_of_lengthTwoSource_injective
    σ hNoParallelσ
  apply lengthTwoSource_injective_of_dualTarget_injective σ τ D
  exact ExtDegreeNakayamaReduction.lengthTwoTarget_injective_of_extTarget_injective
    τ hNoParallelτ hTarget

omit [IsAlgClosed K] [Finite ι] [Finite κ] in
/-- The symmetric endpoint statement: source-injectivity on an aligned dual
skeleton implies target-injectivity on the original skeleton. -/
theorem extTarget_injective_of_dualExtSource_injective
    (D : IndecomposableSkeleton.AlignedAntiEquivalence σ τ)
    (hNoParallelσ : NoParallelExtSupport (K := K) σ)
    (hNoParallelτ : NoParallelExtSupport (K := K) τ)
    (hSource : Function.Injective
      (ExtGabrielArrowIndex.source (K := K) τ)) :
    Function.Injective
      (ExtGabrielArrowIndex.target (K := K) σ) := by
  apply LengthTwo.extTarget_injective_of_lengthTwoTarget_injective
    σ hNoParallelσ
  apply lengthTwoTarget_injective_of_dualSource_injective σ τ D
  exact ExtDegreeNakayamaReduction.lengthTwoSource_injective_of_extSource_injective
    τ hNoParallelτ hSource

omit [IsAlgClosed K] [Finite ι] [Finite κ] in
/-- Paper-facing orientation: target-injectivity on a skeleton transports to
source-injectivity on its aligned dual skeleton. -/
theorem dualExtSource_injective_of_extTarget_injective
    (D : IndecomposableSkeleton.AlignedAntiEquivalence σ τ)
    (hNoParallelσ : NoParallelExtSupport (K := K) σ)
    (hNoParallelτ : NoParallelExtSupport (K := K) τ)
    (hTarget : Function.Injective
      (ExtGabrielArrowIndex.target (K := K) σ)) :
    Function.Injective
      (ExtGabrielArrowIndex.source (K := K) τ) := by
  apply LengthTwo.extSource_injective_of_lengthTwoSource_injective
    τ hNoParallelτ
  apply dualLengthTwoSource_injective_of_target_injective σ τ D
  exact ExtDegreeNakayamaReduction.lengthTwoTarget_injective_of_extTarget_injective
    σ hNoParallelσ hTarget

omit [IsAlgClosed K] [Finite ι] [Finite κ] in
/-- Dually, source-injectivity on a skeleton transports to
target-injectivity on its aligned dual skeleton. -/
theorem dualExtTarget_injective_of_extSource_injective
    (D : IndecomposableSkeleton.AlignedAntiEquivalence σ τ)
    (hNoParallelσ : NoParallelExtSupport (K := K) σ)
    (hNoParallelτ : NoParallelExtSupport (K := K) τ)
    (hSource : Function.Injective
      (ExtGabrielArrowIndex.source (K := K) σ)) :
    Function.Injective
      (ExtGabrielArrowIndex.target (K := K) τ) := by
  apply LengthTwo.extTarget_injective_of_lengthTwoTarget_injective
    τ hNoParallelτ
  apply dualLengthTwoTarget_injective_of_source_injective σ τ D
  exact ExtDegreeNakayamaReduction.lengthTwoSource_injective_of_extSource_injective
    σ hNoParallelσ hSource

end AlignedAntiEquivalence

end OpConjecture.ExtDualTransport
