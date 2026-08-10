import OpConjecture.RepresentationTheory.LeftRejective

/-!
# Literal additive-subcategory form
-/

noncomputable section

open Set
open CategoryTheory

namespace OpConjecture.IndecomposableSkeleton

universe u v w

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)

/-- Exact quotient-side statement for an arbitrary full additive, replete,
summand-closed subcategory. -/
theorem isClosedUnderQuotients_iff_trace_mem_and_rightRejective
    (C : AdditiveRepleteSummandSubcategory.{u, w} (R := R)) :
    C.carrier.IsClosedUnderQuotients ↔
      (∀ X : FGModuleCat.{w} R,
        C.carrier
          (σ.traceObject (σ.support C) X)) ∧
      IsRightRejective C := by
  let S : Set ι := σ.support C
  have hgen : σ.generated S = C := by
    simpa only [S] using generated_support σ C
  have hbase :=
    (qClosed_iff_generated_isClosedUnderQuotients
      σ S).symm.trans
        (qClosed_iff_trace_iff_rightRejective
          σ S)
  change
    (σ.generated S).carrier.IsClosedUnderQuotients ↔
      (∀ X : FGModuleCat.{w} R,
        (σ.generated S).carrier (σ.traceObject S X)) ∧
      IsRightRejective (σ.generated S) at hbase
  change
    C.carrier.IsClosedUnderQuotients ↔
      (∀ X : FGModuleCat.{w} R,
        C.carrier (σ.traceObject S X)) ∧
      IsRightRejective C
  simpa only [hgen] using hbase

/-- Exact first equivalence, without mentioning the adjoint package. -/
theorem isClosedUnderQuotients_iff_trace_mem
    (C : AdditiveRepleteSummandSubcategory.{u, w} (R := R)) :
    C.carrier.IsClosedUnderQuotients ↔
      ∀ X : FGModuleCat.{w} R,
        C.carrier
          (σ.traceObject (σ.support C) X) := by
  let S : Set ι := σ.support C
  have hgen : σ.generated S = C := by
    simpa only [S] using generated_support σ C
  have hbase :=
    (qClosed_iff_generated_isClosedUnderQuotients
      σ S).symm.trans
        (qClosed_iff_traceObject_inAdd
          σ S)
  change
    (σ.generated S).carrier.IsClosedUnderQuotients ↔
      ∀ X : FGModuleCat.{w} R,
        (σ.generated S).carrier (σ.traceObject S X) at hbase
  change
    C.carrier.IsClosedUnderQuotients ↔
      ∀ X : FGModuleCat.{w} R,
        C.carrier (σ.traceObject S X)
  simpa only [hgen] using hbase

/-- Exact quotient-closed iff right-rejective equivalence. -/
theorem isClosedUnderQuotients_iff_rightRejective
    (σ : IndecomposableSkeleton.{u, v, w} R ι)
    (C : AdditiveRepleteSummandSubcategory.{u, w} (R := R)) :
    C.carrier.IsClosedUnderQuotients ↔
      IsRightRejective C := by
  let S : Set ι := σ.support C
  have hgen : σ.generated S = C := by
    simpa only [S] using generated_support σ C
  have hbase :=
    (qClosed_iff_generated_isClosedUnderQuotients
      σ S).symm.trans
        (qClosed_iff_rightRejective
          σ S)
  change
    (σ.generated S).carrier.IsClosedUnderQuotients ↔
      IsRightRejective (σ.generated S) at hbase
  change
    C.carrier.IsClosedUnderQuotients ↔
      IsRightRejective C
  simpa only [hgen] using hbase

/-- Exact dual statement for an arbitrary literal additive subcategory. -/
theorem isClosedUnderSubobjects_iff_reject_mem_and_leftRejective
    (hfinite : ∀ X : FGModuleCat.{w} R, IsFiniteLength R X)
    (C : AdditiveRepleteSummandSubcategory.{u, w} (R := R)) :
    C.carrier.IsClosedUnderSubobjects ↔
      (∀ X : FGModuleCat.{w} R,
        C.carrier
          (σ.rejectQuotientObject (σ.support C) X)) ∧
      IsLeftRejective C := by
  let S : Set ι := σ.support C
  have hgen : σ.generated S = C := by
    simpa only [S] using generated_support σ C
  have hbase :=
    (sClosed_iff_generated_isClosedUnderSubobjects
      σ S).symm.trans
        (sClosed_iff_rejectQuotient_inAdd_iff_leftRejective
          σ hfinite S)
  change
    (σ.generated S).carrier.IsClosedUnderSubobjects ↔
      (∀ X : FGModuleCat.{w} R,
        (σ.generated S).carrier
          (σ.rejectQuotientObject S X)) ∧
      IsLeftRejective (σ.generated S) at hbase
  change
    C.carrier.IsClosedUnderSubobjects ↔
      (∀ X : FGModuleCat.{w} R,
        C.carrier (σ.rejectQuotientObject S X)) ∧
      IsLeftRejective C
  simpa only [hgen] using hbase

/-- The submodule-closed iff left-rejective clause as printed in the
manuscript. -/
theorem isClosedUnderSubobjects_iff_leftRejective
    (σ : IndecomposableSkeleton.{u, v, w} R ι)
    (hfinite : ∀ X : FGModuleCat.{w} R, IsFiniteLength R X)
    (C : AdditiveRepleteSummandSubcategory.{u, w} (R := R)) :
    C.carrier.IsClosedUnderSubobjects ↔
      IsLeftRejective C := by
  let S : Set ι := σ.support C
  have hgen : σ.generated S = C := by
    simpa only [S] using generated_support σ C
  have hbase :=
    (sClosed_iff_generated_isClosedUnderSubobjects
      σ S).symm.trans
        (sClosed_iff_leftRejective
          σ hfinite S)
  change
    (σ.generated S).carrier.IsClosedUnderSubobjects ↔
      IsLeftRejective (σ.generated S) at hbase
  change
    C.carrier.IsClosedUnderSubobjects ↔
      IsLeftRejective C
  simpa only [hgen] using hbase

end OpConjecture.IndecomposableSkeleton

