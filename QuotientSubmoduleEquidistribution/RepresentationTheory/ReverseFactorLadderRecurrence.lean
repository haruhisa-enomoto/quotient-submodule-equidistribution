import QuotientSubmoduleEquidistribution.RepresentationTheory.DualityConsequences
import QuotientSubmoduleEquidistribution.RepresentationTheory.FactorCategoryFactorLadderRecurrence
import QuotientSubmoduleEquidistribution.RepresentationTheory.ReverseFactorHomRealization

/-!
# Reverse factor ladders by opposite duality

The reverse ladder on a finite module category is the forward factor
ladder on an aligned dual category, pulled back to the original deleted
labels.  This is the literal formal counterpart of applying vector-space
duality to the factor ladder for the opposite algebra.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe u v w

variable {k R S : Type u} [Field k]
  [Ring R] [Algebra k R] [FiniteDimensional k R]
  [Ring S] [Algebra k S] [FiniteDimensional k S]
  [IsNoetherianRing R] [IsNoetherianRing S]
  {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)
  (τ : IndecomposableSkeleton.{u, w, u} S κ)

namespace AlignedAntiEquivalence

variable (D : AlignedAntiEquivalence σ τ)

/-- Duality restricts to an equivalence between the deleted labels. -/
def deletedLabelEquiv (K : Set ι) :
    DeletedLabel K ≃ DeletedLabel (D.labelEquiv '' K) where
  toFun x := ⟨D.labelEquiv x.1, by
    rintro ⟨y, hy, hxy⟩
    exact x.2 ((D.labelEquiv.injective hxy) ▸ hy)⟩
  invFun y := ⟨D.labelEquiv.symm y.1, by
    intro hy
    exact y.2 ⟨D.labelEquiv.symm y.1, hy,
      D.labelEquiv.apply_symm_apply y.1⟩⟩
  left_inv x := by
    ext
    exact D.labelEquiv.symm_apply_apply x.1
  right_inv y := by
    ext
    exact D.labelEquiv.apply_symm_apply y.1

omit [Fintype ι] [Fintype κ] in
/-- The dual image of the deleted injective boundary is exactly the
deleted projective boundary. -/
theorem image_deletedInjectiveSet_eq_deletedProjectiveSet
    (K : Set ι) :
    D.deletedLabelEquiv σ τ K '' deletedInjectiveSet σ K =
      deletedProjectiveSet τ (D.labelEquiv '' K) := by
  ext y
  rw [Set.mem_image_equiv]
  change
    Injective (σ.obj ((D.deletedLabelEquiv σ τ K).symm y).1) ↔
      Projective (τ.obj y.1)
  simpa [deletedLabelEquiv] using
    (D.injective_iff_projective_image σ τ
      (D.labelEquiv.symm y.1))

end AlignedAntiEquivalence

namespace AlignedBiduality

variable (D : AlignedBiduality σ τ)

/-- The reverse factor-ladder datum, in the original deleted coordinates:
run the forward factor ladder in the dual category and pull it back along
the duality of indecomposable labels. -/
def finiteDimensionalReverseFactorLadderData (K : Set ι) :
    FactorLadder.Data (DeletedLabel K) :=
  FactorLadder.Data.pullback
    (τ.finiteDimensionalFactorLadderData k S
      (D.forward.labelEquiv '' K))
    (D.forward.deletedLabelEquiv σ τ K)

omit [Algebra k R] [FiniteDimensional k R] [Fintype ι] in
/-- The reverse datum is intertwined with the forward datum on the dual
category. -/
theorem finiteDimensionalReverseFactorLadderData_relabeling
    (K : Set ι) :
    FactorLadder.Data.Relabeling
      (D.finiteDimensionalReverseFactorLadderData
        (k := k) (S := S) σ τ K)
      (τ.finiteDimensionalFactorLadderData k S
        (D.forward.labelEquiv '' K))
      (D.forward.deletedLabelEquiv σ τ K) :=
  FactorLadder.Data.Relabeling.pullback _ _

omit [Algebra k R] [FiniteDimensional k R] [Fintype ι] in
/-- The reverse half of the paper's factor-ladder theorem.  It is a
formal consequence of the already constructed forward quotient ladder in
the dual category; no second mesh or radical-layer argument is assumed. -/
theorem generated_isClosedUnderSubobjects_iff_reverseFactorLadder_reaches_injective
    (K : Set ι) :
    (σ.generated K).carrier.IsClosedUnderSubobjects ↔
      ∀ x : DeletedLabel K,
        (D.finiteDimensionalReverseFactorLadderData
          (k := k) (S := S) σ τ K).ReachesBoundary
            (deletedInjectiveSet σ K) x := by
  let e := D.forward.labelEquiv
  let Kdual : Set κ := e '' K
  let eDeleted : DeletedLabel K ≃ DeletedLabel Kdual :=
    D.forward.deletedLabelEquiv σ τ K
  let A := D.finiteDimensionalReverseFactorLadderData
    (k := k) (S := S) σ τ K
  let B := τ.finiteDimensionalFactorLadderData k S Kdual
  have hclosure :
      (σ.generated K).carrier.IsClosedUnderSubobjects ↔
        (τ.generated Kdual).carrier.IsClosedUnderQuotients :=
    (sClosed_iff_generated_isClosedUnderSubobjects σ K).symm.trans <|
      (D.sClosure_isClosed_iff_qClosure_image σ τ K).trans <|
        qClosed_iff_generated_isClosedUnderQuotients τ Kdual
  have hforward :
      (τ.generated Kdual).carrier.IsClosedUnderQuotients ↔
        ∀ y : DeletedLabel Kdual,
          B.ReachesBoundary (deletedProjectiveSet τ Kdual) y := by
    exact τ.finiteDimensional_generated_isClosedUnderQuotients_iff_factorLadder_reaches_projective
      (k := k) (R := S) Kdual
  have hboundary :
      eDeleted '' deletedInjectiveSet σ K =
        deletedProjectiveSet τ Kdual := by
    exact D.forward.image_deletedInjectiveSet_eq_deletedProjectiveSet
      σ τ K
  have hrel : FactorLadder.Data.Relabeling A B eDeleted := by
    exact D.finiteDimensionalReverseFactorLadderData_relabeling
      (k := k) (S := S) σ τ K
  have hreach :
      (∀ y : DeletedLabel Kdual,
          B.ReachesBoundary (deletedProjectiveSet τ Kdual) y) ↔
        ∀ x : DeletedLabel K,
          A.ReachesBoundary (deletedInjectiveSet σ K) x := by
    constructor
    · intro h x
      have hx := h (eDeleted x)
      rw [← hboundary] at hx
      exact (hrel.reachesBoundary_image_iff
        (deletedInjectiveSet σ K) x).1 hx
    · intro h y
      have hy := h (eDeleted.symm y)
      have hy' := (hrel.reachesBoundary_image_iff
        (deletedInjectiveSet σ K) (eDeleted.symm y)).2 hy
      rw [hboundary] at hy'
      simpa using hy'
  exact (hclosure.trans hforward).trans hreach

end AlignedBiduality

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton

namespace QuotientSubmoduleEquidistribution

universe u

variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
  [FiniteDimensional k A]

/-- Canonical right-module form of the reverse factor-ladder theorem.
The aligned biduality here is the maintained `Hom_k(-, k)` duality between
right `A`-modules and right `Aᵐᵒᵖ`-modules. -/
theorem right_generated_isClosedUnderSubobjects_iff_reverseFactorLadder_reaches_injective
    (hA : IsRightRepresentationFinite.{u, u, u} k A) :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional k A
    letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional k Aᵐᵒᵖ
    letI : Finite
        (CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) := hA
    let hAop : IsRightRepresentationFinite.{u, u, u} k Aᵐᵒᵖ :=
      (rightRepresentationFinite_op_iff k A).1 hA
    letI : Finite
        (CanonicalIndecomposableIndex.{u, u} (Aᵐᵒᵖ)ᵐᵒᵖ) := hAop
    letI : Fintype
        (CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) :=
      Fintype.ofFinite _
    letI : Fintype
        (CanonicalIndecomposableIndex.{u, u} (Aᵐᵒᵖ)ᵐᵒᵖ) :=
      Fintype.ofFinite _
    let σ := rightIndecomposableSkeleton.{u, u, u} k A
    let τ := rightIndecomposableSkeleton.{u, u, u} k Aᵐᵒᵖ
    let D := rightOppositeAlignedBiduality k A
    ∀ K : Set (CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ),
      (σ.generated K).carrier.IsClosedUnderSubobjects ↔
        ∀ x : IndecomposableSkeleton.DeletedLabel K,
          (D.finiteDimensionalReverseFactorLadderData
            (k := k) (S := (Aᵐᵒᵖ)ᵐᵒᵖ) σ τ K).ReachesBoundary
              (IndecomposableSkeleton.deletedInjectiveSet σ K) x := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional k A
  letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional k Aᵐᵒᵖ
  letI : Finite
      (CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) := hA
  let hAop : IsRightRepresentationFinite.{u, u, u} k Aᵐᵒᵖ :=
    (rightRepresentationFinite_op_iff k A).1 hA
  letI : Finite
      (CanonicalIndecomposableIndex.{u, u} (Aᵐᵒᵖ)ᵐᵒᵖ) := hAop
  letI : Fintype
      (CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) :=
    Fintype.ofFinite _
  letI : Fintype
      (CanonicalIndecomposableIndex.{u, u} (Aᵐᵒᵖ)ᵐᵒᵖ) :=
    Fintype.ofFinite _
  let σ := rightIndecomposableSkeleton.{u, u, u} k A
  let τ := rightIndecomposableSkeleton.{u, u, u} k Aᵐᵒᵖ
  let D := rightOppositeAlignedBiduality k A
  dsimp only
  intro K
  exact
    D.generated_isClosedUnderSubobjects_iff_reverseFactorLadder_reaches_injective
      (k := k) (R := Aᵐᵒᵖ) (S := (Aᵐᵒᵖ)ᵐᵒᵖ) σ τ K

end QuotientSubmoduleEquidistribution
