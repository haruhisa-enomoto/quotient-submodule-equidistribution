import OpConjecture.RepresentationTheory.ReverseFactorLadderRecurrence

/-!
# Determination of the closure profiles by the valued AR quiver

The forward and reverse factor-ladder predicates below use only the finite
vertex set, the projective/injective boundary, AR translation, and the
valued multiplicities of the unified AR middles.  This file identifies their
support posets, without changing the underlying vertex subsets, with the
literal quotient- and submodule-closed support posets.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory Polynomial

namespace OpConjecture.IndecomposableSkeleton

universe u v w

variable {k R S : Type u} [Field k]
  [Ring R] [Algebra k R] [FiniteDimensional k R]
  [Ring S] [Algebra k S] [FiniteDimensional k S]
  [IsNoetherianRing R] [IsNoetherianRing S]
  {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)
  (τ : IndecomposableSkeleton.{u, w, u} S κ)

/-- The quotient-side support predicate read solely from the forward valued
AR meshes and translation. -/
def QuotientARClosedSupport (K : Set ι) : Prop :=
  ∀ x : DeletedLabel K,
    (σ.finiteDimensionalFactorLadderData k R K).ReachesBoundary
      (deletedProjectiveSet σ K) x

/-- The submodule-side support predicate read from the reversed valued AR
meshes and translation. -/
def SubmoduleARClosedSupport
    (D : AlignedBiduality σ τ) (K : Set ι) : Prop :=
  ∀ x : DeletedLabel K,
    (D.finiteDimensionalReverseFactorLadderData
      (k := k) (S := S) σ τ K).ReachesBoundary
        (deletedInjectiveSet σ K) x

/-- Vertex subsets accepted by the forward AR recursion. -/
abbrev QuotientARCloseds :=
  {K : Set ι // QuotientARClosedSupport (k := k) (R := R) σ K}

/-- Vertex subsets accepted by the reverse AR recursion. -/
abbrev SubmoduleARCloseds (D : AlignedBiduality σ τ) :=
  {K : Set ι //
    SubmoduleARClosedSupport (k := k) (S := S) σ τ D K}

noncomputable instance quotientARClosedsFintype :
    Fintype (QuotientARCloseds (k := k) (R := R) σ) :=
  Fintype.ofFinite _

noncomputable instance submoduleARClosedsFintype
    (D : AlignedBiduality σ τ) :
    Fintype (SubmoduleARCloseds (k := k) (S := S) σ τ D) :=
  Fintype.ofFinite _

/-- The literal quotient-closed supports are exactly the supports selected by
the forward valued AR recursion. -/
theorem qClosure_isClosed_iff_quotientARClosedSupport (K : Set ι) :
    σ.qClosure.IsClosed K ↔
      QuotientARClosedSupport (k := k) (R := R) σ K := by
  exact (qClosed_iff_generated_isClosedUnderQuotients σ K).trans
    (σ.finiteDimensional_generated_isClosedUnderQuotients_iff_factorLadder_reaches_projective
      (k := k) (R := R) K)

omit [Algebra k R] [FiniteDimensional k R] [Fintype ι] in
/-- The literal submodule-closed supports are exactly the supports selected by
the reverse valued AR recursion. -/
theorem sClosure_isClosed_iff_submoduleARClosedSupport
    (D : AlignedBiduality σ τ) (K : Set ι) :
    σ.sClosure.IsClosed K ↔
      SubmoduleARClosedSupport (k := k) (S := S) σ τ D K := by
  exact (sClosed_iff_generated_isClosedUnderSubobjects σ K).trans
    (D.generated_isClosedUnderSubobjects_iff_reverseFactorLadder_reaches_injective
      (k := k) (R := R) (S := S) σ τ K)

/-- Identity-on-support order isomorphism from quotient-closed subcategories
to the supports reconstructed from the valued AR quiver. -/
def qClosedsOrderIsoQuotientARCloseds :
    σ.qClosure.Closeds ≃o
      QuotientARCloseds (k := k) (R := R) σ where
  toFun K := ⟨K.1,
    (qClosure_isClosed_iff_quotientARClosedSupport
      (k := k) (R := R) σ K.1).1 K.2⟩
  invFun K := ⟨K.1,
    (qClosure_isClosed_iff_quotientARClosedSupport
      (k := k) (R := R) σ K.1).2 K.2⟩
  left_inv K := by rfl
  right_inv K := by rfl
  map_rel_iff' := by rfl

/-- Identity-on-support order isomorphism from submodule-closed
subcategories to the supports reconstructed from the valued AR quiver. -/
def sClosedsOrderIsoSubmoduleARCloseds
    (D : AlignedBiduality σ τ) :
    σ.sClosure.Closeds ≃o
      SubmoduleARCloseds (k := k) (S := S) σ τ D where
  toFun K := ⟨K.1,
    (sClosure_isClosed_iff_submoduleARClosedSupport
      (k := k) (R := R) (S := S) σ τ D K.1).1 K.2⟩
  invFun K := ⟨K.1,
    (sClosure_isClosed_iff_submoduleARClosedSupport
      (k := k) (R := R) (S := S) σ τ D K.1).2 K.2⟩
  left_inv K := by rfl
  right_inv K := by rfl
  map_rel_iff' := by rfl

@[simp]
theorem qClosedsOrderIsoQuotientARCloseds_coe
    (K : σ.qClosure.Closeds) :
    ((qClosedsOrderIsoQuotientARCloseds
      (k := k) (R := R) σ K :
        QuotientARCloseds (k := k) (R := R) σ) : Set ι) = K.1 :=
  rfl

omit [Algebra k R] [FiniteDimensional k R] [Fintype ι] in
@[simp]
theorem sClosedsOrderIsoSubmoduleARCloseds_coe
    (D : AlignedBiduality σ τ) (K : σ.sClosure.Closeds) :
    ((sClosedsOrderIsoSubmoduleARCloseds
      (k := k) (R := R) (S := S) σ τ D K :
        SubmoduleARCloseds (k := k) (S := S) σ τ D) : Set ι) = K.1 :=
  rfl

/-- The quotient-closed size generating polynomial is computed entirely by
the forward valued AR recursion. -/
theorem qClosure_levelPolynomial_eq_quotientARCloseds :
    σ.qClosure.levelPolynomial =
      ∑ K : QuotientARCloseds (k := k) (R := R) σ,
        X ^ K.1.ncard := by
  classical
  exact OpConjecture.SetClosure.levelPolynomial_eq_sum_stat
    σ.qClosure
    (qClosedsOrderIsoQuotientARCloseds
      (k := k) (R := R) σ).symm.toEquiv
    (fun K : QuotientARCloseds (k := k) (R := R) σ ↦ K.1.ncard)
    (by intro K; rfl)

omit [Algebra k R] [FiniteDimensional k R] in
/-- The submodule-closed size generating polynomial is computed entirely by
the reverse valued AR recursion. -/
theorem sClosure_levelPolynomial_eq_submoduleARCloseds
    (D : AlignedBiduality σ τ) :
    σ.sClosure.levelPolynomial =
      ∑ K : SubmoduleARCloseds (k := k) (S := S) σ τ D,
        X ^ K.1.ncard := by
  classical
  exact OpConjecture.SetClosure.levelPolynomial_eq_sum_stat
    σ.sClosure
    (sClosedsOrderIsoSubmoduleARCloseds
      (k := k) (R := R) (S := S) σ τ D).symm.toEquiv
    (fun K : SubmoduleARCloseds (k := k) (S := S) σ τ D ↦ K.1.ncard)
    (by intro K; rfl)

/-- A single certificate packages the two reconstructed families, their
inclusion orders, and their size generating polynomials. -/
structure ARQuiverDeterminationCertificate
    (D : AlignedBiduality σ τ) where
  quotientOrderIso :
    σ.qClosure.Closeds ≃o
      QuotientARCloseds (k := k) (R := R) σ
  submoduleOrderIso :
    σ.sClosure.Closeds ≃o
      SubmoduleARCloseds (k := k) (S := S) σ τ D
  quotientPolynomial :
    σ.qClosure.levelPolynomial =
      ∑ K : QuotientARCloseds (k := k) (R := R) σ,
        X ^ K.1.ncard
  submodulePolynomial :
    σ.sClosure.levelPolynomial =
      ∑ K : SubmoduleARCloseds (k := k) (S := S) σ τ D,
        X ^ K.1.ncard

/-- The exact abstract packaging of `cor:ar-determination`. -/
def finiteDimensionalARQuiverDetermination
    (D : AlignedBiduality σ τ) :
    ARQuiverDeterminationCertificate
      (k := k) (R := R) (S := S) σ τ D where
  quotientOrderIso :=
    qClosedsOrderIsoQuotientARCloseds (k := k) (R := R) σ
  submoduleOrderIso :=
    sClosedsOrderIsoSubmoduleARCloseds
      (k := k) (R := R) (S := S) σ τ D
  quotientPolynomial :=
    qClosure_levelPolynomial_eq_quotientARCloseds
      (k := k) (R := R) σ
  submodulePolynomial :=
    sClosure_levelPolynomial_eq_submoduleARCloseds
      (k := k) (R := R) (S := S) σ τ D

end OpConjecture.IndecomposableSkeleton

namespace OpConjecture

universe u

variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
  [FiniteDimensional k A]

/-- Canonical right-module form of `cor:ar-determination`: the valued AR
recursions reconstruct the two literal support posets, without changing their
underlying vertex subsets, and compute both level polynomials. -/
def rightARQuiverDetermination
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
    IndecomposableSkeleton.ARQuiverDeterminationCertificate
      (k := k) (R := Aᵐᵒᵖ) (S := (Aᵐᵒᵖ)ᵐᵒᵖ) σ τ D := by
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
  exact σ.finiteDimensionalARQuiverDetermination
    (k := k) (R := Aᵐᵒᵖ) (S := (Aᵐᵒᵖ)ᵐᵒᵖ) τ D

end OpConjecture
