import QuotientSubmoduleEquidistribution.RepresentationDirected.IyamaWordMeshDirectedEndpoint
import QuotientSubmoduleEquidistribution.RepresentationTheory.FiniteDimensionalARNonvanishing
import QuotientSubmoduleEquidistribution.RepresentationTheory.OppositeDuality

/-!
# The representation-directed theorem for an algebra

This file specializes the abstract finite-skeleton Bruhat-profile theorem to
the canonical indecomposable skeleton of a finite-dimensional algebra.  The
finite Auslander--Reiten translation data and the dual skeleton are built by
the existing module-category constructions.
-/

set_option autoImplicit false

noncomputable section

namespace QuotientSubmoduleEquidistribution

open RepresentationDirected
open RepresentationDirected.DirectedAROrbit
open RepresentationDirected.IyamaMesh.WordMesh.DirectedEndpoint
open RepresentationDirected.SimpleGraphCoxeter
open RepresentationDirected.SimpleGraphBruhat

universe u

/-- A finite-dimensional algebra is right representation-directed when its
canonical indecomposable skeleton is finite and has no cycle of nonzero
nonisomorphisms. -/
def IsRightRepresentationDirected
    (K A : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A] : Prop :=
  IsRightRepresentationFinite.{u, u, u} K A ∧
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    HasAcyclicNonzeroNonisomorphisms
      (rightIndecomposableSkeleton.{u, u, u} K A)

/-- The canonical ordered Auslander--Reiten word of a right
representation-directed algebra is reduced in its orbit-graph Coxeter
group. -/
theorem rightRepresentationDirectedWord_isReduced
    (K A : Type u)
    [Field K] [IsAlgClosed K]
    [Ring A] [Algebra K A] [FiniteDimensional K A]
    (h : IsRightRepresentationDirected K A) :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    letI : Finite (CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) := h.1
    letI : Fintype (CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) :=
      Fintype.ofFinite _
    let sigma := rightIndecomposableSkeleton.{u, u, u} K A
    letI : Finite (ProjectiveLabel sigma) :=
      Finite.of_injective Subtype.val Subtype.val_injective
    letI : Fintype (ProjectiveLabel sigma) := Fintype.ofFinite _
    let T := sigma.finiteDimensionalARTranslationData K Aᵐᵒᵖ
    let E := DirectedOrderChoice.chosen sigma h.2
    IsReduced (OrderedARWord.orbitGraph sigma h.2 T)
      (OrderedARWord.wordFor sigma h.2 T E) := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  letI : Finite (CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) := h.1
  letI : Fintype (CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) :=
    Fintype.ofFinite _
  let sigma := rightIndecomposableSkeleton.{u, u, u} K A
  letI : Finite (ProjectiveLabel sigma) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype (ProjectiveLabel sigma) := Fintype.ofFinite _
  let T := sigma.finiteDimensionalARTranslationData K Aᵐᵒᵖ
  let E := DirectedOrderChoice.chosen sigma h.2
  exact DirectedSorting.orderedARWordFor_isReduced_of_meshExactness
    (K := K) (R := Aᵐᵒᵖ) sigma h.2 T E
    ((hasUniformMeshExactnessFor K sigma h.2 T E) Finset.univ)

/-- The complete Bruhat-interval parametrization in the
representation-directed theorem, specialized to the canonical module
skeleton.  Its two support maps are the lexicographically first quotient
supports and the reverse-colexicographically last submodule supports. -/
noncomputable def rightRepresentationDirectedProfile
    (K A : Type u)
    [Field K] [IsAlgClosed K]
    [Ring A] [Algebra K A] [FiniteDimensional K A]
    (h : IsRightRepresentationDirected K A) :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K Aᵐᵒᵖ
    letI : Finite (CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) := h.1
    let sigma := rightIndecomposableSkeleton.{u, u, u} K A
    let B := rightOppositeAlignedBiduality K A
    letI : Finite
        (CanonicalIndecomposableIndex.{u, u} (Aᵐᵒᵖ)ᵐᵒᵖ) :=
      Finite.of_injective B.forward.labelEquiv.symm
        B.forward.labelEquiv.symm.injective
    letI : Fintype (CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) :=
      Fintype.ofFinite _
    letI : Fintype
        (CanonicalIndecomposableIndex.{u, u} (Aᵐᵒᵖ)ᵐᵒᵖ) :=
      Fintype.ofFinite _
    let T := sigma.finiteDimensionalARTranslationData K Aᵐᵒᵖ
    let E := DirectedOrderChoice.chosen sigma h.2
    RepresentationDirected.ProfileParametrization sigma
      (BruhatLowerInterval
        (OrderedARWord.orbitGraph sigma h.2 T)
        (OrderedARWord.wordFor sigma h.2 T E)) := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K Aᵐᵒᵖ
  letI : Finite (CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) := h.1
  let sigma := rightIndecomposableSkeleton.{u, u, u} K A
  let tau := rightIndecomposableSkeleton.{u, u, u} K Aᵐᵒᵖ
  let B := rightOppositeAlignedBiduality K A
  let Bdual : tau.AlignedBiduality sigma :=
    { forward := B.backward
      backward := B.forward
      backward_label := by
        rw [B.backward_label]
        rfl }
  letI : Finite (CanonicalIndecomposableIndex.{u, u} (Aᵐᵒᵖ)ᵐᵒᵖ) :=
    Finite.of_injective B.forward.labelEquiv.symm
      B.forward.labelEquiv.symm.injective
  letI : Fintype (CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) :=
    Fintype.ofFinite _
  letI : Fintype (CanonicalIndecomposableIndex.{u, u} (Aᵐᵒᵖ)ᵐᵒᵖ) :=
    Fintype.ofFinite _
  let Tsigma := sigma.finiteDimensionalARTranslationData K Aᵐᵒᵖ
  let Ttau := tau.finiteDimensionalARTranslationData K (Aᵐᵒᵖ)ᵐᵒᵖ
  exact explicitProfileParametrizationOfDirected
    (FSource := K) (FTarget := K)
    sigma tau Bdual h.2 Tsigma Ttau

/-- The paper's representation-directed class theorem, stated directly for
the canonical indecomposable isomorphism classes of a finite-dimensional
algebra over an algebraically closed field. -/
theorem rightRepresentationDirected_quotientSubmoduleEquidistribution
    (K A : Type u)
    [Field K] [IsAlgClosed K]
    [Ring A] [Algebra K A] [FiniteDimensional K A]
    (h : IsRightRepresentationDirected K A) :
    RightQuotientSubmoduleEquidistribution K A h.1 := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K Aᵐᵒᵖ
  letI : Finite (CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) := h.1
  let sigma := rightIndecomposableSkeleton.{u, u, u} K A
  let tau := rightIndecomposableSkeleton.{u, u, u} K Aᵐᵒᵖ
  let B := rightOppositeAlignedBiduality K A
  let Bdual : tau.AlignedBiduality sigma :=
    { forward := B.backward
      backward := B.forward
      backward_label := by
        rw [B.backward_label]
        rfl }
  letI : Finite (CanonicalIndecomposableIndex.{u, u} (Aᵐᵒᵖ)ᵐᵒᵖ) :=
    Finite.of_injective B.forward.labelEquiv.symm
      B.forward.labelEquiv.symm.injective
  letI : Fintype (CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) :=
    Fintype.ofFinite _
  letI : Fintype (CanonicalIndecomposableIndex.{u, u} (Aᵐᵒᵖ)ᵐᵒᵖ) :=
    Fintype.ofFinite _
  let Tsigma := sigma.finiteDimensionalARTranslationData K Aᵐᵒᵖ
  let Ttau := tau.finiteDimensionalARTranslationData K (Aᵐᵒᵖ)ᵐᵒᵖ
  exact quotientSubmoduleEquidistribution_of_directed
    (FSource := K) (FTarget := K)
    sigma tau Bdual h.2 Tsigma Ttau

/-- The exact common polynomial in the representation-directed theorem is
the reverse Coxeter-length polynomial of the principal Bruhat interval below
the canonical ordered Auslander--Reiten word. -/
theorem rightRepresentationDirected_levelPolynomials_eq_bruhat
    (K A : Type u)
    [Field K] [IsAlgClosed K]
    [Ring A] [Algebra K A] [FiniteDimensional K A]
    (h : IsRightRepresentationDirected K A) :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    letI : Finite (CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) := h.1
    letI : Fintype (CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) :=
      Fintype.ofFinite _
    let sigma := rightIndecomposableSkeleton.{u, u, u} K A
    letI : Finite (ProjectiveLabel sigma) :=
      Finite.of_injective Subtype.val Subtype.val_injective
    letI : Fintype (ProjectiveLabel sigma) := Fintype.ofFinite _
    let T := sigma.finiteDimensionalARTranslationData K Aᵐᵒᵖ
    let E := DirectedOrderChoice.chosen sigma h.2
    let G := OrderedARWord.orbitGraph sigma h.2 T
    let Q := OrderedARWord.wordFor sigma h.2 T E
    let hReduced : IsReduced G Q :=
      rightRepresentationDirectedWord_isReduced K A h
    sigma.qClosure.levelPolynomial =
        bruhatLowerIntervalReverseLengthPolynomial G Q hReduced ∧
      sigma.sClosure.levelPolynomial =
        bruhatLowerIntervalReverseLengthPolynomial G Q hReduced := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  letI : Finite (CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) := h.1
  letI : Fintype (CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) :=
    Fintype.ofFinite _
  let sigma := rightIndecomposableSkeleton.{u, u, u} K A
  letI : Finite (ProjectiveLabel sigma) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype (ProjectiveLabel sigma) := Fintype.ofFinite _
  let T := sigma.finiteDimensionalARTranslationData K Aᵐᵒᵖ
  let E := DirectedOrderChoice.chosen sigma h.2
  let G := OrderedARWord.orbitGraph sigma h.2 T
  let Q := OrderedARWord.wordFor sigma h.2 T E
  let hReduced : IsReduced G Q :=
    rightRepresentationDirectedWord_isReduced K A h
  have hMesh := hasUniformMeshExactnessFor K sigma h.2 T E
  have hSort :=
    OrbitGraphDuality.hasLocalClosureCorrespondence_wordFor
      (KField := K) sigma h.2 T E hMesh
  have hQuotient : sigma.qClosure.levelPolynomial =
      bruhatLowerIntervalReverseLengthPolynomial G Q hReduced :=
    DirectedQuotientProfile.Positioned.quotientLevelPolynomial_eq_bruhatLowerIntervalFor
      sigma hSort hReduced
  have hEqual :=
    rightRepresentationDirected_quotientSubmoduleEquidistribution K A h
  change sigma.qClosure.levelPolynomial =
    sigma.sClosure.levelPolynomial at hEqual
  exact ⟨hQuotient, hEqual.symm.trans hQuotient⟩

end QuotientSubmoduleEquidistribution
