import OpConjecture.RepresentationDirected.ARWordDirectedSorting
import OpConjecture.RepresentationDirected.FixedWordProfile
import OpConjecture.RepresentationDirected.SimpleGraphBruhat

/-!
# Quotient profile of the ordered Auslander--Reiten word

This file transports the directed-sorting theorem from omitted word positions
to literal quotient-closed supports.  Under the isolated uniform
mesh-exactness input, locally reduced position sets and fixed-word elements
are equivalent to quotient-closed supports, with the exact reverse-length
profile.  No concrete algebra or module classification is used.
-/

set_option autoImplicit false

noncomputable section

namespace OpConjecture.RepresentationDirected.DirectedQuotientProfile

open Polynomial
open OpConjecture.RepresentationDirected.FixedWord
open OpConjecture.RepresentationDirected
open OpConjecture.RepresentationDirected.DirectedAROrbit
open OpConjecture.RepresentationDirected.DirectedSorting
open OpConjecture.RepresentationDirected.FixedWordProfile
open OpConjecture.RepresentationDirected.PrincipalPositivity
open OpConjecture.RepresentationDirected.SimpleGraphBruhat
open OpConjecture.RepresentationDirected.SimpleGraphCoxeter

universe uR uIota

variable {K R : Type uR} [Field K] [IsAlgClosed K]
  [Ring R] [Algebra K R] [FiniteDimensional K R] [IsNoetherianRing R]
  {Iota : Type uIota} [Fintype Iota]
  (sigma : IndecomposableSkeleton.{uR, uIota, uR} R Iota)

local instance : Finite (ProjectiveLabel sigma) :=
  Finite.of_injective Subtype.val Subtype.val_injective

local instance : Fintype (ProjectiveLabel sigma) := Fintype.ofFinite _

def locallyReducedToQClosed
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (hMeshExactness : ∀
      (D : Finset (Fin (OrderedARWord.word sigma H T).length))
      (a : Fin (OrderedARWord.word sigma H T).length),
      PositiveRightAdditiveForcesMeshInverseNonnegative
        (ARWord.SelectedSegments.segmentGraph
          (OrderedARWord.orbitGraph sigma H T)
          (OrderedARWord.word sigma H T)
          (rowRestrictedOmissions D a))
        (ARWord.SelectedSegments.segmentWord
          (OrderedARWord.word sigma H T)
          (rowRestrictedOmissions D a))) :
    LocallyReducedPositions
        (OrderedARWord.orbitGraph sigma H T)
        (OrderedARWord.word sigma H T) →
      sigma.qClosure.Closeds := fun d ↦ by
  let D := d.1
  refine ⟨{i | i ∉ omittedLabelFinset sigma H T D}, ?_⟩
  apply (qClosed_iff_wordMixedMultiplicity_nonnegative
    (K := K) (R := R) sigma H T D).2
  intro a x
  exact wordMixedMultiplicity_nonnegative_of_allLocalReduced
    (K := K) (R := R) sigma H T D d.2 (hMeshExactness D) a x

theorem locallyReducedToQClosed_injective
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (hMeshExactness : ∀
      (D : Finset (Fin (OrderedARWord.word sigma H T).length))
      (a : Fin (OrderedARWord.word sigma H T).length),
      PositiveRightAdditiveForcesMeshInverseNonnegative
        (ARWord.SelectedSegments.segmentGraph
          (OrderedARWord.orbitGraph sigma H T)
          (OrderedARWord.word sigma H T)
          (rowRestrictedOmissions D a))
        (ARWord.SelectedSegments.segmentWord
          (OrderedARWord.word sigma H T)
          (rowRestrictedOmissions D a))) :
    Function.Injective
      (locallyReducedToQClosed (K := K) (R := R)
        sigma H T hMeshExactness) := by
  intro d e hde
  apply Subtype.ext
  ext x
  have hsets := congrArg
    (fun C : sigma.qClosure.Closeds ↦ (C : Set Iota)) hde
  have hmem := Set.ext_iff.mp hsets
    (OrderedARWord.positionEquiv sigma H T x)
  change (OrderedARWord.positionEquiv sigma H T x ∉
      omittedLabelFinset sigma H T d.1) ↔
    (OrderedARWord.positionEquiv sigma H T x ∉
      omittedLabelFinset sigma H T e.1) at hmem
  simp only [mem_omittedLabelFinset_iff] at hmem
  tauto

theorem locallyReducedToQClosed_surjective
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (hMeshExactness : ∀
      (D : Finset (Fin (OrderedARWord.word sigma H T).length))
      (a : Fin (OrderedARWord.word sigma H T).length),
      PositiveRightAdditiveForcesMeshInverseNonnegative
        (ARWord.SelectedSegments.segmentGraph
          (OrderedARWord.orbitGraph sigma H T)
          (OrderedARWord.word sigma H T)
          (rowRestrictedOmissions D a))
        (ARWord.SelectedSegments.segmentWord
          (OrderedARWord.word sigma H T)
          (rowRestrictedOmissions D a))) :
    Function.Surjective
      (locallyReducedToQClosed (K := K) (R := R)
        sigma H T hMeshExactness) := by
  classical
  intro C
  let D : Finset (Fin (OrderedARWord.word sigma H T).length) :=
    Finset.univ.filter fun x ↦
      OrderedARWord.positionEquiv sigma H T x ∉ (C : Set Iota)
  have hSupport : {i | i ∉ omittedLabelFinset sigma H T D} =
      (C : Set Iota) := by
    ext i
    obtain ⟨x, rfl⟩ :=
      (OrderedARWord.positionEquiv sigma H T).surjective i
    simp [D]
  have hClosedD : sigma.qClosure.IsClosed
      {i | i ∉ omittedLabelFinset sigma H T D} := by
    rw [hSupport]
    exact C.2
  have hNonnegative :=
    (qClosed_iff_wordMixedMultiplicity_nonnegative
      (K := K) (R := R) sigma H T D).1 hClosedD
  have hLocal := allLocalReduced_of_wordMixedMultiplicity_nonnegative
    (K := K) (R := R) sigma H T D hNonnegative
  let d : LocallyReducedPositions
      (OrderedARWord.orbitGraph sigma H T)
      (OrderedARWord.word sigma H T) := ⟨D, hLocal⟩
  refine ⟨d, ?_⟩
  apply Subtype.ext
  exact hSupport

def locallyReducedPositionsEquivQClosed
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (hMeshExactness : ∀
      (D : Finset (Fin (OrderedARWord.word sigma H T).length))
      (a : Fin (OrderedARWord.word sigma H T).length),
      PositiveRightAdditiveForcesMeshInverseNonnegative
        (ARWord.SelectedSegments.segmentGraph
          (OrderedARWord.orbitGraph sigma H T)
          (OrderedARWord.word sigma H T)
          (rowRestrictedOmissions D a))
        (ARWord.SelectedSegments.segmentWord
          (OrderedARWord.word sigma H T)
          (rowRestrictedOmissions D a))) :
    LocallyReducedPositions
        (OrderedARWord.orbitGraph sigma H T)
        (OrderedARWord.word sigma H T) ≃
      sigma.qClosure.Closeds :=
  Equiv.ofBijective
    (locallyReducedToQClosed (K := K) (R := R)
      sigma H T hMeshExactness)
    ⟨locallyReducedToQClosed_injective (K := K) (R := R)
        sigma H T hMeshExactness,
      locallyReducedToQClosed_surjective (K := K) (R := R)
        sigma H T hMeshExactness⟩

theorem support_locallyReducedPositionsEquivQClosed
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (hMeshExactness : ∀
      (D : Finset (Fin (OrderedARWord.word sigma H T).length))
      (a : Fin (OrderedARWord.word sigma H T).length),
      PositiveRightAdditiveForcesMeshInverseNonnegative
        (ARWord.SelectedSegments.segmentGraph
          (OrderedARWord.orbitGraph sigma H T)
          (OrderedARWord.word sigma H T)
          (rowRestrictedOmissions D a))
        (ARWord.SelectedSegments.segmentWord
          (OrderedARWord.word sigma H T)
          (rowRestrictedOmissions D a)))
    (d : LocallyReducedPositions
      (OrderedARWord.orbitGraph sigma H T)
      (OrderedARWord.word sigma H T)) :
    (((locallyReducedPositionsEquivQClosed (K := K) (R := R)
        sigma H T hMeshExactness d : sigma.qClosure.Closeds) : Set Iota)) =
      {i | i ∉ omittedLabelFinset sigma H T d.1} := rfl

include K in
def fixedWordElementEquivQClosed
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (hMeshExactness : ∀
      (D : Finset (Fin (OrderedARWord.word sigma H T).length))
      (a : Fin (OrderedARWord.word sigma H T).length),
      PositiveRightAdditiveForcesMeshInverseNonnegative
        (ARWord.SelectedSegments.segmentGraph
          (OrderedARWord.orbitGraph sigma H T)
          (OrderedARWord.word sigma H T)
          (rowRestrictedOmissions D a))
        (ARWord.SelectedSegments.segmentWord
          (OrderedARWord.word sigma H T)
          (rowRestrictedOmissions D a))) :
    FixedWordSubwords.FixedWordElement
        (system (OrderedARWord.orbitGraph sigma H T))
        (OrderedARWord.word sigma H T) ≃
      sigma.qClosure.Closeds := by
  exact (fixedWordElementEquivLocallyReducedPositions
      (OrderedARWord.orbitGraph sigma H T)
      (OrderedARWord.word sigma H T)).trans
        (locallyReducedPositionsEquivQClosed (K := K) (R := R)
          sigma H T hMeshExactness)

theorem support_fixedWordElementEquivQClosed
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (hMeshExactness : ∀
      (D : Finset (Fin (OrderedARWord.word sigma H T).length))
      (a : Fin (OrderedARWord.word sigma H T).length),
      PositiveRightAdditiveForcesMeshInverseNonnegative
        (ARWord.SelectedSegments.segmentGraph
          (OrderedARWord.orbitGraph sigma H T)
          (OrderedARWord.word sigma H T)
          (rowRestrictedOmissions D a))
        (ARWord.SelectedSegments.segmentWord
          (OrderedARWord.word sigma H T)
          (rowRestrictedOmissions D a)))
    (u : FixedWordSubwords.FixedWordElement
      (system (OrderedARWord.orbitGraph sigma H T))
      (OrderedARWord.word sigma H T)) :
    (((fixedWordElementEquivQClosed (K := K) (R := R)
        sigma H T hMeshExactness u : sigma.qClosure.Closeds) : Set Iota)) =
      {i | i ∉ omittedLabelFinset sigma H T
        (lexFirstLocalPositions
          (OrderedARWord.orbitGraph sigma H T)
          (OrderedARWord.word sigma H T) u).1} := by
  rfl

theorem card_omittedLabelFinset
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (D : Finset (Fin (OrderedARWord.word sigma H T).length)) :
    (omittedLabelFinset sigma H T D).card = D.card := by
  simp [omittedLabelFinset]

theorem ncard_fixedWordElementEquivQClosed
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (hMeshExactness : ∀
      (D : Finset (Fin (OrderedARWord.word sigma H T).length))
      (a : Fin (OrderedARWord.word sigma H T).length),
      PositiveRightAdditiveForcesMeshInverseNonnegative
        (ARWord.SelectedSegments.segmentGraph
          (OrderedARWord.orbitGraph sigma H T)
          (OrderedARWord.word sigma H T)
          (rowRestrictedOmissions D a))
        (ARWord.SelectedSegments.segmentWord
          (OrderedARWord.word sigma H T)
          (rowRestrictedOmissions D a)))
    (u : FixedWordSubwords.FixedWordElement
      (system (OrderedARWord.orbitGraph sigma H T))
      (OrderedARWord.word sigma H T)) :
    ((((fixedWordElementEquivQClosed (K := K) (R := R)
        sigma H T hMeshExactness u : sigma.qClosure.Closeds) : Set Iota).ncard)) =
      (OrderedARWord.word sigma H T).length -
        (system (OrderedARWord.orbitGraph sigma H T)).length u.1 := by
  have hCard : Nat.card Iota =
      (OrderedARWord.word sigma H T).length := by
    rw [Nat.card_eq_fintype_card]
    symm
    simpa only [Fintype.card_fin] using Fintype.card_congr
      (OrderedARWord.positionEquiv sigma H T)
  rw [support_fixedWordElementEquivQClosed
    (K := K) (R := R) sigma H T hMeshExactness u]
  change ((↑(omittedLabelFinset sigma H T
    (lexFirstLocalPositions
      (OrderedARWord.orbitGraph sigma H T)
      (OrderedARWord.word sigma H T) u).1) : Set Iota)ᶜ).ncard = _
  rw [Set.ncard_compl, Set.ncard_coe_finset,
    card_omittedLabelFinset sigma H T,
    card_lexFirstLocalPositions, hCard]

include K in
theorem quotientLevelPolynomial_eq_fixedWordReverseLength
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (hMeshExactness : ∀
      (D : Finset (Fin (OrderedARWord.word sigma H T).length))
      (a : Fin (OrderedARWord.word sigma H T).length),
      PositiveRightAdditiveForcesMeshInverseNonnegative
        (ARWord.SelectedSegments.segmentGraph
          (OrderedARWord.orbitGraph sigma H T)
          (OrderedARWord.word sigma H T)
          (rowRestrictedOmissions D a))
        (ARWord.SelectedSegments.segmentWord
          (OrderedARWord.word sigma H T)
          (rowRestrictedOmissions D a))) :
    sigma.qClosure.levelPolynomial =
      ∑ u : FixedWordSubwords.FixedWordElement
        (system (OrderedARWord.orbitGraph sigma H T))
        (OrderedARWord.word sigma H T),
        X ^ ((OrderedARWord.word sigma H T).length -
          (system (OrderedARWord.orbitGraph sigma H T)).length u.1) := by
  exact OpConjecture.SetClosure.levelPolynomial_eq_sum_stat
    sigma.qClosure
    (fixedWordElementEquivQClosed (K := K) (R := R)
      sigma H T hMeshExactness)
    (fun u ↦ (OrderedARWord.word sigma H T).length -
      (system (OrderedARWord.orbitGraph sigma H T)).length u.1)
    (ncard_fixedWordElementEquivQClosed (K := K) (R := R)
      sigma H T hMeshExactness)

include K in
/-- Quotient-closed supports are parametrized by the intrinsic principal
Bruhat interval below the ordered AR-word product. -/
def bruhatLowerIntervalEquivQClosed
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (hMeshExactness : ∀
      (D : Finset (Fin (OrderedARWord.word sigma H T).length))
      (a : Fin (OrderedARWord.word sigma H T).length),
      PositiveRightAdditiveForcesMeshInverseNonnegative
        (ARWord.SelectedSegments.segmentGraph
          (OrderedARWord.orbitGraph sigma H T)
          (OrderedARWord.word sigma H T)
          (rowRestrictedOmissions D a))
        (ARWord.SelectedSegments.segmentWord
          (OrderedARWord.word sigma H T)
          (rowRestrictedOmissions D a))) :
    BruhatLowerInterval
        (OrderedARWord.orbitGraph sigma H T)
        (OrderedARWord.word sigma H T) ≃
      sigma.qClosure.Closeds := by
  let hReduced : IsReduced
      (OrderedARWord.orbitGraph sigma H T)
      (OrderedARWord.word sigma H T) :=
    orderedARWord_isReduced_of_meshExactness
      (K := K) (R := R) sigma H T (hMeshExactness Finset.univ)
  exact (fixedWordElementEquivBruhatLowerInterval
      (OrderedARWord.orbitGraph sigma H T)
      (OrderedARWord.word sigma H T) hReduced).symm.trans
    (fixedWordElementEquivQClosed (K := K) (R := R)
      sigma H T hMeshExactness)

include K in
/-- Omitted skeleton labels attached to the lex-first reduced support of a
Bruhat-interval element. -/
def bruhatLexFirstOmittedLabels
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (hMeshExactness : ∀
      (D : Finset (Fin (OrderedARWord.word sigma H T).length))
      (a : Fin (OrderedARWord.word sigma H T).length),
      PositiveRightAdditiveForcesMeshInverseNonnegative
        (ARWord.SelectedSegments.segmentGraph
          (OrderedARWord.orbitGraph sigma H T)
          (OrderedARWord.word sigma H T)
          (rowRestrictedOmissions D a))
        (ARWord.SelectedSegments.segmentWord
          (OrderedARWord.word sigma H T)
          (rowRestrictedOmissions D a)))
    (u : BruhatLowerInterval
      (OrderedARWord.orbitGraph sigma H T)
      (OrderedARWord.word sigma H T)) : Finset Iota :=
  omittedLabelFinset sigma H T
    (bruhatLexFirstPositions
      (OrderedARWord.orbitGraph sigma H T)
      (OrderedARWord.word sigma H T)
      (orderedARWord_isReduced_of_meshExactness
        (K := K) (R := R) sigma H T (hMeshExactness Finset.univ)) u)

include K in
/-- The quotient-closed support indexed by a Bruhat element is exactly the
complement of its lex-first omitted labels. -/
theorem support_bruhatLowerIntervalEquivQClosed
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (hMeshExactness : ∀
      (D : Finset (Fin (OrderedARWord.word sigma H T).length))
      (a : Fin (OrderedARWord.word sigma H T).length),
      PositiveRightAdditiveForcesMeshInverseNonnegative
        (ARWord.SelectedSegments.segmentGraph
          (OrderedARWord.orbitGraph sigma H T)
          (OrderedARWord.word sigma H T)
          (rowRestrictedOmissions D a))
        (ARWord.SelectedSegments.segmentWord
          (OrderedARWord.word sigma H T)
          (rowRestrictedOmissions D a)))
    (u : BruhatLowerInterval
      (OrderedARWord.orbitGraph sigma H T)
      (OrderedARWord.word sigma H T)) :
    (((bruhatLowerIntervalEquivQClosed (K := K) (R := R)
        sigma H T hMeshExactness u : sigma.qClosure.Closeds) : Set Iota)) =
      (↑(bruhatLexFirstOmittedLabels (K := K) (R := R)
        sigma H T hMeshExactness u) : Set Iota)ᶜ := by
  rfl

include K in
/-- The omitted-label support of a Bruhat element has its Coxeter length. -/
theorem card_bruhatLexFirstOmittedLabels
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (hMeshExactness : ∀
      (D : Finset (Fin (OrderedARWord.word sigma H T).length))
      (a : Fin (OrderedARWord.word sigma H T).length),
      PositiveRightAdditiveForcesMeshInverseNonnegative
        (ARWord.SelectedSegments.segmentGraph
          (OrderedARWord.orbitGraph sigma H T)
          (OrderedARWord.word sigma H T)
          (rowRestrictedOmissions D a))
        (ARWord.SelectedSegments.segmentWord
          (OrderedARWord.word sigma H T)
          (rowRestrictedOmissions D a)))
    (u : BruhatLowerInterval
      (OrderedARWord.orbitGraph sigma H T)
      (OrderedARWord.word sigma H T)) :
    (bruhatLexFirstOmittedLabels (K := K) (R := R)
      sigma H T hMeshExactness u).card =
      (system (OrderedARWord.orbitGraph sigma H T)).length u.1 := by
  unfold bruhatLexFirstOmittedLabels
  rw [card_omittedLabelFinset,
    card_bruhatLexFirstPositions]

include K in
/-- Paper-facing quotient profile: the quotient-closed level polynomial is
the reverse Coxeter-length polynomial of the principal Bruhat interval. -/
theorem quotientLevelPolynomial_eq_bruhatLowerInterval
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (hMeshExactness : ∀
      (D : Finset (Fin (OrderedARWord.word sigma H T).length))
      (a : Fin (OrderedARWord.word sigma H T).length),
      PositiveRightAdditiveForcesMeshInverseNonnegative
        (ARWord.SelectedSegments.segmentGraph
          (OrderedARWord.orbitGraph sigma H T)
          (OrderedARWord.word sigma H T)
          (rowRestrictedOmissions D a))
        (ARWord.SelectedSegments.segmentWord
          (OrderedARWord.word sigma H T)
          (rowRestrictedOmissions D a))) :
    let hReduced : IsReduced
        (OrderedARWord.orbitGraph sigma H T)
        (OrderedARWord.word sigma H T) :=
      orderedARWord_isReduced_of_meshExactness
        (K := K) (R := R) sigma H T (hMeshExactness Finset.univ)
    sigma.qClosure.levelPolynomial =
      bruhatLowerIntervalReverseLengthPolynomial
        (OrderedARWord.orbitGraph sigma H T)
        (OrderedARWord.word sigma H T) hReduced := by
  dsimp only
  let hReduced : IsReduced
      (OrderedARWord.orbitGraph sigma H T)
      (OrderedARWord.word sigma H T) :=
    orderedARWord_isReduced_of_meshExactness
      (K := K) (R := R) sigma H T (hMeshExactness Finset.univ)
  calc
    sigma.qClosure.levelPolynomial =
        ∑ u : FixedWordSubwords.FixedWordElement
          (system (OrderedARWord.orbitGraph sigma H T))
          (OrderedARWord.word sigma H T),
          X ^ ((OrderedARWord.word sigma H T).length -
            (system (OrderedARWord.orbitGraph sigma H T)).length u.1) :=
      quotientLevelPolynomial_eq_fixedWordReverseLength
        (K := K) (R := R) sigma H T hMeshExactness
    _ = ∑ D : LocallyReducedPositions
          (OrderedARWord.orbitGraph sigma H T)
          (OrderedARWord.word sigma H T),
          X ^ ((OrderedARWord.word sigma H T).length - D.1.card) :=
      (locallyReducedPositions_generatingFunction
        (OrderedARWord.orbitGraph sigma H T)
        (OrderedARWord.word sigma H T)).symm
    _ = bruhatLowerIntervalReverseLengthPolynomial
          (OrderedARWord.orbitGraph sigma H T)
          (OrderedARWord.word sigma H T) hReduced :=
      locallyReducedPositions_generatingFunction_eq_bruhatLowerInterval
        (OrderedARWord.orbitGraph sigma H T)
        (OrderedARWord.word sigma H T) hReduced

end OpConjecture.RepresentationDirected.DirectedQuotientProfile
