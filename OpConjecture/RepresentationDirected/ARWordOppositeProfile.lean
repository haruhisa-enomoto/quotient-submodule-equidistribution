import OpConjecture.RepresentationDirected.SimpleGraphBruhatReversal
import OpConjecture.RepresentationDirected.ProfileInterface
import OpConjecture.RepresentationTheory.DualityConsequences

set_option autoImplicit false

noncomputable section

namespace OpConjecture.RepresentationDirected.OppositeSubmodule

open OpConjecture.RepresentationDirected.FixedWord
open FixedWordSubwords
open FixedWordProfile
open SimpleGraphBruhat
open SimpleGraphCoxeter

universe uL

variable {L : Type uL} [Fintype L]

/-! ## Conditional categorical/profile assembly -/

universe uR uS uI uK uMR uMS

/-- Relabel a finite set of word positions. -/
def positionLabelFinset
    {n : ℕ} {I : Type*} (e : Fin n ≃ I)
    (P : Finset (Fin n)) : Finset I :=
  P.map e.toEmbedding

@[simp]
theorem card_positionLabelFinset
    {n : ℕ} {I : Type*} (e : Fin n ≃ I)
    (P : Finset (Fin n)) :
    (positionLabelFinset e P).card = P.card := by
  simp [positionLabelFinset]

/-- Exact interface still needed from the categorical opposite construction.

It deliberately records a reversed-word quotient profile and position-label
alignment instead of asserting that two independently chosen directed linear
orders are definitionally reverse to one another. -/
structure ReversedQuotientProfileData
    {R : Type uR} [Ring R] [IsNoetherianRing R]
    {S : Type uS} [Ring S] [IsNoetherianRing S]
    {I : Type uI} {Kappa : Type uK}
    (sigma : IndecomposableSkeleton.{uR, uI, uMR} R I)
    (tau : IndecomposableSkeleton.{uS, uK, uMS} S Kappa)
    (G : SimpleGraph L) (Q : List L) (hQ : IsReduced G Q) where
  duality : tau.AlignedBiduality sigma
  sourcePosition : Fin Q.length ≃ I
  oppositePosition : Fin Q.reverse.length ≃ Kappa
  position_dual : ∀ p : Fin Q.reverse.length,
    duality.forward.labelEquiv (oppositePosition p) =
      sourcePosition ((reverseIndexEquiv Q).symm p)
  oppositeQuotientClosedEquiv :
    BruhatLowerInterval G Q.reverse ≃ tau.qClosure.Closeds
  support_oppositeQuotientClosedEquiv :
    ∀ u : BruhatLowerInterval G Q.reverse,
      (((oppositeQuotientClosedEquiv u : tau.qClosure.Closeds) :
          Set Kappa)) =
        (↑(positionLabelFinset oppositePosition
          (bruhatLexFirstPositions G Q.reverse
            ((isReduced_reverse_iff G Q).2 hQ) u)) : Set Kappa)ᶜ

namespace ReversedQuotientProfileData

variable
    {R : Type uR} [Ring R] [IsNoetherianRing R]
    {S : Type uS} [Ring S] [IsNoetherianRing S]
    {I : Type uI} {Kappa : Type uK}
    {sigma : IndecomposableSkeleton.{uR, uI, uMR} R I}
    {tau : IndecomposableSkeleton.{uS, uK, uMS} S Kappa}
    {G : SimpleGraph L} {Q : List L} {hQ : IsReduced G Q}
    (p : ReversedQuotientProfileData sigma tau G Q hQ)

/-- Omitted source labels at the genuine colex-last positions. -/
def colexLastOmittedLabels
    (u : BruhatLowerInterval G Q) : Finset I :=
  positionLabelFinset p.sourcePosition
    (bruhatColexLastPositions G Q hQ u)

/-- Transport the reversed-word quotient classification through inversion
and contragredient duality. -/
def bruhatLowerIntervalEquivSubmoduleClosed :
    BruhatLowerInterval G Q ≃ sigma.sClosure.Closeds :=
  (bruhatLowerIntervalReverseEquiv G Q hQ).trans <|
    p.oppositeQuotientClosedEquiv.trans <|
      (OpConjecture.IndecomposableSkeleton.AlignedBiduality.quotientToSubmoduleClosedOrderIso
        tau sigma p.duality).toEquiv

/-- The explicit position alignment identifies duals of reversed-word labels
with labels at the pulled-back original positions. -/
theorem map_oppositePositionLabels
    (P : Finset (Fin Q.reverse.length)) :
    (positionLabelFinset p.oppositePosition P).map
        p.duality.forward.labelEquiv.toEmbedding =
      positionLabelFinset p.sourcePosition
        (unreversePositionsIn Q P) := by
  ext i
  constructor
  · intro hi
    rw [Finset.mem_map] at hi
    obtain ⟨a, ha, hai⟩ := hi
    rw [positionLabelFinset, Finset.mem_map] at ha
    obtain ⟨x, hx, hxa⟩ := ha
    subst a
    rw [positionLabelFinset, Finset.mem_map]
    refine ⟨(reverseIndexEquiv Q).symm x, ?_, ?_⟩
    · rw [unreversePositionsIn, Finset.mem_map]
      exact ⟨x, hx, rfl⟩
    · exact (p.position_dual x).symm.trans hai
  · intro hi
    rw [positionLabelFinset, Finset.mem_map] at hi
    obtain ⟨y, hy, hyi⟩ := hi
    rw [unreversePositionsIn, Finset.mem_map] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    subst y
    rw [Finset.mem_map]
    refine ⟨p.oppositePosition x, ?_, ?_⟩
    · rw [positionLabelFinset, Finset.mem_map]
      exact ⟨x, hx, rfl⟩
    · exact (p.position_dual x).trans hyi

/-- The transported submodule-closed support is exactly the complement of
the colex-last omitted source labels. -/
theorem support_bruhatLowerIntervalEquivSubmoduleClosed
    (u : BruhatLowerInterval G Q) :
    (((p.bruhatLowerIntervalEquivSubmoduleClosed u :
        sigma.sClosure.Closeds) : Set I)) =
      (↑(p.colexLastOmittedLabels u) : Set I)ᶜ := by
  let hQr : IsReduced G Q.reverse :=
    (isReduced_reverse_iff G Q).2 hQ
  let uR : BruhatLowerInterval G Q.reverse :=
    bruhatLowerIntervalReverseEquiv G Q hQ u
  let P : Finset (Fin Q.reverse.length) :=
    bruhatLexFirstPositions G Q.reverse hQr uR
  change
    p.duality.forward.labelEquiv ''
        (((p.oppositeQuotientClosedEquiv uR :
          tau.qClosure.Closeds) : Set Kappa)) =
      (↑(positionLabelFinset p.sourcePosition
        (unreversePositionsIn Q P)) : Set I)ᶜ
  rw [p.support_oppositeQuotientClosedEquiv uR,
    Equiv.image_compl]
  congr 1
  simpa [P] using congrArg
    (fun F : Finset I ↦ (↑F : Set I))
    (p.map_oppositePositionLabels P)

/-- The colex-last omitted label set has Coxeter cardinality. -/
theorem card_colexLastOmittedLabels
    (u : BruhatLowerInterval G Q) :
    (p.colexLastOmittedLabels u).card =
      (system G).length u.1 := by
  rw [colexLastOmittedLabels, card_positionLabelFinset,
    card_bruhatColexLastPositions]

/-- Assemble the exact two-sided profile once the quotient classification
for the source word is supplied.  The submodule classification is derived,
not an additional input. -/
def profileParametrization
    (quotientClosedEquiv :
      Equiv (BruhatLowerInterval G Q) sigma.qClosure.Closeds)
    (support_quotientClosedEquiv :
      ∀ u : BruhatLowerInterval G Q,
        (((quotientClosedEquiv u : sigma.qClosure.Closeds) : Set I)) =
          (↑(positionLabelFinset p.sourcePosition
            (bruhatLexFirstPositions G Q hQ u)) : Set I)ᶜ) :
    ProfileParametrization sigma (BruhatLowerInterval G Q) where
  length u := (system G).length u.1
  lexFirstOmitted u :=
    positionLabelFinset p.sourcePosition
      (bruhatLexFirstPositions G Q hQ u)
  colexLastOmitted := p.colexLastOmittedLabels
  card_lexFirstOmitted u := by
    rw [card_positionLabelFinset, card_bruhatLexFirstPositions]
  card_colexLastOmitted := p.card_colexLastOmittedLabels
  quotientClosedEquiv := quotientClosedEquiv
  submoduleClosedEquiv := p.bruhatLowerIntervalEquivSubmoduleClosed
  support_quotientClosedEquiv := support_quotientClosedEquiv
  support_submoduleClosedEquiv :=
    p.support_bruhatLowerIntervalEquivSubmoduleClosed

/-- Conditional paper-facing endpoint: synchronized reversed-word quotient
data and the source quotient classification imply strong
quotient--submodule equidistribution. -/
theorem quotientSubmoduleEquidistribution
    [Finite I]
    (quotientClosedEquiv :
      Equiv (BruhatLowerInterval G Q) sigma.qClosure.Closeds)
    (support_quotientClosedEquiv :
      ∀ u : BruhatLowerInterval G Q,
        (((quotientClosedEquiv u : sigma.qClosure.Closeds) : Set I)) =
          (↑(positionLabelFinset p.sourcePosition
            (bruhatLexFirstPositions G Q hQ u)) : Set I)ᶜ) :
    sigma.QuotientSubmoduleEquidistribution := by
  letI := bruhatLowerIntervalFintype G Q hQ
  exact
    (p.profileParametrization quotientClosedEquiv
      support_quotientClosedEquiv).quotientSubmoduleEquidistribution

end ReversedQuotientProfileData

end OpConjecture.RepresentationDirected.OppositeSubmodule
