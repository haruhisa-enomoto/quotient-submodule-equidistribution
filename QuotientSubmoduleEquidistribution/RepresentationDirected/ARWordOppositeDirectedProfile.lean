import QuotientSubmoduleEquidistribution.RepresentationDirected.ARWordOrbitGraphDuality
import QuotientSubmoduleEquidistribution.RepresentationDirected.ARWordOppositeProfile

/-!
# Opposite profiles for explicitly ordered Auslander--Reiten words

This file combines explicit-order directed sorting, orbit-graph relabeling,
literal opposite-word reversal, Bruhat profiles, and categorical duality.
Under the isolated uniform finite mesh-exactness input on the source and
opposite words, it constructs the complete two-sided profile and proves
quotient--submodule equidistribution.

All statements are abstract.  No concrete algebra, quiver presentation,
module enumeration, or classification is used.
-/

set_option autoImplicit false

noncomputable section

namespace QuotientSubmoduleEquidistribution.RepresentationDirected.OppositeDirectedProfile

open QuotientSubmoduleEquidistribution.RepresentationDirected.FixedWord
open QuotientSubmoduleEquidistribution.RepresentationDirected
open QuotientSubmoduleEquidistribution.RepresentationDirected.ARWordDuality
open QuotientSubmoduleEquidistribution.RepresentationDirected.ARWord.SelectedSegments
open QuotientSubmoduleEquidistribution.RepresentationDirected.DirectedAROrbit
open QuotientSubmoduleEquidistribution.RepresentationDirected.DirectedQuotientProfile.Positioned
open QuotientSubmoduleEquidistribution.RepresentationDirected.DirectedSorting
open QuotientSubmoduleEquidistribution.RepresentationDirected.FixedWordSubwords
open QuotientSubmoduleEquidistribution.RepresentationDirected.FixedWordProfile
open QuotientSubmoduleEquidistribution.RepresentationDirected.OppositeSubmodule
open QuotientSubmoduleEquidistribution.RepresentationDirected.OrbitGraphDuality
open QuotientSubmoduleEquidistribution.RepresentationDirected.PrincipalPositivity
open QuotientSubmoduleEquidistribution.RepresentationDirected.SimpleGraphBruhat
open QuotientSubmoduleEquidistribution.RepresentationDirected.SimpleGraphCoxeter

universe uR uS uI uK

variable
    {R : Type uR} [Ring R] [IsNoetherianRing R]
    {S : Type uS} [Ring S] [IsNoetherianRing S]
    {I : Type uI} {Kappa : Type uK}
    [Fintype I] [Fintype Kappa]
    (sigma : IndecomposableSkeleton.{uR, uI, uR} R I)
    (tau : IndecomposableSkeleton.{uS, uK, uS} S Kappa)

local instance : Finite (ProjectiveLabel sigma) :=
  Finite.of_injective Subtype.val Subtype.val_injective

local instance : Fintype (ProjectiveLabel sigma) := Fintype.ofFinite _

/-! ## Relabelled opposite word and its genuine positions -/

/-- The target explicit AR word with orbit letters relabelled into the
source orbit-label type. -/
def relabelledOppositeWord
    (B : tau.AlignedBiduality sigma)
    (Hsigma : HasAcyclicNonzeroNonisomorphisms sigma)
    (Htau : HasAcyclicNonzeroNonisomorphisms tau)
    (Tsigma : sigma.FiniteARTranslationData)
    (Ttau : tau.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma) :
    List (ProjectiveLabel sigma) :=
  (OrderedARWord.wordFor tau Htau Ttau
      (oppositeOrderChoice sigma tau B E)).map
    (dualOrbitLabelEquiv sigma tau B Hsigma Tsigma)

/-- Genuine target positions, with the mapped word's position type
identified value-for-value with the native target word's positions. -/
def actualRelabelledOppositePosition
    (B : tau.AlignedBiduality sigma)
    (Hsigma : HasAcyclicNonzeroNonisomorphisms sigma)
    (Htau : HasAcyclicNonzeroNonisomorphisms tau)
    (Tsigma : sigma.FiniteARTranslationData)
    (Ttau : tau.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma) :
    Fin (relabelledOppositeWord sigma tau B Hsigma Htau
      Tsigma Ttau E).length ≃ Kappa :=
  (mapIndexEquiv
    (OrderedARWord.wordFor tau Htau Ttau
      (oppositeOrderChoice sigma tau B E))
    (dualOrbitLabelEquiv sigma tau B Hsigma Tsigma)).trans
      (OrderedARWord.positionEquivFor tau Htau Ttau
        (oppositeOrderChoice sigma tau B E))

/-- Synchronized reversed source positions, transported back across the
literal target-word/reversed-source-word equality. -/
def synchronizedRelabelledOppositePosition
    (B : tau.AlignedBiduality sigma)
    (Hsigma : HasAcyclicNonzeroNonisomorphisms sigma)
    (Htau : HasAcyclicNonzeroNonisomorphisms tau)
    (Tsigma : sigma.FiniteARTranslationData)
    (Ttau : tau.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma) :
    Fin (relabelledOppositeWord sigma tau B Hsigma Htau
      Tsigma Ttau E).length ≃ Kappa :=
  let hword := map_wordFor_oppositeOrderChoice_eq_reverse
    sigma tau B Hsigma Htau Tsigma Ttau E
  (finCongr (congrArg List.length hword)).trans
    (synchronizedOppositePosition sigma tau B
      (OrderedARWord.positionEquivFor sigma Hsigma Tsigma E))

/-- Genuine target positions coincide with the synchronized reversed source
positions. -/
theorem actualRelabelledOppositePosition_eq
    (B : tau.AlignedBiduality sigma)
    (Hsigma : HasAcyclicNonzeroNonisomorphisms sigma)
    (Htau : HasAcyclicNonzeroNonisomorphisms tau)
    (Tsigma : sigma.FiniteARTranslationData)
    (Ttau : tau.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma) :
    actualRelabelledOppositePosition sigma tau B Hsigma Htau
        Tsigma Ttau E =
      synchronizedRelabelledOppositePosition sigma tau B Hsigma Htau
        Tsigma Ttau E := by
  apply Equiv.ext
  intro p
  apply B.forward.labelEquiv.injective
  let pT : Fin (OrderedARWord.wordFor tau Htau Ttau
      (oppositeOrderChoice sigma tau B E)).length :=
    mapIndexEquiv
      (OrderedARWord.wordFor tau Htau Ttau
        (oppositeOrderChoice sigma tau B E))
      (dualOrbitLabelEquiv sigma tau B Hsigma Tsigma) p
  let pR : Fin (OrderedARWord.wordFor sigma Hsigma Tsigma E).reverse.length :=
    finCongr (congrArg List.length
      (map_wordFor_oppositeOrderChoice_eq_reverse
        sigma tau B Hsigma Htau Tsigma Ttau E)) p
  have hMappedCard :
      ((OrderedARWord.wordFor tau Htau Ttau
        (oppositeOrderChoice sigma tau B E)).map
          (dualOrbitLabelEquiv sigma tau B Hsigma Tsigma)).length =
        Fintype.card I := by
    calc
      _ = (OrderedARWord.wordFor sigma Hsigma Tsigma E).reverse.length :=
        congrArg List.length
          (map_wordFor_oppositeOrderChoice_eq_reverse
            sigma tau B Hsigma Htau Tsigma Ttau E)
      _ = Fintype.card I := by
        rw [List.length_reverse,
          OrderedARWord.wordFor_length sigma Hsigma Tsigma E]
  change B.forward.labelEquiv
      (OrderedARWord.positionEquivFor tau Htau Ttau
        (oppositeOrderChoice sigma tau B E) pT) =
    B.forward.labelEquiv
      (synchronizedOppositePosition sigma tau B
        (OrderedARWord.positionEquivFor sigma Hsigma Tsigma E) pR)
  rw [positionEquivFor_oppositeOrderChoice_dual,
    synchronizedOppositePosition_dual]
  apply congrArg (OrderedARWord.positionEquivFor sigma Hsigma Tsigma E)
  apply (reverseIndexEquiv
    (OrderedARWord.wordFor sigma Hsigma Tsigma E)).injective
  rw [Equiv.apply_symm_apply]
  apply Fin.ext
  simp [pT, pR, reverseWordPositionEquiv, reverseIndexEquiv,
    mapIndexEquiv, Fin.rev]
  omega
  all_goals exact Hsigma

omit [Fintype I] [Fintype Kappa] in
private theorem hasLocalClosureCorrespondence_congr_word
    (G : SimpleGraph (ProjectiveLabel sigma))
    {W Q : List (ProjectiveLabel sigma)} (h : W = Q)
    (position : Fin Q.length ≃ Kappa) :
    HasLocalClosureCorrespondence tau G W
        ((finCongr (congrArg List.length h)).trans position) ↔
      HasLocalClosureCorrespondence tau G Q position := by
  subst Q
  rfl

/-- Rewriting the relabelled target word as the reversed source word also
rewrites its genuine target positions to synchronized reversed positions. -/
theorem relabelledOppositeSorting_iff_reverseSorting
    (B : tau.AlignedBiduality sigma)
    (Hsigma : HasAcyclicNonzeroNonisomorphisms sigma)
    (Htau : HasAcyclicNonzeroNonisomorphisms tau)
    (Tsigma : sigma.FiniteARTranslationData)
    (Ttau : tau.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (G : SimpleGraph (ProjectiveLabel sigma)) :
    HasLocalClosureCorrespondence tau G
        (relabelledOppositeWord sigma tau B Hsigma Htau Tsigma Ttau E)
        (actualRelabelledOppositePosition
          sigma tau B Hsigma Htau Tsigma Ttau E) ↔
      HasLocalClosureCorrespondence tau G
        (OrderedARWord.wordFor sigma Hsigma Tsigma E).reverse
        (synchronizedOppositePosition sigma tau B
          (OrderedARWord.positionEquivFor sigma Hsigma Tsigma E)) := by
  rw [actualRelabelledOppositePosition_eq sigma tau B Hsigma Htau
    Tsigma Ttau E]
  let hword :
      relabelledOppositeWord sigma tau B Hsigma Htau Tsigma Ttau E =
        (OrderedARWord.wordFor sigma Hsigma Tsigma E).reverse :=
    map_wordFor_oppositeOrderChoice_eq_reverse
      sigma tau B Hsigma Htau Tsigma Ttau E
  exact hasLocalClosureCorrespondence_congr_word sigma tau G hword
    (synchronizedOppositePosition sigma tau B
      (OrderedARWord.positionEquivFor sigma Hsigma Tsigma E))

/-! ## Production opposite-profile data and parametrization -/

/-- Reversed-word quotient-profile data built from the relabelled target
local closure correspondence. -/
def explicitReversedQuotientProfileData
    (B : tau.AlignedBiduality sigma)
    (Hsigma : HasAcyclicNonzeroNonisomorphisms sigma)
    (Htau : HasAcyclicNonzeroNonisomorphisms tau)
    (Tsigma : sigma.FiniteARTranslationData)
    (Ttau : tau.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (hReduced : IsReduced (OrderedARWord.orbitGraph sigma Hsigma Tsigma)
      (OrderedARWord.wordFor sigma Hsigma Tsigma E))
    (hOppositeSort : HasLocalClosureCorrespondence tau
      (OrderedARWord.orbitGraph sigma Hsigma Tsigma)
      (relabelledOppositeWord sigma tau B Hsigma Htau Tsigma Ttau E)
      (actualRelabelledOppositePosition
        sigma tau B Hsigma Htau Tsigma Ttau E)) :
    ReversedQuotientProfileData sigma tau
      (OrderedARWord.orbitGraph sigma Hsigma Tsigma)
      (OrderedARWord.wordFor sigma Hsigma Tsigma E) hReduced := by
  let G := OrderedARWord.orbitGraph sigma Hsigma Tsigma
  let Q := OrderedARWord.wordFor sigma Hsigma Tsigma E
  let oppositePosition := synchronizedOppositePosition sigma tau B
    (OrderedARWord.positionEquivFor sigma Hsigma Tsigma E)
  have hReverseSort : HasLocalClosureCorrespondence tau G Q.reverse
      oppositePosition :=
    (relabelledOppositeSorting_iff_reverseSorting
      sigma tau B Hsigma Htau Tsigma Ttau E G).1 hOppositeSort
  have hReverseReduced : IsReduced G Q.reverse :=
    (isReduced_reverse_iff G Q).2 hReduced
  exact
    { duality := B
      sourcePosition :=
        OrderedARWord.positionEquivFor sigma Hsigma Tsigma E
      oppositePosition := oppositePosition
      position_dual := by
        intro p
        exact synchronizedOppositePosition_dual sigma tau B
          (OrderedARWord.positionEquivFor sigma Hsigma Tsigma E) p
      oppositeQuotientClosedEquiv :=
        bruhatLowerIntervalEquivQClosedFor tau
          hReverseSort hReverseReduced
      support_oppositeQuotientClosedEquiv := by
        intro u
        simpa only [positionLabelFinset,
          bruhatLexFirstOmittedLabelsFor, omittedLabelsFor] using
          (support_bruhatLowerIntervalEquivQClosedFor tau
            hReverseSort hReverseReduced u) }

/-- Public two-sided profile parametrization attached to an explicit source
order and its synchronized opposite order.  Both quotient classifications
use the production `DirectedQuotientProfile.Positioned` adapter. -/
def explicitProfileParametrization
    (B : tau.AlignedBiduality sigma)
    (Hsigma : HasAcyclicNonzeroNonisomorphisms sigma)
    (Htau : HasAcyclicNonzeroNonisomorphisms tau)
    (Tsigma : sigma.FiniteARTranslationData)
    (Ttau : tau.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (hReduced : IsReduced (OrderedARWord.orbitGraph sigma Hsigma Tsigma)
      (OrderedARWord.wordFor sigma Hsigma Tsigma E))
    (hSourceSort : HasLocalClosureCorrespondence sigma
      (OrderedARWord.orbitGraph sigma Hsigma Tsigma)
      (OrderedARWord.wordFor sigma Hsigma Tsigma E)
      (OrderedARWord.positionEquivFor sigma Hsigma Tsigma E))
    (hOppositeSort : HasLocalClosureCorrespondence tau
      (OrderedARWord.orbitGraph sigma Hsigma Tsigma)
      (relabelledOppositeWord sigma tau B Hsigma Htau Tsigma Ttau E)
      (actualRelabelledOppositePosition
        sigma tau B Hsigma Htau Tsigma Ttau E)) :
    ProfileParametrization sigma
      (BruhatLowerInterval
        (OrderedARWord.orbitGraph sigma Hsigma Tsigma)
        (OrderedARWord.wordFor sigma Hsigma Tsigma E)) := by
  let p := explicitReversedQuotientProfileData sigma tau B Hsigma Htau
    Tsigma Ttau E hReduced hOppositeSort
  have hpSource : p.sourcePosition =
      OrderedARWord.positionEquivFor sigma Hsigma Tsigma E := rfl
  exact p.profileParametrization
    (bruhatLowerIntervalEquivQClosedFor sigma hSourceSort hReduced)
    (fun u ↦ by
      rw [hpSource]
      simpa only [positionLabelFinset,
        bruhatLexFirstOmittedLabelsFor, omittedLabelsFor] using
        (support_bruhatLowerIntervalEquivQClosedFor sigma
          hSourceSort hReduced u))

/-! ## End-to-end mesh-exactness endpoint -/

/-- Uniform finite mesh exactness for all omission sets and all starting
rows of one explicit AR word. -/
def HasUniformMeshExactnessFor
    (rho : IndecomposableSkeleton.{uR, uI, uR} R I)
    (H : HasAcyclicNonzeroNonisomorphisms rho)
    (T : rho.FiniteARTranslationData)
    (E : DirectedOrderChoice rho) : Prop :=
  ∀ (D : Finset (Fin (OrderedARWord.wordFor rho H T E).length))
    (a : Fin (OrderedARWord.wordFor rho H T E).length),
    PositiveRightAdditiveForcesMeshInverseNonnegative
      (segmentGraph (OrderedARWord.orbitGraph rho H T)
        (OrderedARWord.wordFor rho H T E)
        (rowRestrictedOmissions D a))
      (segmentWord (OrderedARWord.wordFor rho H T E)
        (rowRestrictedOmissions D a))

/-- End-to-end two-sided Bruhat profile from uniform mesh exactness on the
source word and its synchronized opposite word.  In particular, the
resulting structure records the lex-first quotient supports, colex-last
submodule supports, both closed-set equivalences, and their common length
statistic. -/
def explicitProfileParametrization_of_explicitOrderMeshExactness
    {KSource : Type uR} [Field KSource] [IsAlgClosed KSource]
    [Algebra KSource R] [FiniteDimensional KSource R]
    {KTarget : Type uS} [Field KTarget] [IsAlgClosed KTarget]
    [Algebra KTarget S] [FiniteDimensional KTarget S]
    (B : tau.AlignedBiduality sigma)
    (Hsigma : HasAcyclicNonzeroNonisomorphisms sigma)
    (Htau : HasAcyclicNonzeroNonisomorphisms tau)
    (Tsigma : sigma.FiniteARTranslationData)
    (Ttau : tau.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (hSourceMesh : HasUniformMeshExactnessFor sigma Hsigma Tsigma E)
    (hOppositeMesh : HasUniformMeshExactnessFor tau Htau Ttau
      (oppositeOrderChoice sigma tau B E)) :
    ProfileParametrization sigma
      (BruhatLowerInterval
        (OrderedARWord.orbitGraph sigma Hsigma Tsigma)
        (OrderedARWord.wordFor sigma Hsigma Tsigma E)) := by
  let G := OrderedARWord.orbitGraph sigma Hsigma Tsigma
  let Q := OrderedARWord.wordFor sigma Hsigma Tsigma E
  have hSourceSort : HasLocalClosureCorrespondence sigma G Q
      (OrderedARWord.positionEquivFor sigma Hsigma Tsigma E) :=
    hasLocalClosureCorrespondence_wordFor (KField := KSource)
      sigma Hsigma Tsigma E hSourceMesh
  have hReduced : IsReduced G Q :=
    orderedARWordFor_isReduced_of_meshExactness
      (K := KSource) (R := R) sigma Hsigma Tsigma E
      (hSourceMesh Finset.univ)
  have hOppositeSort : HasLocalClosureCorrespondence tau G
      (relabelledOppositeWord sigma tau B Hsigma Htau Tsigma Ttau E)
      (actualRelabelledOppositePosition
        sigma tau B Hsigma Htau Tsigma Ttau E) := by
    simpa only [G, relabelledOppositeWord,
      actualRelabelledOppositePosition] using
      (directedSortingFor_dualRelabelledLocalClosure
        (KField := KTarget) sigma tau B Hsigma Htau Tsigma Ttau
        (oppositeOrderChoice sigma tau B E) hOppositeMesh)
  exact explicitProfileParametrization sigma tau B Hsigma Htau
    Tsigma Ttau E hReduced hSourceSort hOppositeSort

/-- End-to-end representation-directed endpoint.  Source reducedness,
source local closure, and target relabelled local closure are all derived
internally from the two explicit-order uniform mesh-exactness hypotheses. -/
theorem quotientSubmoduleEquidistribution_of_explicitOrderMeshExactness
    {KSource : Type uR} [Field KSource] [IsAlgClosed KSource]
    [Algebra KSource R] [FiniteDimensional KSource R]
    {KTarget : Type uS} [Field KTarget] [IsAlgClosed KTarget]
    [Algebra KTarget S] [FiniteDimensional KTarget S]
    (B : tau.AlignedBiduality sigma)
    (Hsigma : HasAcyclicNonzeroNonisomorphisms sigma)
    (Htau : HasAcyclicNonzeroNonisomorphisms tau)
    (Tsigma : sigma.FiniteARTranslationData)
    (Ttau : tau.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (hSourceMesh : HasUniformMeshExactnessFor sigma Hsigma Tsigma E)
    (hOppositeMesh : HasUniformMeshExactnessFor tau Htau Ttau
      (oppositeOrderChoice sigma tau B E)) :
    sigma.HasQuotientSubmoduleEquidistribution := by
  let G := OrderedARWord.orbitGraph sigma Hsigma Tsigma
  let Q := OrderedARWord.wordFor sigma Hsigma Tsigma E
  have hReduced : IsReduced G Q :=
    orderedARWordFor_isReduced_of_meshExactness
      (K := KSource) (R := R) sigma Hsigma Tsigma E
      (hSourceMesh Finset.univ)
  let p := explicitProfileParametrization_of_explicitOrderMeshExactness
    (KSource := KSource) (KTarget := KTarget)
    sigma tau B Hsigma Htau Tsigma Ttau E hSourceMesh hOppositeMesh
  letI := bruhatLowerIntervalFintype G Q hReduced
  exact p.quotientSubmoduleEquidistribution

end QuotientSubmoduleEquidistribution.RepresentationDirected.OppositeDirectedProfile
