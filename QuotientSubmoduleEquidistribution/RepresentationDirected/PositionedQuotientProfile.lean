import QuotientSubmoduleEquidistribution.RepresentationDirected.ARWordDirectedSorting
import QuotientSubmoduleEquidistribution.RepresentationDirected.FixedWordProfile
import QuotientSubmoduleEquidistribution.RepresentationDirected.SimpleGraphBruhat

/-!
# Quotient profiles from a positioned word

This file isolates the part of the representation-directed quotient profile
which no longer depends on Auslander--Reiten theory.  Given a finite word, an
equivalence from its positions to indecomposable labels, and the exact
correspondence between locally reduced position sets and quotient-closed
complements, it constructs the fixed-word and principal-Bruhat-interval
profiles with their literal supports and cardinalities.

The adapter is deliberately independent of how the word was ordered.  It can
therefore be instantiated both by the default directed order and by the
explicit reverse order transported across opposite duality.
-/

set_option autoImplicit false

noncomputable section

namespace QuotientSubmoduleEquidistribution.RepresentationDirected.DirectedQuotientProfile.Positioned

open Polynomial
open QuotientSubmoduleEquidistribution.RepresentationDirected.FixedWord
open QuotientSubmoduleEquidistribution.RepresentationDirected
open QuotientSubmoduleEquidistribution.RepresentationDirected.FixedWordProfile
open QuotientSubmoduleEquidistribution.RepresentationDirected.SimpleGraphBruhat
open QuotientSubmoduleEquidistribution.RepresentationDirected.SimpleGraphCoxeter

universe uR uI uL

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
variable {I : Type uI} [Fintype I]
variable (sigma : IndecomposableSkeleton.{uR, uI, uR} R I)
variable {L : Type uL} [Fintype L]

/-- Transport omitted word positions through an arbitrary position
equivalence. -/
def omittedLabelsFor {Q : List L} (position : Fin Q.length ≃ I)
    (D : Finset (Fin Q.length)) : Finset I := by
  classical
  exact D.map position.toEmbedding

omit [Fintype I] [Fintype L] in
@[simp]
theorem mem_omittedLabelsFor_iff {Q : List L}
    (position : Fin Q.length ≃ I)
    (D : Finset (Fin Q.length)) (x : Fin Q.length) :
    position x ∈ omittedLabelsFor position D ↔ x ∈ D := by
  classical
  simp [omittedLabelsFor]

omit [Fintype I] [Fintype L] in
@[simp]
theorem card_omittedLabelsFor {Q : List L}
    (position : Fin Q.length ≃ I)
    (D : Finset (Fin Q.length)) :
    (omittedLabelsFor position D).card = D.card := by
  classical
  simp [omittedLabelsFor]

/-- The exact output of directed sorting consumed by the profile layer. -/
def HasLocalClosureCorrespondence
    (G : SimpleGraph L) (Q : List L)
    (position : Fin Q.length ≃ I) : Prop :=
  ∀ D : Finset (Fin Q.length),
    SortingExchange.AreAllLocalSubwordsReduced (system G) Q D ↔
      sigma.qClosure.IsClosed
        {i | i ∉ omittedLabelsFor position D}

variable {G : SimpleGraph L} {Q : List L}
variable {position : Fin Q.length ≃ I}

/-- A locally reduced position set determines the complementary
quotient-closed support. -/
def locallyReducedToQClosedFor
    (hSort : HasLocalClosureCorrespondence sigma G Q position) :
    LocallyReducedPositions G Q → sigma.qClosure.Closeds :=
  fun d ↦
    ⟨{i | i ∉ omittedLabelsFor position d.1},
      (hSort d.1).1 d.2⟩

omit [Fintype I] [Fintype L] in
theorem locallyReducedToQClosedFor_injective
    (hSort : HasLocalClosureCorrespondence sigma G Q position) :
    Function.Injective (locallyReducedToQClosedFor sigma hSort) := by
  intro d e hde
  apply Subtype.ext
  ext x
  have hsets := congrArg
    (fun C : sigma.qClosure.Closeds ↦ (C : Set I)) hde
  have hmem := Set.ext_iff.mp hsets (position x)
  change (position x ∉ omittedLabelsFor position d.1) ↔
    (position x ∉ omittedLabelsFor position e.1) at hmem
  simp only [mem_omittedLabelsFor_iff] at hmem
  tauto

omit [Fintype I] [Fintype L] in
theorem locallyReducedToQClosedFor_surjective
    (hSort : HasLocalClosureCorrespondence sigma G Q position) :
    Function.Surjective (locallyReducedToQClosedFor sigma hSort) := by
  classical
  intro C
  let D : Finset (Fin Q.length) :=
    Finset.univ.filter fun x ↦ position x ∉ (C : Set I)
  have hSupport : {i | i ∉ omittedLabelsFor position D} =
      (C : Set I) := by
    ext i
    obtain ⟨x, rfl⟩ := position.surjective i
    simp [D]
  have hLocal : SortingExchange.AreAllLocalSubwordsReduced
      (system G) Q D := by
    apply (hSort D).2
    rw [hSupport]
    exact C.2
  let d : LocallyReducedPositions G Q := ⟨D, hLocal⟩
  refine ⟨d, ?_⟩
  apply Subtype.ext
  exact hSupport

/-- Generic quotient-profile equivalence downstream of directed sorting. -/
def locallyReducedPositionsEquivQClosedFor
    (hSort : HasLocalClosureCorrespondence sigma G Q position) :
    LocallyReducedPositions G Q ≃ sigma.qClosure.Closeds :=
  Equiv.ofBijective (locallyReducedToQClosedFor sigma hSort)
    ⟨locallyReducedToQClosedFor_injective sigma hSort,
      locallyReducedToQClosedFor_surjective sigma hSort⟩

omit [Fintype I] [Fintype L] in
@[simp]
theorem support_locallyReducedPositionsEquivQClosedFor
    (hSort : HasLocalClosureCorrespondence sigma G Q position)
    (d : LocallyReducedPositions G Q) :
    (((locallyReducedPositionsEquivQClosedFor sigma hSort d :
      sigma.qClosure.Closeds) : Set I)) =
      {i | i ∉ omittedLabelsFor position d.1} := rfl

/-- Fixed-word elements inherit the same quotient-closed parametrization. -/
def fixedWordElementEquivQClosedFor
    (hSort : HasLocalClosureCorrespondence sigma G Q position) :
    FixedWordSubwords.FixedWordElement (system G) Q ≃
      sigma.qClosure.Closeds :=
  (fixedWordElementEquivLocallyReducedPositions G Q).trans
    (locallyReducedPositionsEquivQClosedFor sigma hSort)

omit [Fintype I] in
@[simp]
theorem support_fixedWordElementEquivQClosedFor
    (hSort : HasLocalClosureCorrespondence sigma G Q position)
    (u : FixedWordSubwords.FixedWordElement (system G) Q) :
    (((fixedWordElementEquivQClosedFor sigma hSort u :
      sigma.qClosure.Closeds) : Set I)) =
      {i | i ∉ omittedLabelsFor position
        (lexFirstLocalPositions G Q u).1} := rfl

@[simp]
theorem ncard_fixedWordElementEquivQClosedFor
    (hSort : HasLocalClosureCorrespondence sigma G Q position)
    (u : FixedWordSubwords.FixedWordElement (system G) Q) :
    (((fixedWordElementEquivQClosedFor sigma hSort u :
      sigma.qClosure.Closeds) : Set I).ncard) =
      Q.length - (system G).length u.1 := by
  have hCard : Nat.card I = Q.length := by
    rw [Nat.card_eq_fintype_card]
    symm
    simpa only [Fintype.card_fin] using Fintype.card_congr position
  change ((↑(omittedLabelsFor position
    (lexFirstLocalPositions G Q u).1) : Set I)ᶜ).ncard = _
  rw [Set.ncard_compl, Set.ncard_coe_finset,
    card_omittedLabelsFor position,
    card_lexFirstLocalPositions, hCard]

/-- Reverse-length fixed-word profile obtained from the local closure
correspondence. -/
theorem quotientLevelPolynomial_eq_fixedWordReverseLengthFor
    (hSort : HasLocalClosureCorrespondence sigma G Q position) :
    sigma.qClosure.levelPolynomial =
      ∑ u : FixedWordSubwords.FixedWordElement (system G) Q,
        X ^ (Q.length - (system G).length u.1) := by
  exact QuotientSubmoduleEquidistribution.SetClosure.levelPolynomial_eq_sum_stat
    sigma.qClosure
    (fixedWordElementEquivQClosedFor sigma hSort)
    (fun u ↦ Q.length - (system G).length u.1)
    (ncard_fixedWordElementEquivQClosedFor sigma hSort)

/-! ## Principal Bruhat interval -/

/-- For a reduced ambient word, the fixed-word classification is
equivalently a classification by its principal lower Bruhat interval. -/
def bruhatLowerIntervalEquivQClosedFor
    (hSort : HasLocalClosureCorrespondence sigma G Q position)
    (hReduced : IsReduced G Q) :
    BruhatLowerInterval G Q ≃ sigma.qClosure.Closeds :=
  (fixedWordElementEquivBruhatLowerInterval G Q hReduced).symm.trans
    (fixedWordElementEquivQClosedFor sigma hSort)

/-- Skeleton labels at the lex-first reduced positions representing a
Bruhat-interval element. -/
def bruhatLexFirstOmittedLabelsFor
    (position : Fin Q.length ≃ I)
    (hReduced : IsReduced G Q)
    (u : BruhatLowerInterval G Q) : Finset I :=
  omittedLabelsFor position (bruhatLexFirstPositions G Q hReduced u)

omit [Fintype I] in
@[simp]
theorem support_bruhatLowerIntervalEquivQClosedFor
    (hSort : HasLocalClosureCorrespondence sigma G Q position)
    (hReduced : IsReduced G Q)
    (u : BruhatLowerInterval G Q) :
    (((bruhatLowerIntervalEquivQClosedFor sigma hSort hReduced u :
      sigma.qClosure.Closeds) : Set I)) =
      (↑(bruhatLexFirstOmittedLabelsFor position hReduced u) : Set I)ᶜ := by
  rfl

omit [Fintype I] in
@[simp]
theorem card_bruhatLexFirstOmittedLabelsFor
    (position : Fin Q.length ≃ I)
    (hReduced : IsReduced G Q)
    (u : BruhatLowerInterval G Q) :
    (bruhatLexFirstOmittedLabelsFor position hReduced u).card =
      (system G).length u.1 := by
  unfold bruhatLexFirstOmittedLabelsFor
  rw [card_omittedLabelsFor, card_bruhatLexFirstPositions]

@[simp]
theorem ncard_bruhatLowerIntervalEquivQClosedFor
    (hSort : HasLocalClosureCorrespondence sigma G Q position)
    (hReduced : IsReduced G Q)
    (u : BruhatLowerInterval G Q) :
    (((bruhatLowerIntervalEquivQClosedFor sigma hSort hReduced u :
      sigma.qClosure.Closeds) : Set I).ncard) =
      Q.length - (system G).length u.1 := by
  have hCard : Nat.card I = Q.length := by
    rw [Nat.card_eq_fintype_card]
    symm
    simpa only [Fintype.card_fin] using Fintype.card_congr position
  rw [support_bruhatLowerIntervalEquivQClosedFor,
    Set.ncard_compl, Set.ncard_coe_finset,
    card_bruhatLexFirstOmittedLabelsFor, hCard]

/-- Paper-facing quotient profile for an arbitrary positioned reduced word. -/
theorem quotientLevelPolynomial_eq_bruhatLowerIntervalFor
    (hSort : HasLocalClosureCorrespondence sigma G Q position)
    (hReduced : IsReduced G Q) :
    sigma.qClosure.levelPolynomial =
      bruhatLowerIntervalReverseLengthPolynomial G Q hReduced := by
  letI := bruhatLowerIntervalFintype G Q hReduced
  unfold bruhatLowerIntervalReverseLengthPolynomial
  exact QuotientSubmoduleEquidistribution.SetClosure.levelPolynomial_eq_sum_stat
    sigma.qClosure
    (bruhatLowerIntervalEquivQClosedFor sigma hSort hReduced)
    (fun u ↦ Q.length - (system G).length u.1)
    (ncard_bruhatLowerIntervalEquivQClosedFor sigma hSort hReduced)

end QuotientSubmoduleEquidistribution.RepresentationDirected.DirectedQuotientProfile.Positioned
