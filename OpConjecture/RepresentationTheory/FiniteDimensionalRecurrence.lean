import OpConjecture.RepresentationTheory.CanonicalAnnihilatorFactorFamily
import OpConjecture.RepresentationTheory.QuotientDimensionDrop
import OpConjecture.RepresentationTheory.FaithfulCoreNormalForm
import OpConjecture.Combinatorics.BottomThreeFourFaithfulRecurrence

/-!
# Finite-dimensional algebra adapter for the repaired bottom recurrence

This file bundles a finite-dimensional algebra together with a finite complete
indecomposable skeleton.  Its proper-factor operation is the canonical
quotient skeleton, so the abstract simultaneous recurrence can use the actual
annihilator fibers and the strict dimension measure.
-/

noncomputable section

open Set

namespace OpConjecture.BottomLevels.FiniteDimensionalRecurrence

open OpConjecture.AnnihilatorInflation
open OpConjecture.AnnihilatorInflation.Skeleton
open OpConjecture.IndecomposableSkeleton.FaithfulCore
open OpConjecture.QuotientSkeletonAlignment
open BottomThreeFourFaithfulRecurrence

universe u

variable (K : Type u) [Field K]

/-- A finite-dimensional algebra with a finite complete indecomposable
skeleton, including the two Noetherian instances used by the module API. -/
structure AlgebraNode where
  Carrier : Type u
  [ring : Ring Carrier]
  [algebra : Algebra K Carrier]
  [finiteDimensional : FiniteDimensional K Carrier]
  [noetherian : IsNoetherianRing Carrier]
  [noetherianOpposite : IsNoetherianRing Carrierᵐᵒᵖ]
  Index : Type (u + 1)
  [finiteIndex : Finite Index]
  skeleton : IndecomposableSkeleton.{u, u + 1, u} Carrier Index

namespace AlgebraNode

instance (B : AlgebraNode K) : Ring B.Carrier := B.ring
instance (B : AlgebraNode K) : Algebra K B.Carrier := B.algebra
instance (B : AlgebraNode K) : FiniteDimensional K B.Carrier :=
  B.finiteDimensional
instance (B : AlgebraNode K) : IsNoetherianRing B.Carrier := B.noetherian
instance (B : AlgebraNode K) : IsNoetherianRing B.Carrierᵐᵒᵖ :=
  B.noetherianOpposite
instance (B : AlgebraNode K) : Finite B.Index := B.finiteIndex

/-- Ground-field dimension is the well-founded recurrence measure. -/
abbrev measure (B : AlgebraNode K) : ℕ :=
  Module.finrank K B.Carrier

/-- The actual proper annihilators realized by either closure lattice. -/
abbrev ProperFactor (B : AlgebraNode K) :=
  ProperRealizedAnnihilator B.skeleton

/-- The canonical quotient node associated to a proper realized
annihilator. -/
noncomputable def factor (B : AlgebraNode K) (I : ProperFactor K B) :
    AlgebraNode K := by
  letI factorNoeth : IsNoetherianRing (Quotient.Factor I.1.1) :=
    factorNoetherian K B.Carrier I.1.1
  letI factorArtinianOpposite :
      IsArtinianRing (Quotient.Factor I.1.1)ᵐᵒᵖ :=
    IsArtinianRing.of_finite K _
  letI factorNoethOpposite :
      IsNoetherianRing (Quotient.Factor I.1.1)ᵐᵒᵖ := inferInstance
  exact
    { Carrier := Quotient.Factor I.1.1
      ring := inferInstance
      algebra := inferInstance
      finiteDimensional := inferInstance
      noetherian := factorNoeth
      noetherianOpposite := factorNoethOpposite
      Index := FactorIndex B.Carrier I.1.1
      finiteIndex :=
        Finite.of_injective
          (inflationLabelEmbedding B.skeleton I.1.1
            (canonicalFactorSkeleton K B.Carrier I.1.1))
          (inflationLabel_injective B.skeleton I.1.1
            (canonicalFactorSkeleton K B.Carrier I.1.1))
      skeleton := canonicalFactorSkeleton K B.Carrier I.1.1 }

/-- Proper factors strictly lower the node measure. -/
theorem factor_measure_lt (B : AlgebraNode K) (I : ProperFactor K B) :
    measure K (factor K B I) < measure K B :=
  by
    change Module.finrank K (Quotient.Factor I.1.1) <
      Module.finrank K B.Carrier
    exact properRealized_factor_finrank_lt K B.Carrier B.skeleton I

/-- Quotient closure of a node's chosen skeleton. -/
abbrev qClosure (B : AlgebraNode K) := B.skeleton.qClosure

/-- Submodule closure of a node's chosen skeleton. -/
abbrev sClosure (B : AlgebraNode K) := B.skeleton.sClosure

/-- Faithfulness of a support in a node. -/
abbrev IsFaithfulSupport (B : AlgebraNode K) :=
  AnnihilatorInflation.IsFaithfulSupport B.skeleton.obj

/-- The actual quotient-side minimal faithful core. -/
noncomputable def quotientCoreData (B : AlgebraNode K) :=
  concreteQuotientCoreData (K := K) B.skeleton

/-- The actual submodule-side minimal faithful core. -/
noncomputable def submoduleCoreData (B : AlgebraNode K) :=
  concreteSubmoduleCoreData (K := K) B.skeleton

/-- Ringel's core-cardinality proposition gives equality of the two actual
minimal-core sizes. -/
theorem core_ncard_eq_of_ringel (B : AlgebraNode K)
    (hRingel : RingelCoreCardinality B.skeleton) :
    ((quotientCoreData K B).core : Set B.Index).ncard =
      ((submoduleCoreData K B).core : Set B.Index).ncard :=
  OpConjecture.IndecomposableSkeleton.FaithfulCore.core_ncard_eq_of_ringel
    B.skeleton (closedFaithfulNormalForm (K := K) B.skeleton) hRingel

/-- The exact canonical quotient-side recurrence in node notation. -/
theorem qRecurrence (B : AlgebraNode K) (n : ℕ) :
    (qClosure K B).levelCount n =
      MinimalFaithfulCore.faithfulLevelCount
          (qClosure K B) (IsFaithfulSupport K B) n +
        ∑ I : ProperFactor K B,
          MinimalFaithfulCore.faithfulLevelCount
            (qClosure K (factor K B I))
            (IsFaithfulSupport K (factor K B I)) n := by
  convert
    canonical_qLevelCount_eq_faithful_add_sum_factorFaithful
      K B.Carrier B.skeleton n using 1
  · classical
    simp only [qClosure, IsFaithfulSupport, factor,
      canonicalFactorQClosure, canonicalFactorObj,
      canonicalFactorSkeleton]
    congr 1

/-- The exact canonical submodule-side recurrence in node notation. -/
theorem sRecurrence (B : AlgebraNode K) (n : ℕ) :
    (sClosure K B).levelCount n =
      MinimalFaithfulCore.faithfulLevelCount
          (sClosure K B) (IsFaithfulSupport K B) n +
        ∑ I : ProperFactor K B,
          MinimalFaithfulCore.faithfulLevelCount
            (sClosure K (factor K B I))
            (IsFaithfulSupport K (factor K B I)) n := by
  convert
    canonical_sLevelCount_eq_faithful_add_sum_factorFaithful
      K B.Carrier B.skeleton n using 1
  · classical
    simp only [sClosure, IsFaithfulSupport, factor,
      canonicalFactorSClosure, canonicalFactorObj,
      canonicalFactorSkeleton]
    congr 1

/-- The faithful quotient-side count of a node at one level. -/
abbrev faithfulQCount (B : AlgebraNode K) (n : ℕ) : ℕ :=
  MinimalFaithfulCore.faithfulLevelCount
    (qClosure K B) (IsFaithfulSupport K B) n

/-- The faithful submodule-side count of a node at one level. -/
abbrev faithfulSCount (B : AlgebraNode K) (n : ℕ) : ℕ :=
  MinimalFaithfulCore.faithfulLevelCount
    (sClosure K B) (IsFaithfulSupport K B) n

/-- The only inputs not supplied canonically by finite-dimensional quotient
inflation and Ringel core cardinality.  `smallCore` is the connected
hereditary/Nakayama/lollipop branch; `disconnected` is block-product
transport. -/
structure RemainingData (Connected : AlgebraNode K → Prop) where
  ringel : ∀ B : AlgebraNode K, RingelCoreCardinality B.skeleton
  smallCore :
    ∀ (B : AlgebraNode K) (n : ℕ), n = 3 ∨ n = 4 → Connected B →
      ((quotientCoreData K B).core : Set B.Index).ncard < n →
      (faithfulQCount K B n = faithfulSCount K B n) ∨
        (qClosure K B).levelCount n = (sClosure K B).levelCount n
  disconnected :
    ∀ B : AlgebraNode K, ¬ Connected B →
      (∀ B' : AlgebraNode K, measure K B' < measure K B →
        (qClosure K B').levelCount 3 =
            (sClosure K B').levelCount 3 ∧
          (qClosure K B').levelCount 4 =
            (sClosure K B').levelCount 4) →
      (qClosure K B).levelCount 3 =
          (sClosure K B).levelCount 3 ∧
        (qClosure K B).levelCount 4 =
          (sClosure K B).levelCount 4

/-- The concrete finite-dimensional data instantiate every field of the
abstract simultaneous recurrence. -/
theorem threeFourCoreRecurrenceData
    (Connected : AlgebraNode K → Prop)
    (D : RemainingData K Connected) :
    ThreeFourCoreRecurrenceData
      (fun B : AlgebraNode K ↦ B.Index)
      (qClosure K) (sClosure K)
      (IsFaithfulSupport K) (IsFaithfulSupport K)
      (quotientCoreData K) (submoduleCoreData K)
      (measure K) (ProperFactor K) (factor K) Connected where
  factorSmaller := factor_measure_lt K
  coreCard := fun B ↦ core_ncard_eq_of_ringel K B (D.ringel B)
  recurrenceQ := fun B n _ ↦ qRecurrence K B n
  recurrenceS := fun B n _ ↦ sRecurrence K B n
  smallCore := D.smallCore
  disconnected := D.disconnected

/-- Final repaired coefficient endpoint for every node in the family.  The
remaining hypotheses are exactly Ringel's stable duality, the connected
small-core cases, and disconnected block transport. -/
theorem levelCount_three_and_four_eq
    (Connected : AlgebraNode K → Prop)
    (D : RemainingData K Connected)
    (B : AlgebraNode K) :
    (qClosure K B).levelCount 3 = (sClosure K B).levelCount 3 ∧
      (qClosure K B).levelCount 4 = (sClosure K B).levelCount 4 :=
  BottomThreeFourFaithfulRecurrence.levelCount_three_and_four_eq
    (fun C : AlgebraNode K ↦ C.Index)
    (qClosure K) (sClosure K)
    (IsFaithfulSupport K) (IsFaithfulSupport K)
    (quotientCoreData K) (submoduleCoreData K)
    (measure K) (ProperFactor K) (factor K) Connected
    (threeFourCoreRecurrenceData K Connected D) B

end AlgebraNode

end OpConjecture.BottomLevels.FiniteDimensionalRecurrence
