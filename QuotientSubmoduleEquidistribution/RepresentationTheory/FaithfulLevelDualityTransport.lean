import QuotientSubmoduleEquidistribution.RepresentationTheory.DualityConsequences
import QuotientSubmoduleEquidistribution.RepresentationTheory.FaithfulLevelMoritaTransport

/-!
# Duality transport of faithful level counts

An aligned biduality exchanges quotient and submodule closure.  It also
exchanges the injective and projective boundaries which generate the two
minimal faithful cores.  Consequently it preserves faithful level counts,
with the quotient and submodule sides interchanged.
-/

noncomputable section

open Set
open CategoryTheory

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton.AlignedBiduality

universe uR uS vR vS

open QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {S : Type uS} [Ring S] [IsNoetherianRing S]
  {iota : Type vR} {kappa : Type vS}
  (sigma : IndecomposableSkeleton.{uR, vR, uR} R iota)
  (tau : IndecomposableSkeleton.{uS, vS, uS} S kappa)
  (D : AlignedBiduality sigma tau)

/-- The forward label equivalence carries source injectives to target
projectives. -/
theorem image_injectiveLabels_eq_projectiveLabels :
    D.forward.labelEquiv '' injectiveLabels sigma =
      projectiveLabels tau := by
  ext j
  rw [Set.mem_image_equiv]
  change Injective (sigma.obj (D.forward.labelEquiv.symm j)) ↔
    Projective (tau.obj j)
  simpa using
    (D.forward.injective_iff_projective_image
      sigma tau (D.forward.labelEquiv.symm j))

/-- The forward label equivalence carries source projectives to target
injectives. -/
theorem image_projectiveLabels_eq_injectiveLabels :
    D.forward.labelEquiv '' projectiveLabels sigma =
      injectiveLabels tau := by
  have hboundary : ∀ i,
      Projective (sigma.obj i) ↔
        Injective (tau.obj (D.forward.labelEquiv i)) := by
    intro i
    have h :=
      D.backward.injective_iff_projective_image
        tau sigma (D.forward.labelEquiv i)
    rw [D.backward_label] at h
    simpa using h.symm
  ext j
  rw [Set.mem_image_equiv]
  change Projective (sigma.obj (D.forward.labelEquiv.symm j)) ↔
    Injective (tau.obj j)
  simpa using hboundary (D.forward.labelEquiv.symm j)

/-- Biduality carries the quotient faithful core to the target submodule
faithful core. -/
theorem image_quotientCore_eq_submoduleCore :
    D.forward.labelEquiv '' (quotientCore sigma : Set iota) =
      (submoduleCore tau : Set kappa) := by
  change D.forward.labelEquiv '' sigma.qClosure (injectiveLabels sigma) =
    tau.sClosure (projectiveLabels tau)
  rw [D.image_qClosure_eq_sClosure,
    image_injectiveLabels_eq_projectiveLabels sigma tau D]

/-- Biduality carries the submodule faithful core to the target quotient
faithful core. -/
theorem image_submoduleCore_eq_quotientCore :
    D.forward.labelEquiv '' (submoduleCore sigma : Set iota) =
      (quotientCore tau : Set kappa) := by
  change D.forward.labelEquiv '' sigma.sClosure (projectiveLabels sigma) =
    tau.qClosure (injectiveLabels tau)
  rw [D.image_sClosure_eq_qClosure,
    image_projectiveLabels_eq_injectiveLabels sigma tau D]

/-- Quotient-core cardinality on the source equals submodule-core
cardinality on the target. -/
theorem quotientCore_ncard_eq_submoduleCore
    (D : AlignedBiduality sigma tau) :
    (quotientCore sigma : Set iota).ncard =
      (submoduleCore tau : Set kappa).ncard := by
  calc
    (quotientCore sigma : Set iota).ncard =
        (D.forward.labelEquiv ''
          (quotientCore sigma : Set iota)).ncard :=
      (Set.ncard_image_of_injective _
        D.forward.labelEquiv.injective).symm
    _ = (submoduleCore tau : Set kappa).ncard := by
      rw [image_quotientCore_eq_submoduleCore sigma tau D]

/-- Submodule-core cardinality on the source equals quotient-core
cardinality on the target. -/
theorem submoduleCore_ncard_eq_quotientCore
    (D : AlignedBiduality sigma tau) :
    (submoduleCore sigma : Set iota).ncard =
      (quotientCore tau : Set kappa).ncard := by
  calc
    (submoduleCore sigma : Set iota).ncard =
        (D.forward.labelEquiv ''
          (submoduleCore sigma : Set iota)).ncard :=
      (Set.ncard_image_of_injective _
        D.forward.labelEquiv.injective).symm
    _ = (quotientCore tau : Set kappa).ncard := by
      rw [image_submoduleCore_eq_quotientCore sigma tau D]

/-- Biduality preserves every faithful level count while exchanging quotient
closure on the source with submodule closure on the target. -/
theorem quotientFaithfulLevelCount_eq_submodule
    {FaithfulQsigma FaithfulSsigma : Set iota → Prop}
    {FaithfulQtau FaithfulStau : Set kappa → Prop}
    (Nsigma : ClosedFaithfulNormalForm sigma
      FaithfulQsigma FaithfulSsigma)
    (Ntau : ClosedFaithfulNormalForm tau FaithfulQtau FaithfulStau)
    (D : AlignedBiduality sigma tau)
    (hSigma : Monotone FaithfulQsigma)
    (hTau : Monotone FaithfulStau)
    (n : ℕ) :
    BottomLevels.MinimalFaithfulCore.faithfulLevelCount
        sigma.qClosure FaithfulQsigma n =
      BottomLevels.MinimalFaithfulCore.faithfulLevelCount
        tau.sClosure FaithfulStau n := by
  apply
    BottomLevels.MinimalFaithfulCore.faithfulLevelCount_eq_of_relabeling
      (qToSClosureRelabeling sigma tau D)
      (quotientCoreData sigma Nsigma) (submoduleCoreData tau Ntau)
      hSigma hTau
  change D.forward.labelEquiv ''
      ((quotientCoreData sigma Nsigma).core : Set iota) =
    ((submoduleCoreData tau Ntau).core : Set kappa)
  simpa only [quotientCoreData_core, submoduleCoreData_core] using
    image_quotientCore_eq_submoduleCore sigma tau D

/-- Biduality preserves every faithful level count while exchanging
submodule closure on the source with quotient closure on the target. -/
theorem submoduleFaithfulLevelCount_eq_quotient
    {FaithfulQsigma FaithfulSsigma : Set iota → Prop}
    {FaithfulQtau FaithfulStau : Set kappa → Prop}
    (Nsigma : ClosedFaithfulNormalForm sigma
      FaithfulQsigma FaithfulSsigma)
    (Ntau : ClosedFaithfulNormalForm tau FaithfulQtau FaithfulStau)
    (D : AlignedBiduality sigma tau)
    (hSigma : Monotone FaithfulSsigma)
    (hTau : Monotone FaithfulQtau)
    (n : ℕ) :
    BottomLevels.MinimalFaithfulCore.faithfulLevelCount
        sigma.sClosure FaithfulSsigma n =
      BottomLevels.MinimalFaithfulCore.faithfulLevelCount
        tau.qClosure FaithfulQtau n := by
  apply
    BottomLevels.MinimalFaithfulCore.faithfulLevelCount_eq_of_relabeling
      (sToQClosureRelabeling sigma tau D)
      (submoduleCoreData sigma Nsigma) (quotientCoreData tau Ntau)
      hSigma hTau
  change D.forward.labelEquiv ''
      ((submoduleCoreData sigma Nsigma).core : Set iota) =
    ((quotientCoreData tau Ntau).core : Set kappa)
  simpa only [submoduleCoreData_core, quotientCoreData_core] using
    image_submoduleCore_eq_quotientCore sigma tau D

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton.AlignedBiduality
