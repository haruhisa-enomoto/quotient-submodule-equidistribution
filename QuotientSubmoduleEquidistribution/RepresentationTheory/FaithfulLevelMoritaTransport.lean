import QuotientSubmoduleEquidistribution.RepresentationTheory.FaithfulCoreMoritaTransport

/-!
# Morita transport of faithful level counts

An aligned equivalence relabels the quotient and submodule closure systems and
carries their canonical faithful cores onto one another.  Consequently, once
faithfulness is upward closed, it preserves the faithful closed supports at
each fixed cardinality.
-/

noncomputable section

open Set

namespace QuotientSubmoduleEquidistribution.BottomLevels.MinimalFaithfulCore

universe u v

variable {E : Type u} {F : Type v}
  {c : SetClosure E} {d : SetClosure F}
  {FaithfulC : Set E → Prop} {FaithfulD : Set F → Prop}

/-- A relabeling which identifies two minimal faithful cores preserves the
number of faithful closed sets at every cardinality. -/
theorem faithfulLevelCount_eq_of_relabeling
    (h : SetClosure.RelabelingEquiv c d)
    (C : Data c FaithfulC) (D : Data d FaithfulD)
    (hC : Monotone FaithfulC) (hD : Monotone FaithfulD)
    (hcore : h.equiv '' (C.core : Set E) = (D.core : Set F))
    (n : ℕ) :
    faithfulLevelCount c FaithfulC n =
      faithfulLevelCount d FaithfulD n := by
  classical
  unfold faithfulLevelCount
  calc
    (faithfulLevel c FaithfulC n).ncard =
        (h.closedsOrderIso '' faithfulLevel c FaithfulC n).ncard :=
      (Set.ncard_image_of_injective _ h.closedsOrderIso.injective).symm
    _ = (faithfulLevel d FaithfulD n).ncard := by
      congr 1
      ext T
      change T ∈ h.closedsOrderIso.toEquiv ''
          faithfulLevel c FaithfulC n ↔ _
      rw [Set.mem_image_equiv]
      simp only [faithfulLevel, Set.mem_setOf_eq]
      rw [C.faithful_iff_core_subset hC,
        D.faithful_iff_core_subset hD]
      have hT : h.equiv ''
          ((h.closedsOrderIso.symm T : c.Closeds) : Set E) =
          (T : Set F) := by
        rw [← h.coe_closedsOrderIso_apply]
        simp
      have hcard_map :
          (T : Set F).ncard =
            ((h.closedsOrderIso.symm T : c.Closeds) : Set E).ncard := by
        rw [← hT]
        exact Set.ncard_image_of_injective _ h.equiv.injective
      constructor
      · rintro ⟨hfaithful, hcard⟩
        constructor
        · rw [← hcore, ← hT]
          exact Set.image_mono hfaithful
        · exact hcard_map.trans hcard
      · rintro ⟨hfaithful, hcard⟩
        constructor
        · rw [← Set.image_subset_image_iff h.equiv.injective]
          calc
            h.equiv '' (C.core : Set E) =
                (D.core : Set F) := hcore
            _ ⊆ (T : Set F) := hfaithful
            _ = h.equiv ''
                ((h.closedsOrderIso.symm T : c.Closeds) : Set E) :=
              hT.symm
        · exact hcard_map.symm.trans hcard

end QuotientSubmoduleEquidistribution.BottomLevels.MinimalFaithfulCore

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton.AlignedEquivalence

universe uR uS vR vS

open QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {S : Type uS} [Ring S] [IsNoetherianRing S]
  {iota : Type vR} {kappa : Type vS}
  (sigma : IndecomposableSkeleton.{uR, vR, uR} R iota)
  (tau : IndecomposableSkeleton.{uS, vS, uS} S kappa)

/-- Aligned equivalence preserves every quotient-side faithful level count
when the two faithfulness predicates have the canonical normal form. -/
theorem quotientFaithfulLevelCount_eq
    {FaithfulQsigma FaithfulSsigma : Set iota → Prop}
    {FaithfulQtau FaithfulStau : Set kappa → Prop}
    (E : AlignedEquivalence sigma tau)
    (Nsigma : ClosedFaithfulNormalForm sigma
      FaithfulQsigma FaithfulSsigma)
    (Ntau : ClosedFaithfulNormalForm tau FaithfulQtau FaithfulStau)
    (hSigma : Monotone FaithfulQsigma)
    (hTau : Monotone FaithfulQtau)
    (n : ℕ) :
    BottomLevels.MinimalFaithfulCore.faithfulLevelCount
        sigma.qClosure FaithfulQsigma n =
      BottomLevels.MinimalFaithfulCore.faithfulLevelCount
        tau.qClosure FaithfulQtau n := by
  apply
    BottomLevels.MinimalFaithfulCore.faithfulLevelCount_eq_of_relabeling
      (qClosureRelabeling sigma tau E)
      (quotientCoreData sigma Nsigma) (quotientCoreData tau Ntau)
      hSigma hTau
  change E.labelEquiv ''
      ((quotientCoreData sigma Nsigma).core : Set iota) =
    ((quotientCoreData tau Ntau).core : Set kappa)
  simpa only [quotientCoreData_core] using
    image_quotientCore sigma tau E

/-- Aligned equivalence preserves every submodule-side faithful level count
when the two faithfulness predicates have the canonical normal form. -/
theorem submoduleFaithfulLevelCount_eq
    {FaithfulQsigma FaithfulSsigma : Set iota → Prop}
    {FaithfulQtau FaithfulStau : Set kappa → Prop}
    (E : AlignedEquivalence sigma tau)
    (Nsigma : ClosedFaithfulNormalForm sigma
      FaithfulQsigma FaithfulSsigma)
    (Ntau : ClosedFaithfulNormalForm tau FaithfulQtau FaithfulStau)
    (hSigma : Monotone FaithfulSsigma)
    (hTau : Monotone FaithfulStau)
    (n : ℕ) :
    BottomLevels.MinimalFaithfulCore.faithfulLevelCount
        sigma.sClosure FaithfulSsigma n =
      BottomLevels.MinimalFaithfulCore.faithfulLevelCount
        tau.sClosure FaithfulStau n := by
  apply
    BottomLevels.MinimalFaithfulCore.faithfulLevelCount_eq_of_relabeling
      (sClosureRelabeling sigma tau E)
      (submoduleCoreData sigma Nsigma) (submoduleCoreData tau Ntau)
      hSigma hTau
  change E.labelEquiv ''
      ((submoduleCoreData sigma Nsigma).core : Set iota) =
    ((submoduleCoreData tau Ntau).core : Set kappa)
  simpa only [submoduleCoreData_core] using
    image_submoduleCore sigma tau E

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton.AlignedEquivalence
