import QuotientSubmoduleEquidistribution.RepresentationTheory.RingelEtaCoreCardinality

/-!
# Full Ringel core equivalence

The stable Ringel equivalence pairs the nonprojective/noninjective parts of
the torsionless and cotorsionless cores.  The Nakayama equivalence pairs their
projective/injective boundaries.  This file glues those two equivalences into
the actual core bijection, without assuming representation-finiteness.
-/

noncomputable section

open Set CategoryTheory

namespace QuotientSubmoduleEquidistribution.RingelStable

universe u v

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  [IsNoetherianRing Rᵐᵒᵖ]
  {iota : Type v}
  (sigma : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, v, u} R iota)

open QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore
open FaithfulCoreAdapter

/-- Ringel's forward map, using the Nakayama boundary equivalence on
projectives and the stable equivalence off that boundary. -/
def coreForwardOfEtaStableData
    (boundary :
      {i // i ∈ projectiveSet sigma} ≃
        {i // i ∈ injectiveSet sigma})
    (eta : RingelEtaStableData sigma)
    (x : {i // i ∈ (submoduleCore sigma : Set iota)}) :
    {i // i ∈ (quotientCore sigma : Set iota)} := by
  classical
  by_cases hx : x.1 ∈ projectiveSet sigma
  · let y := boundary ⟨x.1, hx⟩
    exact ⟨y.1, injectiveSet_subset_quotientCore sigma y.2⟩
  · let y := eta.nonboundaryEquiv ⟨x.1, x.2, hx⟩
    exact ⟨y.1, y.2.1⟩

/-- The inverse glued core map. -/
def coreBackwardOfEtaStableData
    (boundary :
      {i // i ∈ projectiveSet sigma} ≃
        {i // i ∈ injectiveSet sigma})
    (eta : RingelEtaStableData sigma)
    (y : {i // i ∈ (quotientCore sigma : Set iota)}) :
    {i // i ∈ (submoduleCore sigma : Set iota)} := by
  classical
  by_cases hy : y.1 ∈ injectiveSet sigma
  · let x := boundary.symm ⟨y.1, hy⟩
    exact ⟨x.1, projectiveSet_subset_submoduleCore sigma x.2⟩
  · let x := eta.nonboundaryEquiv.symm ⟨y.1, y.2, hy⟩
    exact ⟨x.1, x.2.1⟩

omit [IsNoetherianRing Rᵐᵒᵖ] in
theorem coreForwardOfEtaStableData_of_projective
    (boundary :
      {i // i ∈ projectiveSet sigma} ≃
        {i // i ∈ injectiveSet sigma})
    (eta : RingelEtaStableData sigma)
    (x : {i // i ∈ (submoduleCore sigma : Set iota)})
    (hx : x.1 ∈ projectiveSet sigma) :
    coreForwardOfEtaStableData sigma boundary eta x =
      ⟨(boundary ⟨x.1, hx⟩).1,
        injectiveSet_subset_quotientCore sigma
          (boundary ⟨x.1, hx⟩).2⟩ := by
  apply Subtype.ext
  simp [coreForwardOfEtaStableData, hx]

omit [IsNoetherianRing Rᵐᵒᵖ] in
theorem coreForwardOfEtaStableData_of_nonprojective
    (boundary :
      {i // i ∈ projectiveSet sigma} ≃
        {i // i ∈ injectiveSet sigma})
    (eta : RingelEtaStableData sigma)
    (x : {i // i ∈ (submoduleCore sigma : Set iota)})
    (hx : x.1 ∉ projectiveSet sigma) :
    coreForwardOfEtaStableData sigma boundary eta x =
      ⟨(eta.nonboundaryEquiv ⟨x.1, x.2, hx⟩).1,
        (eta.nonboundaryEquiv ⟨x.1, x.2, hx⟩).2.1⟩ := by
  apply Subtype.ext
  simp [coreForwardOfEtaStableData, hx]

omit [IsNoetherianRing Rᵐᵒᵖ] in
theorem coreBackwardOfEtaStableData_of_injective
    (boundary :
      {i // i ∈ projectiveSet sigma} ≃
        {i // i ∈ injectiveSet sigma})
    (eta : RingelEtaStableData sigma)
    (y : {i // i ∈ (quotientCore sigma : Set iota)})
    (hy : y.1 ∈ injectiveSet sigma) :
    coreBackwardOfEtaStableData sigma boundary eta y =
      ⟨(boundary.symm ⟨y.1, hy⟩).1,
        projectiveSet_subset_submoduleCore sigma
          (boundary.symm ⟨y.1, hy⟩).2⟩ := by
  apply Subtype.ext
  simp [coreBackwardOfEtaStableData, hy]

omit [IsNoetherianRing Rᵐᵒᵖ] in
theorem coreBackwardOfEtaStableData_of_noninjective
    (boundary :
      {i // i ∈ projectiveSet sigma} ≃
        {i // i ∈ injectiveSet sigma})
    (eta : RingelEtaStableData sigma)
    (y : {i // i ∈ (quotientCore sigma : Set iota)})
    (hy : y.1 ∉ injectiveSet sigma) :
    coreBackwardOfEtaStableData sigma boundary eta y =
      ⟨(eta.nonboundaryEquiv.symm ⟨y.1, y.2, hy⟩).1,
        (eta.nonboundaryEquiv.symm ⟨y.1, y.2, hy⟩).2.1⟩ := by
  apply Subtype.ext
  simp [coreBackwardOfEtaStableData, hy]

/-- Glue Ringel's stable equivalence away from the boundary to the Nakayama
equivalence on the projective/injective boundary. -/
def coreEquivOfEtaStableData
    (boundary :
      {i // i ∈ projectiveSet sigma} ≃
        {i // i ∈ injectiveSet sigma})
    (eta : RingelEtaStableData sigma) :
    {i // i ∈ (submoduleCore sigma : Set iota)} ≃
      {i // i ∈ (quotientCore sigma : Set iota)} where
  toFun := coreForwardOfEtaStableData sigma boundary eta
  invFun := coreBackwardOfEtaStableData sigma boundary eta
  left_inv x := by
    classical
    by_cases hx : x.1 ∈ projectiveSet sigma
    · rw [coreForwardOfEtaStableData_of_projective sigma boundary eta x hx]
      let y := boundary ⟨x.1, hx⟩
      have hy : y.1 ∈ injectiveSet sigma := y.2
      rw [coreBackwardOfEtaStableData_of_injective sigma boundary eta _ hy]
      apply Subtype.ext
      change
        (boundary.symm (boundary ⟨x.1, hx⟩)).1 = x.1
      exact congrArg Subtype.val
        (boundary.symm_apply_apply ⟨x.1, hx⟩)
    · rw [coreForwardOfEtaStableData_of_nonprojective sigma boundary eta x hx]
      have hy :
          (eta.nonboundaryEquiv ⟨x.1, x.2, hx⟩).1 ∉
            injectiveSet sigma :=
        (eta.nonboundaryEquiv ⟨x.1, x.2, hx⟩).2.2
      rw [coreBackwardOfEtaStableData_of_noninjective sigma boundary eta _ hy]
      apply Subtype.ext
      change
        (eta.nonboundaryEquiv.symm
          (eta.nonboundaryEquiv ⟨x.1, x.2, hx⟩)).1 = x.1
      exact congrArg Subtype.val
        (eta.nonboundaryEquiv.symm_apply_apply ⟨x.1, x.2, hx⟩)
  right_inv y := by
    classical
    by_cases hy : y.1 ∈ injectiveSet sigma
    · rw [coreBackwardOfEtaStableData_of_injective sigma boundary eta y hy]
      let x := boundary.symm ⟨y.1, hy⟩
      have hx : x.1 ∈ projectiveSet sigma := x.2
      rw [coreForwardOfEtaStableData_of_projective sigma boundary eta _ hx]
      apply Subtype.ext
      change
        (boundary (boundary.symm ⟨y.1, hy⟩)).1 = y.1
      exact congrArg Subtype.val
        (boundary.apply_symm_apply ⟨y.1, hy⟩)
    · rw [coreBackwardOfEtaStableData_of_noninjective sigma boundary eta y hy]
      have hx :
          (eta.nonboundaryEquiv.symm ⟨y.1, y.2, hy⟩).1 ∉
            projectiveSet sigma :=
        (eta.nonboundaryEquiv.symm ⟨y.1, y.2, hy⟩).2.2
      rw [coreForwardOfEtaStableData_of_nonprojective sigma boundary eta _ hx]
      apply Subtype.ext
      change
        (eta.nonboundaryEquiv
          (eta.nonboundaryEquiv.symm ⟨y.1, y.2, hy⟩)).1 = y.1
      exact congrArg Subtype.val
        (eta.nonboundaryEquiv.apply_symm_apply ⟨y.1, y.2, hy⟩)

/-- Paper-facing Ringel correspondence: the compiled `Dη` equivalence
induces a bijection between the torsionless and cotorsionless cores for an
arbitrary chosen indecomposable skeleton. -/
def ringelCoreEquiv
    (K : Type u) [Field K] [Algebra K R] [FiniteDimensional K R] :
    {i // i ∈ (submoduleCore sigma : Set iota)} ≃
      {i // i ∈ (quotientCore sigma : Set iota)} :=
  coreEquivOfEtaStableData sigma
    (projectiveInjectiveLabelEquiv (R := R) K sigma)
    (etaStableDataOfAmbientEquivalence sigma
      (QuotientSubmoduleEquidistribution.RingelEta.ringelEtaStableEquivalence
        (R := R) K))

end QuotientSubmoduleEquidistribution.RingelStable
