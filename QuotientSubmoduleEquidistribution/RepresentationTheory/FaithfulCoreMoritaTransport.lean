import QuotientSubmoduleEquidistribution.RepresentationTheory.FaithfulCore
import QuotientSubmoduleEquidistribution.RepresentationTheory.MoritaConsequences

/-!
# Morita transport of the faithful cores

An aligned equivalence preserves categorical projectives and injectives.
Together with the existing transport of quotient and submodule generation,
this identifies the two faithful cores and preserves their cardinalities.
-/

noncomputable section

open Set
open CategoryTheory

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton.AlignedEquivalence

universe uR uS vR vS

open QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {S : Type uS} [Ring S] [IsNoetherianRing S]
  {iota : Type vR} {kappa : Type vS}
  (sigma : IndecomposableSkeleton.{uR, vR, uR} R iota)
  (tau : IndecomposableSkeleton.{uS, vS, uS} S kappa)
  (E : AlignedEquivalence sigma tau)

/-- A label represents a projective object exactly when its aligned target
label does. -/
theorem mem_projectiveLabels_labelEquiv_iff (i : iota) :
    E.labelEquiv i ∈ projectiveLabels tau ↔
      i ∈ projectiveLabels sigma := by
  change Projective (tau.obj (E.labelEquiv i)) ↔ Projective (sigma.obj i)
  constructor
  · intro hTarget
    have hMap : Projective
        (E.categoryEquiv.functor.obj (sigma.obj i)) :=
      Projective.of_iso (E.objIso i).symm hTarget
    exact (E.categoryEquiv.map_projective_iff (sigma.obj i)).mp hMap
  · intro hSource
    have hMap : Projective
        (E.categoryEquiv.functor.obj (sigma.obj i)) :=
      (E.categoryEquiv.map_projective_iff (sigma.obj i)).mpr hSource
    exact Projective.of_iso (E.objIso i) hMap

/-- A label represents an injective object exactly when its aligned target
label does. -/
theorem mem_injectiveLabels_labelEquiv_iff (i : iota) :
    E.labelEquiv i ∈ injectiveLabels tau ↔
      i ∈ injectiveLabels sigma := by
  change Injective (tau.obj (E.labelEquiv i)) ↔ Injective (sigma.obj i)
  constructor
  · intro hTarget
    have hMap : Injective
        (E.categoryEquiv.functor.obj (sigma.obj i)) :=
      Injective.of_iso (E.objIso i).symm hTarget
    exact (E.categoryEquiv.map_injective_iff (sigma.obj i)).mp hMap
  · intro hSource
    have hMap : Injective
        (E.categoryEquiv.functor.obj (sigma.obj i)) :=
      (E.categoryEquiv.map_injective_iff (sigma.obj i)).mpr hSource
    exact Injective.of_iso (E.objIso i) hMap

/-- The label equivalence carries the projective-label set onto the target
projective-label set. -/
theorem image_projectiveLabels :
    E.labelEquiv '' projectiveLabels sigma = projectiveLabels tau := by
  ext j
  rw [Set.mem_image_equiv]
  simpa using
    (mem_projectiveLabels_labelEquiv_iff
      sigma tau E (E.labelEquiv.symm j)).symm

/-- The label equivalence carries the injective-label set onto the target
injective-label set. -/
theorem image_injectiveLabels :
    E.labelEquiv '' injectiveLabels sigma = injectiveLabels tau := by
  ext j
  rw [Set.mem_image_equiv]
  simpa using
    (mem_injectiveLabels_labelEquiv_iff
      sigma tau E (E.labelEquiv.symm j)).symm

/-- An aligned equivalence carries the quotient faithful core onto the
target quotient faithful core. -/
theorem image_quotientCore :
    E.labelEquiv '' (quotientCore sigma : Set iota) =
      (quotientCore tau : Set kappa) := by
  change E.labelEquiv '' sigma.qClosure (injectiveLabels sigma) =
    tau.qClosure (injectiveLabels tau)
  rw [image_qClosure sigma tau E, image_injectiveLabels sigma tau E]

/-- An aligned equivalence carries the submodule faithful core onto the
target submodule faithful core. -/
theorem image_submoduleCore :
    E.labelEquiv '' (submoduleCore sigma : Set iota) =
      (submoduleCore tau : Set kappa) := by
  change E.labelEquiv '' sigma.sClosure (projectiveLabels sigma) =
    tau.sClosure (projectiveLabels tau)
  rw [image_sClosure sigma tau E, image_projectiveLabels sigma tau E]

include E in
/-- Quotient-core cardinality is invariant under an aligned equivalence. -/
theorem quotientCore_ncard_eq :
    (quotientCore sigma : Set iota).ncard =
      (quotientCore tau : Set kappa).ncard := by
  calc
    (quotientCore sigma : Set iota).ncard =
        (E.labelEquiv '' (quotientCore sigma : Set iota)).ncard :=
      (Set.ncard_image_of_injective _ E.labelEquiv.injective).symm
    _ = (quotientCore tau : Set kappa).ncard := by
      rw [image_quotientCore sigma tau E]

include E in
/-- Submodule-core cardinality is invariant under an aligned equivalence. -/
theorem submoduleCore_ncard_eq :
    (submoduleCore sigma : Set iota).ncard =
      (submoduleCore tau : Set kappa).ncard := by
  calc
    (submoduleCore sigma : Set iota).ncard =
        (E.labelEquiv '' (submoduleCore sigma : Set iota)).ncard :=
      (Set.ncard_image_of_injective _ E.labelEquiv.injective).symm
    _ = (submoduleCore tau : Set kappa).ncard := by
      rw [image_submoduleCore sigma tau E]

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton.AlignedEquivalence
