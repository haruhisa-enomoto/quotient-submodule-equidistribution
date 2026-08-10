import QuotientSubmoduleEquidistribution.RepresentationTheory.ProjectiveInjectiveBoundary
import QuotientSubmoduleEquidistribution.RepresentationTheory.FaithfulCore

/-!
# The exact Ringel seam for the faithful cores

This specializes the stable counting adapter to the two concrete closure
cores.  The only remaining datum is the object-level stable assignment
extracted from Ringel's stable duality; the projective--injective boundary
and the finite-cardinality bookkeeping are proved here rather than assumed.
-/

noncomputable section

open Set CategoryTheory

namespace QuotientSubmoduleEquidistribution.RingelStable

universe u v

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {iota : Type v} [Finite iota]
  (sigma : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, v, u} R iota)

namespace FaithfulCoreAdapter

open QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore

/-- The precise object-level output required from Ringel's stable duality
after composing with Artin duality.  Its source is the torsionless
(`Sub`-of-projective) core and its target is the cotorsionless
(`Fac`-of-injective) core. -/
abbrev RingelEtaStableData :=
  RingelStableAssignment sigma
    (submoduleCore sigma : Set iota)
    (quotientCore sigma : Set iota)

omit [Finite iota] in
/-- Every projective skeleton label belongs to the torsionless core. -/
theorem projectiveSet_subset_submoduleCore :
    projectiveSet sigma ⊆ (submoduleCore sigma : Set iota) := by
  intro i hi
  exact sigma.sClosure.le_closure (projectiveLabels sigma) hi

omit [Finite iota] in
/-- Every injective skeleton label belongs to the cotorsionless core. -/
theorem injectiveSet_subset_quotientCore :
    injectiveSet sigma ⊆ (quotientCore sigma : Set iota) := by
  intro i hi
  exact sigma.qClosure.le_closure (injectiveLabels sigma) hi

/-- Ringel's stable assignment implies the faithful-core cardinality
statement.  This theorem does not assume the desired equality: the
nonboundary bijection is reflected from stable isomorphisms, while the
boundary equality is supplied by the Nakayama equivalence proved in
`BoundaryPairing`. -/
theorem ringelCoreCardinality_of_etaStableData
    [IsNoetherianRing Rᵐᵒᵖ]
    (K : Type u) [Field K] [Algebra K R] [FiniteDimensional K R]
    (eta : RingelEtaStableData sigma) :
    RingelCoreCardinality sigma := by
  have h := eta.ncard_eq_of_boundary_ncard_eq
    (projectiveSet_subset_submoduleCore sigma)
    (injectiveSet_subset_quotientCore sigma)
    (projectiveSet_ncard_eq_injectiveSet_ncard (R := R) K sigma)
  exact h.symm

end FaithfulCoreAdapter

end QuotientSubmoduleEquidistribution.RingelStable
