import QuotientSubmoduleEquidistribution.RepresentationDirected.ARWordOppositeDirectedProfile
import QuotientSubmoduleEquidistribution.RepresentationDirected.IyamaWordMeshPreStrictRealization

/-!
# The unconditional representation-directed word profile

This file composes the abstract word-mesh realization with directed sorting
and opposite-word duality.  It removes the final uniform mesh-exactness
hypotheses from the representation-directed profile and equidistribution
theorems.

No concrete algebra, quiver presentation, module enumeration, or module
classification is used.
-/

set_option autoImplicit false
noncomputable section

namespace QuotientSubmoduleEquidistribution.RepresentationDirected.IyamaMesh.WordMesh.DirectedEndpoint

open QuotientSubmoduleEquidistribution.RepresentationDirected.FixedWord
open QuotientSubmoduleEquidistribution.RepresentationDirected
open QuotientSubmoduleEquidistribution.RepresentationDirected.ARWordDuality
open QuotientSubmoduleEquidistribution.RepresentationDirected.DirectedAROrbit
open QuotientSubmoduleEquidistribution.RepresentationDirected.DualDirectedOrder
open QuotientSubmoduleEquidistribution.RepresentationDirected.OppositeDirectedProfile
open QuotientSubmoduleEquidistribution.RepresentationDirected.PrincipalPositivity
open QuotientSubmoduleEquidistribution.RepresentationDirected.SimpleGraphBruhat
open QuotientSubmoduleEquidistribution.RepresentationDirected.SimpleGraphCoxeter
open QuotientSubmoduleEquidistribution.RepresentationDirected.IyamaMesh.WordMesh.PreStrictRealization

universe uF uR uS uI uJ

/-! ## Uniform exactness for an explicit AR word -/

/-- The abstract word-mesh category supplies uniform selected-segment mesh
exactness for every explicitly ordered finite Auslander--Reiten word. -/
theorem hasUniformMeshExactnessFor
    (F : Type uF) [Field F]
    {R : Type uR} [Ring R] [IsNoetherianRing R]
    {I : Type uI} [Fintype I]
    (sigma : IndecomposableSkeleton.{uR, uI, uR} R I)
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma) :
    HasUniformMeshExactnessFor sigma H T E := by
  exact MeshExactness.uniformSelectedSegmentMeshInverseNonnegative _ _
    (uniformSelectedSegmentRepresentableMeshExactness (K := F) _ _)

/-! ## The profile and equidistribution endpoints -/

/-- The complete lex-first quotient and colex-last submodule profile follows
from the abstract word mesh, without an additional exactness hypothesis. -/
def explicitProfileParametrization
    {R : Type uR} [Ring R] [IsNoetherianRing R]
    {S : Type uS} [Ring S] [IsNoetherianRing S]
    {I : Type uI} {J : Type uJ} [Fintype I] [Fintype J]
    (sigma : IndecomposableSkeleton.{uR, uI, uR} R I)
    (tau : IndecomposableSkeleton.{uS, uJ, uS} S J)
    {FSource : Type uR} [Field FSource] [IsAlgClosed FSource]
    [Algebra FSource R] [FiniteDimensional FSource R]
    {FTarget : Type uS} [Field FTarget] [IsAlgClosed FTarget]
    [Algebra FTarget S] [FiniteDimensional FTarget S]
    (B : tau.AlignedBiduality sigma)
    (Hsigma : HasAcyclicNonzeroNonisomorphisms sigma)
    (Htau : HasAcyclicNonzeroNonisomorphisms tau)
    (Tsigma : sigma.FiniteARTranslationData)
    (Ttau : tau.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma) :
    QuotientSubmoduleEquidistribution.RepresentationDirected.ProfileParametrization sigma
      (BruhatLowerInterval
        (DirectedAROrbit.OrderedARWord.orbitGraph sigma Hsigma Tsigma)
        (DirectedAROrbit.OrderedARWord.wordFor sigma Hsigma Tsigma E)) :=
  OppositeDirectedProfile.explicitProfileParametrization_of_explicitOrderMeshExactness
    (KSource := FSource) (KTarget := FTarget)
    sigma tau B Hsigma Htau Tsigma Ttau E
    (hasUniformMeshExactnessFor FSource sigma Hsigma Tsigma E)
    (hasUniformMeshExactnessFor FTarget tau Htau Ttau
      (oppositeOrderChoice sigma tau B E))

/-- Abstract representation-directed quotient--submodule equidistribution:
once the finite skeletons, directedness, AR translations, and contragredient
duality are supplied, Iyama's word mesh discharges the remaining exactness
input. -/
theorem quotientSubmoduleEquidistribution
    {R : Type uR} [Ring R] [IsNoetherianRing R]
    {S : Type uS} [Ring S] [IsNoetherianRing S]
    {I : Type uI} {J : Type uJ} [Fintype I] [Fintype J]
    (sigma : IndecomposableSkeleton.{uR, uI, uR} R I)
    (tau : IndecomposableSkeleton.{uS, uJ, uS} S J)
    {FSource : Type uR} [Field FSource] [IsAlgClosed FSource]
    [Algebra FSource R] [FiniteDimensional FSource R]
    {FTarget : Type uS} [Field FTarget] [IsAlgClosed FTarget]
    [Algebra FTarget S] [FiniteDimensional FTarget S]
    (B : tau.AlignedBiduality sigma)
    (Hsigma : HasAcyclicNonzeroNonisomorphisms sigma)
    (Htau : HasAcyclicNonzeroNonisomorphisms tau)
    (Tsigma : sigma.FiniteARTranslationData)
    (Ttau : tau.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma) :
    sigma.HasQuotientSubmoduleEquidistribution :=
  OppositeDirectedProfile.quotientSubmoduleEquidistribution_of_explicitOrderMeshExactness
    (KSource := FSource) (KTarget := FTarget)
    sigma tau B Hsigma Htau Tsigma Ttau E
    (hasUniformMeshExactnessFor FSource sigma Hsigma Tsigma E)
    (hasUniformMeshExactnessFor FTarget tau Htau Ttau
      (oppositeOrderChoice sigma tau B E))

/-- The precise Bruhat profile in the default directed order; its structure
contains the reduced source word, lex-first quotient supports, colex-last
submodule supports, and their common length statistic. -/
def explicitProfileParametrizationOfDirected
    {R : Type uR} [Ring R] [IsNoetherianRing R]
    {S : Type uS} [Ring S] [IsNoetherianRing S]
    {I : Type uI} {J : Type uJ} [Fintype I] [Fintype J]
    (sigma : IndecomposableSkeleton.{uR, uI, uR} R I)
    (tau : IndecomposableSkeleton.{uS, uJ, uS} S J)
    {FSource : Type uR} [Field FSource] [IsAlgClosed FSource]
    [Algebra FSource R] [FiniteDimensional FSource R]
    {FTarget : Type uS} [Field FTarget] [IsAlgClosed FTarget]
    [Algebra FTarget S] [FiniteDimensional FTarget S]
    (B : tau.AlignedBiduality sigma)
    (Hsigma : HasAcyclicNonzeroNonisomorphisms sigma)
    (Tsigma : sigma.FiniteARTranslationData)
    (Ttau : tau.FiniteARTranslationData) :
    QuotientSubmoduleEquidistribution.RepresentationDirected.ProfileParametrization sigma
      (BruhatLowerInterval
        (DirectedAROrbit.OrderedARWord.orbitGraph sigma Hsigma Tsigma)
        (DirectedAROrbit.OrderedARWord.wordFor sigma Hsigma Tsigma
          (DirectedOrderChoice.chosen sigma Hsigma))) :=
  explicitProfileParametrization
    (FSource := FSource) (FTarget := FTarget)
    sigma tau B Hsigma
      (dual_hasAcyclicNonzeroNonisomorphisms sigma tau B.backward Hsigma)
      Tsigma Ttau (DirectedOrderChoice.chosen sigma Hsigma)

/-- Paper-facing directed form: the source cycle-free hypothesis chooses the
required Hom order, and aligned biduality transports cycle-freeness to the
opposite skeleton. -/
theorem quotientSubmoduleEquidistribution_of_directed
    {R : Type uR} [Ring R] [IsNoetherianRing R]
    {S : Type uS} [Ring S] [IsNoetherianRing S]
    {I : Type uI} {J : Type uJ} [Fintype I] [Fintype J]
    (sigma : IndecomposableSkeleton.{uR, uI, uR} R I)
    (tau : IndecomposableSkeleton.{uS, uJ, uS} S J)
    {FSource : Type uR} [Field FSource] [IsAlgClosed FSource]
    [Algebra FSource R] [FiniteDimensional FSource R]
    {FTarget : Type uS} [Field FTarget] [IsAlgClosed FTarget]
    [Algebra FTarget S] [FiniteDimensional FTarget S]
    (B : tau.AlignedBiduality sigma)
    (Hsigma : HasAcyclicNonzeroNonisomorphisms sigma)
    (Tsigma : sigma.FiniteARTranslationData)
    (Ttau : tau.FiniteARTranslationData) :
    sigma.HasQuotientSubmoduleEquidistribution :=
  quotientSubmoduleEquidistribution
    (FSource := FSource) (FTarget := FTarget)
    sigma tau B Hsigma
      (dual_hasAcyclicNonzeroNonisomorphisms sigma tau B.backward Hsigma)
      Tsigma Ttau (DirectedOrderChoice.chosen sigma Hsigma)

end QuotientSubmoduleEquidistribution.RepresentationDirected.IyamaMesh.WordMesh.DirectedEndpoint
