import QuotientSubmoduleEquidistribution.Combinatorics.FixedStripCyclicBalance
import QuotientSubmoduleEquidistribution.RepresentationTheory.FourVertexReversePacketCoordinates

/-!
# The fixed-strip reversal target

After pulling dual row-`F` packets back to source coordinates, the manuscript
groups the two packet families into cyclic binary systems.  This file states
that exact remaining parametrization and connects it to the fixed field of
the concrete four-vertex reversal balance.
-/

set_option autoImplicit false
noncomputable section

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe u v w

variable {k R S : Type u} [Field k] [IsAlgClosed k]
  [Ring R] [Algebra k R] [FiniteDimensional k R]
  [Ring S] [Algebra k S] [FiniteDimensional k S]
  [IsNoetherianRing R] [IsNoetherianRing S]
  {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
  [DecidableEq ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)
  (τ : IndecomposableSkeleton.{u, w, u} S κ)
  (D : AlignedBiduality σ τ)

/-- The manuscript's fixed-strip construction, isolated at its exact
mathematical interface: quotient row-`F` supports are rises and reverse
row-`F` supports are falls in the same finite cyclic binary fibers. -/
abbrev ActualFixedStripCyclicParametrization :=
  QuotientSubmoduleEquidistribution.FixedStripCyclicBalance.Parametrization
    (QuotientFixedPacketFour (k := k) (R := R) σ)
    (SourceReverseFixedPacketFour
      (k := k) (R := R) σ τ D)

omit [IsAlgClosed k] [DecidableEq ι] in
/-- Any construction of the actual cyclic fixed-strip parametrization proves
the fixed-packet cardinality required by reversal balance. -/
theorem fixedPacketFour_card_eq_of_cyclicParametrization
    (P : ActualFixedStripCyclicParametrization
      (k := k) (R := R) σ τ D) :
    Fintype.card (QuotientFixedPacketFour (k := k) (R := R) σ) =
      Fintype.card (SubmoduleFixedPacketFour (k := k) (S := S) τ) := by
  calc
    Fintype.card (QuotientFixedPacketFour (k := k) (R := R) σ) =
        Fintype.card (SourceReverseFixedPacketFour
          (k := k) (R := R) σ τ D) :=
      QuotientSubmoduleEquidistribution.FixedStripCyclicBalance.Parametrization.card_eq P
    _ = Fintype.card (SubmoduleFixedPacketFour
          (k := k) (S := S) τ) :=
      (Fintype.card_congr
        (submoduleFixedPacketFourEquivSourceReverse
          (k := k) (R := R) (S := S) σ τ D)).symm

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
