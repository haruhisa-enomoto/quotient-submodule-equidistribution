import OpConjecture.RepresentationTheory.FourVertexReverseFixedStripReconstruction

/-!
# The actual fixed-strip cyclic parametrization

The quotient reconstruction identifies actual quotient row-`F` supports
with rises, and the reverse reconstruction identifies source-coordinate
reverse row-`F` supports with falls in exactly the same finite cyclic binary
systems.  This closes the manuscript's fixed-strip count.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace OpConjecture.IndecomposableSkeleton

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

/-- The manuscript's actual fixed-strip construction: contexts are
projective/fixed-center pairs, positions are their periodic two-cycle
neighbors, and the bit is projective irreducible incidence. -/
def actualFixedStripCyclicParametrization :
    ActualFixedStripCyclicParametrization
      (k := k) (R := R) σ τ D where
  Context := FintypeCat.of
    ((σ.finiteDimensionalARTranslationData k R).FixedStripContext σ)
  Position C := FintypeCat.of
    ((σ.finiteDimensionalARTranslationData k R).FixedStripPosition σ C)
  step C := FiniteARTranslationData.fixedStripStep
    (AR := σ.finiteDimensionalARTranslationData k R) (k := k)
      σ τ D (τ.finiteDimensionalARTranslationData k S) C
  bit C := FiniteARTranslationData.fixedStripBit
    (AR := σ.finiteDimensionalARTranslationData k R) σ C
  quotientEquiv :=
    FiniteARTranslationData.quotientFixedPacketFourEquivFixedStripRise
      (k := k) (R := R) (S := S) σ τ D
  reverseEquiv :=
    FiniteARTranslationData.sourceReverseFixedPacketFourEquivFixedStripFall
      (k := k) (R := R) (S := S) σ τ D

omit [IsAlgClosed k] in
include D in
/-- Unconditional fixed-strip reversal balance on actual four-vertex
row-`F` packet supports. -/
theorem fixedPacketFour_card_eq :
    Fintype.card (QuotientFixedPacketFour (k := k) (R := R) σ) =
      Fintype.card (SubmoduleFixedPacketFour (k := k) (S := S) τ) :=
  fixedPacketFour_card_eq_of_cyclicParametrization
    (k := k) (R := R) (S := S) σ τ D
      (actualFixedStripCyclicParametrization
        (k := k) (R := R) (S := S) σ τ D)

end OpConjecture.IndecomposableSkeleton
