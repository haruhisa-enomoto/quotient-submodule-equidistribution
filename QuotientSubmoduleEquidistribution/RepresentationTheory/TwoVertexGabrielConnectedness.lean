import QuotientSubmoduleEquidistribution.RepresentationTheory.GabrielArrowBridge
import QuotientSubmoduleEquidistribution.RepresentationTheory.TwoVertexArrowSupport
import QuotientSubmoduleEquidistribution.RepresentationTheory.TwoVertexPeirceConnectedness

/-!
# From Peirce cotangent classes to connected arrow support

This file isolates the remaining split-basic Gabriel input in the standard
block-connectedness argument.  The ring-theoretic theorem supplies a nonzero
off-diagonal class in one orientation; explicit detection maps from such
classes to arrows then give connected two-vertex support.
-/

noncomputable section

namespace QuotientSubmoduleEquidistribution.TwoVertexGabrielConnectedness

universe u w

open QuotientSubmoduleEquidistribution.TwoVertexArrowSupport

variable {R : Type u} [Ring R]
  {Arrow : Type w} (D : Data Arrow)

/-- A block-connected complementary idempotent pair yields connected arrow
support as soon as nonzero off-diagonal cotangent classes are detected by
arrows with the corresponding endpoints. -/
theorem underlyingConnected_of_blockConnected
    (J : Ideal R) [J.IsTwoSided]
    (e f : R)
    (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f)
    (hsum : e + f = 1)
    (he0 : e ≠ 0)
    (hf0 : f ≠ 0)
    (hConnected : ∀ z : R, IsIdempotentElem z → IsMulCentral z →
      z = 0 ∨ z = 1)
    (hResidueEF : ∀ r : R, e * r * f ∈ J)
    (hResidueFE : ∀ r : R, f * r * e ∈ J)
    (hNilpotent : IsNilpotent J)
    (hDetectEF :
      (∃ r ∈ J, e * r * f ∉ J ^ 2) → D.HasArrow 0 1)
    (hDetectFE :
      (∃ r ∈ J, f * r * e ∉ J ^ 2) → D.HasArrow 1 0) :
    D.UnderlyingConnected := by
  rcases
      QuotientSubmoduleEquidistribution.TwoVertexPeirceConnectedness.exists_cross_cotangent_of_blockConnected
          J e f he hf hsum he0 hf0 hConnected
          hResidueEF hResidueFE hNilpotent with
    hEF | hFE
  · exact Or.inl (hDetectEF hEF)
  · exact Or.inr (hDetectFE hFE)

/-! ## Minimal Ext-Gabriel detection interface -/

universe v

open CategoryTheory
open QuotientSubmoduleEquidistribution.GabrielArrowBridge

variable {K S Peirce : Type u}
  [Field K]
  [Ring S] [Small.{u} S] [IsNoetherianRing S] [Algebra K S]
  [Ring Peirce] [IsArtinianRing Peirce]
  {ι : Type v} [Finite ι]
  (σ : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, v, u} S ι)

/-- Nonvanishing of a cross `Ext¹` group after the two simple labels have
been relabelled by `Fin 2`.  The disjunction deliberately forgets the
left/right Gabriel-arrow convention. -/
def HasCrossExt (relabel : σ.SimpleIndex ≃ Fin 2) : Prop :=
  Nontrivial
      (ExtOne σ (relabel.symm 0) (relabel.symm 1)) ∨
    Nontrivial
      (ExtOne σ (relabel.symm 1) (relabel.symm 0))

/-- The Peirce/cotangent datum used to deduce connectedness of a two-vertex
Ext-Gabriel support from block connectedness.  Besides a nontrivial vertex
idempotent, it records containment of both full off-diagonal corners in the
Jacobson radical.  Only one implication from a nonzero cross cotangent class
to some cross `Ext¹` is required, so the interface is insensitive to the two
common arrow-orientation conventions. -/
structure TwoVertexPeirceExtData
    (relabel : σ.SimpleIndex ≃ Fin 2) where
  vertexZero : Peirce
  vertexZero_idempotent : IsIdempotentElem vertexZero
  vertexZero_ne_zero : vertexZero ≠ 0
  vertexZero_ne_one : vertexZero ≠ 1
  forward_mem_jacobson (r : Peirce) :
    vertexZero * r * (1 - vertexZero) ∈ Ring.jacobson Peirce
  backward_mem_jacobson (r : Peirce) :
    (1 - vertexZero) * r * vertexZero ∈ Ring.jacobson Peirce
  crossExt_of_crossCotangent :
    ((∃ r ∈ Ring.jacobson Peirce,
          vertexZero * r * (1 - vertexZero) ∉
            (Ring.jacobson Peirce) ^ 2) ∨
        ∃ r ∈ Ring.jacobson Peirce,
          (1 - vertexZero) * r * vertexZero ∉
            (Ring.jacobson Peirce) ^ 2) →
      HasCrossExt σ relabel

namespace TwoVertexPeirceExtData

omit [Finite ι] in
/-- Block connectedness forces a cross `Ext¹` group once the exact
Peirce/cotangent detection theorem has been supplied. -/
theorem hasCrossExt_of_blockConnected
    (relabel : σ.SimpleIndex ≃ Fin 2)
    (P : TwoVertexPeirceExtData (Peirce := Peirce) σ relabel)
    (hConnected : ∀ z : Peirce, IsIdempotentElem z → IsMulCentral z →
      z = 0 ∨ z = 1) :
    HasCrossExt σ relabel := by
  apply P.crossExt_of_crossCotangent
  apply
    QuotientSubmoduleEquidistribution.TwoVertexPeirceConnectedness.exists_cross_jacobson_cotangent_of_blockConnected
        P.vertexZero (1 - P.vertexZero)
        P.vertexZero_idempotent P.vertexZero_idempotent.one_sub
        (by noncomm_ring)
        P.vertexZero_ne_zero
  · intro hComplement
    apply P.vertexZero_ne_one
    exact (sub_eq_zero.mp hComplement).symm
  · exact hConnected
  · exact P.forward_mem_jacobson
  · exact P.backward_mem_jacobson

end TwoVertexPeirceExtData

end QuotientSubmoduleEquidistribution.TwoVertexGabrielConnectedness
