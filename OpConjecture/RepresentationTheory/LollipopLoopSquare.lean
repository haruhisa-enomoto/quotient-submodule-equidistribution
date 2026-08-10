import OpConjecture.RepresentationTheory.OneWayLollipopCotangentAdapter
import OpConjecture.RepresentationTheory.CyclicRightIdealTop

/-!
# Vanishing of the lollipop loop square

This file formalizes the presentation-free module argument in the exceptional
three-object faithful core.  A hypothetical nonzero loop square generates a
torsionless cyclic right ideal with the same simple top as the loop vertex.
The exceptional-core dichotomy makes that ideal either the vertex projective
or the unique nonprojective torsionless object.  In either case, equality of
nested finite-dimensional cyclic ideals contradicts the radical-square
position of the original loop representative.
-/

noncomputable section

open CategoryTheory Set MulOpposite

namespace OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore

universe u v w

open OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank

variable {K B : Type u} [Field K] [Ring B] [Algebra K B]
  [FiniteDimensional K B] [IsNoetherianRing Bᵐᵒᵖ]
  {kappa : Type v} [Finite kappa]
  (tau : OpConjecture.IndecomposableSkeleton.{u, v, u} Bᵐᵒᵖ kappa)
  {Arrow : Type w}
  {source target : Arrow → tau.SimpleIndex}
  (G : SplitBasicGabrielArrowRealization tau source target)

include K in
/-- The manuscript's loop-square contradiction, isolated from the general
cyclic-top input.  If every nonzero square of the chosen loop representative
has the expected simple top, then exceptional-core uniqueness forces that
square to vanish. -/
theorem loopRepresentative_sq_eq_zero_of_square_top
    (hRingel : RingelCoreCardinality tau)
    (hRank : projectiveRank tau = 2)
    (hCore : (quotientCore tau : Set kappa).ncard = 3)
    (ell : Arrow) (hLoop : source ell = target ell)
    (hx2 : G.representative ell ∉ (Ring.jacobson B) ^ 2)
    (hSquareTop : G.representative ell * G.representative ell ≠ 0 →
      Nonempty
        (FGModuleCat.of Bᵐᵒᵖ
            (OpConjecture.Tsukamoto.cyclicRightIdealFG
                (G.representative ell * G.representative ell) ⧸
              Module.jacobson Bᵐᵒᵖ
                (OpConjecture.Tsukamoto.cyclicRightIdealFG
                  (G.representative ell * G.representative ell))) ≅
          tau.obj (target ell).1)) :
    G.representative ell * G.representative ell = 0 := by
  let x := G.representative ell
  by_contra hxx
  have hxxJ2 : x * x ∈ (Ring.jacobson B) ^ 2 := by
    have hprod : x * x ∈ Ring.jacobson B * Ring.jacobson B :=
      Ideal.mul_mem_mul (G.representative_mem_jacobson ell)
        (G.representative_mem_jacobson ell)
    rw [Ideal.IsTwoSided.pow_succ]
    simpa [Submodule.pow_one] using hprod
  have hleSqX :
      OpConjecture.Tsukamoto.principalRightIdeal (x * x) ≤
        OpConjecture.Tsukamoto.principalRightIdeal x :=
    OpConjecture.Tsukamoto.principalRightIdeal_le_of_eq_mul rfl
  have hleXVertex :
      OpConjecture.Tsukamoto.principalRightIdeal x ≤
        OpConjecture.Tsukamoto.principalRightIdeal (G.vertex (target ell)) := by
    simpa [x, hLoop] using G.arrowIdeal_le_source ell
  have hleSqVertex :
      OpConjecture.Tsukamoto.principalRightIdeal (x * x) ≤
        OpConjecture.Tsukamoto.principalRightIdeal (G.vertex (target ell)) :=
    hleSqX.trans hleXVertex
  have eTop := (hSquareTop hxx).some
  rcases
      CyclicRightIdeal.iso_targetProjective_or_exceptional_of_top_iso
        tau hRingel hRank hCore (x * x) (target ell) eTop with
    hProjective | hExceptional
  · obtain ⟨eSqProjective⟩ := hProjective
    let eSqVertex :
        OpConjecture.Tsukamoto.cyclicRightIdealFG (x * x) ≅
          OpConjecture.Tsukamoto.cyclicRightIdealFG
            (G.vertex (target ell)) :=
      eSqProjective ≪≫
        (SplitBasicGabrielArrowRealization.vertexIso tau G (target ell)).symm
    have hideals :
        OpConjecture.Tsukamoto.principalRightIdeal (x * x) =
          OpConjecture.Tsukamoto.principalRightIdeal
            (G.vertex (target ell)) :=
      OpConjecture.Tsukamoto.principalRightIdeal_eq_of_le_of_iso
        K hleSqVertex eSqVertex
    have hvertexMem :
        op (G.vertex (target ell)) ∈
          OpConjecture.Tsukamoto.principalRightIdeal (x * x) := by
      rw [hideals]
      exact Ideal.subset_span (Set.mem_singleton _)
    have hvertexJ2 : G.vertex (target ell) ∈ (Ring.jacobson B) ^ 2 :=
      OpConjecture.Tsukamoto.unop_mem_twoSidedIdeal_of_mem_principalRightIdeal
        ((Ring.jacobson B) ^ 2) hxxJ2 hvertexMem
    have hvertexJ : G.vertex (target ell) ∈ Ring.jacobson B :=
      Ideal.pow_le_self two_ne_zero hvertexJ2
    exact G.vertex_ne_zero (target ell)
      (OpConjecture.Tsukamoto.idempotent_eq_zero_of_mem_jacobson
        (G.vertex_idempotent (target ell)) hvertexJ)
  · obtain ⟨eSqExceptional⟩ := hExceptional
    let E := G.toExceptionalArrowIdealData
    have hLoopLabel : E.idealLabel ell =
        exceptionalLabel tau hRingel hRank hCore :=
      E.loop_idealLabel_eq_exceptionalLabel tau
        hRingel hRank hCore ell hLoop
    let eXExceptional :
        OpConjecture.Tsukamoto.cyclicRightIdealFG x ≅
          tau.obj (exceptionalLabel tau hRingel hRank hCore) :=
      SplitBasicGabrielArrowRealization.arrowIso tau G ell ≪≫
        eqToIso (congrArg tau.obj hLoopLabel)
    let eSqX :
        OpConjecture.Tsukamoto.cyclicRightIdealFG (x * x) ≅
          OpConjecture.Tsukamoto.cyclicRightIdealFG x :=
      eSqExceptional ≪≫ eXExceptional.symm
    have hideals :
        OpConjecture.Tsukamoto.principalRightIdeal (x * x) =
          OpConjecture.Tsukamoto.principalRightIdeal x :=
      OpConjecture.Tsukamoto.principalRightIdeal_eq_of_le_of_iso
        K hleSqX eSqX
    have hxMem : op x ∈
        OpConjecture.Tsukamoto.principalRightIdeal (x * x) := by
      rw [hideals]
      exact Ideal.subset_span (Set.mem_singleton _)
    apply hx2
    simpa [x] using
      (OpConjecture.Tsukamoto.unop_mem_twoSidedIdeal_of_mem_principalRightIdeal
        ((Ring.jacobson B) ^ 2) hxxJ2 hxMem)

include K in
/-- A loop representative fixed on the right by its vertex idempotent
squares to zero.  The cyclic square has the same simple top as the vertex
projective, so the exceptional-core dichotomy supplies the contradiction. -/
theorem loopRepresentative_sq_eq_zero
    (hRingel : RingelCoreCardinality tau)
    (hRank : projectiveRank tau = 2)
    (hCore : (quotientCore tau : Set kappa).ncard = 3)
    (ell : Arrow) (hLoop : source ell = target ell)
    (hx2 : G.representative ell ∉ (Ring.jacobson B) ^ 2)
    (hxRight : G.representative ell * G.vertex (target ell) =
      G.representative ell) :
    G.representative ell * G.representative ell = 0 := by
  apply loopRepresentative_sq_eq_zero_of_square_top
    (K := K) tau G hRingel hRank hCore ell hLoop hx2
  intro hxx
  apply cyclicRightIdeal_topIso_of_ne_zero_of_right_fixed
    (K := K) tau G (target ell) hxx
  calc
    (G.representative ell * G.representative ell) *
          G.vertex (target ell) =
        G.representative ell *
          (G.representative ell * G.vertex (target ell)) := by
            rw [mul_assoc]
    _ = G.representative ell * G.representative ell := by
      rw [hxRight]

end OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore

namespace OpConjecture.QuotientSurvival.TwoCoordinateData

open OpConjecture.CotangentExtBridge
open OpConjecture.GabrielArrowBridge

universe u v

variable {K B : Type u}
  [Field K] [Ring B] [Algebra K B]
  [FiniteDimensional K B] [IsArtinianRing B]
  {kappa : Type v}
  [Small.{u} Bᵐᵒᵖ] [IsNoetherianRing Bᵐᵒᵖ] [Finite kappa]
  (D : OpConjecture.QuotientSurvival.TwoCoordinateData
    (K := K) (B := B))
  (tau : OpConjecture.IndecomposableSkeleton.{u, v, u} Bᵐᵒᵖ kappa)

/-- The incoming one-way lollipop support in an exceptional three-object
faithful core is one of the dead- and live-path coordinate algebras. -/
theorem algEquiv_b0_or_b1_of_incomingOneWayLollipop
    (hNoParallel : NoParallelExtSupport (K := K) tau)
    (hShape :
      (D.alignedExtTwoVertexSupport tau hNoParallel).IsOneWayLollipopAt 0 1)
    (hIncoming :
      ¬ (D.alignedExtTwoVertexSupport tau hNoParallel).HasArrow 0 1 ∧
        (D.alignedExtTwoVertexSupport tau hNoParallel).HasArrow 1 0)
    (hRingel :
      OpConjecture.IndecomposableSkeleton.FaithfulCore.RingelCoreCardinality
        tau)
    (hRank :
      OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.projectiveRank
        tau = 2)
    (hCore :
      (OpConjecture.IndecomposableSkeleton.FaithfulCore.quotientCore tau :
        Set kappa).ncard = 3) :
    Nonempty (OpConjecture.LollipopConcrete.B0Model K ≃ₐ[K] B) ∨
      Nonempty (OpConjecture.LollipopConcrete.B1.B1Model K ≃ₐ[K] B) := by
  let E :=
    OpConjecture.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
      D tau
  let R :=
    OpConjecture.CoordinateGabrielRealization.automaticExtArrowCotangentRepresentativeData
      D tau
  let G :=
    OpConjecture.CoordinateGabrielRealization.ExtArrowCotangentRepresentativeData.toSplitBasicGabrielArrowRealization
      R
  let loopArrow := hShape.2.1.choose
  have hLoopSpec := hShape.2.1.choose_spec
  have hLoopSource := hLoopSpec.1
  have hLoopTarget := hLoopSpec.2
  change E.symm (ExtGabrielArrowIndex.source tau loopArrow) = 0 at hLoopSource
  change E.symm (ExtGabrielArrowIndex.target tau loopArrow) = 0 at hLoopTarget
  have hLoop : ExtGabrielArrowIndex.source tau loopArrow =
      ExtGabrielArrowIndex.target tau loopArrow := by
    apply E.symm.injective
    exact hLoopSource.trans hLoopTarget.symm
  have hxRight : R.representative loopArrow *
      G.vertex (ExtGabrielArrowIndex.target tau loopArrow) =
        R.representative loopArrow := by
    simpa [G,
      OpConjecture.CoordinateGabrielRealization.ExtArrowCotangentRepresentativeData.toSplitBasicGabrielArrowRealization]
      using R.representative_right_fixed loopArrow
  have hxsq : R.representative loopArrow * R.representative loopArrow = 0 :=
    OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.loopRepresentative_sq_eq_zero
      (K := K) tau G hRingel hRank hCore loopArrow hLoop
        (R.representative_not_mem_square loopArrow) hxRight
  let C := D.incomingOneWayLollipopCotangentData
    tau hNoParallel hShape hIncoming
  have hCsq : C.x * C.x = 0 := by
    simpa [C, incomingOneWayLollipopCotangentData, R, loopArrow] using hxsq
  exact C.algEquiv_b0_or_b1 hCsq

end OpConjecture.QuotientSurvival.TwoCoordinateData
