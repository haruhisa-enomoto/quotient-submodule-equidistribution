import OpConjecture.RepresentationTheory.BasicTwoCoordinateData
import OpConjecture.RepresentationTheory.LollipopLoopSquare
import OpConjecture.RepresentationTheory.PeirceCotangentCornerDimension

/-!
# Reindexing split coordinates and their Ext support

This file tracks a permutation of a split semisimple quotient through the
coordinate-simple alignment and the multiplicity-bearing Ext support.
-/

noncomputable section

open CategoryTheory

namespace OpConjecture.SplitBasicCoordinateSystem.QuotientCoordinateData

universe u v w x

variable {K B : Type u} {I : Type v} {J : Type w}
  [Field K] [Ring B] [Algebra K B] [IsArtinianRing B]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  (D : QuotientCoordinateData (K := K) (B := B) (I := I))
  (p : I ≃ J)

omit [IsArtinianRing B] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] in
@[simp]
theorem coordinateCharacter_reindex (j : J) :
    OpConjecture.CotangentExtBridge.CoordinateData.coordinateCharacter
        (D.reindex p) j =
      OpConjecture.CotangentExtBridge.CoordinateData.coordinateCharacter
        D (p.symm j) := by
  ext b
  change
    (Equiv.piCongrLeft (fun _ : J ↦ K) p
      (D.quotientEquiv
        (Ideal.Quotient.mk (Ring.jacobson B) b))) j =
      D.quotientEquiv
        (Ideal.Quotient.mk (Ring.jacobson B) b) (p.symm j)
  rw [Equiv.piCongrLeft_apply]
  simp

omit [IsArtinianRing B] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] in
@[simp]
theorem coordinateCharacterOp_reindex (j : J) :
    OpConjecture.CotangentExtBridge.CoordinateData.coordinateCharacterOp
        (D.reindex p) j =
      OpConjecture.CotangentExtBridge.CoordinateData.coordinateCharacterOp
        D (p.symm j) := by
  ext b
  simp [OpConjecture.CotangentExtBridge.CoordinateData.coordinateCharacterOp]

/-- Reindexing does not change a coordinate simple; it only renames its
coordinate. -/
def coordinateSimpleIso_reindex (j : J) :
    OpConjecture.CotangentExtBridge.CoordinateData.coordinateSimple
        (D.reindex p) j ≅
      OpConjecture.CotangentExtBridge.CoordinateData.coordinateSimple
        D (p.symm j) := by
  let L :
      (OpConjecture.CotangentExtBridge.CoordinateData.coordinateSimple
          (D.reindex p) j : Type u) ≃ₗ[Bᵐᵒᵖ]
        (OpConjecture.CotangentExtBridge.CoordinateData.coordinateSimple
          D (p.symm j) : Type u) :=
    { toFun := id
      invFun := id
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := by
        intro b x
        change
          OpConjecture.CotangentExtBridge.CoordinateData.coordinateCharacterOp
              (D.reindex p) j b * (show K from x) =
            OpConjecture.CotangentExtBridge.CoordinateData.coordinateCharacterOp
              D (p.symm j) b * (show K from x)
        rw [coordinateCharacterOp_reindex D p j] }
  exact L.toModuleIso

variable {kappa : Type x} [IsNoetherianRing Bᵐᵒᵖ]
  (tau : OpConjecture.IndecomposableSkeleton.{u, x, u} Bᵐᵒᵖ kappa)

/-- The coordinate-to-simple equivalence is reindexed by precomposition
with the inverse coordinate permutation. -/
theorem coordinateSimpleIndexEquiv_reindex :
    OpConjecture.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
        (D.reindex p) tau =
      p.symm.trans
        (OpConjecture.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
          D tau) := by
  apply Equiv.ext
  intro j
  apply Subtype.ext
  let F := forget₂ (FGModuleCat.{u} Bᵐᵒᵖ) (ModuleCat.{u} Bᵐᵒᵖ)
  let eFG :
      OpConjecture.CotangentExtBridge.CoordinateData.coordinateSimpleFG
          (D.reindex p) j ≅
        OpConjecture.CotangentExtBridge.CoordinateData.coordinateSimpleFG
          D (p.symm j) :=
    F.preimageIso
      (OpConjecture.CotangentExtBridge.CoordinateData.coordinateSimpleFGForgetIso
          (D.reindex p) j ≪≫
        coordinateSimpleIso_reindex D p j ≪≫
        (OpConjecture.CotangentExtBridge.CoordinateData.coordinateSimpleFGForgetIso
          D (p.symm j)).symm)
  apply tau.eq_of_iso
  exact ⟨
    (OpConjecture.CotangentExtBridge.CoordinateData.coordinateSimpleFGIsoAligned
      (D.reindex p) tau j).symm ≪≫
      eFG ≪≫
      OpConjecture.CotangentExtBridge.CoordinateData.coordinateSimpleFGIsoAligned
        D tau (p.symm j)⟩

end OpConjecture.SplitBasicCoordinateSystem.QuotientCoordinateData

namespace OpConjecture.QuotientSurvival.TwoCoordinateData

open OpConjecture.GabrielArrowBridge

universe u v

variable {K B : Type u}
  [Field K] [Ring B] [Algebra K B] [IsArtinianRing B]
  {kappa : Type v} [IsNoetherianRing Bᵐᵒᵖ]
  (D : OpConjecture.QuotientSurvival.TwoCoordinateData
    (K := K) (B := B))
  (tau : OpConjecture.IndecomposableSkeleton.{u, v, u} Bᵐᵒᵖ kappa)
  (hNoParallel : NoParallelExtSupport (K := K) tau)
  (p : Fin 2 ≃ Fin 2)

private theorem alignedExtTwoVertexSupport_source_reindex
    (a : ExtGabrielArrowIndex (K := K) tau) :
    (alignedExtTwoVertexSupport (D.reindex p) tau hNoParallel).source a =
      p ((D.alignedExtTwoVertexSupport tau hNoParallel).source a) := by
  change
    (OpConjecture.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
        (D.reindex p) tau).symm
        (ExtGabrielArrowIndex.source tau a) =
      p ((OpConjecture.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
        D tau).symm (ExtGabrielArrowIndex.source tau a))
  rw [OpConjecture.SplitBasicCoordinateSystem.QuotientCoordinateData.coordinateSimpleIndexEquiv_reindex]
  simp

private theorem alignedExtTwoVertexSupport_target_reindex
    (a : ExtGabrielArrowIndex (K := K) tau) :
    (alignedExtTwoVertexSupport (D.reindex p) tau hNoParallel).target a =
      p ((D.alignedExtTwoVertexSupport tau hNoParallel).target a) := by
  change
    (OpConjecture.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
        (D.reindex p) tau).symm
        (ExtGabrielArrowIndex.target tau a) =
      p ((OpConjecture.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
        D tau).symm (ExtGabrielArrowIndex.target tau a))
  rw [OpConjecture.SplitBasicCoordinateSystem.QuotientCoordinateData.coordinateSimpleIndexEquiv_reindex]
  simp

theorem hasArrow_reindex_iff (i j : Fin 2) :
    (alignedExtTwoVertexSupport (D.reindex p) tau hNoParallel).HasArrow
        (p i) (p j) ↔
      (D.alignedExtTwoVertexSupport tau hNoParallel).HasArrow i j := by
  constructor
  · rintro ⟨a, ha, hb⟩
    refine ⟨a, ?_, ?_⟩
    · apply p.injective
      rw [alignedExtTwoVertexSupport_source_reindex] at ha
      exact ha
    · apply p.injective
      rw [alignedExtTwoVertexSupport_target_reindex] at hb
      exact hb
  · rintro ⟨a, ha, hb⟩
    refine ⟨a, ?_, ?_⟩
    · rw [alignedExtTwoVertexSupport_source_reindex, ha]
    · rw [alignedExtTwoVertexSupport_target_reindex, hb]

theorem hasLoopAt_reindex_iff (i : Fin 2) :
    (alignedExtTwoVertexSupport (D.reindex p) tau hNoParallel).HasLoopAt
        (p i) ↔
      (D.alignedExtTwoVertexSupport tau hNoParallel).HasLoopAt i :=
  hasArrow_reindex_iff D tau hNoParallel p i i

/-- A coordinate permutation carries the one-way-lollipop shape to the
same shape at the renamed vertices. -/
theorem isOneWayLollipopAt_reindex
    {i j : Fin 2}
    (hShape :
      (D.alignedExtTwoVertexSupport tau hNoParallel).IsOneWayLollipopAt i j) :
    (alignedExtTwoVertexSupport (D.reindex p) tau hNoParallel).IsOneWayLollipopAt
      (p i) (p j) := by
  refine ⟨fun h ↦ hShape.1 (p.injective h), ?_, ?_, ?_⟩
  · exact (hasLoopAt_reindex_iff D tau hNoParallel p i).2 hShape.2.1
  · exact fun h ↦ hShape.2.2.1
      ((hasLoopAt_reindex_iff D tau hNoParallel p j).1 h)
  · rcases hShape.2.2.2 with hForward | hBackward
    · left
      exact ⟨
        (hasArrow_reindex_iff D tau hNoParallel p i j).2 hForward.1,
        fun h ↦ hForward.2
          ((hasArrow_reindex_iff D tau hNoParallel p j i).1 h)⟩
    · right
      exact ⟨
        fun h ↦ hBackward.1
          ((hasArrow_reindex_iff D tau hNoParallel p i j).1 h),
        (hasArrow_reindex_iff D tau hNoParallel p j i).2 hBackward.2⟩

private theorem exists_finTwoEquiv_map_distinct_to_zero_one
    {i j : Fin 2} (hij : i ≠ j) :
    ∃ p : Fin 2 ≃ Fin 2, p i = 0 ∧ p j = 1 := by
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact ⟨Equiv.refl _, rfl, rfl⟩
  · exact ⟨Equiv.swap 0 1, by simp, by simp⟩
  · exact (hij rfl).elim

/-- Every one-way lollipop can be reindexed so that its loop is at `0` and
the other vertex is `1`.  After this normalization the cross arrow is
canonically either incoming (`1 → 0`) or outgoing (`0 → 1`). -/
theorem exists_reindex_normalized_oneWayLollipop
    {i j : Fin 2}
    (hShape :
      (D.alignedExtTwoVertexSupport tau hNoParallel).IsOneWayLollipopAt i j) :
    ∃ p : Fin 2 ≃ Fin 2,
      let D' := D.reindex p
      let S' := alignedExtTwoVertexSupport D' tau hNoParallel
      S'.IsOneWayLollipopAt 0 1 ∧
        ((¬ S'.HasArrow 0 1 ∧ S'.HasArrow 1 0) ∨
          (S'.HasArrow 0 1 ∧ ¬ S'.HasArrow 1 0)) := by
  obtain ⟨p, hpi, hpj⟩ :=
    exists_finTwoEquiv_map_distinct_to_zero_one hShape.1
  refine ⟨p, ?_⟩
  let D' := D.reindex p
  let S' := alignedExtTwoVertexSupport D' tau hNoParallel
  have hShape' : S'.IsOneWayLollipopAt (p i) (p j) :=
    isOneWayLollipopAt_reindex D tau hNoParallel p hShape
  have hNormalized : S'.IsOneWayLollipopAt 0 1 := by
    simpa only [hpi, hpj] using hShape'
  refine ⟨hNormalized, ?_⟩
  rcases hNormalized.2.2.2 with hOutgoing | hIncoming
  · exact Or.inr hOutgoing
  · exact Or.inl hIncoming

variable [FiniteDimensional K B]

/-- An arbitrary one-way lollipop is either recognized as a dead/live
model after coordinate normalization, or its normalized cross arrow is the
opposite (outgoing) orientation.  This isolates exactly the remaining
opposite-algebra step. -/
theorem algEquiv_b0_or_b1_or_normalizedOutgoing_of_oneWayLollipop
    [Finite kappa]
    {i j : Fin 2}
    (hShape :
      (D.alignedExtTwoVertexSupport tau hNoParallel).IsOneWayLollipopAt i j)
    (hRingel :
      OpConjecture.IndecomposableSkeleton.FaithfulCore.RingelCoreCardinality
        tau)
    (hRank :
      OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.projectiveRank
        tau = 2)
    (hCore :
      (OpConjecture.IndecomposableSkeleton.FaithfulCore.quotientCore tau :
        Set kappa).ncard = 3) :
    (Nonempty (OpConjecture.LollipopConcrete.B0Model K ≃ₐ[K] B) ∨
      Nonempty (OpConjecture.LollipopConcrete.B1.B1Model K ≃ₐ[K] B)) ∨
      ∃ D' : OpConjecture.QuotientSurvival.TwoCoordinateData
          (K := K) (B := B),
        let S' := alignedExtTwoVertexSupport D' tau hNoParallel
        S'.IsOneWayLollipopAt 0 1 ∧
          S'.HasArrow 0 1 ∧ ¬ S'.HasArrow 1 0 := by
  obtain ⟨p, hNormalized, hDirection⟩ :=
    exists_reindex_normalized_oneWayLollipop
      D tau hNoParallel hShape
  generalize D.reindex p = D' at hNormalized hDirection
  rcases hDirection with hIncoming | hOutgoing
  · left
    exact algEquiv_b0_or_b1_of_incomingOneWayLollipop
      (K := K) (B := B) (kappa := kappa) D' tau
      hNoParallel hNormalized hIncoming hRingel hRank hCore
  · right
    exact ⟨D', hNormalized, hOutgoing⟩

variable [Small.{u} Bᵐᵒᵖ] [IsArtinianRing Bᵐᵒᵖ]

omit [FiniteDimensional K B] [IsArtinianRing Bᵐᵒᵖ] in
/-- The support built from any split-basic realization with the coordinate
simple equivalence is definitionally the aligned Ext support used by the
coordinate recognition theorems. -/
theorem splitBasic_twoVertexSupport_eq_aligned
    (G : OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.SplitBasicExtGabrielArrowRealization.Data
      (K := K) tau) :
    OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.SplitBasicExtGabrielArrowRealization.twoVertexSupport
        tau G
          (OpConjecture.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
            D tau).symm hNoParallel =
      D.alignedExtTwoVertexSupport tau hNoParallel := by
  rfl

end OpConjecture.QuotientSurvival.TwoCoordinateData
