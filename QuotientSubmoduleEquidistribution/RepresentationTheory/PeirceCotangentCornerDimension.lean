import QuotientSubmoduleEquidistribution.RepresentationTheory.PeirceCotangentSpanning
import QuotientSubmoduleEquidistribution.RepresentationTheory.CoordinateSimpleAlignment
import QuotientSubmoduleEquidistribution.RepresentationTheory.TwoVertexArrowSupport
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Four-corner control of the Jacobson cotangent space

No bound quiver or module classification occurs here.  The only input is a
split two-coordinate semisimple quotient and finite-dimensional linear
algebra.
-/

noncomputable section

namespace QuotientSubmoduleEquidistribution.QuotientSurvival

universe u v

variable {K B : Type u}
  [Field K] [Ring B] [Algebra K B] [IsArtinianRing B]

private abbrev J (B : Type u) [Ring B] := Ring.jacobson B

namespace TwoCoordinateData

variable (D : TwoCoordinateData (K := K) (B := B))

/-- The image in `B/J²` of the `(i,j)` Peirce corner of `J`. -/
def jacobsonCotangentCornerSubmodule (i j : Fin 2) :
    Submodule K
      (B ⧸ jacobsonSquareSubmodule (K := K) (B := B)) :=
  ((J B : Submodule B B).restrictScalars K).map
    ((jacobsonSquareSubmodule (K := K) (B := B)).mkQ.comp
      (D.peirceLinearMap i j))

/-- Every Peirce corner class is a Jacobson cotangent class. -/
theorem jacobsonCotangentCornerSubmodule_le
    (i j : Fin 2) :
    D.jacobsonCotangentCornerSubmodule i j ≤
      jacobsonCotangentSubmodule (K := K) (B := B) := by
  rintro q ⟨z, hz, rfl⟩
  apply Submodule.mem_map.mpr
  refine ⟨D.liftedCoordinate i * z * D.liftedCoordinate j, ?_, rfl⟩
  exact (J B).mul_mem_right _ ((J B).mul_mem_left _ hz)

/-- The four Peirce corner subspaces span the whole cotangent space. -/
theorem jacobsonCotangentSubmodule_le_fourCorners :
    jacobsonCotangentSubmodule (K := K) (B := B) ≤
      (D.jacobsonCotangentCornerSubmodule 0 0 ⊔
        D.jacobsonCotangentCornerSubmodule 0 1) ⊔
      (D.jacobsonCotangentCornerSubmodule 1 0 ⊔
        D.jacobsonCotangentCornerSubmodule 1 1) := by
  let J2K := jacobsonSquareSubmodule (K := K) (B := B)
  rintro q ⟨z, hz, rfl⟩
  let e0 := D.liftedCoordinate 0
  let e1 := D.liftedCoordinate 1
  have hsum : e0 + e1 = 1 := by
    simpa [e0, e1, Fin.sum_univ_two] using
      D.liftedCoordinate_complete.complete
  have hdecomp :
      z = e0 * z * e0 + e0 * z * e1 +
        (e1 * z * e0 + e1 * z * e1) := by
    calc
      z = (e0 + e1) * z * (e0 + e1) := by rw [hsum]; simp
      _ = e0 * z * e0 + e0 * z * e1 +
          (e1 * z * e0 + e1 * z * e1) := by noncomm_ring
  have h00 : J2K.mkQ (e0 * z * e0) ∈
      D.jacobsonCotangentCornerSubmodule 0 0 := by
    apply Submodule.mem_map.mpr
    exact ⟨z, hz, rfl⟩
  have h01 : J2K.mkQ (e0 * z * e1) ∈
      D.jacobsonCotangentCornerSubmodule 0 1 := by
    apply Submodule.mem_map.mpr
    exact ⟨z, hz, rfl⟩
  have h10 : J2K.mkQ (e1 * z * e0) ∈
      D.jacobsonCotangentCornerSubmodule 1 0 := by
    apply Submodule.mem_map.mpr
    exact ⟨z, hz, rfl⟩
  have h11 : J2K.mkQ (e1 * z * e1) ∈
      D.jacobsonCotangentCornerSubmodule 1 1 := by
    apply Submodule.mem_map.mpr
    exact ⟨z, hz, rfl⟩
  rw [hdecomp, map_add, map_add, map_add]
  have hleft :
      J2K.mkQ (e0 * z * e0) + J2K.mkQ (e0 * z * e1) ∈
        D.jacobsonCotangentCornerSubmodule 0 0 ⊔
          D.jacobsonCotangentCornerSubmodule 0 1 :=
    Submodule.add_mem _ (Submodule.mem_sup_left h00)
      (Submodule.mem_sup_right h01)
  have hright :
      J2K.mkQ (e1 * z * e0) + J2K.mkQ (e1 * z * e1) ∈
        D.jacobsonCotangentCornerSubmodule 1 0 ⊔
          D.jacobsonCotangentCornerSubmodule 1 1 :=
    Submodule.add_mem _ (Submodule.mem_sup_left h10)
      (Submodule.mem_sup_right h11)
  exact Submodule.add_mem _ (Submodule.mem_sup_left hleft)
    (Submodule.mem_sup_right hright)

/-- Exact four-corner spanning identity in `B/J²`. -/
theorem jacobsonCotangentSubmodule_eq_fourCorners :
    jacobsonCotangentSubmodule (K := K) (B := B) =
      (D.jacobsonCotangentCornerSubmodule 0 0 ⊔
        D.jacobsonCotangentCornerSubmodule 0 1) ⊔
      (D.jacobsonCotangentCornerSubmodule 1 0 ⊔
        D.jacobsonCotangentCornerSubmodule 1 1) := by
  apply le_antisymm D.jacobsonCotangentSubmodule_le_fourCorners
  apply sup_le
  · apply sup_le
    · exact jacobsonCotangentCornerSubmodule_le (D := D) 0 0
    · exact jacobsonCotangentCornerSubmodule_le (D := D) 0 1
  · apply sup_le
    · exact jacobsonCotangentCornerSubmodule_le (D := D) 1 0
    · exact jacobsonCotangentCornerSubmodule_le (D := D) 1 1

/-- Global cotangent dimension is bounded by the sum of the four Peirce
corner dimensions. -/
theorem finrank_jacobsonCotangentSubmodule_le_sum_corners
    [FiniteDimensional K B] :
    Module.finrank K
        (jacobsonCotangentSubmodule (K := K) (B := B)) ≤
      (Module.finrank K (D.jacobsonCotangentCornerSubmodule 0 0) +
        Module.finrank K (D.jacobsonCotangentCornerSubmodule 0 1)) +
      (Module.finrank K (D.jacobsonCotangentCornerSubmodule 1 0) +
        Module.finrank K (D.jacobsonCotangentCornerSubmodule 1 1)) := by
  rw [D.jacobsonCotangentSubmodule_eq_fourCorners]
  exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans
    (Nat.add_le_add
      (Submodule.finrank_add_le_finrank_add_finrank _ _)
      (Submodule.finrank_add_le_finrank_add_finrank _ _))

/-- The loop--two-cycle local bounds `(1,1,1,0)` imply the single global
dimension premise consumed by `PeirceCotangentSpanning`. -/
theorem cotangentDimensionAtMostThree_of_corner_bounds
    [FiniteDimensional K B]
    (h00 : Module.finrank K
      (D.jacobsonCotangentCornerSubmodule 0 0) ≤ 1)
    (h01 : Module.finrank K
      (D.jacobsonCotangentCornerSubmodule 0 1) ≤ 1)
    (h10 : Module.finrank K
      (D.jacobsonCotangentCornerSubmodule 1 0) ≤ 1)
    (h11 : Module.finrank K
      (D.jacobsonCotangentCornerSubmodule 1 1) = 0) :
    CotangentDimensionAtMostThree (K := K) (B := B) := by
  have hglobal := D.finrank_jacobsonCotangentSubmodule_le_sum_corners
  dsimp only [CotangentDimensionAtMostThree]
  omega

/-! ## Exact missing comparison with the maintained Ext support -/

open QuotientSubmoduleEquidistribution.GabrielArrowBridge

variable {kappa : Type v}
  [Small.{u} Bᵐᵒᵖ] [IsNoetherianRing Bᵐᵒᵖ]
  [IsArtinianRing Bᵐᵒᵖ] [Finite kappa]
  (tau : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, v, u} Bᵐᵒᵖ kappa)

/-- The missing ring-to-category comparison, stated only at the dimension
level needed here.  `ProjectiveRadicalExt` already identifies `Ext¹` with
maps from the first radical layer of the coordinate projective; what is not
yet maintained is the comparison of that layer with the Peirce quotient
`eᵢJeⱼ/eᵢJ²eⱼ`. -/
def CotangentCornerFinrankControlledByAlignedExt : Prop :=
  ∀ i j : Fin 2,
    Module.finrank K (D.jacobsonCotangentCornerSubmodule i j) ≤
      Module.finrank K
        (ExtOne tau
          (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
            D tau i)
          (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
            D tau j))

/-- Literal multiplicity-bearing Ext-Gabriel loop at coordinate `i`. -/
def HasAlignedExtGabrielLoopAt (i : Fin 2) : Prop :=
  ∃ a : ExtGabrielArrowIndex (K := K) tau,
    ExtGabrielArrowIndex.source tau a =
        QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
          D tau i ∧
      ExtGabrielArrowIndex.target tau a =
        QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
          D tau i

/-- The multiplicity-bearing Ext-Gabriel support, relabelled by the two
split coordinates. -/
def alignedExtTwoVertexSupport
    (hNoParallel : NoParallelExtSupport (K := K) tau) :
    QuotientSubmoduleEquidistribution.TwoVertexArrowSupport.Data
      (ExtGabrielArrowIndex (K := K) tau) where
  source a :=
    (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
      D tau).symm (ExtGabrielArrowIndex.source tau a)
  target a :=
    (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
      D tau).symm (ExtGabrielArrowIndex.target tau a)
  pair_injective := by
    intro a b hab
    apply ExtGabrielArrowIndex.source_target_injective tau hNoParallel
    apply Prod.ext
    · exact
        (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
          D tau).symm.injective (congrArg Prod.fst hab)
    · exact
        (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
          D tau).symm.injective (congrArg Prod.snd hab)

omit [IsArtinianRing Bᵐᵒᵖ] [Finite kappa] in
/-- What the maintained cotangent-to-Ext detector already proves: an empty
off-diagonal Ext-support pair has zero Peirce cotangent corner.  This is only
qualitative and requires distinct vertices; it gives neither the occupied
corner upper bounds nor the absent diagonal-loop bound needed below. -/
theorem jacobsonCotangentCornerSubmodule_eq_bot_of_crossExt_trivial
    {i j : Fin 2} (hij : i ≠ j)
    (hExt : ¬ Nontrivial
      (ExtOne tau
        (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
          D tau i)
        (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
          D tau j))) :
    D.jacobsonCotangentCornerSubmodule i j = ⊥ := by
  apply (Submodule.eq_bot_iff
    (D.jacobsonCotangentCornerSubmodule i j)).mpr
  rintro q ⟨z, hz, rfl⟩
  apply (Submodule.Quotient.mk_eq_zero
    (jacobsonSquareSubmodule (K := K) (B := B))).mpr
  by_contra hcorner
  apply hExt
  exact
    QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.nontrivial_aligned_ext_one_of_cross_cotangent
      D tau hij hz hcorner

omit [IsArtinianRing Bᵐᵒᵖ] [Finite kappa] in
/-- Once the missing Peirce-layer comparison is supplied, no-parallelness
bounds all four corner dimensions by one.  Vanishing of the unused diagonal
`Ext¹` corner then gives the required `(1,1,1,0)` bounds. -/
theorem cotangentDimensionAtMostThree_of_cornerExtControl
    [FiniteDimensional K B]
    (hcontrol : D.CotangentCornerFinrankControlledByAlignedExt tau)
    (hNoParallel : NoParallelExtSupport (K := K) tau)
    (h11zero : Module.finrank K
      (ExtOne tau
        (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
          D tau 1)
        (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
          D tau 1)) = 0) :
    CotangentDimensionAtMostThree (K := K) (B := B) := by
  apply D.cotangentDimensionAtMostThree_of_corner_bounds
  · exact (hcontrol 0 0).trans
      (hNoParallel
        (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
          D tau 0)
        (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
          D tau 0)).2
  · exact (hcontrol 0 1).trans
      (hNoParallel
        (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
          D tau 0)
        (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
          D tau 1)).2
  · exact (hcontrol 1 0).trans
      (hNoParallel
        (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
          D tau 1)
        (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
          D tau 0)).2
  · have hle := hcontrol 1 1
    omega

omit [IsArtinianRing Bᵐᵒᵖ] [Finite kappa] in
/-- Support-form version: absence of the second diagonal Ext loop supplies
the zero fourth corner.  In the maintained multiplicity-bearing Gabriel
support this absence is exactly the `¬ HasLoopAt 1` field of the
loop--two-cycle branch. -/
theorem cotangentDimensionAtMostThree_of_cornerExtControl_of_no_second_loop
    [FiniteDimensional K B]
    (hcontrol : D.CotangentCornerFinrankControlledByAlignedExt tau)
    (hNoParallel : NoParallelExtSupport (K := K) tau)
    (hNoSecondLoop : ¬ Nontrivial
      (ExtOne tau
        (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
          D tau 1)
        (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
          D tau 1))) :
    CotangentDimensionAtMostThree (K := K) (B := B) := by
  apply D.cotangentDimensionAtMostThree_of_cornerExtControl tau
    hcontrol hNoParallel
  let E := ExtOne tau
    (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
      D tau 1)
    (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
      D tau 1)
  letI : FiniteDimensional K E :=
    (hNoParallel
      (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
        D tau 1)
      (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
        D tau 1)).1
  by_contra hne
  have hpos : 0 < Module.finrank K E := Nat.pos_of_ne_zero hne
  letI : Nontrivial E := Module.nontrivial_of_finrank_pos hpos
  exact hNoSecondLoop inferInstance

omit [IsArtinianRing Bᵐᵒᵖ] [Finite kappa] in
/-- Literal Ext-Gabriel support version.  No arrow at `(1,1)` forces the
aligned diagonal `Ext¹` space to vanish; combined with no-parallelness and
the missing corner comparison, this gives the global dimension bound. -/
theorem cotangentDimensionAtMostThree_of_cornerExtControl_of_no_second_gabrielLoop
    [FiniteDimensional K B]
    (hcontrol : D.CotangentCornerFinrankControlledByAlignedExt tau)
    (hNoParallel : NoParallelExtSupport (K := K) tau)
    (hNoSecondLoop : ¬ D.HasAlignedExtGabrielLoopAt tau 1) :
    CotangentDimensionAtMostThree (K := K) (B := B) := by
  apply D.cotangentDimensionAtMostThree_of_cornerExtControl_of_no_second_loop
    tau hcontrol hNoParallel
  intro hNontrivial
  let s :=
    QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
      D tau 1
  letI : FiniteDimensional K (ExtOne tau s s) :=
    (hNoParallel s s).1
  letI : Nontrivial (ExtOne tau s s) := hNontrivial
  let a : ExtGabrielArrowIndex (K := K) tau :=
    ⟨s, s, ⟨0, Module.finrank_pos⟩⟩
  apply hNoSecondLoop
  refine ⟨a, ?_, ?_⟩
  · rfl
  · rfl

omit [IsArtinianRing Bᵐᵒᵖ] [Finite kappa] in
/-- Exact loop--two-cycle support wrapper.  The support shape supplies the
missing diagonal vanishing, while no-parallelness supplies the three local
upper bounds after the sole Peirce-layer comparison premise. -/
theorem cotangentDimensionAtMostThree_of_loopTwoCycleSupport
    [FiniteDimensional K B]
    (hcontrol : D.CotangentCornerFinrankControlledByAlignedExt tau)
    (hNoParallel : NoParallelExtSupport (K := K) tau)
    (hShape :
      (D.alignedExtTwoVertexSupport tau hNoParallel).IsLoopTwoCycleAt 0 1) :
    CotangentDimensionAtMostThree (K := K) (B := B) := by
  apply
    D.cotangentDimensionAtMostThree_of_cornerExtControl_of_no_second_gabrielLoop
      tau hcontrol hNoParallel
  intro hLoop
  apply hShape.2.2.1
  rcases hLoop with ⟨a, haSource, haTarget⟩
  refine ⟨a, ?_, ?_⟩
  · change
      (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
        D tau).symm (ExtGabrielArrowIndex.source tau a) = 1
    rw [haSource]
    exact Equiv.symm_apply_apply _ 1
  · change
      (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
        D tau).symm (ExtGabrielArrowIndex.target tau a) = 1
    rw [haTarget]
    exact Equiv.symm_apply_apply _ 1

end TwoCoordinateData

end QuotientSubmoduleEquidistribution.QuotientSurvival
