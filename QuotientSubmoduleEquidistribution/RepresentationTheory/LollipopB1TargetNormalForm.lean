import QuotientSubmoduleEquidistribution.RepresentationTheory.LollipopB1ExhaustivenessReduction

noncomputable section

namespace QuotientSubmoduleEquidistribution.LollipopConcrete.B1.ModuleLayer.ExhaustivenessReduction

universe u

variable (K : Type u) [Field K]

namespace SplittingFlag

variable {K}

/-- The coordinates left after removing all stem-active directions. -/
def inactiveTopCoords (D : FiniteB1Rep K) (F : SplittingFlag K D)
    (z : NormalV₁ D F) : JordanCoords D F :=
  (((z.1.1.1.1, z.1.1.1.2), 0), 0)

def inactiveBottomCoords (D : FiniteB1Rep K) (F : SplittingFlag K D)
    (z : NormalV₁ D F) : JordanCoords D F :=
  (((z.2.1.1.1.1.1, 0), z.2.1.1.1.2), 0)

/-- Subtracting the active section leaves exactly the `X/U` top,
`X/W` bottom, and `S1` coordinates. -/
theorem sub_activeEmbed_eq_inactive (D : FiniteB1Rep K)
    (F : SplittingFlag K D) (z : NormalV₁ D F) :
    z - activeEmbed D F (activeProjection D F z) =
      (inactiveTopCoords D F z,
        ((inactiveBottomCoords D F z, z.2.1.2), 0)) := by
  ext <;> simp [activeEmbed, activeProjection, activeTopCoords,
    activeBottomCoords, inactiveTopCoords, inactiveBottomCoords]

theorem inactiveTop_mem_mobile (D : FiniteB1Rep K)
    (F : SplittingFlag K D) (z : NormalV₁ D F) :
    jordanEquivLoopRange D F (inactiveTopCoords D F z) ∈
      mobileBottom K D := by
  rw [← F.x_sup_u]
  apply Submodule.mem_sup.mpr
  refine ⟨z.1.1.1.1.1, z.1.1.1.1.2,
    z.1.1.1.2.1, z.1.1.1.2.2, ?_⟩
  apply Subtype.ext
  rw [jordanEquivLoopRange_apply_coe]
  simp [inactiveTopCoords]

theorem inactiveBottom_mem_killed (D : FiniteB1Rep K)
    (F : SplittingFlag K D) (z : NormalV₁ D F) :
    jordanEquivLoopRange D F (inactiveBottomCoords D F z) ∈
      killedBottom K D := by
  rw [← F.x_sup_w]
  apply Submodule.mem_sup.mpr
  refine ⟨z.2.1.1.1.1.1.1, z.2.1.1.1.1.1.2,
    z.2.1.1.1.2.1, z.2.1.1.1.2.2, ?_⟩
  apply Subtype.ext
  rw [jordanEquivLoopRange_apply_coe]
  simp [inactiveBottomCoords]

/-- The inactive remainder is exactly a vector in the original stem
kernel.  This is the load-bearing section identity needed to prove that the
selected active coordinates hit the whole stem range. -/
theorem normalV₁Equiv_sub_active_mem_stemKernel
    (D : FiniteB1Rep K) (F : SplittingFlag K D)
    (z : NormalV₁ D F) :
    normalV₁Equiv D F
      (z - activeEmbed D F (activeProjection D F z)) ∈
        stemKernel K D := by
  rw [sub_activeEmbed_eq_inactive]
  rw [normalV₁Equiv_apply, kernelEquivLoopKernel_apply_coe]
  let eTop : mobileBottom K D :=
    ⟨jordanEquivLoopRange D F (inactiveTopCoords D F z),
      inactiveTop_mem_mobile D F z⟩
  have htop :
      ((loopTopEquivRange D F).symm (eTop.1 : loopRange K D) : D.V₁) ∈
        stemKernel K D :=
    loopTopEquivRange_symm_mobile_mem_stemKernel D F eTop
  have hbottom :
      (jordanEquivLoopRange D F (inactiveBottomCoords D F z) : D.V₁) ∈
        stemKernel K D := by
    change stemMap K D
      (jordanEquivLoopRange D F (inactiveBottomCoords D F z) : D.V₁) = 0
    exact inactiveBottom_mem_killed D F z
  have hs1 : (z.2.1.2 : D.V₁) ∈ stemKernel K D :=
    s1Space_le_stemKernel D F z.2.1.2.2
  simpa [eTop, inactiveBottomCoords] using
    Submodule.add_mem (stemKernel K D) htop
      (Submodule.add_mem (stemKernel K D) hbottom hs1)

/-- The active stem map has exactly the same range as the original stem. -/
theorem range_activeStem_eq_stemRange
    (D : FiniteB1Rep K) (F : SplittingFlag K D) :
    LinearMap.range ((stemMap K D).comp (activeSource D F)) =
      LinearMap.range (stemMap K D) := by
  apply le_antisymm
  · rintro y ⟨c, rfl⟩
    exact ⟨activeSource D F c, rfl⟩
  · rintro y ⟨v, rfl⟩
    let z : NormalV₁ D F := (normalV₁Equiv D F).symm v
    let c : StemCoords D F := activeProjection D F z
    refine ⟨c, ?_⟩
    have hker := normalV₁Equiv_sub_active_mem_stemKernel D F z
    change stemMap K D
      (normalV₁Equiv D F
        (z - activeEmbed D F (activeProjection D F z))) = 0 at hker
    rw [map_sub, map_sub] at hker
    have hz : normalV₁Equiv D F z = v :=
      (normalV₁Equiv D F).apply_symm_apply v
    change stemMap K D (activeSource D F c) = stemMap K D v
    rw [activeSource_apply]
    rw [← hz]
    exact (sub_eq_zero.mp hker).symm

/-- Active coordinates identify linearly with the full stem range. -/
def stemCoordsEquivStemRange (D : FiniteB1Rep K)
    (F : SplittingFlag K D) :
    StemCoords D F ≃ₗ[K] LinearMap.range (stemMap K D) := by
  let f : StemCoords D F →ₗ[K] LinearMap.range (stemMap K D) :=
    LinearMap.codRestrict (LinearMap.range (stemMap K D))
      ((stemMap K D).comp (activeSource D F))
      (fun c => ⟨activeSource D F c, rfl⟩)
  exact LinearEquiv.ofBijective f ⟨by
    intro c d h
    apply activeStem_injective D F
    exact congrArg Subtype.val h, by
    intro y
    have hy : y.1 ∈ LinearMap.range
        ((stemMap K D).comp (activeSource D F)) := by
      rw [range_activeStem_eq_stemRange D F]
      exact y.2
    rcases hy with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    apply Subtype.ext
    exact hc⟩

/-- Complete target coordinates: the active stem range plus the residual
`S2` tail. -/
abbrev NormalV₂ (D : FiniteB1Rep K) (F : SplittingFlag K D) :=
  StemCoords D F × F.residualTail

def normalV₂Equiv (D : FiniteB1Rep K) (F : SplittingFlag K D) :
    NormalV₂ D F ≃ₗ[K] D.V₂ :=
  (((stemCoordsEquivStemRange D F).prodCongr
      (LinearEquiv.refl K F.residualTail)).trans
    ((LinearMap.range (stemMap K D)).prodEquivOfIsCompl
      F.residualTail F.stemRange_tail_compl))

/-- Stem in normal coordinates. -/
def normalStem (D : FiniteB1Rep K) (F : SplittingFlag K D) :
    NormalV₁ D F →ₗ[K] NormalV₂ D F where
  toFun z := (activeProjection D F z, 0)
  map_add' z w := by ext <;> simp
  map_smul' c z := by ext <;> simp

@[simp] theorem normalV₂Equiv_active_zero (D : FiniteB1Rep K)
    (F : SplittingFlag K D) (c : StemCoords D F) :
    normalV₂Equiv D F (c, 0) =
      stemMap K D (activeSource D F c) := by
  simp [normalV₂Equiv, stemCoordsEquivStemRange]

/-- The two coordinate equivalences conjugate the normal stem to the
original stem. -/
theorem normalV₂Equiv_stem (D : FiniteB1Rep K)
    (F : SplittingFlag K D) (z : NormalV₁ D F) :
    normalV₂Equiv D F (normalStem D F z) =
      stemMap K D (normalV₁Equiv D F z) := by
  have hker := normalV₁Equiv_sub_active_mem_stemKernel D F z
  change stemMap K D
    (normalV₁Equiv D F
      (z - activeEmbed D F (activeProjection D F z))) = 0 at hker
  rw [map_sub, map_sub] at hker
  have hmain := sub_eq_zero.mp hker
  rw [show normalStem D F z = (activeProjection D F z, 0) from rfl]
  rw [normalV₂Equiv_active_zero]
  exact hmain.symm

end SplittingFlag

end QuotientSubmoduleEquidistribution.LollipopConcrete.B1.ModuleLayer.ExhaustivenessReduction
