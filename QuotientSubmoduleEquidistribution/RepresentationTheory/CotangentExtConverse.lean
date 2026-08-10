import QuotientSubmoduleEquidistribution.RepresentationTheory.CoordinateSimpleAlignment

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MulOpposite

namespace QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData

universe u v w

variable {K B : Type u} {I : Type v}
  [Field K] [Ring B] [Algebra K B] [IsArtinianRing B]
  [Fintype I] [DecidableEq I]

variable (D : CoordinateData (K := K) (B := B) (I := I))

/-- A radical element, left-projected to the `i`th vertex, regarded as an
element of the kernel of the canonical vertex-projective quotient. -/
def vertexKernelElementOfJacobian
    (i : I) (z : B) (hz : z ∈ Ring.jacobson B) :
    D.vertexTopKernel i := by
  let e := D.liftedCoordinate i
  let p : QuotientSubmoduleEquidistribution.Tsukamoto.principalRightIdeal e :=
    ⟨op (e * z), by
      rw [show op (e * z) = op z * op e by simp]
      exact (QuotientSubmoduleEquidistribution.Tsukamoto.principalRightIdeal e).mul_mem_left _
        (Ideal.subset_span (Set.mem_singleton (op e)))⟩
  exact ⟨p, by
    change D.coordinateCharacter i (e * z) = 0
    rw [map_mul, D.coordinateCharacter_liftedCoordinate_same]
    simp [D.coordinateCharacter_eq_zero_of_mem_jacobson i hz]⟩

/-- Every map from the `i`th vertex kernel to the `j`th coordinate simple
annihilates the left-projected square of the ring radical. -/
theorem kernelMap_eq_zero_on_jacobson_sq
    (i j : I)
    (f : D.KernelToCoordinateLinearMap i j)
    {z : B} (hz : z ∈ (Ring.jacobson B) ^ 2) :
    f (D.vertexKernelElementOfJacobian i z
      (Ideal.pow_le_self (by omega : (2 : Nat) ≠ 0) hz)) = 0 := by
  letI : Module Bᵐᵒᵖ K := D.coordinateSimpleModule j
  let J := Ring.jacobson B
  have hzMul : z ∈ J * J := by
    have hz' := hz
    rw [show (2 : Nat) = 1 + 1 by omega,
      Ideal.IsTwoSided.pow_add 1 1, Submodule.pow_one] at hz'
    exact hz'
  have hgenerated :
      ∃ hzJ : z ∈ J,
        f (D.vertexKernelElementOfJacobian i z hzJ) = 0 := by
    apply Submodule.smul_induction_on
      (p := fun z ↦ ∃ hzJ : z ∈ J,
        f (D.vertexKernelElementOfJacobian i z hzJ) = 0) hzMul
    · intro r hr s hs
      have hrs : r * s ∈ J := J.mul_mem_right s hr
      refine ⟨hrs, ?_⟩
      let x := D.vertexKernelElementOfJacobian i r hr
      have hsmul :
          D.vertexKernelElementOfJacobian i (r * s) hrs =
            (op s) • x := by
        apply Subtype.ext
        apply Subtype.ext
        simp [vertexKernelElementOfJacobian, x, mul_assoc]
      change f (D.vertexKernelElementOfJacobian i (r * s) hrs) = 0
      rw [hsmul, map_smul]
      exact jacobson_smul_eq_zero_of_simple (B := B)
        (D.coordinateSimple j) (D.coordinateSimple_simple j) hs (f x)
    · intro x y hx hy
      obtain ⟨hxJ, hfx⟩ := hx
      obtain ⟨hyJ, hfy⟩ := hy
      let hxyJ : x + y ∈ J := J.add_mem hxJ hyJ
      refine ⟨hxyJ, ?_⟩
      have hadd :
          D.vertexKernelElementOfJacobian i (x + y) hxyJ =
            D.vertexKernelElementOfJacobian i x hxJ +
              D.vertexKernelElementOfJacobian i y hyJ := by
        apply Subtype.ext
        apply Subtype.ext
        simp [vertexKernelElementOfJacobian, mul_add]
      rw [hadd, map_add, hfx, hfy, add_zero]
  obtain ⟨hzJ, hfz⟩ := hgenerated
  simpa only [Subsingleton.elim hzJ
    (Ideal.pow_le_self (by omega : (2 : Nat) ≠ 0) hz)] using hfz

/-- Projectivity of the vertex middle term makes every degree-one extension
class come from a map out of the vertex kernel.  A nonzero class has a
nonzero such lift. -/
theorem exists_nonzero_kernel_map_of_nontrivial_ext_one
    (i j : I)
    (hExt : Nontrivial
      (Ext (D.coordinateSimple i) (D.coordinateSimple j) 1)) :
    ∃ f : D.KernelToCoordinateLinearMap i j, f ≠ 0 := by
  letI : Module Bᵐᵒᵖ K := D.coordinateSimpleModule j
  letI : Nontrivial
      (Ext (D.coordinateSimple i) (D.coordinateSimple j) 1) := hExt
  letI : Projective (D.vertexPresentation i).X₂ :=
    D.vertexPresentation_projective_middle i
  have hPresentationExt : Nontrivial
      (Ext (D.vertexPresentation i).X₃ (D.coordinateSimple j) 1) := by
    simpa [vertexPresentation, coordinateSimple] using hExt
  letI : Nontrivial
      (Ext (D.vertexPresentation i).X₃ (D.coordinateSimple j) 1) :=
    hPresentationExt
  obtain ⟨xi, hxi⟩ := exists_ne
    (0 : Ext (D.vertexPresentation i).X₃ (D.coordinateSimple j) 1)
  obtain ⟨z, hz⟩ :=
    Ext.contravariant_sequence_exact₃
      (D.vertexPresentation_shortExact i) (D.coordinateSimple j) xi
      (Ext.eq_zero_of_projective _) (add_zero 1)
  let f : D.KernelToCoordinateLinearMap i j :=
    (Ext.addEquiv₀ z).hom
  refine ⟨f, ?_⟩
  intro hf
  apply hxi
  rw [← hz]
  have hfCat : Ext.addEquiv₀ z = 0 := by
    apply ModuleCat.hom_ext
    exact hf
  have hzZero : z = 0 := by
    apply (Ext.linearEquiv₀ (R := K)).injective
    simpa using hfCat
  rw [hzZero]
  simp

/-- Converse cotangent--Ext detection for canonical coordinate simples.  A
nonzero `Ext¹(S_i,S_j)` group, including the loop case `i=j`, yields an
element of `e_i J e_j` which is nonzero modulo `J²`. -/
theorem exists_cross_cotangent_of_nontrivial_ext_one
    (i j : I)
    (hExt : Nontrivial
      (Ext (D.coordinateSimple i) (D.coordinateSimple j) 1)) :
    ∃ r : B,
      r ∈ Ring.jacobson B ∧
        D.liftedCoordinate i * r * D.liftedCoordinate j ∉
          (Ring.jacobson B) ^ 2 := by
  letI : Module Bᵐᵒᵖ K := D.coordinateSimpleModule j
  obtain ⟨f, hf⟩ :=
    D.exists_nonzero_kernel_map_of_nontrivial_ext_one i j hExt
  have hex : ∃ x : D.vertexTopKernel i, f x ≠ 0 := by
    by_contra h
    push Not at h
    apply hf
    ext x
    simpa using h x
  obtain ⟨x, hx⟩ := hex
  let r : B := unop x.1.1
  have hr : r ∈ Ring.jacobson B :=
    D.unop_mem_jacobson_of_mem_vertexTop_ker i x
  refine ⟨r, hr, ?_⟩
  intro hcorner
  have hleftOp :
      x.1.1 * op (D.liftedCoordinate i) = x.1.1 :=
    QuotientSubmoduleEquidistribution.Tsukamoto.mul_op_eq_self_of_mem_principalRightIdeal
      (D.liftedCoordinate_complete.idem i) x.1.property
  have hleft : D.liftedCoordinate i * r = r := by
    simpa [r] using congrArg unop hleftOp
  have hrjSq : r * D.liftedCoordinate j ∈ (Ring.jacobson B) ^ 2 := by
    simpa [hleft, mul_assoc] using hcorner
  have hkill := D.kernelMap_eq_zero_on_jacobson_sq i j f hrjSq
  have hkernelEq :
      D.vertexKernelElementOfJacobian i
          (r * D.liftedCoordinate j)
          (Ideal.pow_le_self (by omega : (2 : Nat) ≠ 0) hrjSq) =
        (op (D.liftedCoordinate j)) • x := by
    apply Subtype.ext
    apply Subtype.ext
    simp [vertexKernelElementOfJacobian, r, mul_assoc, hleftOp]
  rw [hkernelEq, map_smul] at hkill
  have hchar :
      D.coordinateCharacterOp j (op (D.liftedCoordinate j)) = 1 := by
    simp [coordinateCharacterOp]
  change
    D.coordinateCharacterOp j (op (D.liftedCoordinate j)) * f x = 0
      at hkill
  rw [hchar, one_mul] at hkill
  exact hx hkill

section SkeletonAlignment

variable {iota : Type w} [IsNoetherianRing Bᵐᵒᵖ]
  (sigma : IndecomposableSkeleton.{u, w, u} Bᵐᵒᵖ iota)

/-- Every ordered nonzero simple--simple `Ext¹` support pair in an aligned
skeleton has a representative in the corresponding coordinate cotangent
corner. -/
theorem exists_aligned_cross_cotangent_of_nontrivial_ext_one
    (s t : sigma.SimpleIndex)
    (hExt : Nontrivial
      (QuotientSubmoduleEquidistribution.GabrielArrowBridge.ExtOne sigma s t)) :
    let i := (D.coordinateSimpleIndexEquiv sigma).symm s
    let j := (D.coordinateSimpleIndexEquiv sigma).symm t
    ∃ r : B,
      r ∈ Ring.jacobson B ∧
        D.liftedCoordinate i * r * D.liftedCoordinate j ∉
          (Ring.jacobson B) ^ 2 := by
  let i := (D.coordinateSimpleIndexEquiv sigma).symm s
  let j := (D.coordinateSimpleIndexEquiv sigma).symm t
  have hCoordinate : Nontrivial
      (Ext (D.coordinateSimple i) (D.coordinateSimple j) 1) := by
    apply (D.nontrivial_coordinateExtOne_iff_aligned sigma i j).mpr
    simpa [i, j] using hExt
  exact D.exists_cross_cotangent_of_nontrivial_ext_one i j hCoordinate

/-- Support-form Gabriel arrows therefore all admit cotangent
representatives, with the endpoint order preserved by the alignment. -/
theorem exists_aligned_cross_cotangent_of_gabrielArrow
    (a : QuotientSubmoduleEquidistribution.GabrielArrowBridge.GabrielArrowIndex sigma) :
    let i := (D.coordinateSimpleIndexEquiv sigma).symm a.1.1
    let j := (D.coordinateSimpleIndexEquiv sigma).symm a.1.2
    ∃ r : B,
      r ∈ Ring.jacobson B ∧
        D.liftedCoordinate i * r * D.liftedCoordinate j ∉
          (Ring.jacobson B) ^ 2 :=
  D.exists_aligned_cross_cotangent_of_nontrivial_ext_one
    sigma a.1.1 a.1.2 a.2

/-- The same existence theorem indexed by the multiplicity-bearing
Ext-Gabriel arrow type.  No no-parallel hypothesis is needed merely to choose
a representative for each arrow index. -/
theorem exists_aligned_cross_cotangent_of_extGabrielArrow
    (a : QuotientSubmoduleEquidistribution.GabrielArrowBridge.ExtGabrielArrowIndex
      (K := K) sigma) :
    let i := (D.coordinateSimpleIndexEquiv sigma).symm a.1
    let j := (D.coordinateSimpleIndexEquiv sigma).symm a.2.1
    ∃ r : B,
      r ∈ Ring.jacobson B ∧
        D.liftedCoordinate i * r * D.liftedCoordinate j ∉
          (Ring.jacobson B) ^ 2 := by
  let s := a.1
  let t := a.2.1
  have hpos :
      0 < Module.finrank K
        (QuotientSubmoduleEquidistribution.GabrielArrowBridge.ExtOne sigma s t) :=
    by
      have hlt := a.2.2.isLt
      dsimp [s, t] at hlt ⊢
      omega
  letI : Nontrivial
      (QuotientSubmoduleEquidistribution.GabrielArrowBridge.ExtOne sigma s t) :=
    Module.nontrivial_of_finrank_pos hpos
  exact D.exists_aligned_cross_cotangent_of_nontrivial_ext_one
    sigma s t inferInstance

end SkeletonAlignment

end QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData
