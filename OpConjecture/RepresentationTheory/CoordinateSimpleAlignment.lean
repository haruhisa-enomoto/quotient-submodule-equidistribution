import OpConjecture.RepresentationTheory.CotangentExtBridge
import OpConjecture.RepresentationTheory.SimpleLevels
import OpConjecture.RepresentationTheory.TwoVertexGabrielConnectedness

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MulOpposite

namespace OpConjecture.CotangentExtBridge.CoordinateData

universe u v w

variable {K B : Type u} {I : Type v}
  [Field K] [Ring B] [Algebra K B] [IsArtinianRing B]
  [Fintype I] [DecidableEq I]

variable (D : CoordinateData (K := K) (B := B) (I := I))

/-- The opposite of an element of the Jacobson radical acts through the
Jacobson radical of the opposite ring. -/
theorem op_mem_jacobson_of_mem_jacobson
    {x : B} (hx : x ∈ Ring.jacobson B) :
    op x ∈ Ring.jacobson Bᵐᵒᵖ := by
  rw [← Ideal.jacobson_bot]
  rw [Ideal.mem_jacobson_iff]
  intro y
  have hnilJ : IsNilpotent (Ring.jacobson B) := by
    simpa only [Ideal.jacobson_bot] using
      (IsArtinianRing.isNilpotent_jacobson_bot (R := B))
  obtain ⟨n, hn⟩ := hnilJ
  have hxyJ : x * unop y ∈ Ring.jacobson B :=
    (Ring.jacobson B).mul_mem_right _ hx
  have hpowJ : (x * unop y) ^ n ∈ (Ring.jacobson B) ^ n :=
    Ideal.pow_mem_pow hxyJ n
  have hpowBase : (x * unop y) ^ n = 0 := by
    rw [hn] at hpowJ
    simpa using hpowJ
  have hpow : (y * op x) ^ n = 0 := by
    change (op (x * unop y)) ^ n = 0
    simpa using congrArg op hpowBase
  have hnil : IsNilpotent (y * op x) := ⟨n, hpow⟩
  let U : (Bᵐᵒᵖ)ˣ := hnil.isUnit_add_one.unit
  refine ⟨↑U⁻¹, ?_⟩
  rw [Submodule.mem_bot]
  calc
    ↑U⁻¹ * y * op x + ↑U⁻¹ - 1 =
        ↑U⁻¹ * (y * op x + 1) - 1 := by
          simp [mul_add, mul_assoc]
    _ = ↑U⁻¹ * ↑U - 1 := by
          rw [hnil.isUnit_add_one.unit_spec]
    _ = 0 := by simp

/-- The Jacobson radical of `B` annihilates every simple right `B`-module. -/
theorem jacobson_smul_eq_zero_of_simple
    (S : ModuleCat.{u} Bᵐᵒᵖ) (hS : Simple S)
    {x : B} (hx : x ∈ Ring.jacobson B) (s : S) :
    op x • s = 0 := by
  letI : Simple S := hS
  letI : IsSimpleModule Bᵐᵒᵖ S :=
    isSimpleModule_of_simple S
  have hxop : op x ∈ Ring.jacobson Bᵐᵒᵖ :=
    op_mem_jacobson_of_mem_jacobson (B := B) hx
  exact Module.mem_annihilator.mp
    (IsSemisimpleModule.jacobson_le_annihilator Bᵐᵒᵖ S hxop) s

/-- Right multiplication by a lifted coordinate agrees modulo the radical
with multiplication by the corresponding scalar coordinate. -/
theorem liftedCoordinate_mul_sub_coordinate_mem_jacobson
    (i : I) (b : B) :
    D.liftedCoordinate i * b -
        D.liftedCoordinate i *
          algebraMap K B (D.coordinateCharacter i b) ∈
      Ring.jacobson B := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply D.quotientEquiv.injective
  simp only [map_sub, map_mul, map_zero,
    OpConjecture.SplitBasicCoordinateSystem.QuotientCoordinateData.quotient_mk_liftedCoordinate]
  simp only [OpConjecture.SplitBasicCoordinateSystem.QuotientCoordinateData.quotientCoordinate,
    D.quotientEquiv.apply_symm_apply]
  ext k
  by_cases hki : k = i
  · subst k
    simp [coordinateCharacter]
  · simp [hki]

/-- A vector fixed by one lifted coordinate gives a nonzero morphism from
the corresponding coordinate simple. -/
def coordinateSimpleToFixedVector
    (S : ModuleCat.{u} Bᵐᵒᵖ) (hS : Simple S)
    (i : I) (s : S)
    (hfixed : op (D.liftedCoordinate i) • s = s) :
    D.coordinateSimple i ⟶ S := by
  letI : Simple S := hS
  letI : Module Bᵐᵒᵖ K := D.coordinateSimpleModule i
  exact ModuleCat.ofHom
    { toFun := fun k ↦ op (algebraMap K B k) • s
      map_add' := fun k l ↦ by simp [add_smul]
      map_smul' := fun b k ↦ by
        let e := D.liftedCoordinate i
        let q := D.coordinateCharacter i (unop b)
        have hrad :
            e * unop b - e * algebraMap K B q ∈ Ring.jacobson B := by
          simpa [e, q] using
            D.liftedCoordinate_mul_sub_coordinate_mem_jacobson i (unop b)
        have hradZero :
            op (e * unop b - e * algebraMap K B q) • s = 0 :=
          jacobson_smul_eq_zero_of_simple (B := B) S hS hrad s
        change
          op (algebraMap K B (q * k)) • s =
            b • op (algebraMap K B k) • s
        let a := algebraMap K B k
        let c := algebraMap K B q
        have hcommK (a : B) (k : K) :
            a * algebraMap K B k = algebraMap K B k * a :=
          (Algebra.commutes k a).symm
        have hact (z : B) : op z • s = op (e * z) • s := by
          calc
            op z • s = op z • (op e • s) := by rw [hfixed]
            _ = op (e * z) • s := by
              rw [← mul_smul, ← op_mul]
        have hradEq :
            op (e * unop b) • s = op (e * c) • s := by
          rw [MulOpposite.op_sub, sub_smul, sub_eq_zero] at hradZero
          exact hradZero
        calc
          op (algebraMap K B (q * k)) • s =
              op (e * (c * a)) • s := by
            rw [map_mul]
            exact hact (c * a)
          _ = op ((e * c) * a) • s := by rw [mul_assoc]
          _ = op a • (op (e * c) • s) := by
            rw [← mul_smul, ← op_mul]
          _ = op a • (op (e * unop b) • s) := by rw [hradEq]
          _ = op ((e * unop b) * a) • s := by
            rw [← mul_smul, ← op_mul]
          _ = op (e * (a * unop b)) • s := by
            rw [mul_assoc, hcommK (unop b) k]
          _ = op (a * unop b) • s := (hact (a * unop b)).symm
          _ = b • op a • s := by
            rw [show b = op (unop b) by simp, ← mul_smul, ← op_mul]
            simp }

/-- Every simple right module over a split basic Artinian algebra is one of
the canonical coordinate simples. -/
theorem coordinateSimple_complete
    (S : ModuleCat.{u} Bᵐᵒᵖ) (hS : Simple S) :
    ∃ i : I, Nonempty (S ≅ D.coordinateSimple i) := by
  classical
  letI : Simple S := hS
  letI : IsSimpleModule Bᵐᵒᵖ S :=
    isSimpleModule_of_simple S
  letI : Nontrivial S := IsSimpleModule.nontrivial Bᵐᵒᵖ S
  obtain ⟨s, hs⟩ := exists_ne (0 : S)
  have hsum :
      ∑ i : I, op (D.liftedCoordinate i) • s = s := by
    calc
      ∑ i : I, op (D.liftedCoordinate i) • s =
          (∑ i : I, op (D.liftedCoordinate i)) • s :=
        Finset.sum_smul.symm
      _ = op (∑ i : I, D.liftedCoordinate i) • s := by
        have hopSum :=
          map_sum (MulOpposite.opAddEquiv : B ≃+ Bᵐᵒᵖ)
            (fun i : I ↦ D.liftedCoordinate i) Finset.univ
        exact congrArg (fun z : Bᵐᵒᵖ ↦ z • s) hopSum.symm
      _ = s := by
        rw [D.liftedCoordinate_complete.complete]
        simp
  have hex : ∃ i : I, op (D.liftedCoordinate i) • s ≠ 0 := by
    by_contra h
    push Not at h
    have hz : ∑ i : I, op (D.liftedCoordinate i) • s = 0 :=
      Finset.sum_eq_zero (fun i _ ↦ h i)
    exact hs (hsum ▸ hz)
  obtain ⟨i, hi⟩ := hex
  let t : S := op (D.liftedCoordinate i) • s
  have ht : t ≠ 0 := hi
  have hfixed : op (D.liftedCoordinate i) • t = t := by
    dsimp only [t]
    rw [← mul_smul, ← op_mul,
      D.liftedCoordinate_complete.idem i]
  let f : D.coordinateSimple i ⟶ S :=
    D.coordinateSimpleToFixedVector S hS i t hfixed
  have hf : f ≠ 0 := by
    intro hf
    have happly := congrArg (fun g : D.coordinateSimple i ⟶ S ↦ g (1 : K)) hf
    change op (algebraMap K B 1) • t = 0 at happly
    exact ht (by simpa using happly)
  letI : Simple (D.coordinateSimple i) := D.coordinateSimple_simple i
  haveI : IsIso f := isIso_of_hom_simple hf
  exact ⟨i, ⟨(asIso f).symm⟩⟩

/-- Existence and uniqueness of the coordinate label of a simple module. -/
theorem existsUnique_coordinateSimple
    (S : ModuleCat.{u} Bᵐᵒᵖ) (hS : Simple S) :
    ∃! i : I, Nonempty (S ≅ D.coordinateSimple i) := by
  obtain ⟨i, hi⟩ := D.coordinateSimple_complete S hS
  refine ⟨i, hi, ?_⟩
  intro j hj
  obtain ⟨ei⟩ := hi
  obtain ⟨ej⟩ := hj
  by_contra hij
  exact (D.coordinateSimple_not_iso hij).false
    (ej.symm ≪≫ ei)

/-! ## Alignment with an arbitrary complete indecomposable skeleton -/

section SkeletonAlignment

variable {iota : Type w} [IsNoetherianRing Bᵐᵒᵖ]
  (sigma : IndecomposableSkeleton.{u, w, u} Bᵐᵒᵖ iota)

/-- The coordinate simple bundled as a finitely generated right module. -/
def coordinateSimpleFG (i : I) : FGModuleCat.{u} Bᵐᵒᵖ := by
  letI : Module Bᵐᵒᵖ K := D.coordinateSimpleModule i
  letI : Module.Finite Bᵐᵒᵖ K := D.coordinateSimple_moduleFinite i
  exact FGModuleCat.of Bᵐᵒᵖ K

omit [IsArtinianRing B] [Fintype I] [DecidableEq I]
    [IsNoetherianRing Bᵐᵒᵖ] in
theorem coordinateSimpleFG_isSimpleModule (i : I) :
    IsSimpleModule Bᵐᵒᵖ (D.coordinateSimpleFG i) := by
  letI : Module Bᵐᵒᵖ K := D.coordinateSimpleModule i
  change IsSimpleModule Bᵐᵒᵖ K
  exact D.coordinateSimple_isSimpleModule i

omit [IsArtinianRing B] [Fintype I] [DecidableEq I] in
theorem coordinateSimpleFG_simple (i : I) :
    Simple (D.coordinateSimpleFG i) :=
  (IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).mpr
    (D.coordinateSimpleFG_isSimpleModule i)

omit [IsArtinianRing B] [Fintype I] [DecidableEq I]
    [IsNoetherianRing Bᵐᵒᵖ] in
theorem coordinateSimpleFG_indecomposable (i : I) :
    OpConjecture.Foundation.IsIndecomposableModule Bᵐᵒᵖ (D.coordinateSimpleFG i) := by
  letI : IsSimpleModule Bᵐᵒᵖ (D.coordinateSimpleFG i) :=
    D.coordinateSimpleFG_isSimpleModule i
  exact OpConjecture.Foundation.IsSimpleModule.isIndecomposableModule

/-- Forgetting finite generation recovers the original coordinate simple. -/
def coordinateSimpleFGForgetIso (i : I) :
    (forget₂ (FGModuleCat.{u} Bᵐᵒᵖ) (ModuleCat.{u} Bᵐᵒᵖ)).obj
        (D.coordinateSimpleFG i) ≅
      D.coordinateSimple i :=
  Iso.refl _

/-- The unique skeleton index representing a coordinate simple. -/
def coordinateSkeletonIndex (i : I) : iota :=
  (sigma.complete (D.coordinateSimpleFG i)
    (D.coordinateSimpleFG_indecomposable i)).choose

/-- The chosen coordinate simple isomorphism to its skeleton representative. -/
def coordinateSimpleFGIsoSkeleton (i : I) :
    D.coordinateSimpleFG i ≅ sigma.obj (D.coordinateSkeletonIndex sigma i) :=
  (sigma.complete (D.coordinateSimpleFG i)
    (D.coordinateSimpleFG_indecomposable i)).choose_spec.some

/-- The coordinate label viewed as a simple index of the chosen skeleton. -/
def coordinateSimpleIndex (i : I) : sigma.SimpleIndex :=
  ⟨D.coordinateSkeletonIndex sigma i,
    (Simple.iff_of_iso (D.coordinateSimpleFGIsoSkeleton sigma i)).mp
      (D.coordinateSimpleFG_simple i)⟩

theorem coordinateSimpleIndex_injective :
    Function.Injective (D.coordinateSimpleIndex sigma) := by
  intro i j hij
  have hindex :
      D.coordinateSkeletonIndex sigma i =
        D.coordinateSkeletonIndex sigma j :=
    congrArg Subtype.val hij
  let eFG : D.coordinateSimpleFG i ≅ D.coordinateSimpleFG j :=
    D.coordinateSimpleFGIsoSkeleton sigma i ≪≫
      eqToIso (congrArg sigma.obj hindex) ≪≫
      (D.coordinateSimpleFGIsoSkeleton sigma j).symm
  let F := forget₂ (FGModuleCat.{u} Bᵐᵒᵖ) (ModuleCat.{u} Bᵐᵒᵖ)
  let e : D.coordinateSimple i ≅ D.coordinateSimple j :=
    (D.coordinateSimpleFGForgetIso i).symm ≪≫
      F.mapIso eFG ≪≫
      D.coordinateSimpleFGForgetIso j
  by_contra hne
  exact (D.coordinateSimple_not_iso hne).false e

theorem coordinateSimpleIndex_surjective :
    Function.Surjective (D.coordinateSimpleIndex sigma) := by
  intro s
  let F := forget₂ (FGModuleCat.{u} Bᵐᵒᵖ) (ModuleCat.{u} Bᵐᵒᵖ)
  have hSM : IsSimpleModule Bᵐᵒᵖ (sigma.obj s.1) :=
    (IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).mp s.2
  have hS : Simple (F.obj (sigma.obj s.1)) :=
    (simple_iff_isSimpleModule' _).mpr hSM
  obtain ⟨i, ⟨e⟩⟩ := D.coordinateSimple_complete (F.obj (sigma.obj s.1)) hS
  let eFG : sigma.obj s.1 ≅ D.coordinateSimpleFG i :=
    F.preimageIso (e ≪≫ (D.coordinateSimpleFGForgetIso i).symm)
  have hidx : D.coordinateSkeletonIndex sigma i = s.1 :=
    sigma.eq_of_iso ⟨
      (D.coordinateSimpleFGIsoSkeleton sigma i).symm ≪≫ eFG.symm⟩
  refine ⟨i, Subtype.ext ?_⟩
  exact hidx

/-- The explicit coordinate-to-simple-skeleton alignment equivalence. -/
def coordinateSimpleIndexEquiv : I ≃ sigma.SimpleIndex :=
  Equiv.ofBijective (D.coordinateSimpleIndex sigma)
    ⟨D.coordinateSimpleIndex_injective sigma,
      D.coordinateSimpleIndex_surjective sigma⟩

/-- The explicit finitely generated module isomorphism attached to a
coordinate label under the alignment equivalence. -/
def coordinateSimpleFGIsoAligned (i : I) :
    D.coordinateSimpleFG i ≅
      sigma.obj ((D.coordinateSimpleIndexEquiv sigma) i).1 :=
  D.coordinateSimpleFGIsoSkeleton sigma i

/-- The inverse alignment also carries an explicit module isomorphism. -/
def alignedSimpleFGIso (s : sigma.SimpleIndex) :
    D.coordinateSimpleFG ((D.coordinateSimpleIndexEquiv sigma).symm s) ≅
      sigma.obj s.1 :=
  D.coordinateSimpleFGIsoSkeleton sigma
      ((D.coordinateSimpleIndexEquiv sigma).symm s) ≪≫
    eqToIso (congrArg (fun t : sigma.SimpleIndex ↦ sigma.obj t.1)
      ((D.coordinateSimpleIndexEquiv sigma).apply_symm_apply s))

/-- The module-category isomorphism from a coordinate simple to its aligned
simple skeleton representative. -/
def coordinateSimpleIsoAligned (i : I) :
    D.coordinateSimple i ≅
      ModuleCat.of Bᵐᵒᵖ
        (sigma.obj ((D.coordinateSimpleIndexEquiv sigma) i).1) := by
  let F := forget₂ (FGModuleCat.{u} Bᵐᵒᵖ) (ModuleCat.{u} Bᵐᵒᵖ)
  exact
    (D.coordinateSimpleFGForgetIso i).symm ≪≫
      F.mapIso (D.coordinateSimpleFGIsoAligned sigma i)

/-- Ext in degree one is invariant under the explicit coordinate-to-skeleton
alignment, with the ordered pair of arguments unchanged. -/
def coordinateExtOneIsoAligned (i j : I) :
    AddCommGrpCat.of
        (Ext (D.coordinateSimple i) (D.coordinateSimple j) 1) ≅
      AddCommGrpCat.of
        (OpConjecture.GabrielArrowBridge.ExtOne sigma
          ((D.coordinateSimpleIndexEquiv sigma) i)
          ((D.coordinateSimpleIndexEquiv sigma) j)) := by
  let eᵢ := D.coordinateSimpleIsoAligned sigma i
  let eⱼ := D.coordinateSimpleIsoAligned sigma j
  exact
    ((Abelian.extFunctor 1).mapIso eᵢ.symm.op).app
        (D.coordinateSimple j) ≪≫
      ((Abelian.extFunctor 1).obj
        (Opposite.op
          (ModuleCat.of Bᵐᵒᵖ
            (sigma.obj ((D.coordinateSimpleIndexEquiv sigma) i).1)))).mapIso eⱼ

/-- Nonvanishing of `Ext¹` is preserved and reflected by the explicit
coordinate-to-skeleton alignment. -/
theorem nontrivial_coordinateExtOne_iff_aligned (i j : I) :
    Nontrivial (Ext (D.coordinateSimple i) (D.coordinateSimple j) 1) ↔
      Nontrivial
        (OpConjecture.GabrielArrowBridge.ExtOne sigma
          ((D.coordinateSimpleIndexEquiv sigma) i)
          ((D.coordinateSimpleIndexEquiv sigma) j)) := by
  let e := D.coordinateExtOneIsoAligned sigma i j
  let ee :
      Ext (D.coordinateSimple i) (D.coordinateSimple j) 1 ≃
        OpConjecture.GabrielArrowBridge.ExtOne sigma
          ((D.coordinateSimpleIndexEquiv sigma) i)
          ((D.coordinateSimpleIndexEquiv sigma) j) :=
    Equiv.ofBijective e.hom
      (ConcreteCategory.bijective_of_isIso e.hom)
  constructor
  · intro h
    letI : Nontrivial (Ext (D.coordinateSimple i) (D.coordinateSimple j) 1) := h
    exact ee.symm.nontrivial
  · intro h
    letI : Nontrivial
        (OpConjecture.GabrielArrowBridge.ExtOne sigma
          ((D.coordinateSimpleIndexEquiv sigma) i)
          ((D.coordinateSimpleIndexEquiv sigma) j)) := h
    exact ee.nontrivial

/-- A nonzero ordered cross-cotangent class gives the ordered nonzero
`Ext¹` group between the aligned simple skeleton labels. -/
theorem nontrivial_aligned_ext_one_of_cross_cotangent
    {i j : I} (hij : i ≠ j) {r : B}
    (hr : r ∈ Ring.jacobson B)
    (hcorner :
      D.liftedCoordinate i * r * D.liftedCoordinate j ∉
        (Ring.jacobson B) ^ 2) :
    Nontrivial
      (OpConjecture.GabrielArrowBridge.ExtOne sigma
        ((D.coordinateSimpleIndexEquiv sigma) i)
        ((D.coordinateSimpleIndexEquiv sigma) j)) :=
  (D.nontrivial_coordinateExtOne_iff_aligned sigma i j).mp
    (D.nontrivial_ext_one_of_cross_cotangent hij hr hcorner)

/-- For two coordinates, exhaustion and Ext transport discharge the entire
Peirce-to-skeleton detection interface used by the connectedness argument. -/
def twoVertexPeirceExtData
    [Finite iota]
    (D : CoordinateData (K := K) (B := B) (I := Fin 2))
    (sigma : IndecomposableSkeleton.{u, w, u} Bᵐᵒᵖ iota) :
    OpConjecture.TwoVertexGabrielConnectedness.TwoVertexPeirceExtData
      (Peirce := B) sigma (D.coordinateSimpleIndexEquiv sigma).symm where
  vertexZero := D.liftedCoordinate 0
  vertexZero_idempotent := D.liftedCoordinate_complete.idem 0
  vertexZero_ne_zero := D.liftedCoordinate_ne_zero 0
  vertexZero_ne_one :=
    D.liftedCoordinate_ne_one_of_exists_ne 0 ⟨1, by decide⟩
  forward_mem_jacobson := D.coordinate_complement_mem_jacobson 0
  backward_mem_jacobson := D.complement_coordinate_mem_jacobson 0
  crossExt_of_crossCotangent := by
    have hsum :
        D.liftedCoordinate 0 + D.liftedCoordinate 1 = 1 := by
      simpa [Fin.sum_univ_two] using D.liftedCoordinate_complete.complete
    have hcomp : 1 - D.liftedCoordinate 0 = D.liftedCoordinate 1 := by
      rw [← hsum]
      noncomm_ring
    intro hcross
    rcases hcross with hforward | hbackward
    · left
      obtain ⟨r, hr, hcorner⟩ := hforward
      have hExt :=
        D.nontrivial_aligned_ext_one_of_cross_cotangent sigma
          (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide)
          hr (by simpa [hcomp] using hcorner)
      simpa [OpConjecture.TwoVertexGabrielConnectedness.HasCrossExt] using hExt
    · right
      obtain ⟨r, hr, hcorner⟩ := hbackward
      have hExt :=
        D.nontrivial_aligned_ext_one_of_cross_cotangent sigma
          (i := (1 : Fin 2)) (j := (0 : Fin 2)) (by decide)
          hr (by simpa [hcomp] using hcorner)
      simpa [OpConjecture.TwoVertexGabrielConnectedness.HasCrossExt] using hExt

end SkeletonAlignment

end OpConjecture.CotangentExtBridge.CoordinateData
