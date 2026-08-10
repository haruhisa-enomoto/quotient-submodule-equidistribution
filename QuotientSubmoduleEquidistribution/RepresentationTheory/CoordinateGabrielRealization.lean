import QuotientSubmoduleEquidistribution.RepresentationTheory.CoordinateSimpleAlignment
import QuotientSubmoduleEquidistribution.RepresentationTheory.CotangentExtConverse
import QuotientSubmoduleEquidistribution.RepresentationTheory.SplitBasicGabrielArrowRealization

/-!
# Coordinate split-basic Ext--Gabriel realization

This file contains the general construction downstream from the
reverse Ext-to-cotangent theorem in `CotangentExtConverse`.  Coordinate simple
exhaustion and Ext transport come from `CoordinateSimpleAlignment`.

There are no concrete algebras, quivers, or module classifications here.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open MulOpposite Set

namespace QuotientSubmoduleEquidistribution.CoordinateGabrielRealization

universe u v w

variable {K B : Type u} {I : Type v}
  [Field K] [Ring B] [Algebra K B]
  [IsArtinianRing B] [IsArtinianRing Bᵐᵒᵖ]
  [Fintype I] [DecidableEq I]

abbrev CoordinateData :=
  QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData
    (K := K) (B := B) (I := I)

namespace CoordinateData

variable (D : CoordinateData (K := K) (B := B) (I := I))

/-- The two finitely generated bundles of a principal right ideal are
definitionally the same object.  This explicit identity isomorphism lets us
transport module tops across the instance boundary. -/
noncomputable def cyclicIdentityIso (c : B) :
    QuotientSubmoduleEquidistribution.Tsukamoto.cyclicRightIdealFG c ≅
      FGModuleCat.of Bᵐᵒᵖ
        (QuotientSubmoduleEquidistribution.Tsukamoto.principalRightIdeal c) :=
  Iso.refl _

/-! ## Tops of coordinate projectives -/

omit [IsArtinianRing Bᵐᵒᵖ] in
/-- The kernel of the coordinate character on `eᵢB` is the module
Jacobson radical of that coordinate projective. -/
theorem ker_vertexTopLinearMap_eq_jacobson (i : I) :
    letI : Module Bᵐᵒᵖ K := D.coordinateSimpleModule i
    LinearMap.ker (D.vertexTopLinearMap i) =
      Module.jacobson Bᵐᵒᵖ
        (QuotientSubmoduleEquidistribution.Tsukamoto.principalRightIdeal
          (D.liftedCoordinate i)) := by
  letI : Module Bᵐᵒᵖ K := D.coordinateSimpleModule i
  letI : IsSimpleModule Bᵐᵒᵖ K :=
    D.coordinateSimple_isSimpleModule i
  apply le_antisymm
  · intro x hx
    have hxJ : unop x.1 ∈ Ring.jacobson B :=
      D.unop_mem_jacobson_of_mem_vertexTop_ker i ⟨x, hx⟩
    have hxJop : op (unop x.1) ∈ Ring.jacobson Bᵐᵒᵖ :=
      QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.op_mem_jacobson_of_mem_jacobson
        (B := B) hxJ
    let e := D.liftedCoordinate i
    let xₑ : QuotientSubmoduleEquidistribution.Tsukamoto.principalRightIdeal e :=
      ⟨op e, Ideal.subset_span (Set.mem_singleton (op e))⟩
    have hsmul :
        op (unop x.1) • xₑ ∈
          Ring.jacobson Bᵐᵒᵖ •
            (⊤ : Submodule Bᵐᵒᵖ
              (QuotientSubmoduleEquidistribution.Tsukamoto.principalRightIdeal e)) :=
      Submodule.smul_mem_smul hxJop Submodule.mem_top
    have heq : op (unop x.1) • xₑ = x := by
      apply Subtype.ext
      change x.1 * op e = x.1
      exact
        QuotientSubmoduleEquidistribution.Tsukamoto.mul_op_eq_self_of_mem_principalRightIdeal
          (D.liftedCoordinate_complete.idem i) x.property
    rw [heq] at hsmul
    exact (Ring.jacobson_smul_top_le Bᵐᵒᵖ _) hsmul
  · exact
      IsSemisimpleModule.jacobson_le_ker Bᵐᵒᵖ Bᵐᵒᵖ
        (QuotientSubmoduleEquidistribution.Tsukamoto.principalRightIdeal
          (D.liftedCoordinate i)) K
        (D.vertexTopLinearMap i)

/-- The top of a coordinate projective is its coordinate simple. -/
noncomputable def vertexTopLinearEquiv (i : I) :
    letI : Module Bᵐᵒᵖ K := D.coordinateSimpleModule i
    (QuotientSubmoduleEquidistribution.Tsukamoto.principalRightIdeal
        (D.liftedCoordinate i) ⧸
      Module.jacobson Bᵐᵒᵖ
        (QuotientSubmoduleEquidistribution.Tsukamoto.principalRightIdeal
          (D.liftedCoordinate i))) ≃ₗ[Bᵐᵒᵖ] K := by
  letI : Module Bᵐᵒᵖ K := D.coordinateSimpleModule i
  rw [← D.ker_vertexTopLinearMap_eq_jacobson i]
  exact
    (D.vertexTopLinearMap i).quotKerEquivOfSurjective
      (D.vertexTopLinearMap_surjective i)

/-- Cyclic-ideal bundle form of the coordinate-projective top equivalence. -/
noncomputable def vertexTopCyclicLinearEquiv (i : I) :
    letI : Module Bᵐᵒᵖ K := D.coordinateSimpleModule i
    ((QuotientSubmoduleEquidistribution.Tsukamoto.cyclicRightIdealFG
        (D.liftedCoordinate i) : Type u) ⧸
      Module.jacobson Bᵐᵒᵖ
        (QuotientSubmoduleEquidistribution.Tsukamoto.cyclicRightIdealFG
          (D.liftedCoordinate i))) ≃ₗ[Bᵐᵒᵖ] K := by
  letI : Module Bᵐᵒᵖ K := D.coordinateSimpleModule i
  exact
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.SplitBasicGabrielArrowRealization.moduleTopLinearEquivOfIso
        (cyclicIdentityIso (B := B) (D.liftedCoordinate i))).trans
      (D.vertexTopLinearEquiv i)

/-! ## Cyclic tops of nonzero Peirce cotangent representatives -/

omit [IsArtinianRing Bᵐᵒᵖ] in
/-- If `eᵢc = c`, then the cyclic ideal generated by `c` lies in `eᵢB`. -/
theorem principalRightIdeal_le_coordinate
    {i : I} {c : B}
    (hleft : D.liftedCoordinate i * c = c) :
    QuotientSubmoduleEquidistribution.Tsukamoto.principalRightIdeal c ≤
      QuotientSubmoduleEquidistribution.Tsukamoto.principalRightIdeal
        (D.liftedCoordinate i) := by
  apply Ideal.span_le.mpr
  rw [Set.singleton_subset_iff]
  apply Ideal.mem_span_singleton'.mpr
  refine ⟨op c, ?_⟩
  rw [← op_mul, hleft]

/-- A radical corner generator as an element of the source-projective
kernel. -/
def cornerKernelElement
    (i : I) {c : B}
    (hcJ : c ∈ Ring.jacobson B)
    (hleft : D.liftedCoordinate i * c = c) :
    D.vertexTopKernel i := by
  let p : QuotientSubmoduleEquidistribution.Tsukamoto.principalRightIdeal
      (D.liftedCoordinate i) :=
    ⟨op c,
      D.principalRightIdeal_le_coordinate hleft
        (Ideal.mem_span_singleton_self (op c))⟩
  exact ⟨p, by
    change D.coordinateCharacter i c = 0
    exact D.coordinateCharacter_eq_zero_of_mem_jacobson i hcJ⟩

/-- Inclusion of a radical-generated cyclic ideal into the kernel of the
source-coordinate projective quotient. -/
def cyclicToVertexKernelLinearMap
    (i : I) {c : B}
    (hcJ : c ∈ Ring.jacobson B)
    (hleft : D.liftedCoordinate i * c = c) :
    QuotientSubmoduleEquidistribution.Tsukamoto.principalRightIdeal c →ₗ[Bᵐᵒᵖ]
      D.vertexTopKernel i where
  toFun x :=
    ⟨⟨x.1, D.principalRightIdeal_le_coordinate hleft x.property⟩, by
      change D.coordinateCharacter i (unop x.1) = 0
      exact D.coordinateCharacter_eq_zero_of_mem_jacobson i
        (QuotientSubmoduleEquidistribution.Tsukamoto.unop_mem_jacobson_of_mem_principalRightIdeal
          hcJ x.property)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A cotangent functional chosen to detect one class outside `J²`. -/
noncomputable def detectingFunctional
    (_D : CoordinateData (K := K) (B := B) (I := I))
    {c : B} (hc2 : c ∉ (Ring.jacobson B) ^ 2) : B →ₗ[K] K :=
  (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.exists_cotangent_functional
    (K := K) hc2).choose

omit [IsArtinianRing B] [IsArtinianRing Bᵐᵒᵖ]
    [Fintype I] [DecidableEq I] in
theorem detectingFunctional_ne_zero
    {c : B} (hc2 : c ∉ (Ring.jacobson B) ^ 2) :
    D.detectingFunctional hc2 c ≠ 0 :=
  (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.exists_cotangent_functional
    (K := K) hc2).choose_spec.1

omit [IsArtinianRing B] [IsArtinianRing Bᵐᵒᵖ]
    [Fintype I] [DecidableEq I] in
theorem detectingFunctional_vanishes_square
    {c : B} (hc2 : c ∉ (Ring.jacobson B) ^ 2) :
    ∀ z ∈ (Ring.jacobson B) ^ 2,
      D.detectingFunctional hc2 z = 0 :=
  (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.exists_cotangent_functional
    (K := K) hc2).choose_spec.2

/-- Restriction of the detecting cotangent functional to the generated
cyclic ideal. -/
def cornerTopLinearMap
    (i j : I) {c : B}
    (hcJ : c ∈ Ring.jacobson B)
    (hleft : D.liftedCoordinate i * c = c)
    (hc2 : c ∉ (Ring.jacobson B) ^ 2) :
    letI : Module Bᵐᵒᵖ K := D.coordinateSimpleModule j
    QuotientSubmoduleEquidistribution.Tsukamoto.principalRightIdeal c →ₗ[Bᵐᵒᵖ] K := by
  letI : Module Bᵐᵒᵖ K := D.coordinateSimpleModule j
  exact
    (D.cotangentKernelLinearMap i j
      (D.detectingFunctional hc2)
      (D.detectingFunctional_vanishes_square hc2)).comp
        (D.cyclicToVertexKernelLinearMap i hcJ hleft)

omit [IsArtinianRing Bᵐᵒᵖ] in
theorem cornerTopLinearMap_generator_ne_zero
    (i j : I) {c : B}
    (hcJ : c ∈ Ring.jacobson B)
    (hleft : D.liftedCoordinate i * c = c)
    (hright : c * D.liftedCoordinate j = c)
    (hc2 : c ∉ (Ring.jacobson B) ^ 2) :
    letI : Module Bᵐᵒᵖ K := D.coordinateSimpleModule j
    D.cornerTopLinearMap i j hcJ hleft hc2
        ⟨op c, Ideal.mem_span_singleton_self (op c)⟩ ≠ 0 := by
  letI : Module Bᵐᵒᵖ K := D.coordinateSimpleModule j
  change D.detectingFunctional hc2 (c * D.liftedCoordinate j) ≠ 0
  rw [hright]
  exact D.detectingFunctional_ne_zero hc2

omit [IsArtinianRing Bᵐᵒᵖ] in
theorem cornerTopLinearMap_ne_zero
    (i j : I) {c : B}
    (hcJ : c ∈ Ring.jacobson B)
    (hleft : D.liftedCoordinate i * c = c)
    (hright : c * D.liftedCoordinate j = c)
    (hc2 : c ∉ (Ring.jacobson B) ^ 2) :
    letI : Module Bᵐᵒᵖ K := D.coordinateSimpleModule j
    D.cornerTopLinearMap i j hcJ hleft hc2 ≠ 0 := by
  letI : Module Bᵐᵒᵖ K := D.coordinateSimpleModule j
  intro hzero
  apply D.cornerTopLinearMap_generator_ne_zero i j hcJ hleft hright hc2
  exact DFunLike.congr_fun hzero
    ⟨op c, Ideal.mem_span_singleton_self (op c)⟩

omit [IsArtinianRing Bᵐᵒᵖ] in
/-- The detected cyclic quotient surjects onto its target coordinate
simple. -/
theorem cornerTopLinearMap_surjective
    (i j : I) {c : B}
    (hcJ : c ∈ Ring.jacobson B)
    (hleft : D.liftedCoordinate i * c = c)
    (hright : c * D.liftedCoordinate j = c)
    (hc2 : c ∉ (Ring.jacobson B) ^ 2) :
    letI : Module Bᵐᵒᵖ K := D.coordinateSimpleModule j
    Function.Surjective
      (D.cornerTopLinearMap i j hcJ hleft hc2) := by
  letI : Module Bᵐᵒᵖ K := D.coordinateSimpleModule j
  let g :
      QuotientSubmoduleEquidistribution.Tsukamoto.principalRightModule c ⟶
        D.coordinateSimple j :=
    ModuleCat.ofHom (D.cornerTopLinearMap i j hcJ hleft hc2)
  have hg : g ≠ 0 := by
    intro hgzero
    apply D.cornerTopLinearMap_ne_zero i j hcJ hleft hright hc2
    have hhom := congrArg
      (fun q : QuotientSubmoduleEquidistribution.Tsukamoto.principalRightModule c ⟶
          D.coordinateSimple j ↦ q.hom) hgzero
    change D.cornerTopLinearMap i j hcJ hleft hc2 = 0 at hhom
    exact hhom
  letI : Simple (D.coordinateSimple j) := D.coordinateSimple_simple j
  letI : Epi g := epi_of_nonzero_to_simple hg
  exact (ModuleCat.epi_iff_surjective g).mp inferInstance

omit [IsArtinianRing Bᵐᵒᵖ] in
/-- The detected quotient's kernel is exactly the radical of its cyclic
ideal. -/
theorem ker_cornerTopLinearMap_eq_jacobson
    (i j : I) {c : B}
    (hcJ : c ∈ Ring.jacobson B)
    (hleft : D.liftedCoordinate i * c = c)
    (hright : c * D.liftedCoordinate j = c)
    (hc2 : c ∉ (Ring.jacobson B) ^ 2) :
    letI : Module Bᵐᵒᵖ K := D.coordinateSimpleModule j
    LinearMap.ker (D.cornerTopLinearMap i j hcJ hleft hc2) =
      Module.jacobson Bᵐᵒᵖ
        (QuotientSubmoduleEquidistribution.Tsukamoto.principalRightIdeal c) := by
  letI : Module Bᵐᵒᵖ K := D.coordinateSimpleModule j
  letI : IsSimpleModule Bᵐᵒᵖ K :=
    D.coordinateSimple_isSimpleModule j
  let g := D.cornerTopLinearMap i j hcJ hleft hc2
  let xc : QuotientSubmoduleEquidistribution.Tsukamoto.principalRightIdeal c :=
    ⟨op c, Ideal.mem_span_singleton_self (op c)⟩
  have hgenc : g xc ≠ 0 :=
    D.cornerTopLinearMap_generator_ne_zero i j hcJ hleft hright hc2
  apply le_antisymm
  · intro x hx
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp x.property
    have hax : a • xc = x := by
      apply Subtype.ext
      exact ha
    have hprod : D.coordinateCharacterOp j a * g xc = 0 := by
      calc
        D.coordinateCharacterOp j a * g xc = g (a • xc) := by
          rw [map_smul]
          rfl
        _ = g x := congrArg g hax
        _ = 0 := hx
    have hqa : D.coordinateCharacterOp j a = 0 :=
      (mul_eq_zero.mp hprod).resolve_right hgenc
    have hq : D.coordinateCharacter j (unop a) = 0 := by
      simpa [QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateCharacterOp]
        using hqa
    let d : B := D.liftedCoordinate j * unop a
    have hdJ : d ∈ Ring.jacobson B := by
      have hcong :=
        D.liftedCoordinate_mul_sub_coordinate_mem_jacobson j (unop a)
      simpa [d, hq] using hcong
    have hdJop : op d ∈ Ring.jacobson Bᵐᵒᵖ :=
      QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.op_mem_jacobson_of_mem_jacobson
        (B := B) hdJ
    have hdx : op d • xc = x := by
      apply Subtype.ext
      change op d * op c = x.1
      calc
        op d * op c = op (c * d) := (MulOpposite.op_mul c d).symm
        _ = op (c * unop a) := by simp [d, ← mul_assoc, hright]
        _ = a * op c := by simp [op_mul]
        _ = x.1 := ha
    have hsmul :
        op d • xc ∈
          Ring.jacobson Bᵐᵒᵖ •
            (⊤ : Submodule Bᵐᵒᵖ
              (QuotientSubmoduleEquidistribution.Tsukamoto.principalRightIdeal c)) :=
      Submodule.smul_mem_smul hdJop Submodule.mem_top
    rw [hdx] at hsmul
    exact (Ring.jacobson_smul_top_le Bᵐᵒᵖ _) hsmul
  · exact
      IsSemisimpleModule.jacobson_le_ker Bᵐᵒᵖ Bᵐᵒᵖ
        (QuotientSubmoduleEquidistribution.Tsukamoto.principalRightIdeal c) K g

/-- The top of a nonzero Peirce cotangent representative's cyclic ideal is
the target coordinate simple. -/
noncomputable def cornerTopLinearEquiv
    (i j : I) {c : B}
    (hcJ : c ∈ Ring.jacobson B)
    (hleft : D.liftedCoordinate i * c = c)
    (hright : c * D.liftedCoordinate j = c)
    (hc2 : c ∉ (Ring.jacobson B) ^ 2) :
    letI : Module Bᵐᵒᵖ K := D.coordinateSimpleModule j
    (QuotientSubmoduleEquidistribution.Tsukamoto.principalRightIdeal c ⧸
      Module.jacobson Bᵐᵒᵖ
        (QuotientSubmoduleEquidistribution.Tsukamoto.principalRightIdeal c)) ≃ₗ[Bᵐᵒᵖ] K := by
  letI : Module Bᵐᵒᵖ K := D.coordinateSimpleModule j
  rw [← D.ker_cornerTopLinearMap_eq_jacobson
    i j hcJ hleft hright hc2]
  exact
    (D.cornerTopLinearMap i j hcJ hleft hc2).quotKerEquivOfSurjective
      (D.cornerTopLinearMap_surjective i j hcJ hleft hright hc2)

/-- Cyclic-ideal bundle form of the detected corner-top equivalence. -/
noncomputable def cornerTopCyclicLinearEquiv
    (i j : I) {c : B}
    (hcJ : c ∈ Ring.jacobson B)
    (hleft : D.liftedCoordinate i * c = c)
    (hright : c * D.liftedCoordinate j = c)
    (hc2 : c ∉ (Ring.jacobson B) ^ 2) :
    letI : Module Bᵐᵒᵖ K := D.coordinateSimpleModule j
    ((QuotientSubmoduleEquidistribution.Tsukamoto.cyclicRightIdealFG c : Type u) ⧸
      Module.jacobson Bᵐᵒᵖ
        (QuotientSubmoduleEquidistribution.Tsukamoto.cyclicRightIdealFG c)) ≃ₗ[Bᵐᵒᵖ] K := by
  letI : Module Bᵐᵒᵖ K := D.coordinateSimpleModule j
  exact
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.SplitBasicGabrielArrowRealization.moduleTopLinearEquivOfIso
        (cyclicIdentityIso (B := B) c)).trans
      (D.cornerTopLinearEquiv i j hcJ hleft hright hc2)

end CoordinateData

/-! ## Automatic Ext-arrow representatives and realization -/

open QuotientSubmoduleEquidistribution.GabrielArrowBridge
open QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore

variable {K B : Type u} {I : Type v} {kappa : Type w}
  [Field K] [IsAlgClosed K]
  [Ring B] [Algebra K B]
  [Small.{u} Bᵐᵒᵖ] [IsNoetherianRing Bᵐᵒᵖ]
  [IsArtinianRing B] [IsArtinianRing Bᵐᵒᵖ]
  [Fintype I] [DecidableEq I] [Finite kappa]
  (D : CoordinateData (K := K) (B := B) (I := I))
  (tau : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, w, u} Bᵐᵒᵖ kappa)

omit [IsAlgClosed K] [IsArtinianRing Bᵐᵒᵖ] [Finite kappa] in
/-- Every multiplicity-bearing Ext arrow has a radical representative fixed
by the aligned source coordinate on the left and target coordinate on the
right, and nonzero modulo `J²`. -/
theorem exists_extArrow_bicorner_cotangent_representative
    (a : ExtGabrielArrowIndex (K := K) tau) :
    let i := (D.coordinateSimpleIndexEquiv tau).symm
      (ExtGabrielArrowIndex.source tau a)
    let j := (D.coordinateSimpleIndexEquiv tau).symm
      (ExtGabrielArrowIndex.target tau a)
    ∃ c : B,
      c ∈ Ring.jacobson B ∧
      D.liftedCoordinate i * c = c ∧
      c * D.liftedCoordinate j = c ∧
      c ∉ (Ring.jacobson B) ^ 2 := by
  let s := ExtGabrielArrowIndex.source tau a
  let t := ExtGabrielArrowIndex.target tau a
  let i := (D.coordinateSimpleIndexEquiv tau).symm s
  let j := (D.coordinateSimpleIndexEquiv tau).symm t
  obtain ⟨r, hr, hcorner⟩ :=
    D.exists_aligned_cross_cotangent_of_extGabrielArrow tau a
  let c := D.liftedCoordinate i * r * D.liftedCoordinate j
  refine ⟨c, ?_, ?_, ?_, hcorner⟩
  · exact Ideal.mul_mem_right _ _
      (Ideal.mul_mem_left _ (D.liftedCoordinate i) hr)
  · dsimp only [c]
    calc
      D.liftedCoordinate i *
            (D.liftedCoordinate i * r * D.liftedCoordinate j) =
          (D.liftedCoordinate i * D.liftedCoordinate i) * r *
            D.liftedCoordinate j := by simp [mul_assoc]
      _ = D.liftedCoordinate i * r * D.liftedCoordinate j := by
        rw [D.liftedCoordinate_complete.idem i]
  · dsimp only [c]
    calc
      (D.liftedCoordinate i * r * D.liftedCoordinate j) *
            D.liftedCoordinate j =
          D.liftedCoordinate i * r *
            (D.liftedCoordinate j * D.liftedCoordinate j) := by
        simp [mul_assoc]
      _ = D.liftedCoordinate i * r * D.liftedCoordinate j := by
        rw [D.liftedCoordinate_complete.idem j]

/-- Representatives for all multiplicity-bearing Ext arrows, stated only
with the properties consumed by the operational realization. -/
structure ExtArrowCotangentRepresentativeData where
  representative : ExtGabrielArrowIndex (K := K) tau → B
  representative_mem_jacobson : ∀ a,
    representative a ∈ Ring.jacobson B
  representative_left_fixed : ∀ a,
    D.liftedCoordinate
          ((D.coordinateSimpleIndexEquiv tau).symm
            (ExtGabrielArrowIndex.source tau a)) *
        representative a = representative a
  representative_right_fixed : ∀ a,
    representative a *
        D.liftedCoordinate
          ((D.coordinateSimpleIndexEquiv tau).symm
            (ExtGabrielArrowIndex.target tau a)) =
      representative a
  representative_not_mem_square : ∀ a,
    representative a ∉ (Ring.jacobson B) ^ 2

/-- The tracked Ext-to-cotangent converse chooses all representatives
automatically. -/
noncomputable def automaticExtArrowCotangentRepresentativeData :
    ExtArrowCotangentRepresentativeData D tau := by
  have hex (a : ExtGabrielArrowIndex (K := K) tau) :
      ∃ c : B,
        c ∈ Ring.jacobson B ∧
        D.liftedCoordinate
              ((D.coordinateSimpleIndexEquiv tau).symm
                (ExtGabrielArrowIndex.source tau a)) * c = c ∧
        c * D.liftedCoordinate
              ((D.coordinateSimpleIndexEquiv tau).symm
                (ExtGabrielArrowIndex.target tau a)) = c ∧
        c ∉ (Ring.jacobson B) ^ 2 :=
    exists_extArrow_bicorner_cotangent_representative D tau a
  exact
    { representative := fun a ↦ (hex a).choose
      representative_mem_jacobson := fun a ↦ (hex a).choose_spec.1
      representative_left_fixed := fun a ↦ (hex a).choose_spec.2.1
      representative_right_fixed := fun a ↦ (hex a).choose_spec.2.2.1
      representative_not_mem_square := fun a ↦ (hex a).choose_spec.2.2.2 }

namespace ExtArrowCotangentRepresentativeData

variable {D tau}
  (R : ExtArrowCotangentRepresentativeData D tau)

/-- Coordinate vertices and chosen corner representatives supply the full
operational split-basic Gabriel realization. -/
noncomputable def toSplitBasicGabrielArrowRealization :
    SplitBasicGabrielArrowRealization tau
      (ExtGabrielArrowIndex.source (K := K) tau)
      (ExtGabrielArrowIndex.target (K := K) tau) where
  vertex s :=
    D.liftedCoordinate ((D.coordinateSimpleIndexEquiv tau).symm s)
  vertex_idempotent s :=
    D.liftedCoordinate_complete.idem
      ((D.coordinateSimpleIndexEquiv tau).symm s)
  vertex_ne_zero s :=
    D.liftedCoordinate_ne_zero
      ((D.coordinateSimpleIndexEquiv tau).symm s)
  vertex_topIso s := by
    refine ⟨ObjectProperty.isoMk _ ?_⟩
    let i := (D.coordinateSimpleIndexEquiv tau).symm s
    have e :
        ModuleCat.of Bᵐᵒᵖ
            ((QuotientSubmoduleEquidistribution.Tsukamoto.cyclicRightIdealFG
                (D.liftedCoordinate i) : Type u) ⧸
              Module.jacobson Bᵐᵒᵖ
                (QuotientSubmoduleEquidistribution.Tsukamoto.cyclicRightIdealFG
                  (D.liftedCoordinate i))) ≅
          (tau.obj s.1).obj :=
      (D.vertexTopCyclicLinearEquiv i).toModuleIso ≪≫
        (forget₂ (FGModuleCat Bᵐᵒᵖ) (ModuleCat Bᵐᵒᵖ)).mapIso
          (D.alignedSimpleFGIso tau s)
    simpa [i] using e
  representative := R.representative
  representative_mem_jacobson := R.representative_mem_jacobson
  arrowIdeal_le_source a :=
    D.principalRightIdeal_le_coordinate
      (R.representative_left_fixed a)
  arrow_topIso a := by
    refine ⟨ObjectProperty.isoMk _ ?_⟩
    let s := ExtGabrielArrowIndex.source tau a
    let t := ExtGabrielArrowIndex.target tau a
    let i := (D.coordinateSimpleIndexEquiv tau).symm s
    let j := (D.coordinateSimpleIndexEquiv tau).symm t
    have e :
        ModuleCat.of Bᵐᵒᵖ
            ((QuotientSubmoduleEquidistribution.Tsukamoto.cyclicRightIdealFG
                (R.representative a) : Type u) ⧸
              Module.jacobson Bᵐᵒᵖ
                (QuotientSubmoduleEquidistribution.Tsukamoto.cyclicRightIdealFG
                  (R.representative a))) ≅
          (tau.obj t.1).obj :=
      (D.cornerTopCyclicLinearEquiv i j
          (R.representative_mem_jacobson a)
          (R.representative_left_fixed a)
          (R.representative_right_fixed a)
          (R.representative_not_mem_square a)).toModuleIso ≪≫
        (forget₂ (FGModuleCat Bᵐᵒᵖ) (ModuleCat Bᵐᵒᵖ)).mapIso
          (D.alignedSimpleFGIso tau t)
    simpa [t] using e

/-- The general converse therefore gives an unconditional operational
realization indexed by all multiplicity-bearing Ext arrows. -/
noncomputable def automaticSplitBasicGabrielArrowRealization :
    SplitBasicGabrielArrowRealization tau
      (ExtGabrielArrowIndex.source (K := K) tau)
      (ExtGabrielArrowIndex.target (K := K) tau) := by
  let R := automaticExtArrowCotangentRepresentativeData D tau
  exact toSplitBasicGabrielArrowRealization R

end ExtArrowCotangentRepresentativeData

end QuotientSubmoduleEquidistribution.CoordinateGabrielRealization
