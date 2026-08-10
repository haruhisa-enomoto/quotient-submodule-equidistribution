import QuotientSubmoduleEquidistribution.RepresentationTheory.SplitBasicCoordinateSystem
import QuotientSubmoduleEquidistribution.RepresentationTheory.GabrielArrowBridge
import QuotientSubmoduleEquidistribution.RepresentationTheory.StrongHeredity
import Mathlib.Algebra.Algebra.Opposite
import Mathlib.Algebra.Category.ModuleCat.Ext.DimensionShifting
import Mathlib.Algebra.Category.ModuleCat.Simple

/-!
# Cotangent classes and degree-one Ext

This file isolates the derived-category argument which turns a nonzero map out
of the kernel of a projective cover into a nonzero `Ext¹` class.  It then builds
the canonical coordinate simple right modules associated to a split basic
quotient and proves that every nonzero cross-cotangent class detects a nonzero
degree-one extension.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open MulOpposite

namespace QuotientSubmoduleEquidistribution.CotangentExtBridge

universe u v

/-! ## The formal dimension-shifting core -/

variable {R : Type u} [Ring R] [Small.{u} R]

/-- A nonzero map out of the kernel in a projective presentation gives a
nonzero degree-one extension whenever every map from the projective middle
term vanishes. -/
theorem nontrivial_ext_one_of_projective_presentation
    {S : ShortComplex (ModuleCat.{u} R)}
    (hS : S.ShortExact) [Projective S.X₂]
    {T : ModuleCat.{u} R}
    (f : S.X₁ ⟶ T) (hf : f ≠ 0)
    (hvanish : ∀ g : S.X₂ ⟶ T, g = 0) :
    Nontrivial (Ext S.X₃ T 1) := by
  let x : Ext S.X₃ T 1 :=
    hS.extClass.comp (Ext.mk₀ f) (add_zero 1)
  have hx : x ≠ 0 := by
    intro hxzero
    obtain ⟨z, hz⟩ :=
      Ext.contravariant_sequence_exact₁ hS T (Ext.mk₀ f)
        (add_zero 1) hxzero
    have hzZero : z = 0 := by
      apply (Ext.linearEquiv₀ (R := ℤ)).injective
      simpa using hvanish (Ext.linearEquiv₀ (R := ℤ) z)
    rw [hzZero] at hz
    apply hf
    apply (Ext.mk₀_bijective S.X₁ T).injective
    simpa using hz.symm
  exact ⟨x, 0, hx⟩

/-! ## Coordinate characters and their right simple modules -/

variable {K B : Type u} {I : Type v}
  [Field K] [Ring B] [Algebra K B] [IsArtinianRing B]
  [Fintype I] [DecidableEq I]

abbrev CoordinateData :=
  QuotientSubmoduleEquidistribution.SplitBasicCoordinateSystem.QuotientCoordinateData
    (K := K) (B := B) (I := I)

namespace CoordinateData

variable (D : CoordinateData (K := K) (B := B) (I := I))

/-- The character obtained by projecting the split basic quotient to one
coordinate. -/
def coordinateCharacter (i : I) : B →ₐ[K] K :=
  (Pi.evalAlgHom K (fun _ : I ↦ K) i).comp
    (D.quotientEquiv.toAlgHom.comp
      (Ideal.Quotient.mkₐ K (Ring.jacobson B)))

@[simp]
theorem coordinateCharacter_liftedCoordinate_same (i : I) :
    D.coordinateCharacter i (D.liftedCoordinate i) = 1 := by
  simp [coordinateCharacter,
    QuotientSubmoduleEquidistribution.SplitBasicCoordinateSystem.QuotientCoordinateData.quotient_mk_liftedCoordinate,
    QuotientSubmoduleEquidistribution.SplitBasicCoordinateSystem.QuotientCoordinateData.quotientCoordinate]

@[simp]
theorem coordinateCharacter_liftedCoordinate_ne
    {i j : I} (hij : i ≠ j) :
    D.coordinateCharacter j (D.liftedCoordinate i) = 0 := by
  simp [coordinateCharacter,
    QuotientSubmoduleEquidistribution.SplitBasicCoordinateSystem.QuotientCoordinateData.quotient_mk_liftedCoordinate,
    QuotientSubmoduleEquidistribution.SplitBasicCoordinateSystem.QuotientCoordinateData.quotientCoordinate,
    hij]

omit [IsArtinianRing B] [Fintype I] [DecidableEq I] in
theorem coordinateCharacter_eq_zero_of_mem_jacobson
    (i : I) {x : B} (hx : x ∈ Ring.jacobson B) :
    D.coordinateCharacter i x = 0 := by
  simp [coordinateCharacter, Ideal.Quotient.eq_zero_iff_mem.mpr hx]

/-- Multiplying by a lifted coordinate agrees modulo the radical with
multiplication by the corresponding scalar coordinate. -/
theorem mul_liftedCoordinate_sub_coordinate_mem_jacobson
    (j : I) (b : B) :
    b * D.liftedCoordinate j -
        algebraMap K B (D.coordinateCharacter j b) *
          D.liftedCoordinate j ∈ Ring.jacobson B := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply D.quotientEquiv.injective
  simp only [map_sub, map_mul, map_zero,
    QuotientSubmoduleEquidistribution.SplitBasicCoordinateSystem.QuotientCoordinateData.quotient_mk_liftedCoordinate]
  simp only [QuotientSubmoduleEquidistribution.SplitBasicCoordinateSystem.QuotientCoordinateData.quotientCoordinate,
    D.quotientEquiv.apply_symm_apply]
  ext k
  by_cases hkj : k = j
  · subst k
    simp [coordinateCharacter]
  · simp [hkj]

omit [IsArtinianRing B] in
/-- A linear functional separates any class outside `J²` and can be chosen
to vanish on `J²`. -/
theorem exists_cotangent_functional
    {c : B} (hc : c ∉ (Ring.jacobson B) ^ 2) :
    ∃ ℓ : B →ₗ[K] K,
      ℓ c ≠ 0 ∧ ∀ z ∈ (Ring.jacobson B) ^ 2, ℓ z = 0 := by
  let Q : Submodule K B :=
    ((Ring.jacobson B) ^ 2 : Submodule B B).restrictScalars K
  have hcQ : c ∉ Q := by
    simpa [Q] using hc
  obtain ⟨ℓ, hℓc, hmap⟩ :=
    Q.exists_dual_map_eq_bot_of_notMem hcQ inferInstance
  refine ⟨ℓ, hℓc, ?_⟩
  intro z hz
  have hzQ : z ∈ Q := by simpa [Q] using hz
  have hmem : ℓ z ∈ Q.map ℓ := ⟨z, hzQ, rfl⟩
  rw [hmap, Submodule.mem_bot] at hmem
  exact hmem

/-- The coordinate character on the opposite ring. -/
def coordinateCharacterOp (i : I) : Bᵐᵒᵖ →+* K :=
  D.coordinateCharacter i |>.toRingHom.fromOpposite
    (fun x y ↦ Commute.all
      (D.coordinateCharacter i x) (D.coordinateCharacter i y))

/-- The corresponding one-dimensional right `B`-module, represented as a
left module over `Bᵐᵒᵖ`. -/
@[reducible]
def coordinateSimpleModule (i : I) : Module Bᵐᵒᵖ K :=
  Module.compHom K (D.coordinateCharacterOp i)

/-- The bundled coordinate simple. -/
def coordinateSimple (i : I) : ModuleCat.{u} Bᵐᵒᵖ :=
  letI : Module Bᵐᵒᵖ K := D.coordinateSimpleModule i
  ModuleCat.of Bᵐᵒᵖ K

omit [IsArtinianRing B] [Fintype I] [DecidableEq I] in
theorem coordinateCharacterOp_surjective (i : I) :
    Function.Surjective (D.coordinateCharacterOp i) := by
  intro k
  refine ⟨op (algebraMap K B k), ?_⟩
  simp [coordinateCharacterOp, coordinateCharacter]

omit [IsArtinianRing B] [Fintype I] [DecidableEq I] in
/-- Every coordinate module is simple. -/
theorem coordinateSimple_isSimpleModule (i : I) :
    letI : Module Bᵐᵒᵖ K := D.coordinateSimpleModule i
    IsSimpleModule Bᵐᵒᵖ K := by
  letI : Module Bᵐᵒᵖ K := D.coordinateSimpleModule i
  rw [isSimpleModule_iff_toSpanSingleton_surjective]
  refine ⟨inferInstance, ?_⟩
  intro x hx y
  let k : K := y * x⁻¹
  obtain ⟨b, hb⟩ := D.coordinateCharacterOp_surjective i k
  refine ⟨b, ?_⟩
  change D.coordinateCharacterOp i b * x = y
  rw [hb]
  simp [k, hx]

omit [IsArtinianRing B] [Fintype I] [DecidableEq I] in
/-- Each coordinate simple is cyclic, hence finitely generated over the
opposite ring. -/
theorem coordinateSimple_moduleFinite (i : I) :
    letI : Module Bᵐᵒᵖ K := D.coordinateSimpleModule i
    Module.Finite Bᵐᵒᵖ K := by
  letI : Module Bᵐᵒᵖ K := D.coordinateSimpleModule i
  apply Module.Finite.of_surjective
    (LinearMap.toSpanSingleton Bᵐᵒᵖ K 1)
  intro y
  obtain ⟨b, hb⟩ := D.coordinateCharacterOp_surjective i y
  refine ⟨b, ?_⟩
  change D.coordinateCharacterOp i b * 1 = y
  simpa using hb

omit [IsArtinianRing B] [Fintype I] [DecidableEq I] in
/-- Bundled categorical simplicity of every coordinate module. -/
theorem coordinateSimple_simple (i : I) : Simple (D.coordinateSimple i) := by
  apply (simple_iff_isSimpleModule' (D.coordinateSimple i)).mpr
  exact D.coordinateSimple_isSimpleModule i

/-- Evaluation of an element of the vertex projective by its coordinate
character. -/
def vertexTopLinearMap (i : I) :
    letI : Module Bᵐᵒᵖ K := D.coordinateSimpleModule i
    QuotientSubmoduleEquidistribution.Tsukamoto.principalRightIdeal (D.liftedCoordinate i) →ₗ[Bᵐᵒᵖ] K := by
  letI : Module Bᵐᵒᵖ K := D.coordinateSimpleModule i
  exact
    { toFun := fun x ↦ D.coordinateCharacter i (unop x.1)
      map_add' := fun x y ↦ by simp
      map_smul' := fun b x ↦ by
        change
          D.coordinateCharacter i (unop (b * x.1)) =
            D.coordinateCharacterOp i b *
              D.coordinateCharacter i (unop x.1)
        simp [coordinateCharacterOp, mul_comm] }

/-- The kernel of the coordinate quotient, bundled as a type independently
of the temporary module instance on the target copy of `K`. -/
abbrev vertexTopKernel (i : I) : Type u :=
  letI : Module Bᵐᵒᵖ K := D.coordinateSimpleModule i
  LinearMap.ker (D.vertexTopLinearMap i)

/-- Linear maps from the `i`th projective kernel to the `j`th coordinate
simple, with the latter's module instance hidden in the abbreviation. -/
abbrev KernelToCoordinateLinearMap (i j : I) : Type u :=
  letI : Module Bᵐᵒᵖ K := D.coordinateSimpleModule j
  D.vertexTopKernel i →ₗ[Bᵐᵒᵖ] K

/-- The canonical quotient from a vertex projective to its coordinate
simple. -/
def vertexTopMap (i : I) :
    QuotientSubmoduleEquidistribution.Tsukamoto.principalRightModule (D.liftedCoordinate i) ⟶
      D.coordinateSimple i := by
  letI : Module Bᵐᵒᵖ K := D.coordinateSimpleModule i
  exact ModuleCat.ofHom (D.vertexTopLinearMap i)

/-- The standard projective presentation of the `i`th coordinate simple. -/
def vertexPresentation (i : I) : ShortComplex (ModuleCat.{u} Bᵐᵒᵖ) := by
  letI : Module Bᵐᵒᵖ K := D.coordinateSimpleModule i
  exact (D.vertexTopLinearMap i).shortComplexKer

/-- Bundle a kernel-to-coordinate linear map as the corresponding morphism
out of the projective presentation kernel. -/
def kernelToCoordinateMorphism
    (i j : I) (f : D.KernelToCoordinateLinearMap i j) :
    (D.vertexPresentation i).X₁ ⟶ D.coordinateSimple j := by
  letI : Module Bᵐᵒᵖ K := D.coordinateSimpleModule j
  exact ModuleCat.ofHom f

theorem vertexTopLinearMap_surjective (i : I) :
    Function.Surjective (D.vertexTopLinearMap i) := by
  intro y
  let e := D.liftedCoordinate i
  let x : QuotientSubmoduleEquidistribution.Tsukamoto.principalRightIdeal e :=
    ⟨op (e * algebraMap K B y), by
      rw [show op (e * algebraMap K B y) =
        op (algebraMap K B y) * op e by simp]
      exact (QuotientSubmoduleEquidistribution.Tsukamoto.principalRightIdeal e).mul_mem_left _
        (Ideal.subset_span (Set.mem_singleton (op e)))⟩
  refine ⟨x, ?_⟩
  change D.coordinateCharacter i (e * algebraMap K B y) = y
  simp [e]

/-- The kernel of the vertex-top quotient consists of radical elements. -/
theorem unop_mem_jacobson_of_mem_vertexTop_ker
    (i : I) (x : D.vertexTopKernel i) :
    unop x.1.1 ∈ Ring.jacobson B := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply D.quotientEquiv.injective
  ext k
  by_cases hki : k = i
  · subst k
    have hx := x.property
    change D.coordinateCharacter i (unop x.1.1) = 0 at hx
    simpa [coordinateCharacter] using hx
  · have hfixedOp :
        x.1.1 * op (D.liftedCoordinate i) = x.1.1 :=
      QuotientSubmoduleEquidistribution.Tsukamoto.mul_op_eq_self_of_mem_principalRightIdeal
        (D.liftedCoordinate_complete.idem i) x.1.property
    have hfixed : D.liftedCoordinate i * unop x.1.1 = unop x.1.1 := by
      simpa using congrArg unop hfixedOp
    rw [← hfixed, map_mul,
      QuotientSubmoduleEquidistribution.SplitBasicCoordinateSystem.QuotientCoordinateData.quotient_mk_liftedCoordinate]
    simp [QuotientSubmoduleEquidistribution.SplitBasicCoordinateSystem.QuotientCoordinateData.quotientCoordinate,
      hki]

/-- A cotangent functional gives a right-module map from the radical kernel
of the `i`th vertex projective to the `j`th coordinate simple. -/
def cotangentKernelLinearMap
    (i j : I) (ℓ : B →ₗ[K] K)
    (hℓ : ∀ z ∈ (Ring.jacobson B) ^ 2, ℓ z = 0) :
    letI : Module Bᵐᵒᵖ K := D.coordinateSimpleModule j
    D.vertexTopKernel i →ₗ[Bᵐᵒᵖ] K := by
  letI : Module Bᵐᵒᵖ K := D.coordinateSimpleModule j
  exact
    { toFun := fun x ↦ ℓ (unop x.1.1 * D.liftedCoordinate j)
      map_add' := fun x y ↦ by simp [add_mul]
      map_smul' := fun b x ↦ by
        let a : B := unop x.1.1
        let d : B := unop b
        let e : B := D.liftedCoordinate j
        let q : K := D.coordinateCharacter j d
        have ha : a ∈ Ring.jacobson B :=
          D.unop_mem_jacobson_of_mem_vertexTop_ker i x
        have hright : d * e - algebraMap K B q * e ∈ Ring.jacobson B := by
          simpa [d, e, q] using
            D.mul_liftedCoordinate_sub_coordinate_mem_jacobson j d
        have hcomm : Commute (algebraMap K B q) a :=
          Algebra.commutes q a
        have hscalar :
            algebraMap K B q * (a * e) =
              a * (algebraMap K B q * e) := by
          calc
            algebraMap K B q * (a * e) =
                (algebraMap K B q * a) * e := (mul_assoc _ _ _).symm
            _ = (a * algebraMap K B q) * e := by rw [hcomm.eq]
            _ = a * (algebraMap K B q * e) := mul_assoc _ _ _
        have hdiffEq :
            a * d * e - algebraMap K B q * (a * e) =
              a * (d * e - algebraMap K B q * e) := by
          rw [mul_sub, ← hscalar]
          simp [mul_assoc]
        have hdiff :
            a * d * e - algebraMap K B q * (a * e) ∈
              (Ring.jacobson B) ^ 2 := by
          rw [hdiffEq,
            show (2 : ℕ) = 1 + 1 by omega,
            Ideal.IsTwoSided.pow_add 1 1, Submodule.pow_one]
          exact Ideal.mul_mem_mul ha hright
        have hz := hℓ _ hdiff
        have heq : ℓ (a * d * e) = q * ℓ (a * e) := by
          rw [map_sub, sub_eq_zero] at hz
          calc
            ℓ (a * d * e) = ℓ (algebraMap K B q * (a * e)) := hz
            _ = q * ℓ (a * e) := by
              simpa [Algebra.smul_def] using ℓ.map_smul q (a * e)
        change
          ℓ (unop x.1.1 * unop b * D.liftedCoordinate j) =
            D.coordinateCharacterOp j b *
              ℓ (unop x.1.1 * D.liftedCoordinate j)
        simpa [a, d, e, q, coordinateCharacterOp] using heq }

/-- A nonzero `eᵢJeⱼ` class modulo `J²` produces a nonzero module map
from the radical kernel of the `i`th projective to the `j`th coordinate
simple. -/
theorem exists_nonzero_kernel_map_of_cross_cotangent
    {i j : I} {r : B}
    (hr : r ∈ Ring.jacobson B)
    (hcorner :
      D.liftedCoordinate i * r * D.liftedCoordinate j ∉
        (Ring.jacobson B) ^ 2) :
    letI : Module Bᵐᵒᵖ K := D.coordinateSimpleModule j
    ∃ f : D.vertexTopKernel i →ₗ[Bᵐᵒᵖ] K, f ≠ 0 := by
  letI : Module Bᵐᵒᵖ K := D.coordinateSimpleModule j
  let eᵢ := D.liftedCoordinate i
  let eⱼ := D.liftedCoordinate j
  let c := eᵢ * r * eⱼ
  obtain ⟨ℓ, hℓc, hℓzero⟩ :=
    exists_cotangent_functional (K := K) hcorner
  let f : D.vertexTopKernel i →ₗ[Bᵐᵒᵖ] K :=
    D.cotangentKernelLinearMap i j ℓ hℓzero
  refine ⟨f, ?_⟩
  have hcJ : c ∈ Ring.jacobson B := by
    exact Ideal.mul_mem_right eⱼ _ (Ideal.mul_mem_left _ eᵢ hr)
  let pₓ : QuotientSubmoduleEquidistribution.Tsukamoto.principalRightIdeal eᵢ :=
    ⟨op c, by
      rw [show op c = op (r * eⱼ) * op eᵢ by
        simp [c, eᵢ, eⱼ, mul_assoc]]
      exact (QuotientSubmoduleEquidistribution.Tsukamoto.principalRightIdeal eᵢ).mul_mem_left _
        (Ideal.subset_span (Set.mem_singleton (op eᵢ)))⟩
  let kₓ : D.vertexTopKernel i :=
    ⟨pₓ, by
      change D.coordinateCharacter i c = 0
      exact D.coordinateCharacter_eq_zero_of_mem_jacobson i hcJ⟩
  have hcfix : c * eⱼ = c := by
    dsimp only [c]
    calc
      (eᵢ * r * eⱼ) * eⱼ = eᵢ * r * (eⱼ * eⱼ) := by
        simp [mul_assoc]
      _ = eᵢ * r * eⱼ := by
        rw [D.liftedCoordinate_complete.idem j]
  intro hf
  have happly := LinearMap.congr_fun hf kₓ
  change ℓ (c * eⱼ) = 0 at happly
  rw [hcfix] at happly
  exact hℓc happly

theorem vertexTopMap_epi (i : I) : Epi (D.vertexTopMap i) := by
  apply ConcreteCategory.epi_of_surjective
  intro y
  obtain ⟨x, hx⟩ := D.vertexTopLinearMap_surjective i y
  exact ⟨x, hx⟩

theorem vertexPresentation_shortExact (i : I) :
    (D.vertexPresentation i).ShortExact := by
  letI : Module Bᵐᵒᵖ K := D.coordinateSimpleModule i
  simpa [vertexPresentation] using
    LinearMap.shortExact_shortComplexKer
      (D.vertexTopLinearMap_surjective i)

theorem vertexPresentation_projective_middle (i : I) :
    Projective (D.vertexPresentation i).X₂ := by
  change Projective
    (QuotientSubmoduleEquidistribution.Tsukamoto.principalRightModule
      (D.liftedCoordinate i))
  exact
    (IsProjective.iff_projective
      (QuotientSubmoduleEquidistribution.Tsukamoto.principalRightIdeal
        (D.liftedCoordinate i))).mp
      (QuotientSubmoduleEquidistribution.Tsukamoto.principalRightIdeal_projective
        (D.liftedCoordinate_complete.idem i))

theorem kernelToCoordinateMorphism_ne_zero
    {i j : I} {f : D.KernelToCoordinateLinearMap i j}
    (hf : f ≠ 0) :
    D.kernelToCoordinateMorphism i j f ≠ 0 := by
  letI : Module Bᵐᵒᵖ K := D.coordinateSimpleModule j
  intro hzero
  apply hf
  have hhom := congrArg
    (fun q : (D.vertexPresentation i).X₁ ⟶ D.coordinateSimple j ↦
      q.hom) hzero
  change f = 0 at hhom
  exact hhom

/-- Distinct coordinate vertices admit no linear maps from the `i`th vertex
projective to the `j`th coordinate module. -/
theorem linearMap_vertexProjective_coordinate_eq_zero
    {i j : I} (hij : i ≠ j) :
    letI : Module Bᵐᵒᵖ K := D.coordinateSimpleModule j
    ∀ g : QuotientSubmoduleEquidistribution.Tsukamoto.principalRightIdeal
          (D.liftedCoordinate i) →ₗ[Bᵐᵒᵖ] K,
      g = 0 := by
  letI : Module Bᵐᵒᵖ K := D.coordinateSimpleModule j
  intro g
  apply LinearMap.ext
  intro x
  change g x = 0
  exact (Submodule.span_induction
    (p := fun y _ ↦ ∀ hy : y ∈
      QuotientSubmoduleEquidistribution.Tsukamoto.principalRightIdeal (D.liftedCoordinate i),
        g ⟨y, hy⟩ = 0)
    (fun y hy ↦ by
      rcases Set.mem_singleton_iff.mp hy with rfl
      intro hySpan
      let e := D.liftedCoordinate i
      let xₑ : QuotientSubmoduleEquidistribution.Tsukamoto.principalRightIdeal e :=
        ⟨op e, Ideal.subset_span (Set.mem_singleton (op e))⟩
      change g xₑ = 0
      have hfix : (op e) • xₑ = xₑ := by
        apply Subtype.ext
        change op e * op e = op e
        rw [← op_mul, D.liftedCoordinate_complete.idem i]
      have hm := g.map_smul (op e) xₑ
      have hleft : g ((op e) • xₑ) = g xₑ :=
        congrArg g hfix
      have hm' : g xₑ = (op e) • g xₑ :=
        hleft.symm.trans hm
      change g xₑ = D.coordinateCharacter j e * g xₑ at hm'
      rw [D.coordinateCharacter_liftedCoordinate_ne hij] at hm'
      simpa using hm')
    (by
      intro hzero
      change g (0 : QuotientSubmoduleEquidistribution.Tsukamoto.principalRightIdeal
        (D.liftedCoordinate i)) = 0
      exact map_zero g)
    (fun x y hx hy hxzero hyzero ↦ by
      intro hxy
      change g (⟨x, hx⟩ + ⟨y, hy⟩) = 0
      rw [map_add, hxzero hx, hyzero hy, add_zero])
    (fun b x hx hxzero ↦ by
      intro hbx
      change g (b • ⟨x, hx⟩) = 0
      rw [map_smul, hxzero hx, smul_zero])
    x.property) x.property

/-- Bundled categorical form of the preceding vanishing theorem. -/
theorem hom_vertexProjective_coordinateSimple_eq_zero
    {i j : I} (hij : i ≠ j)
    (g : QuotientSubmoduleEquidistribution.Tsukamoto.principalRightModule
          (D.liftedCoordinate i) ⟶ D.coordinateSimple j) :
    g = 0 := by
  apply ModuleCat.hom_ext
  exact D.linearMap_vertexProjective_coordinate_eq_zero hij g.hom

/-- The coordinate simples are pairwise nonisomorphic. -/
theorem coordinateSimple_not_iso
    {i j : I} (hij : i ≠ j) :
    IsEmpty (D.coordinateSimple i ≅ D.coordinateSimple j) := by
  constructor
  intro e
  letI : Epi (D.vertexTopMap i) := D.vertexTopMap_epi i
  let f := D.vertexTopMap i ≫ e.hom
  have hf : f = 0 :=
    D.hom_vertexProjective_coordinateSimple_eq_zero hij f
  letI : Epi f := by dsimp only [f]; infer_instance
  have hid : 𝟙 (D.coordinateSimple j) = 0 := by
    apply (cancel_epi f).mp
    simp [hf]
  letI : Simple (D.coordinateSimple j) := D.coordinateSimple_simple j
  exact Simple.not_isZero (D.coordinateSimple j)
    ((IsZero.iff_id_eq_zero (D.coordinateSimple j)).mpr hid)

/-- The cotangent-to-Ext bridge for the canonical coordinate simples of a
split basic quotient.  A nonzero cross class in `eᵢ J eⱼ / eᵢ J² eⱼ`
forces `Ext¹(Sᵢ,Sⱼ)` to be nonzero. -/
theorem nontrivial_ext_one_of_cross_cotangent
    {i j : I} (hij : i ≠ j) {r : B}
    (hr : r ∈ Ring.jacobson B)
    (hcorner :
      D.liftedCoordinate i * r * D.liftedCoordinate j ∉
        (Ring.jacobson B) ^ 2) :
    Nontrivial
      (Ext (D.coordinateSimple i) (D.coordinateSimple j) 1) := by
  have hex : ∃ f : D.KernelToCoordinateLinearMap i j, f ≠ 0 := by
    letI : Module Bᵐᵒᵖ K := D.coordinateSimpleModule j
    exact D.exists_nonzero_kernel_map_of_cross_cotangent hr hcorner
  obtain ⟨f, hf⟩ := hex
  letI : Projective (D.vertexPresentation i).X₂ :=
    D.vertexPresentation_projective_middle i
  have hExt :=
    nontrivial_ext_one_of_projective_presentation
      (D.vertexPresentation_shortExact i)
      (D.kernelToCoordinateMorphism i j f)
      (D.kernelToCoordinateMorphism_ne_zero hf)
      (fun g ↦ D.hom_vertexProjective_coordinateSimple_eq_zero hij g)
  simpa [vertexPresentation, coordinateSimple] using hExt

end CoordinateData

end QuotientSubmoduleEquidistribution.CotangentExtBridge
