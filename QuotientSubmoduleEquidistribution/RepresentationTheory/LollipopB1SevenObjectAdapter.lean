import QuotientSubmoduleEquidistribution.RepresentationTheory.LollipopB1QuotientBounds
import QuotientSubmoduleEquidistribution.RepresentationTheory.LollipopB1QuotientPresentations
import QuotientSubmoduleEquidistribution.RepresentationTheory.LollipopB1SubmoduleBounds
import QuotientSubmoduleEquidistribution.RepresentationTheory.LollipopRelationTables
import QuotientSubmoduleEquidistribution.RepresentationTheory.LollipopZeroHomCertificates
import QuotientSubmoduleEquidistribution.RepresentationTheory.FiniteLengthDecomposition

/-!
# Scratch seven-object adapter for the live-path lollipop

This file aligns the seven genuine `B1Model` modules with the maintained
live-path relation table.  It is deliberately conditional on the three pieces
that are not yet tracked for `B1Model`: indecomposability, duplicate-freeness,
and exhaustive classification of the seven named modules.  It also leaves the
two quotient-bad epimorphisms as explicit inputs.  Every good quotient and
submodule row, and both submodule-bad rows, are converted from the tracked
coordinate calculations.
-/

noncomputable section

open Set
open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.LollipopConcrete.B1.ModuleLayer.SevenObjectAdapter

open QuotientRows SubmoduleRows QuotientPresentations

universe u v w

variable (K : Type u) [Field K]

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

abbrev Label :=
  QuotientSubmoduleEquidistribution.BottomLevels.LollipopRelationTables.LivePathLabel

/-- The seven named objects in the relation-table order. -/
def obj : Label → FGModuleCat (B1Model K)
  | .s1 => S1Module K
  | .s2 => S2Module K
  | .x => XModule K
  | .a => AModule K
  | .u => UModule K
  | .w => WModule K
  | .p => PModule K

/-- The exact future module-theoretic input needed to obtain a genuine
duplicate-free, complete skeleton.  Finite length and arbitrary finite
decomposition are derived rather than assumed. -/
structure Classification where
  indecomposable :
    ∀ i, QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule (B1Model K) (obj K i)
  eq_of_iso :
    ∀ {i j}, Nonempty (obj K i ≅ obj K j) → i = j
  exhaustive :
    ∀ M : FGModuleCat (B1Model K),
      QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule (B1Model K) M →
        ∃ i, Nonempty (M ≅ obj K i)

/-- Every finitely generated module over the finite-dimensional live-path
model has finite length. -/
theorem b1Module_finiteLength (M : FGModuleCat.{u} (B1Model K)) :
    IsFiniteLength (B1Model K) M := by
  exact
    ((IsArtinianRing.tfae (B1Model K) M).out 0 3).mp
      (inferInstance : Module.Finite (B1Model K) M)

/-- The seven-object skeleton conditional only on `Classification`. -/
def skeleton (C : Classification K) :
    IndecomposableSkeleton (B1Model K) Label where
  obj := obj K
  indecomposable := C.indecomposable
  finiteLength i := b1Module_finiteLength K (obj K i)
  eq_of_iso := C.eq_of_iso
  complete := C.exhaustive
  decomposes := by
    intro M
    obtain ⟨n, Y, hY, ⟨e⟩⟩ :=
      QuotientSubmoduleEquidistribution.FiniteLengthDecomposition.exists_fin_biproduct_decomposition
        M (b1Module_finiteLength K M)
    let label : Fin n → Label := fun t ↦
      Classical.choose (C.exhaustive (Y t) (hY t))
    let iso (t : Fin n) : Y t ≅ obj K (label t) :=
      Classical.choice (Classical.choose_spec (C.exhaustive (Y t) (hY t)))
    exact ⟨n, label, ⟨e ≪≫ biproduct.mapIso iso⟩⟩

/-! ## Intended three-object cores -/

/-- Intended quotient-faithful core: `X,U,S1`. -/
def quotientCore : Set Label := {.x, .u, .s1}

/-- Intended submodule-faithful core: `P,S2,A`. -/
def submoduleCore : Set Label := {.p, .s2, .a}

@[simp] theorem mem_quotientCore (i : Label) :
    i ∈ quotientCore ↔ i = .x ∨ i = .u ∨ i = .s1 := by
  simp [quotientCore]

@[simp] theorem mem_submoduleCore (i : Label) :
    i ∈ submoduleCore ↔ i = .p ∨ i = .s2 ∨ i = .a := by
  simp [submoduleCore]

theorem quotientCore_ncard : quotientCore.ncard = 3 := by
  exact Set.ncard_eq_three.mpr
    ⟨.x, .u, .s1, by decide, by decide, by decide, rfl⟩

theorem submoduleCore_ncard : submoduleCore.ncard = 3 := by
  exact Set.ncard_eq_three.mpr
    ⟨.p, .s2, .a, by decide, by decide, by decide, rfl⟩

/-! ## Generic finite-biproduct aggregation -/

/-- A common pointwise range bound for all selected representatives bounds
the skeleton trace. -/
theorem trace_le_of_forall_range_le
    {R : Type u} [Ring R] [IsNoetherianRing R]
    {ι : Type v}
    (σ : IndecomposableSkeleton.{u, v, w} R ι)
    {S : Set ι} {Y : FGModuleCat.{w} R}
    (bound : Submodule R Y)
    (hrange : ∀ i : ι, i ∈ S → ∀ f : σ.obj i ⟶ Y,
      LinearMap.range f.hom.hom ≤ bound) :
    σ.trace S Y ≤ bound := by
  apply iSup_le
  intro F
  let Q : FGModuleCat.{w} R := FGModuleCat.of R (Y ⧸ bound)
  let q : Y ⟶ Q := FGModuleCat.ofHom bound.mkQ
  have hcomp : F.map ≫ q = 0 := by
    apply biproduct.hom_ext'
    intro t
    let g : σ.obj (F.label t) ⟶ Y :=
      biproduct.ι (fun s : F.index ↦ σ.obj (F.label s)) t ≫ F.map
    change g ≫ q = 0
    apply FGModuleCat.hom_ext
    change bound.mkQ.comp g.hom.hom = 0
    rw [← LinearMap.range_le_ker_iff, Submodule.ker_mkQ]
    exact hrange (F.label t) (F.mem t) g
  rw [← Submodule.ker_mkQ bound, LinearMap.range_le_ker_iff]
  have hlinear := congrArg (fun z ↦ z.hom.hom) hcomp
  change bound.mkQ.comp F.map.hom.hom = 0 at hlinear
  exact hlinear

/-- Package a common proper range bound as a skeleton omission certificate. -/
def quotientOmissionOfRangeBound
    (C : Classification K)
    {S : Set Label} {j : Label}
    (hnot : j ∉ S)
    (bound : Submodule (B1Model K) (obj K j))
    (bound_ne_top : bound ≠ ⊤)
    (hrange : ∀ i : Label, i ∈ S → ∀ f : obj K i ⟶ obj K j,
      LinearMap.range f.hom.hom ≤ bound) :
    QuotientSubmoduleEquidistribution.BottomLevels.LollipopTableCertificates.Quotient.OmissionCertificate
      (skeleton K C) S j where
  not_mem := hnot
  bound := bound
  bound_ne_top := bound_ne_top
  trace_le_bound := trace_le_of_forall_range_le (skeleton K C) bound hrange

private theorem biproduct_apply_eq_zero_of_components
    {R : Type u} [Ring R]
    {J : Type*} [Fintype J]
    {X : FGModuleCat.{w} R} {Y : J → FGModuleCat.{w} R}
    (g : X ⟶ ⨁ Y) (z : X)
    (h : ∀ j, (g ≫ biproduct.π Y j).hom.hom z = 0) :
    g.hom.hom z = 0 := by
  classical
  let cyclic : Submodule R X := R ∙ z
  letI : Module.Finite R cyclic :=
    Module.Finite.of_fg (Submodule.fg_span_singleton z)
  let inclusion : FGModuleCat.of R cyclic ⟶ X :=
    FGModuleCat.ofHom cyclic.subtype
  have hzero : inclusion ≫ g = 0 := by
    apply biproduct.hom_ext
    intro j
    simp only [Category.assoc, zero_comp]
    apply FGModuleCat.hom_ext
    ext y
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp y.2
    change (g ≫ biproduct.π Y j).hom.hom y.1 = 0
    rw [← hr, map_smul, h j, smul_zero]
  let y : cyclic := ⟨z, Submodule.mem_span_singleton_self z⟩
  have hy := congrArg
    (fun f : FGModuleCat.of R cyclic ⟶ ⨁ Y ↦ f.hom.hom y) hzero
  change g.hom.hom (cyclic.subtype y) = 0 at hy
  exact hy

/-- A common nonzero pointwise kernel is contained in the skeleton reject. -/
theorem witness_le_reject_of_forall_le_ker
    {R : Type u} [Ring R] [IsNoetherianRing R]
    {ι : Type v}
    (σ : IndecomposableSkeleton.{u, v, w} R ι)
    {S : Set ι} {X : FGModuleCat.{w} R}
    (witness : Submodule R X)
    (hker : ∀ i : ι, i ∈ S → ∀ f : X ⟶ σ.obj i,
      witness ≤ LinearMap.ker f.hom.hom) :
    witness ≤ σ.reject S X := by
  apply le_iInf
  intro F
  letI : Fintype F.index := FintypeCat.fintype
  intro z hz
  rw [LinearMap.mem_ker]
  apply biproduct_apply_eq_zero_of_components F.map z
  intro t
  exact LinearMap.mem_ker.mp
    (hker (F.label t) (F.mem t)
      (F.map ≫ biproduct.π
        (fun s : F.index ↦ σ.obj (F.label s)) t) hz)

/-! ## The two quotient-good rows -/

theorem quotientA_hom_S2_eq_zero
    (i : Label) (hi : i ∈ insert .a quotientCore)
    (f : obj K i ⟶ S2Module K) : f = 0 := by
  cases i with
  | s1 => exact (aRow_hom_S2_eq_zero K .s1 f)
  | s2 => simp [quotientCore] at hi
  | x => exact (aRow_hom_S2_eq_zero K .x f)
  | a => exact (aRow_hom_S2_eq_zero K .a f)
  | u => exact (aRow_hom_S2_eq_zero K .u f)
  | w => simp [quotientCore] at hi
  | p => simp [quotientCore] at hi

theorem quotientA_range_W_le
    (i : Label) (hi : i ∈ insert .a quotientCore)
    (f : obj K i ⟶ WModule K) :
    LinearMap.range f.hom.hom ≤ wTopBound K := by
  cases i with
  | s1 => exact (aRowWCommonRangeCertificate K).range_le .s1 f
  | s2 => simp [quotientCore] at hi
  | x => exact (aRowWCommonRangeCertificate K).range_le .x f
  | a => exact (aRowWCommonRangeCertificate K).range_le .a f
  | u => exact (aRowWCommonRangeCertificate K).range_le .u f
  | w => simp [quotientCore] at hi
  | p => simp [quotientCore] at hi

theorem quotientA_range_P_le
    (i : Label) (hi : i ∈ insert .a quotientCore)
    (f : obj K i ⟶ PModule K) :
    LinearMap.range f.hom.hom ≤ pTopBound K := by
  cases i with
  | s1 => exact (aRowPCommonRangeCertificate K).range_le .s1 f
  | s2 => simp [quotientCore] at hi
  | x => exact (aRowPCommonRangeCertificate K).range_le .x f
  | a => exact (aRowPCommonRangeCertificate K).range_le .a f
  | u => exact (aRowPCommonRangeCertificate K).range_le .u f
  | w => simp [quotientCore] at hi
  | p => simp [quotientCore] at hi

theorem quotientS2_range_A_le
    (i : Label) (hi : i ∈ insert .s2 quotientCore)
    (f : obj K i ⟶ AModule K) :
    LinearMap.range f.hom.hom ≤ aVertexTwoBound K := by
  cases i with
  | s1 => exact (s2RowACommonRangeCertificate K).range_le .s1 f
  | s2 => exact (s2RowACommonRangeCertificate K).range_le .s2 f
  | x => exact (s2RowACommonRangeCertificate K).range_le .x f
  | a => simp [quotientCore] at hi
  | u => exact (s2RowACommonRangeCertificate K).range_le .u f
  | w => simp [quotientCore] at hi
  | p => simp [quotientCore] at hi

theorem quotientS2_range_W_le
    (i : Label) (hi : i ∈ insert .s2 quotientCore)
    (f : obj K i ⟶ WModule K) :
    LinearMap.range f.hom.hom ≤ wTopBound K := by
  cases i with
  | s1 => exact (s2RowWCommonRangeCertificate K).range_le .s1 f
  | s2 => exact (s2RowWCommonRangeCertificate K).range_le .s2 f
  | x => exact (s2RowWCommonRangeCertificate K).range_le .x f
  | a => simp [quotientCore] at hi
  | u => exact (s2RowWCommonRangeCertificate K).range_le .u f
  | w => simp [quotientCore] at hi
  | p => simp [quotientCore] at hi

theorem quotientS2_range_P_le
    (i : Label) (hi : i ∈ insert .s2 quotientCore)
    (f : obj K i ⟶ PModule K) :
    LinearMap.range f.hom.hom ≤ pTopBound K := by
  cases i with
  | s1 => exact (s2RowPCommonRangeCertificate K).range_le .s1 f
  | s2 => exact (s2RowPCommonRangeCertificate K).range_le .s2 f
  | x => exact (s2RowPCommonRangeCertificate K).range_le .x f
  | a => simp [quotientCore] at hi
  | u => exact (s2RowPCommonRangeCertificate K).range_le .u f
  | w => simp [quotientCore] at hi
  | p => simp [quotientCore] at hi

def quotientA_omission_S2 (C : Classification K) :
    QuotientSubmoduleEquidistribution.BottomLevels.LollipopTableCertificates.Quotient.OmissionCertificate
      (skeleton K C) (insert .a quotientCore) .s2 :=
  QuotientSubmoduleEquidistribution.BottomLevels.LollipopTableCertificates.Quotient.omissionCertificateOfHomEqZero
    (skeleton K C) (by simp [quotientCore]) (quotientA_hom_S2_eq_zero K)

def quotientA_omission_W (C : Classification K) :
    QuotientSubmoduleEquidistribution.BottomLevels.LollipopTableCertificates.Quotient.OmissionCertificate
      (skeleton K C) (insert .a quotientCore) .w :=
  quotientOmissionOfRangeBound K C (by simp [quotientCore])
    (wTopBound K) (wTopBound_ne_top K) (quotientA_range_W_le K)

def quotientA_omission_P (C : Classification K) :
    QuotientSubmoduleEquidistribution.BottomLevels.LollipopTableCertificates.Quotient.OmissionCertificate
      (skeleton K C) (insert .a quotientCore) .p :=
  quotientOmissionOfRangeBound K C (by simp [quotientCore])
    (pTopBound K) (pTopBound_ne_top K) (quotientA_range_P_le K)

def quotientS2_omission_A (C : Classification K) :
    QuotientSubmoduleEquidistribution.BottomLevels.LollipopTableCertificates.Quotient.OmissionCertificate
      (skeleton K C) (insert .s2 quotientCore) .a :=
  quotientOmissionOfRangeBound K C (by simp [quotientCore])
    (aVertexTwoBound K) (aVertexTwoBound_ne_top K)
    (quotientS2_range_A_le K)

def quotientS2_omission_W (C : Classification K) :
    QuotientSubmoduleEquidistribution.BottomLevels.LollipopTableCertificates.Quotient.OmissionCertificate
      (skeleton K C) (insert .s2 quotientCore) .w :=
  quotientOmissionOfRangeBound K C (by simp [quotientCore])
    (wTopBound K) (wTopBound_ne_top K) (quotientS2_range_W_le K)

def quotientS2_omission_P (C : Classification K) :
    QuotientSubmoduleEquidistribution.BottomLevels.LollipopTableCertificates.Quotient.OmissionCertificate
      (skeleton K C) (insert .s2 quotientCore) .p :=
  quotientOmissionOfRangeBound K C (by simp [quotientCore])
    (pTopBound K) (pTopBound_ne_top K) (quotientS2_range_P_le K)

def quotientA_omissions (C : Classification K) :
    ∀ j : Label, j ∉ insert .a quotientCore →
      QuotientSubmoduleEquidistribution.BottomLevels.LollipopTableCertificates.Quotient.OmissionCertificate
        (skeleton K C) (insert .a quotientCore) j := by
  intro j hj
  cases j with
  | s1 => simp [quotientCore] at hj
  | s2 => exact quotientA_omission_S2 K C
  | x => simp [quotientCore] at hj
  | a => simp [quotientCore] at hj
  | u => simp [quotientCore] at hj
  | w => exact quotientA_omission_W K C
  | p => exact quotientA_omission_P K C

def quotientS2_omissions (C : Classification K) :
    ∀ j : Label, j ∉ insert .s2 quotientCore →
      QuotientSubmoduleEquidistribution.BottomLevels.LollipopTableCertificates.Quotient.OmissionCertificate
        (skeleton K C) (insert .s2 quotientCore) j := by
  intro j hj
  cases j with
  | s1 => simp [quotientCore] at hj
  | s2 => simp [quotientCore] at hj
  | x => simp [quotientCore] at hj
  | a => exact quotientS2_omission_A K C
  | u => simp [quotientCore] at hj
  | w => exact quotientS2_omission_W K C
  | p => exact quotientS2_omission_P K C

/-! ## The two submodule-good rows -/

theorem submoduleS1_uSocle_le_ker
    (i : Label) (hi : i ∈ insert .s1 submoduleCore)
    (f : UModule K ⟶ obj K i) :
    uSocleLine K ≤ LinearMap.ker f.hom.hom := by
  cases i with
  | s1 => exact (s1RowUCommonKernelCertificate K).witness_le_ker .s1 f
  | s2 => exact (s1RowUCommonKernelCertificate K).witness_le_ker .s2 f
  | x => simp [submoduleCore] at hi
  | a => exact (s1RowUCommonKernelCertificate K).witness_le_ker .a f
  | u => simp [submoduleCore] at hi
  | w => simp [submoduleCore] at hi
  | p => exact (s1RowUCommonKernelCertificate K).witness_le_ker .p f

theorem submoduleS1_xSocle_le_ker
    (i : Label) (hi : i ∈ insert .s1 submoduleCore)
    (f : XModule K ⟶ obj K i) :
    xSocleLine K ≤ LinearMap.ker f.hom.hom := by
  cases i with
  | s1 => exact (s1RowXCommonKernelCertificate K).witness_le_ker .s1 f
  | s2 => exact (s1RowXCommonKernelCertificate K).witness_le_ker .s2 f
  | x => simp [submoduleCore] at hi
  | a => exact (s1RowXCommonKernelCertificate K).witness_le_ker .a f
  | u => simp [submoduleCore] at hi
  | w => simp [submoduleCore] at hi
  | p => exact (s1RowXCommonKernelCertificate K).witness_le_ker .p f

theorem submoduleS1_wSocle_le_ker
    (i : Label) (hi : i ∈ insert .s1 submoduleCore)
    (f : WModule K ⟶ obj K i) :
    wSocleLine K ≤ LinearMap.ker f.hom.hom := by
  cases i with
  | s1 => exact (s1RowWCommonKernelCertificate K).witness_le_ker .s1 f
  | s2 => exact (s1RowWCommonKernelCertificate K).witness_le_ker .s2 f
  | x => simp [submoduleCore] at hi
  | a => exact (s1RowWCommonKernelCertificate K).witness_le_ker .a f
  | u => simp [submoduleCore] at hi
  | w => simp [submoduleCore] at hi
  | p => exact (s1RowWCommonKernelCertificate K).witness_le_ker .p f

theorem submoduleU_s1Generator_le_ker
    (i : Label) (hi : i ∈ insert .u submoduleCore)
    (f : S1Module K ⟶ obj K i) :
    s1GeneratorLine K ≤ LinearMap.ker f.hom.hom := by
  cases i with
  | s1 => simp [submoduleCore] at hi
  | s2 => exact (uRowS1CommonKernelCertificate K).witness_le_ker .s2 f
  | x => simp [submoduleCore] at hi
  | a => exact (uRowS1CommonKernelCertificate K).witness_le_ker .a f
  | u => exact (uRowS1CommonKernelCertificate K).witness_le_ker .u f
  | w => simp [submoduleCore] at hi
  | p => exact (uRowS1CommonKernelCertificate K).witness_le_ker .p f

theorem submoduleU_xSocle_le_ker
    (i : Label) (hi : i ∈ insert .u submoduleCore)
    (f : XModule K ⟶ obj K i) :
    xSocleLine K ≤ LinearMap.ker f.hom.hom := by
  cases i with
  | s1 => simp [submoduleCore] at hi
  | s2 => exact (uRowXCommonKernelCertificate K).witness_le_ker .s2 f
  | x => simp [submoduleCore] at hi
  | a => exact (uRowXCommonKernelCertificate K).witness_le_ker .a f
  | u => exact (uRowXCommonKernelCertificate K).witness_le_ker .u f
  | w => simp [submoduleCore] at hi
  | p => exact (uRowXCommonKernelCertificate K).witness_le_ker .p f

theorem submoduleU_wSocle_le_ker
    (i : Label) (hi : i ∈ insert .u submoduleCore)
    (f : WModule K ⟶ obj K i) :
    wSocleLine K ≤ LinearMap.ker f.hom.hom := by
  cases i with
  | s1 => simp [submoduleCore] at hi
  | s2 => exact (uRowWCommonKernelCertificate K).witness_le_ker .s2 f
  | x => simp [submoduleCore] at hi
  | a => exact (uRowWCommonKernelCertificate K).witness_le_ker .a f
  | u => exact (uRowWCommonKernelCertificate K).witness_le_ker .u f
  | w => simp [submoduleCore] at hi
  | p => exact (uRowWCommonKernelCertificate K).witness_le_ker .p f

def submoduleOmissionOfKernelWitness
    (C : Classification K)
    {S : Set Label} {j : Label}
    (hnot : j ∉ S)
    (witness : Submodule (B1Model K) (obj K j))
    (witness_ne_bot : witness ≠ ⊥)
    (hker : ∀ i : Label, i ∈ S → ∀ f : obj K j ⟶ obj K i,
      witness ≤ LinearMap.ker f.hom.hom) :
    QuotientSubmoduleEquidistribution.BottomLevels.LollipopTableCertificates.Submodule.OmissionCertificate
      (skeleton K C) S j where
  not_mem := hnot
  witness := witness
  witness_ne_bot := witness_ne_bot
  witness_le_reject :=
    witness_le_reject_of_forall_le_ker (skeleton K C) witness hker

def submoduleS1_omission_U (C : Classification K) :
    QuotientSubmoduleEquidistribution.BottomLevels.LollipopTableCertificates.Submodule.OmissionCertificate
      (skeleton K C) (insert .s1 submoduleCore) .u :=
  submoduleOmissionOfKernelWitness K C (by simp [submoduleCore])
    (uSocleLine K) (uSocleLine_ne_bot K) (submoduleS1_uSocle_le_ker K)

def submoduleS1_omission_X (C : Classification K) :
    QuotientSubmoduleEquidistribution.BottomLevels.LollipopTableCertificates.Submodule.OmissionCertificate
      (skeleton K C) (insert .s1 submoduleCore) .x :=
  submoduleOmissionOfKernelWitness K C (by simp [submoduleCore])
    (xSocleLine K) (xSocleLine_ne_bot K) (submoduleS1_xSocle_le_ker K)

def submoduleS1_omission_W (C : Classification K) :
    QuotientSubmoduleEquidistribution.BottomLevels.LollipopTableCertificates.Submodule.OmissionCertificate
      (skeleton K C) (insert .s1 submoduleCore) .w :=
  submoduleOmissionOfKernelWitness K C (by simp [submoduleCore])
    (wSocleLine K) (wSocleLine_ne_bot K) (submoduleS1_wSocle_le_ker K)

def submoduleU_omission_S1 (C : Classification K) :
    QuotientSubmoduleEquidistribution.BottomLevels.LollipopTableCertificates.Submodule.OmissionCertificate
      (skeleton K C) (insert .u submoduleCore) .s1 :=
  submoduleOmissionOfKernelWitness K C (by simp [submoduleCore])
    (s1GeneratorLine K) (s1GeneratorLine_ne_bot K)
    (submoduleU_s1Generator_le_ker K)

def submoduleU_omission_X (C : Classification K) :
    QuotientSubmoduleEquidistribution.BottomLevels.LollipopTableCertificates.Submodule.OmissionCertificate
      (skeleton K C) (insert .u submoduleCore) .x :=
  submoduleOmissionOfKernelWitness K C (by simp [submoduleCore])
    (xSocleLine K) (xSocleLine_ne_bot K) (submoduleU_xSocle_le_ker K)

def submoduleU_omission_W (C : Classification K) :
    QuotientSubmoduleEquidistribution.BottomLevels.LollipopTableCertificates.Submodule.OmissionCertificate
      (skeleton K C) (insert .u submoduleCore) .w :=
  submoduleOmissionOfKernelWitness K C (by simp [submoduleCore])
    (wSocleLine K) (wSocleLine_ne_bot K) (submoduleU_wSocle_le_ker K)

def submoduleS1_omissions (C : Classification K) :
    ∀ j : Label, j ∉ insert .s1 submoduleCore →
      QuotientSubmoduleEquidistribution.BottomLevels.LollipopTableCertificates.Submodule.OmissionCertificate
        (skeleton K C) (insert .s1 submoduleCore) j := by
  intro j hj
  cases j with
  | s1 => simp [submoduleCore] at hj
  | s2 => simp [submoduleCore] at hj
  | x => exact submoduleS1_omission_X K C
  | a => simp [submoduleCore] at hj
  | u => exact submoduleS1_omission_U K C
  | w => exact submoduleS1_omission_W K C
  | p => simp [submoduleCore] at hj

def submoduleU_omissions (C : Classification K) :
    ∀ j : Label, j ∉ insert .u submoduleCore →
      QuotientSubmoduleEquidistribution.BottomLevels.LollipopTableCertificates.Submodule.OmissionCertificate
        (skeleton K C) (insert .u submoduleCore) j := by
  intro j hj
  cases j with
  | s1 => exact submoduleU_omission_S1 K C
  | s2 => simp [submoduleCore] at hj
  | x => exact submoduleU_omission_X K C
  | a => simp [submoduleCore] at hj
  | u => simp [submoduleCore] at hj
  | w => exact submoduleU_omission_W K C
  | p => simp [submoduleCore] at hj

/-! ## The two submodule-bad rows -/

/-- The tracked `W → X ⊕ P` map, with its codomain family written directly
in skeleton labels. -/
def wIntoSubmoduleXSum :
    obj K .w ⟶
      biproduct (fun t : FintypeCat.of Bool ↦
        obj K (match t with | false => .x | true => .p)) :=
  biproduct.lift fun t ↦
    match t with
    | false => wToX K
    | true => wToP K

@[simp] theorem wIntoSubmoduleXSum_false :
    wIntoSubmoduleXSum K ≫
        biproduct.π
          (fun t : FintypeCat.of Bool ↦
            obj K (match t with | false => .x | true => .p)) false =
      wToX K := by
  simp [wIntoSubmoduleXSum]

@[simp] theorem wIntoSubmoduleXSum_true :
    wIntoSubmoduleXSum K ≫
        biproduct.π
          (fun t : FintypeCat.of Bool ↦
            obj K (match t with | false => .x | true => .p)) true =
      wToP K := by
  simp [wIntoSubmoduleXSum]

theorem wIntoSubmoduleXSum_injective :
    Function.Injective (wIntoSubmoduleXSum K).hom.hom := by
  intro z z' h
  have hxmap : (wToX K).hom.hom z = (wToX K).hom.hom z' := by
    have h' := congrArg
      (fun q ↦
        (biproduct.π
          (fun t : FintypeCat.of Bool ↦
            obj K (match t with | false => .x | true => .p))
          false).hom.hom q) h
    rw [← wIntoSubmoduleXSum_false K]
    exact h'
  have hpmap : (wToP K).hom.hom z = (wToP K).hom.hom z' := by
    have h' := congrArg
      (fun q ↦
        (biproduct.π
          (fun t : FintypeCat.of Bool ↦
            obj K (match t with | false => .x | true => .p))
          true).hom.hom q) h
    rw [← wIntoSubmoduleXSum_true K]
    exact h'
  have hV₁ : z.1 = z'.1 := by
    have hcoord := congrArg (fun q : XModule K ↦ q.1) hxmap
    change z.1 = z'.1 at hcoord
    exact hcoord
  have hV₂ : z.2 = z'.2 := by
    have hcoord := congrArg (fun q : PModule K ↦ q.2.2) hpmap
    change z.2 = z'.2 at hcoord
    exact hcoord
  exact Prod.ext hV₁ hV₂

theorem wIntoSubmoduleXSum_mono : Mono (wIntoSubmoduleXSum K) :=
  (IndecomposableSkeleton.fg_mono_iff_injective (wIntoSubmoduleXSum K)).mpr
    (wIntoSubmoduleXSum_injective K)

/-- Adding `X` to `{P,S2,A}` embeds the omitted `W` into `X ⊕ P`. -/
def submoduleX_generates_W (C : Classification K) :
    (skeleton K C).SubPresentation
      (insert .x submoduleCore) (obj K .w) where
  index := FintypeCat.of Bool
  label
    | false => .x
    | true => .p
  mem t := by cases t <;> simp [submoduleCore]
  map := wIntoSubmoduleXSum K
  mono := wIntoSubmoduleXSum_mono K

/-- Adding `W` to `{P,S2,A}` embeds the omitted `S1` into `W`. -/
def submoduleW_generates_S1 (C : Classification K) :
    (skeleton K C).SubPresentation
      (insert .w submoduleCore) (obj K .s1) where
  index := FintypeCat.of (Fin 1)
  label := fun _ ↦ .w
  mem _ := by simp [submoduleCore]
  map := s1IntoWBadRowSum K
  mono := s1IntoWBadRowSum_mono K

/-! ## Full table assembly, conditional only on the remaining inputs -/

/-- Turn a single epimorphism from a selected named object into a finite-sum
quotient presentation. -/
def singletonFacPresentation
    (C : Classification K) {S : Set Label} {i j : Label}
    (hi : i ∈ S) (f : obj K i ⟶ obj K j) [Epi f] :
    (skeleton K C).FacPresentation S (obj K j) where
  index := FintypeCat.of (Fin 1)
  label := fun _ ↦ i
  mem := fun _ ↦ hi
  map := (biproductUniqueIso fun _ : Fin 1 ↦ obj K i).hom ≫ f
  epi := inferInstance

/-- The two quotient-bad presentations which the coordinate layer must
supply.  They are kept separate from classification and actual-core data. -/
structure QuotientBadPresentations (C : Classification K) where
  p_generates_w :
    (skeleton K C).FacPresentation
      (insert .p quotientCore) (obj K .w)
  w_generates_a :
    (skeleton K C).FacPresentation
      (insert .w quotientCore) (obj K .a)

/-- Both quotient-bad rows, supplied by the explicit epimorphisms
`P ⟶ W` and `W ⟶ A`. -/
def quotientBadPresentations (C : Classification K) :
    QuotientBadPresentations K C where
  p_generates_w := by
    let f : obj K .p ⟶ obj K .w := pToW K
    letI : Epi f := by
      change Epi (pToW K)
      exact pToW_epi K
    exact singletonFacPresentation K C (by simp [quotientCore]) f
  w_generates_a := by
    let f : obj K .w ⟶ obj K .a := wToA K
    letI : Epi f := by
      change Epi (wToA K)
      exact wToA_epi K
    exact singletonFacPresentation K C (by simp [quotientCore]) f

/-- Complete live-path certificates for supplied actual minimal faithful
cores.  No claim that the displayed core sets are actual is made here; those
identifications are explicit hypotheses. -/
def actualLivePathCertificates
    (C : Classification K)
    (badQ : QuotientBadPresentations K C)
    {FaithfulQ FaithfulS : Set Label → Prop}
    (QCore : QuotientSubmoduleEquidistribution.BottomLevels.MinimalFaithfulCore.Data
      (skeleton K C).qClosure FaithfulQ)
    (SCore : QuotientSubmoduleEquidistribution.BottomLevels.MinimalFaithfulCore.Data
      (skeleton K C).sClosure FaithfulS)
    (faithfulQ_monotone : Monotone FaithfulQ)
    (faithfulS_monotone : Monotone FaithfulS)
    (quotient_core : (QCore.core : Set Label) = quotientCore)
    (submodule_core : (SCore.core : Set Label) = submoduleCore) :
    QuotientSubmoduleEquidistribution.BottomLevels.LollipopRelationTables.LivePathCertificates
      (skeleton K C) (QCore := QCore) (SCore := SCore) where
  label := Equiv.refl Label
  faithfulQ_monotone := faithfulQ_monotone
  faithfulS_monotone := faithfulS_monotone
  quotient_core := by
    rw [quotient_core]
    ext i
    cases i <;> simp [quotientCore]
  submodule_core := by
    rw [submodule_core]
    ext i
    cases i <;> simp [submoduleCore]
  quotient_a_omissions := by
    intro j hj
    rw [quotient_core] at hj ⊢
    exact quotientA_omissions K C j hj
  quotient_s2_omissions := by
    intro j hj
    rw [quotient_core] at hj ⊢
    exact quotientS2_omissions K C j hj
  quotient_p_generates_w := by
    rw [quotient_core]
    exact badQ.p_generates_w
  quotient_w_generates_a := by
    rw [quotient_core]
    exact badQ.w_generates_a
  submodule_s1_omissions := by
    intro j hj
    rw [submodule_core] at hj ⊢
    exact submoduleS1_omissions K C j hj
  submodule_u_omissions := by
    intro j hj
    rw [submodule_core] at hj ⊢
    exact submoduleU_omissions K C j hj
  submodule_x_generates_w := by
    rw [submodule_core]
    exact submoduleX_generates_W K C
  submodule_w_generates_s1 := by
    rw [submodule_core]
    exact submoduleW_generates_S1 K C

/-- Literal connected-small-core table data for supplied actual faithful
cores. -/
def actualTableData
    (C : Classification K)
    (badQ : QuotientBadPresentations K C)
    {FaithfulQ FaithfulS : Set Label → Prop}
    (QCore : QuotientSubmoduleEquidistribution.BottomLevels.MinimalFaithfulCore.Data
      (skeleton K C).qClosure FaithfulQ)
    (SCore : QuotientSubmoduleEquidistribution.BottomLevels.MinimalFaithfulCore.Data
      (skeleton K C).sClosure FaithfulS)
    (faithfulQ_monotone : Monotone FaithfulQ)
    (faithfulS_monotone : Monotone FaithfulS)
    (quotient_core : (QCore.core : Set Label) = quotientCore)
    (submodule_core : (SCore.core : Set Label) = submoduleCore) :
    QuotientSubmoduleEquidistribution.BottomLevels.ConnectedSmallCore.LollipopTableData
      (fun _ : Unit ↦ Label)
      (fun _ ↦ (skeleton K C).qClosure)
      (fun _ ↦ (skeleton K C).sClosure)
      (fun _ ↦ FaithfulQ)
      (fun _ ↦ FaithfulS)
      (fun _ ↦ QCore)
      (fun _ ↦ SCore)
      () := by
  let D := actualLivePathCertificates K C badQ QCore SCore
    faithfulQ_monotone faithfulS_monotone quotient_core submodule_core
  exact {
    quotient := D.quotientNamed.toTwoExtensionData
    submodule := D.submoduleNamed.toTwoExtensionData }

/-- Conditional actual degree-four equality.  The only hypotheses are the
future classification/duplicate-free bundle, the two quotient-bad epis, and
the exact identification of the actual minimal faithful cores. -/
theorem actual_faithfulLevelCount_four_eq
    (C : Classification K)
    (badQ : QuotientBadPresentations K C)
    {FaithfulQ FaithfulS : Set Label → Prop}
    (QCore : QuotientSubmoduleEquidistribution.BottomLevels.MinimalFaithfulCore.Data
      (skeleton K C).qClosure FaithfulQ)
    (SCore : QuotientSubmoduleEquidistribution.BottomLevels.MinimalFaithfulCore.Data
      (skeleton K C).sClosure FaithfulS)
    (faithfulQ_monotone : Monotone FaithfulQ)
    (faithfulS_monotone : Monotone FaithfulS)
    (quotient_core : (QCore.core : Set Label) = quotientCore)
    (submodule_core : (SCore.core : Set Label) = submoduleCore) :
    QuotientSubmoduleEquidistribution.BottomLevels.MinimalFaithfulCore.faithfulLevelCount
        (skeleton K C).qClosure FaithfulQ 4 =
      QuotientSubmoduleEquidistribution.BottomLevels.MinimalFaithfulCore.faithfulLevelCount
        (skeleton K C).sClosure FaithfulS 4 :=
  (actualTableData K C badQ QCore SCore faithfulQ_monotone
    faithfulS_monotone quotient_core submodule_core).faithful_four_eq

end QuotientSubmoduleEquidistribution.LollipopConcrete.B1.ModuleLayer.SevenObjectAdapter
