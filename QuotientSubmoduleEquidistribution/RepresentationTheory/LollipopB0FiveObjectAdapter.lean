import QuotientSubmoduleEquidistribution.RepresentationTheory.LollipopB0NamedModuleProperties
import QuotientSubmoduleEquidistribution.RepresentationTheory.LollipopB0QuotientBounds
import QuotientSubmoduleEquidistribution.RepresentationTheory.LollipopB0SubmoduleBounds
import QuotientSubmoduleEquidistribution.RepresentationTheory.LollipopRelationTables
import QuotientSubmoduleEquidistribution.RepresentationTheory.FiniteLengthDecomposition

/-!
# Exact five-object adapter for the dead-path lollipop

This file aligns the five displayed `B₀` modules with the maintained
dead-path labels and turns the four concrete Hom/range/kernel calculations
into exact skeleton-level table certificates.

Indecomposability and pairwise nonisomorphism of the five objects are proved
in `LollipopB0NamedModuleProperties`.  The `Classification` input below
therefore retains only the genuine remaining module-classification
obligation: every indecomposable finitely generated module is one of the five
displayed objects.
-/

noncomputable section

open Set
open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.LollipopConcrete.ModuleLayer.FiveObjectAdapter

universe u v w

variable (K : Type u) [Field K]

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- Every finitely generated `B0Model`-module has finite length. -/
theorem b0Module_finiteLength (M : FGModuleCat.{u} (B0Model K)) :
    IsFiniteLength (B0Model K) M := by
  exact
    ((IsArtinianRing.tfae (B0Model K) M).out 0 3).mp
      (inferInstance : Module.Finite (B0Model K) M)

/-! ## The aligned five-object skeleton -/

abbrev Label :=
  QuotientSubmoduleEquidistribution.BottomLevels.LollipopRelationTables.DeadPathLabel

/-- The five concrete objects in the maintained dead-path table order. -/
def obj : Label → FGModuleCat (B0Model K)
  | .s1 => S1Module K
  | .s2 => S2Module K
  | .x => XModule K
  | .a => AModule K
  | .p => PModule K

/-- The sole remaining classification input for the five-object skeleton. -/
structure Classification where
  exhaustive :
    ∀ M : FGModuleCat (B0Model K),
      QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule (B0Model K) M →
        ∃ i, Nonempty (M ≅ obj K i)

private theorem not_iso_symm
    {X Y : FGModuleCat (B0Model K)}
    (h : ¬ Nonempty (X ≅ Y)) :
    ¬ Nonempty (Y ≅ X) := by
  rintro ⟨e⟩
  exact h ⟨e.symm⟩

/-- The five displayed objects are duplicate-free. -/
theorem obj_eq_of_iso {i j : Label}
    (h : Nonempty (obj K i ≅ obj K j)) : i = j := by
  cases i <;> cases j
  · rfl
  · exact (NamedModules.S1_not_iso_S2 K h).elim
  · exact (NamedModules.S1_not_iso_X K h).elim
  · exact (NamedModules.S1_not_iso_A K h).elim
  · exact (NamedModules.S1_not_iso_P K h).elim
  · exact (not_iso_symm K (NamedModules.S1_not_iso_S2 K) h).elim
  · rfl
  · exact (NamedModules.S2_not_iso_X K h).elim
  · exact (NamedModules.S2_not_iso_A K h).elim
  · exact (NamedModules.S2_not_iso_P K h).elim
  · exact (not_iso_symm K (NamedModules.S1_not_iso_X K) h).elim
  · exact (not_iso_symm K (NamedModules.S2_not_iso_X K) h).elim
  · rfl
  · exact (NamedModules.X_not_iso_A K h).elim
  · exact (NamedModules.X_not_iso_P K h).elim
  · exact (not_iso_symm K (NamedModules.S1_not_iso_A K) h).elim
  · exact (not_iso_symm K (NamedModules.S2_not_iso_A K) h).elim
  · exact (not_iso_symm K (NamedModules.X_not_iso_A K) h).elim
  · rfl
  · exact (NamedModules.A_not_iso_P K h).elim
  · exact (not_iso_symm K (NamedModules.S1_not_iso_P K) h).elim
  · exact (not_iso_symm K (NamedModules.S2_not_iso_P K) h).elim
  · exact (not_iso_symm K (NamedModules.X_not_iso_P K) h).elim
  · exact (not_iso_symm K (NamedModules.A_not_iso_P K) h).elim
  · rfl

/-- All five displayed objects are indecomposable. -/
theorem obj_indecomposable (i : Label) :
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule (B0Model K) (obj K i) := by
  cases i with
  | s1 => exact NamedModules.S1_indec K
  | s2 => exact NamedModules.S2_indec K
  | x => exact NamedModules.X_indec K
  | a => exact NamedModules.A_indec K
  | p => exact NamedModules.P_indec K

/-- The complete duplicate-free skeleton built from the one remaining
exhaustiveness theorem. -/
def skeleton (C : Classification K) :
    IndecomposableSkeleton (B0Model K) Label where
  obj := obj K
  indecomposable := obj_indecomposable K
  finiteLength i := b0Module_finiteLength K (obj K i)
  eq_of_iso := obj_eq_of_iso K
  complete := C.exhaustive
  decomposes := by
    intro M
    obtain ⟨n, Y, hY, ⟨e⟩⟩ :=
      QuotientSubmoduleEquidistribution.FiniteLengthDecomposition.exists_fin_biproduct_decomposition
        M (b0Module_finiteLength K M)
    let label : Fin n → Label := fun t ↦
      Classical.choose (C.exhaustive (Y t) (hY t))
    let iso (t : Fin n) : Y t ≅ obj K (label t) :=
      Classical.choice (Classical.choose_spec (C.exhaustive (Y t) (hY t)))
    exact ⟨n, label, ⟨e ≪≫ biproduct.mapIso iso⟩⟩

/-! ## Named cores and finite bookkeeping -/

/-- Quotient faithful core: `X,A,S₁`. -/
def quotientCore : Set Label := {.x, .a, .s1}

/-- Submodule faithful core: `P,S₂,S₁`. -/
def submoduleCore : Set Label := {.p, .s2, .s1}

@[simp] theorem mem_quotientCore (i : Label) :
    i ∈ quotientCore ↔ i = .x ∨ i = .a ∨ i = .s1 := by
  simp [quotientCore]

@[simp] theorem mem_submoduleCore (i : Label) :
    i ∈ submoduleCore ↔ i = .p ∨ i = .s2 ∨ i = .s1 := by
  simp [submoduleCore]

theorem quotientCore_ncard : quotientCore.ncard = 3 := by
  exact Set.ncard_eq_three.mpr
    ⟨.s1, .x, .a, by decide, by decide, by decide, by
      ext i
      cases i <;> simp [quotientCore]⟩

theorem submoduleCore_ncard : submoduleCore.ncard = 3 := by
  exact Set.ncard_eq_three.mpr
    ⟨.s1, .s2, .p, by decide, by decide, by decide, by
      ext i
      cases i <;> simp [submoduleCore]⟩

/-! ## Transport from the four concrete rows -/

theorem quotientP_hom_S2_eq_zero
    (i : Label) (hi : i ∈ insert .p quotientCore)
    (f : obj K i ⟶ S2Module K) : f = 0 := by
  cases i with
  | s1 => exact hom_S1_S2_eq_zero K f
  | s2 => simp [quotientCore] at hi
  | x => exact hom_X_S2_eq_zero K f
  | a => exact hom_A_S2_eq_zero K f
  | p => exact hom_P_S2_eq_zero K f

theorem quotientS2_range_le_pBound
    (i : Label) (hi : i ∈ insert .s2 quotientCore)
    (f : obj K i ⟶ PModule K) :
    LinearMap.range f.hom.hom ≤ PBound.pRadicalBound K := by
  cases i with
  | s1 => exact PBound.range_S1_P_le K f
  | s2 => exact PBound.range_S2_P_le K f
  | x => exact PBound.range_X_P_le K f
  | a => exact PBound.range_A_P_le K f
  | p => simp [quotientCore] at hi

theorem aStemLine_le_ker_of_mem_submoduleX
    (i : Label) (hi : i ∈ insert .x submoduleCore)
    (f : AModule K ⟶ obj K i) :
    SubmoduleBounds.AStemLine K ≤ LinearMap.ker f.hom.hom := by
  cases i with
  | s1 => exact SubmoduleBounds.AStemLine_le_ker_aSelected K .s1 f
  | s2 => exact SubmoduleBounds.AStemLine_le_ker_aSelected K .s2 f
  | x => exact SubmoduleBounds.AStemLine_le_ker_aSelected K .x f
  | a => simp [submoduleCore] at hi
  | p => exact SubmoduleBounds.AStemLine_le_ker_aSelected K .p f

theorem xSocleLine_le_ker_of_mem_submoduleA
    (i : Label) (hi : i ∈ insert .a submoduleCore)
    (f : XModule K ⟶ obj K i) :
    SubmoduleBounds.xSocleLine K ≤ LinearMap.ker f.hom.hom := by
  cases i with
  | s1 => exact SubmoduleBounds.xSocleLine_le_ker_xSelected K .s1 f
  | s2 => exact SubmoduleBounds.xSocleLine_le_ker_xSelected K .s2 f
  | x => simp [submoduleCore] at hi
  | a => exact SubmoduleBounds.xSocleLine_le_ker_xSelected K .a f
  | p => exact SubmoduleBounds.xSocleLine_le_ker_xSelected K .p f

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

/-- A common pointwise kernel bound is a bound for the maintained
finite-sum reject. -/
theorem witness_le_reject_of_forall_le_ker
    {R : Type u} [Ring R] [IsNoetherianRing R]
    {iota : Type v}
    (sigma : IndecomposableSkeleton.{u, v, w} R iota)
    {S : Set iota} {X : FGModuleCat.{w} R}
    (witness : Submodule R X)
    (hker : ∀ i : iota, i ∈ S → ∀ f : X ⟶ sigma.obj i,
      witness ≤ LinearMap.ker f.hom.hom) :
    witness ≤ sigma.reject S X := by
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
        (fun s : F.index ↦ sigma.obj (F.label s)) t) hz)

/-! ## Maintained omission certificates for the four good rows -/

def quotientP_omission (C : Classification K) :
    BottomLevels.LollipopTableCertificates.Quotient.OmissionCertificate
      (skeleton K C) (insert .p quotientCore) .s2 :=
  BottomLevels.LollipopTableCertificates.Quotient.omissionCertificateOfHomEqZero
    (skeleton K C) (by simp [quotientCore])
      (quotientP_hom_S2_eq_zero K)

def quotientS2_omission (C : Classification K) :
    BottomLevels.LollipopTableCertificates.Quotient.OmissionCertificate
      (skeleton K C) (insert .s2 quotientCore) .p :=
  PBound.omissionCertificateOfRangeBound
    (skeleton K C) (by simp [quotientCore])
      (PBound.pRadicalBound K)
      (PBound.pRadicalBound_ne_top K)
      (quotientS2_range_le_pBound K)

def submoduleX_omission (C : Classification K) :
    BottomLevels.LollipopTableCertificates.Submodule.OmissionCertificate
      (skeleton K C) (insert .x submoduleCore) .a where
  not_mem := by simp [submoduleCore]
  witness := SubmoduleBounds.AStemLine K
  witness_ne_bot := SubmoduleBounds.AStemLine_ne_bot K
  witness_le_reject :=
    witness_le_reject_of_forall_le_ker (skeleton K C)
      (SubmoduleBounds.AStemLine K)
      (aStemLine_le_ker_of_mem_submoduleX K)

def submoduleA_omission (C : Classification K) :
    BottomLevels.LollipopTableCertificates.Submodule.OmissionCertificate
      (skeleton K C) (insert .a submoduleCore) .x where
  not_mem := by simp [submoduleCore]
  witness := SubmoduleBounds.xSocleLine K
  witness_ne_bot := SubmoduleBounds.xSocleLine_ne_bot K
  witness_le_reject :=
    witness_le_reject_of_forall_le_ker (skeleton K C)
      (SubmoduleBounds.xSocleLine K)
      (xSocleLine_le_ker_of_mem_submoduleA K)

def quotientP_omissions (C : Classification K) :
    ∀ j : Label, j ∉ insert .p quotientCore →
      BottomLevels.LollipopTableCertificates.Quotient.OmissionCertificate
        (skeleton K C) (insert .p quotientCore) j := by
  intro j hj
  cases j with
  | s1 => simp [quotientCore] at hj
  | s2 => exact quotientP_omission K C
  | x => simp [quotientCore] at hj
  | a => simp [quotientCore] at hj
  | p => simp [quotientCore] at hj

def quotientS2_omissions (C : Classification K) :
    ∀ j : Label, j ∉ insert .s2 quotientCore →
      BottomLevels.LollipopTableCertificates.Quotient.OmissionCertificate
        (skeleton K C) (insert .s2 quotientCore) j := by
  intro j hj
  cases j with
  | s1 => simp [quotientCore] at hj
  | s2 => simp [quotientCore] at hj
  | x => simp [quotientCore] at hj
  | a => simp [quotientCore] at hj
  | p => exact quotientS2_omission K C

def submoduleX_omissions (C : Classification K) :
    ∀ j : Label, j ∉ insert .x submoduleCore →
      BottomLevels.LollipopTableCertificates.Submodule.OmissionCertificate
        (skeleton K C) (insert .x submoduleCore) j := by
  intro j hj
  cases j with
  | s1 => simp [submoduleCore] at hj
  | s2 => simp [submoduleCore] at hj
  | x => simp [submoduleCore] at hj
  | a => exact submoduleX_omission K C
  | p => simp [submoduleCore] at hj

def submoduleA_omissions (C : Classification K) :
    ∀ j : Label, j ∉ insert .a submoduleCore →
      BottomLevels.LollipopTableCertificates.Submodule.OmissionCertificate
        (skeleton K C) (insert .a submoduleCore) j := by
  intro j hj
  cases j with
  | s1 => simp [submoduleCore] at hj
  | s2 => simp [submoduleCore] at hj
  | x => exact submoduleA_omission K C
  | a => simp [submoduleCore] at hj
  | p => simp [submoduleCore] at hj

/-! ## Adapter for the manuscript's actual faithfulness predicates -/

/--
Align the concrete rows with supplied actual minimal faithful-core data.

Besides the one module-exhaustiveness theorem in `Classification`, the
remaining inputs are exactly monotonicity of actual faithfulness and the
identification of the actual quotient and submodule core carriers with the
two displayed three-object cores.
-/
def actualDeadPathCertificates
    (C : Classification K)
    {FaithfulQ FaithfulS : Set Label → Prop}
    (QCore : BottomLevels.MinimalFaithfulCore.Data
      (skeleton K C).qClosure FaithfulQ)
    (SCore : BottomLevels.MinimalFaithfulCore.Data
      (skeleton K C).sClosure FaithfulS)
    (faithfulQ_monotone : Monotone FaithfulQ)
    (faithfulS_monotone : Monotone FaithfulS)
    (quotient_core : (QCore.core : Set Label) = quotientCore)
    (submodule_core : (SCore.core : Set Label) = submoduleCore) :
    BottomLevels.LollipopRelationTables.DeadPathCertificates
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
  quotient_p_omissions := by
    intro j hj
    rw [quotient_core] at hj ⊢
    exact quotientP_omissions K C j hj
  quotient_s2_omissions := by
    intro j hj
    rw [quotient_core] at hj ⊢
    exact quotientS2_omissions K C j hj
  submodule_x_omissions := by
    intro j hj
    rw [submodule_core] at hj ⊢
    exact submoduleX_omissions K C j hj
  submodule_a_omissions := by
    intro j hj
    rw [submodule_core] at hj ⊢
    exact submoduleA_omissions K C j hj

/-- Literal recurrence table data for the actual faithfulness predicates. -/
def actualTableData
    (C : Classification K)
    {FaithfulQ FaithfulS : Set Label → Prop}
    (QCore : BottomLevels.MinimalFaithfulCore.Data
      (skeleton K C).qClosure FaithfulQ)
    (SCore : BottomLevels.MinimalFaithfulCore.Data
      (skeleton K C).sClosure FaithfulS)
    (faithfulQ_monotone : Monotone FaithfulQ)
    (faithfulS_monotone : Monotone FaithfulS)
    (quotient_core : (QCore.core : Set Label) = quotientCore)
    (submodule_core : (SCore.core : Set Label) = submoduleCore) :
    BottomLevels.ConnectedSmallCore.LollipopTableData
      (fun _ : Unit ↦ Label)
      (fun _ ↦ (skeleton K C).qClosure)
      (fun _ ↦ (skeleton K C).sClosure)
      (fun _ ↦ FaithfulQ)
      (fun _ ↦ FaithfulS)
      (fun _ ↦ QCore)
      (fun _ ↦ SCore)
      () := by
  let D := actualDeadPathCertificates K C QCore SCore
    faithfulQ_monotone faithfulS_monotone quotient_core submodule_core
  exact {
    quotient := D.quotientNamed.toTwoExtensionData
    submodule := D.submoduleNamed.toTwoExtensionData }

/-- The actual faithful degree-four counts agree for the dead-path table. -/
theorem actual_faithfulLevelCount_four_eq
    (C : Classification K)
    {FaithfulQ FaithfulS : Set Label → Prop}
    (QCore : BottomLevels.MinimalFaithfulCore.Data
      (skeleton K C).qClosure FaithfulQ)
    (SCore : BottomLevels.MinimalFaithfulCore.Data
      (skeleton K C).sClosure FaithfulS)
    (faithfulQ_monotone : Monotone FaithfulQ)
    (faithfulS_monotone : Monotone FaithfulS)
    (quotient_core : (QCore.core : Set Label) = quotientCore)
    (submodule_core : (SCore.core : Set Label) = submoduleCore) :
    BottomLevels.MinimalFaithfulCore.faithfulLevelCount
        (skeleton K C).qClosure FaithfulQ 4 =
      BottomLevels.MinimalFaithfulCore.faithfulLevelCount
        (skeleton K C).sClosure FaithfulS 4 :=
  (actualTableData K C QCore SCore faithfulQ_monotone faithfulS_monotone
    quotient_core submodule_core).faithful_four_eq

end QuotientSubmoduleEquidistribution.LollipopConcrete.ModuleLayer.FiveObjectAdapter
