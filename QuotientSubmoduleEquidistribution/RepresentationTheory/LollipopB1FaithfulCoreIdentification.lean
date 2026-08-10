import QuotientSubmoduleEquidistribution.RepresentationTheory.LollipopB1SevenObjectAdapter
import QuotientSubmoduleEquidistribution.RepresentationTheory.FaithfulCoreNormalForm

noncomputable section

open Set
open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.LollipopConcrete.B1.ModuleLayer.SevenObjectAdapter.CoreIdentification

open QuotientSubmoduleEquidistribution.AnnihilatorInflation
open QuotientSubmoduleEquidistribution.LollipopConcrete.B1.ModuleLayer.SubmoduleRows

universe u

variable (K : Type u) [Field K]

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-! ## Coordinate actions detecting all five algebra coordinates -/

@[simp] theorem S1_action_top_e1 (b : B1Model K) :
    (FiniteB1Rep.actionHom K (S1Data K) b
      (FiniteB1Rep.ofV₁ K (S1Data K) 1)).1 = b.fst.1.fst := by
  change
    (b1Action K K (Fin 0 → K)
      (0 : K →ₗ[K] K) (0 : K →ₗ[K] (Fin 0 → K))
      (by simp) b (1, 0)).1 = b.fst.1.fst
  rw [b1Action_formula]
  simp

@[simp] theorem X_action_top_x (b : B1Model K) :
    (FiniteB1Rep.actionHom K (XData K) b
      (FiniteB1Rep.ofV₁ K (XData K) (1, 0))).1.2 = b.fst.1.snd := by
  change
    (b1Action K (K × K) (Fin 0 → K)
      (jordan K).hom.hom (0 : (K × K) →ₗ[K] (Fin 0 → K))
      (by intro z; rfl) b ((1, 0), 0)).1.2 = b.fst.1.snd
  rw [b1Action_formula]
  change b.fst.1.fst * 0 + b.fst.1.snd * 1 = b.fst.1.snd
  simp

@[simp] theorem U_action_vertexTwo_e2 (b : B1Model K) :
    (FiniteB1Rep.actionHom K (UData K) b
      (FiniteB1Rep.ofV₂ K (UData K) 1)).2 = b.fst.2 := by
  change
    (b1Action K (K × K) K
      (jordan K).hom.hom (secondStem K).hom.hom
      (by intro z; rfl) b ((0, 0), 1)).2 = b.fst.2
  rw [b1Action_formula]
  change b.fst.2 * 1 + (b.snd.fst * 0 + b.snd.snd * 0) = b.fst.2
  simp

@[simp] theorem U_action_socle_a (b : B1Model K) :
    (FiniteB1Rep.actionHom K (UData K) b
      (FiniteB1Rep.ofV₁ K (UData K) (0, 1))).2 = b.snd.fst := by
  change
    (b1Action K (K × K) K
      (jordan K).hom.hom (secondStem K).hom.hom
      (by intro z; rfl) b ((0, 1), 0)).2 = b.snd.fst
  rw [b1Action_formula]
  change b.fst.2 * 0 + (b.snd.fst * 1 + b.snd.snd * 0) = b.snd.fst
  simp

@[simp] theorem U_action_top_u (b : B1Model K) :
    (FiniteB1Rep.actionHom K (UData K) b
      (FiniteB1Rep.ofV₁ K (UData K) (1, 0))).2 = b.snd.snd := by
  change
    (b1Action K (K × K) K
      (jordan K).hom.hom (secondStem K).hom.hom
      (by intro z; rfl) b ((1, 0), 0)).2 = b.snd.snd
  rw [b1Action_formula]
  change b.fst.2 * 0 + (b.snd.fst * 0 + b.snd.snd * 1) = b.snd.snd
  simp

@[simp] theorem P_action_top_e1 (b : B1Model K) :
    (FiniteB1Rep.actionHom K (PData K) b
      (FiniteB1Rep.ofV₁ K (PData K) (1, 0))).1.1 = b.fst.1.fst := by
  change
    (b1Action K (K × K) (K × K)
      (jordan K).hom.hom LinearMap.id
      (by intro z; rfl) b ((1, 0), (0, 0))).1.1 = b.fst.1.fst
  rw [b1Action_formula]
  change b.fst.1.fst * 1 + b.fst.1.snd * 0 = b.fst.1.fst
  simp

@[simp] theorem P_action_top_x (b : B1Model K) :
    (FiniteB1Rep.actionHom K (PData K) b
      (FiniteB1Rep.ofV₁ K (PData K) (1, 0))).1.2 = b.fst.1.snd := by
  change
    (b1Action K (K × K) (K × K)
      (jordan K).hom.hom LinearMap.id
      (by intro z; rfl) b ((1, 0), (0, 0))).1.2 = b.fst.1.snd
  rw [b1Action_formula]
  change b.fst.1.fst * 0 + b.fst.1.snd * 1 = b.fst.1.snd
  simp

@[simp] theorem P_action_vertexTwo_e2 (b : B1Model K) :
    (FiniteB1Rep.actionHom K (PData K) b
      (FiniteB1Rep.ofV₂ K (PData K) (1, 0))).2.1 = b.fst.2 := by
  change
    (b1Action K (K × K) (K × K)
      (jordan K).hom.hom LinearMap.id
      (by intro z; rfl) b ((0, 0), (1, 0))).2.1 = b.fst.2
  rw [b1Action_formula]
  change b.fst.2 * 1 + (b.snd.fst * 0 + b.snd.snd * 0) = b.fst.2
  simp

@[simp] theorem P_action_top_a (b : B1Model K) :
    (FiniteB1Rep.actionHom K (PData K) b
      (FiniteB1Rep.ofV₁ K (PData K) (1, 0))).2.1 = b.snd.fst := by
  change
    (b1Action K (K × K) (K × K)
      (jordan K).hom.hom LinearMap.id
      (by intro z; rfl) b ((1, 0), (0, 0))).2.1 = b.snd.fst
  rw [b1Action_formula]
  change b.fst.2 * 0 + (b.snd.fst * 1 + b.snd.snd * 0) = b.snd.fst
  simp

@[simp] theorem P_action_top_u (b : B1Model K) :
    (FiniteB1Rep.actionHom K (PData K) b
      (FiniteB1Rep.ofV₁ K (PData K) (1, 0))).2.2 = b.snd.snd := by
  change
    (b1Action K (K × K) (K × K)
      (jordan K).hom.hom LinearMap.id
      (by intro z; rfl) b ((1, 0), (0, 0))).2.2 = b.snd.snd
  rw [b1Action_formula]
  change b.fst.2 * 0 + (b.snd.fst * 0 + b.snd.snd * 1) = b.snd.snd
  simp

/-! ## Closure-forcing quotient and submodule maps -/

/-- Forget the vertex-two coordinate of `U`; this is the quotient `U ⟶ X`. -/
def uToX : UModule K ⟶ XModule K :=
  homOfComponents K (UData K) (XData K)
    LinearMap.id 0
    (by intro z; rfl)
    (by intro z; rfl)

@[simp] theorem uToX_apply (z : UModule K) :
    (uToX K).hom.hom z = (z.1, 0) := rfl

theorem uToX_surjective : Function.Surjective (uToX K).hom.hom := by
  intro z
  exact ⟨(z.1, 0), by
    apply Prod.ext
    · rfl
    · exact Subsingleton.elim _ _⟩

/-- Project a loop block onto its top; this is the quotient `X ⟶ S₁`. -/
def xToS1 : XModule K ⟶ S1Module K :=
  homOfComponents K (XData K) (S1Data K)
    (LinearMap.fst K K K) 0
    (by intro z; rfl)
    (by intro z; rfl)

@[simp] theorem xToS1_apply (z : XModule K) :
    (xToS1 K).hom.hom z = (z.1.1, 0) := rfl

theorem xToS1_surjective : Function.Surjective (xToS1 K).hom.hom := by
  intro z
  exact ⟨((z.1, 0), 0), by
    apply Prod.ext
    · rfl
    · exact Subsingleton.elim _ _⟩

/-- The vertex-two simple embeds in the first vertex-two coordinate of `P`. -/
def s2ToP : S2Module K ⟶ PModule K :=
  homOfComponents K (S2Data K) (PData K)
    0
    { toFun := fun t ↦ (t, 0)
      map_add' := by simp
      map_smul' := by simp }
    (by intro z; rfl)
    (by intro z; rfl)

@[simp] theorem s2ToP_apply (z : S2Module K) :
    (s2ToP K).hom.hom z = ((0, 0), (z.2, 0)) := by
  apply Prod.ext
  · rfl
  · rfl

theorem s2ToP_injective : Function.Injective (s2ToP K).hom.hom := by
  intro z z' h
  have hcoord := congrArg (fun q : PModule K ↦ q.2.1) h
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · exact hcoord

/-- The lower loop line and matching vertex-two line embed `A` in `P`. -/
def aToP : AModule K ⟶ PModule K :=
  homOfComponents K (AData K) (PData K)
    (lowerInclusion K) (lowerInclusion K)
    (by intro z; rfl)
    (by intro z; rfl)

@[simp] theorem aToP_apply (z : AModule K) :
    (aToP K).hom.hom z = ((0, z.1), (0, z.2)) := rfl

theorem aToP_injective : Function.Injective (aToP K).hom.hom := by
  intro z z' h
  have hV₁ := congrArg (fun q : PModule K ↦ q.1.2) h
  have hV₂ := congrArg (fun q : PModule K ↦ q.2.2) h
  exact Prod.ext hV₁ hV₂

def singletonFacPresentation
    (C : Classification K) {S : Set Label} {i j : Label}
    (hi : i ∈ S) (f : obj K i ⟶ obj K j) [Epi f] :
    (skeleton K C).FacPresentation S (obj K j) where
  index := FintypeCat.of (Fin 1)
  label := fun _ ↦ i
  mem := fun _ ↦ hi
  map := (biproductUniqueIso fun _ : Fin 1 ↦ obj K i).hom ≫ f
  epi := inferInstance

def singletonSubPresentation
    (C : Classification K) {S : Set Label} {i j : Label}
    (hi : i ∈ S) (f : obj K j ⟶ obj K i) [Mono f] :
    (skeleton K C).SubPresentation S (obj K j) where
  index := FintypeCat.of (Fin 1)
  label := fun _ ↦ i
  mem := fun _ ↦ hi
  map := f ≫ (biproductUniqueIso fun _ : Fin 1 ↦ obj K i).inv
  mono := inferInstance

theorem x_mem_qClosure_of_u_mem
    (C : Classification K) {S : Set Label} (hu : .u ∈ S) :
    .x ∈ (skeleton K C).qClosure S := by
  letI : Epi (uToX K) :=
    (IndecomposableSkeleton.fg_epi_iff_surjective (uToX K)).2
      (uToX_surjective K)
  let f : obj K .u ⟶ obj K .x := uToX K
  letI : Epi f := by
    change Epi (uToX K)
    infer_instance
  exact ⟨singletonFacPresentation K C (i := .u) (j := .x) hu f⟩

theorem s1_mem_qClosure_of_x_mem
    (C : Classification K) {S : Set Label} (hx : .x ∈ S) :
    .s1 ∈ (skeleton K C).qClosure S := by
  letI : Epi (xToS1 K) :=
    (IndecomposableSkeleton.fg_epi_iff_surjective (xToS1 K)).2
      (xToS1_surjective K)
  let f : obj K .x ⟶ obj K .s1 := xToS1 K
  letI : Epi f := by
    change Epi (xToS1 K)
    infer_instance
  exact ⟨singletonFacPresentation K C (i := .x) (j := .s1) hx f⟩

theorem s2_mem_sClosure_of_p_mem
    (C : Classification K) {S : Set Label} (hp : .p ∈ S) :
    .s2 ∈ (skeleton K C).sClosure S := by
  letI : Mono (s2ToP K) :=
    (IndecomposableSkeleton.fg_mono_iff_injective (s2ToP K)).2
      (s2ToP_injective K)
  let f : obj K .s2 ⟶ obj K .p := s2ToP K
  letI : Mono f := by
    change Mono (s2ToP K)
    infer_instance
  exact ⟨singletonSubPresentation K C (i := .p) (j := .s2) hp f⟩

theorem a_mem_sClosure_of_p_mem
    (C : Classification K) {S : Set Label} (hp : .p ∈ S) :
    .a ∈ (skeleton K C).sClosure S := by
  letI : Mono (aToP K) :=
    (IndecomposableSkeleton.fg_mono_iff_injective (aToP K)).2
      (aToP_injective K)
  let f : obj K .a ⟶ obj K .p := aToP K
  letI : Mono f := by
    change Mono (aToP K)
    infer_instance
  exact ⟨singletonSubPresentation K C (i := .p) (j := .a) hp f⟩

/-! ## Faithfulness of the two displayed cores -/

theorem quotientCore_faithful :
    IsFaithfulSupport (obj K) quotientCore := by
  unfold IsFaithfulSupport
  apply bot_unique
  intro b hb
  have hS1 := (mem_supportAnnihilator (X := obj K)).1 hb
    (.s1) (by simp [quotientCore])
    (FiniteB1Rep.ofV₁ K (S1Data K) 1)
  have hX := (mem_supportAnnihilator (X := obj K)).1 hb
    (.x) (by simp [quotientCore])
    (FiniteB1Rep.ofV₁ K (XData K) (1, 0))
  have hU2 := (mem_supportAnnihilator (X := obj K)).1 hb
    (.u) (by simp [quotientCore])
    (FiniteB1Rep.ofV₂ K (UData K) 1)
  have hUa := (mem_supportAnnihilator (X := obj K)).1 hb
    (.u) (by simp [quotientCore])
    (FiniteB1Rep.ofV₁ K (UData K) (0, 1))
  have hUu := (mem_supportAnnihilator (X := obj K)).1 hb
    (.u) (by simp [quotientCore])
    (FiniteB1Rep.ofV₁ K (UData K) (1, 0))
  change FiniteB1Rep.actionHom K (S1Data K) b _ = 0 at hS1
  change FiniteB1Rep.actionHom K (XData K) b _ = 0 at hX
  change FiniteB1Rep.actionHom K (UData K) b _ = 0 at hU2 hUa hUu
  have hb11 : b.fst.1.fst = 0 := by
    have h := congrArg Prod.fst hS1
    rw [S1_action_top_e1 K b] at h
    exact h
  have hbx : b.fst.1.snd = 0 := by
    have h := congrArg (fun z ↦ z.1.2) hX
    rw [X_action_top_x K b] at h
    exact h
  have hb2 : b.fst.2 = 0 := by
    have h := congrArg Prod.snd hU2
    rw [U_action_vertexTwo_e2 K b] at h
    exact h
  have hba : b.snd.fst = 0 := by
    have h := congrArg Prod.snd hUa
    rw [U_action_socle_a K b] at h
    exact h
  have hbu : b.snd.snd = 0 := by
    have h := congrArg Prod.snd hUu
    rw [U_action_top_u K b] at h
    exact h
  apply TrivSqZeroExt.ext
  · exact Prod.ext (TrivSqZeroExt.ext hb11 hbx) hb2
  · exact TrivSqZeroExt.ext hba hbu

theorem submoduleCore_faithful :
    IsFaithfulSupport (obj K) submoduleCore := by
  unfold IsFaithfulSupport
  apply bot_unique
  intro b hb
  have hP1 := (mem_supportAnnihilator (X := obj K)).1 hb
    (.p) (by simp [submoduleCore])
    (FiniteB1Rep.ofV₁ K (PData K) (1, 0))
  have hP2 := (mem_supportAnnihilator (X := obj K)).1 hb
    (.p) (by simp [submoduleCore])
    (FiniteB1Rep.ofV₂ K (PData K) (1, 0))
  change FiniteB1Rep.actionHom K (PData K) b _ = 0 at hP1 hP2
  have hb11 : b.fst.1.fst = 0 := by
    have h := congrArg (fun z ↦ z.1.1) hP1
    rw [P_action_top_e1 K b] at h
    exact h
  have hbx : b.fst.1.snd = 0 := by
    have h := congrArg (fun z ↦ z.1.2) hP1
    rw [P_action_top_x K b] at h
    exact h
  have hb2 : b.fst.2 = 0 := by
    have h := congrArg (fun z ↦ z.2.1) hP2
    rw [P_action_vertexTwo_e2 K b] at h
    exact h
  have hba : b.snd.fst = 0 := by
    have h := congrArg (fun z ↦ z.2.1) hP1
    rw [P_action_top_a K b] at h
    exact h
  have hbu : b.snd.snd = 0 := by
    have h := congrArg (fun z ↦ z.2.2) hP1
    rw [P_action_top_u K b] at h
    exact h
  apply TrivSqZeroExt.ext
  · exact Prod.ext (TrivSqZeroExt.ext hb11 hbx) hb2
  · exact TrivSqZeroExt.ext hba hbu

/-! ## Closedness of the two displayed cores -/

theorem quotientCore_hom_S2_eq_zero
    (i : Label) (hi : i ∈ quotientCore)
    (f : obj K i ⟶ S2Module K) : f = 0 := by
  exact quotientA_hom_S2_eq_zero K i
    (by simp only [Set.mem_insert_iff]; exact Or.inr hi) f

theorem quotientCore_range_A_le
    (i : Label) (hi : i ∈ quotientCore)
    (f : obj K i ⟶ AModule K) :
    LinearMap.range f.hom.hom ≤ QuotientRows.aVertexTwoBound K := by
  exact quotientS2_range_A_le K i
    (by simp only [Set.mem_insert_iff]; exact Or.inr hi) f

theorem quotientCore_range_W_le
    (i : Label) (hi : i ∈ quotientCore)
    (f : obj K i ⟶ WModule K) :
    LinearMap.range f.hom.hom ≤ QuotientRows.wTopBound K := by
  exact quotientA_range_W_le K i
    (by simp only [Set.mem_insert_iff]; exact Or.inr hi) f

theorem quotientCore_range_P_le
    (i : Label) (hi : i ∈ quotientCore)
    (f : obj K i ⟶ PModule K) :
    LinearMap.range f.hom.hom ≤ QuotientRows.pTopBound K := by
  exact quotientA_range_P_le K i
    (by simp only [Set.mem_insert_iff]; exact Or.inr hi) f

def quotientCore_S2_omission (C : Classification K) :
    BottomLevels.LollipopTableCertificates.Quotient.OmissionCertificate
      (skeleton K C) quotientCore .s2 :=
  BottomLevels.LollipopTableCertificates.Quotient.omissionCertificateOfHomEqZero
    (skeleton K C) (by simp [quotientCore])
      (quotientCore_hom_S2_eq_zero K)

def quotientCore_A_omission (C : Classification K) :
    BottomLevels.LollipopTableCertificates.Quotient.OmissionCertificate
      (skeleton K C) quotientCore .a :=
  quotientOmissionOfRangeBound K C (by simp [quotientCore])
    (QuotientRows.aVertexTwoBound K)
    (QuotientRows.aVertexTwoBound_ne_top K)
    (quotientCore_range_A_le K)

def quotientCore_W_omission (C : Classification K) :
    BottomLevels.LollipopTableCertificates.Quotient.OmissionCertificate
      (skeleton K C) quotientCore .w :=
  quotientOmissionOfRangeBound K C (by simp [quotientCore])
    (QuotientRows.wTopBound K)
    (QuotientRows.wTopBound_ne_top K)
    (quotientCore_range_W_le K)

def quotientCore_P_omission (C : Classification K) :
    BottomLevels.LollipopTableCertificates.Quotient.OmissionCertificate
      (skeleton K C) quotientCore .p :=
  quotientOmissionOfRangeBound K C (by simp [quotientCore])
    (QuotientRows.pTopBound K)
    (QuotientRows.pTopBound_ne_top K)
    (quotientCore_range_P_le K)

theorem quotientCore_isClosed (C : Classification K) :
    (skeleton K C).qClosure.IsClosed quotientCore := by
  apply BottomLevels.LollipopTableCertificates.Quotient.isClosed_of_omissionCertificates
  intro j hj
  cases j with
  | s1 => simp [quotientCore] at hj
  | s2 => exact quotientCore_S2_omission K C
  | x => simp [quotientCore] at hj
  | a => exact quotientCore_A_omission K C
  | u => simp [quotientCore] at hj
  | w => exact quotientCore_W_omission K C
  | p => exact quotientCore_P_omission K C

theorem submoduleCore_s1Generator_le_ker
    (i : Label) (hi : i ∈ submoduleCore)
    (f : S1Module K ⟶ obj K i) :
    s1GeneratorLine K ≤ LinearMap.ker f.hom.hom := by
  exact submoduleU_s1Generator_le_ker K i
    (by simp only [Set.mem_insert_iff]; exact Or.inr hi) f

theorem submoduleCore_uSocle_le_ker
    (i : Label) (hi : i ∈ submoduleCore)
    (f : UModule K ⟶ obj K i) :
    uSocleLine K ≤ LinearMap.ker f.hom.hom := by
  exact submoduleS1_uSocle_le_ker K i
    (by simp only [Set.mem_insert_iff]; exact Or.inr hi) f

theorem submoduleCore_xSocle_le_ker
    (i : Label) (hi : i ∈ submoduleCore)
    (f : XModule K ⟶ obj K i) :
    xSocleLine K ≤ LinearMap.ker f.hom.hom := by
  exact submoduleS1_xSocle_le_ker K i
    (by simp only [Set.mem_insert_iff]; exact Or.inr hi) f

theorem submoduleCore_wSocle_le_ker
    (i : Label) (hi : i ∈ submoduleCore)
    (f : WModule K ⟶ obj K i) :
    wSocleLine K ≤ LinearMap.ker f.hom.hom := by
  exact submoduleS1_wSocle_le_ker K i
    (by simp only [Set.mem_insert_iff]; exact Or.inr hi) f

def submoduleCore_S1_omission (C : Classification K) :
    BottomLevels.LollipopTableCertificates.Submodule.OmissionCertificate
      (skeleton K C) submoduleCore .s1 :=
  submoduleOmissionOfKernelWitness K C (by simp [submoduleCore])
    (s1GeneratorLine K) (s1GeneratorLine_ne_bot K)
    (submoduleCore_s1Generator_le_ker K)

def submoduleCore_U_omission (C : Classification K) :
    BottomLevels.LollipopTableCertificates.Submodule.OmissionCertificate
      (skeleton K C) submoduleCore .u :=
  submoduleOmissionOfKernelWitness K C (by simp [submoduleCore])
    (uSocleLine K) (uSocleLine_ne_bot K)
    (submoduleCore_uSocle_le_ker K)

def submoduleCore_X_omission (C : Classification K) :
    BottomLevels.LollipopTableCertificates.Submodule.OmissionCertificate
      (skeleton K C) submoduleCore .x :=
  submoduleOmissionOfKernelWitness K C (by simp [submoduleCore])
    (xSocleLine K) (xSocleLine_ne_bot K)
    (submoduleCore_xSocle_le_ker K)

def submoduleCore_W_omission (C : Classification K) :
    BottomLevels.LollipopTableCertificates.Submodule.OmissionCertificate
      (skeleton K C) submoduleCore .w :=
  submoduleOmissionOfKernelWitness K C (by simp [submoduleCore])
    (wSocleLine K) (wSocleLine_ne_bot K)
    (submoduleCore_wSocle_le_ker K)

theorem submoduleCore_isClosed (C : Classification K) :
    (skeleton K C).sClosure.IsClosed submoduleCore := by
  apply BottomLevels.LollipopTableCertificates.Submodule.isClosed_of_omissionCertificates
  intro j hj
  cases j with
  | s1 => exact submoduleCore_S1_omission K C
  | s2 => simp [submoduleCore] at hj
  | x => exact submoduleCore_X_omission K C
  | a => simp [submoduleCore] at hj
  | u => exact submoduleCore_U_omission K C
  | w => exact submoduleCore_W_omission K C
  | p => simp [submoduleCore] at hj

/-! ## Necessity of the faithful generator labels -/

theorem e2_ne_zero : e2 K ≠ 0 := by
  intro h
  have hcoord := congrArg (fun b : B1Model K ↦ b.fst.2) h
  change (1 : K) = 0 at hcoord
  exact one_ne_zero hcoord

theorem x_ne_zero : x K ≠ 0 := by
  intro h
  have hcoord := congrArg (fun b : B1Model K ↦ b.fst.1.snd) h
  change (1 : K) = 0 at hcoord
  exact one_ne_zero hcoord

theorem e2_smul_S1_eq_zero (z : S1Module K) : e2 K • z = 0 := by
  rw [FiniteB1Rep.e2_smul]
  apply Prod.ext
  · rfl
  · exact Subsingleton.elim _ _

theorem e2_smul_X_eq_zero (z : XModule K) : e2 K • z = 0 := by
  rw [FiniteB1Rep.e2_smul]
  apply Prod.ext
  · rfl
  · exact Subsingleton.elim _ _

theorem x_smul_S2_eq_zero (z : S2Module K) : x K • z = 0 := by
  rw [FiniteB1Rep.x_smul]
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · rfl

theorem x_smul_A_eq_zero (z : AModule K) : x K • z = 0 := by
  rw [FiniteB1Rep.x_smul]
  rfl

theorem e2_mem_supportAnnihilator_of_subset_quotientCore_of_not_u
    {S : Set Label} (hS : S ⊆ quotientCore) (hu : .u ∉ S) :
    e2 K ∈ supportAnnihilator (obj K) S := by
  rw [mem_supportAnnihilator]
  intro j hj z
  have hcore := hS hj
  cases j with
  | s1 =>
      change FiniteB1Rep.actionHom K (S1Data K) (e2 K) z = 0
      exact e2_smul_S1_eq_zero K z
  | s2 => simp [quotientCore] at hcore
  | x =>
      change FiniteB1Rep.actionHom K (XData K) (e2 K) z = 0
      exact e2_smul_X_eq_zero K z
  | a => simp [quotientCore] at hcore
  | u => exact (hu hj).elim
  | w => simp [quotientCore] at hcore
  | p => simp [quotientCore] at hcore

theorem x_mem_supportAnnihilator_of_subset_submoduleCore_of_not_p
    {S : Set Label} (hS : S ⊆ submoduleCore) (hp : .p ∉ S) :
    x K ∈ supportAnnihilator (obj K) S := by
  rw [mem_supportAnnihilator]
  intro j hj z
  have hcore := hS hj
  cases j with
  | s1 => simp [submoduleCore] at hcore
  | s2 =>
      change FiniteB1Rep.actionHom K (S2Data K) (x K) z = 0
      exact x_smul_S2_eq_zero K z
  | x => simp [submoduleCore] at hcore
  | a =>
      change FiniteB1Rep.actionHom K (AData K) (x K) z = 0
      exact x_smul_A_eq_zero K z
  | u => simp [submoduleCore] at hcore
  | w => simp [submoduleCore] at hcore
  | p => exact (hp hj).elim

/-! ## Exact alignment with the unconditional faithful cores -/

local instance b1Model_op_isNoetherianRing :
    IsNoetherianRing (B1Model K)ᵐᵒᵖ :=
  IsNoetherianRing.of_finite K (B1Model K)ᵐᵒᵖ

def actualQuotientCoreData (C : Classification K) :=
  QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore.concreteQuotientCoreData
    (K := K) (skeleton K C)

def actualSubmoduleCoreData (C : Classification K) :=
  QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore.concreteSubmoduleCoreData
    (K := K) (skeleton K C)

theorem actualQuotientCore_subset (C : Classification K) :
    ((actualQuotientCoreData K C).core : Set Label) ⊆ quotientCore := by
  apply (actualQuotientCoreData K C).core_le
    ⟨quotientCore, quotientCore_isClosed K C⟩
  simpa only [skeleton] using quotientCore_faithful K

theorem actualSubmoduleCore_subset (C : Classification K) :
    ((actualSubmoduleCoreData K C).core : Set Label) ⊆ submoduleCore := by
  apply (actualSubmoduleCoreData K C).core_le
    ⟨submoduleCore, submoduleCore_isClosed K C⟩
  simpa only [skeleton] using submoduleCore_faithful K

theorem u_mem_actualQuotientCore (C : Classification K) :
    .u ∈ ((actualQuotientCoreData K C).core : Set Label) := by
  by_contra hu
  have hannObj :=
    e2_mem_supportAnnihilator_of_subset_quotientCore_of_not_u K
      (actualQuotientCore_subset K C) hu
  have hann :
      e2 K ∈ supportAnnihilator (skeleton K C).obj
        ((actualQuotientCoreData K C).core : Set Label) := by
    simpa only [skeleton] using hannObj
  have hbot : e2 K ∈ (⊥ : TwoSidedIdeal (B1Model K)) := by
    rw [← (actualQuotientCoreData K C).core_faithful]
    exact hann
  apply e2_ne_zero K
  simpa using hbot

theorem x_mem_actualQuotientCore (C : Classification K) :
    .x ∈ ((actualQuotientCoreData K C).core : Set Label) := by
  have hclosure :=
    x_mem_qClosure_of_u_mem K C (u_mem_actualQuotientCore K C)
  rw [(actualQuotientCoreData K C).core.property.closure_eq] at hclosure
  exact hclosure

theorem s1_mem_actualQuotientCore (C : Classification K) :
    .s1 ∈ ((actualQuotientCoreData K C).core : Set Label) := by
  have hclosure :=
    s1_mem_qClosure_of_x_mem K C (x_mem_actualQuotientCore K C)
  rw [(actualQuotientCoreData K C).core.property.closure_eq] at hclosure
  exact hclosure

theorem actualQuotientCore_eq (C : Classification K) :
    ((actualQuotientCoreData K C).core : Set Label) = quotientCore := by
  apply Set.Subset.antisymm (actualQuotientCore_subset K C)
  intro i hi
  rw [mem_quotientCore] at hi
  rcases hi with rfl | rfl | rfl
  · exact x_mem_actualQuotientCore K C
  · exact u_mem_actualQuotientCore K C
  · exact s1_mem_actualQuotientCore K C

theorem p_mem_actualSubmoduleCore (C : Classification K) :
    .p ∈ ((actualSubmoduleCoreData K C).core : Set Label) := by
  by_contra hp
  have hannObj :=
    x_mem_supportAnnihilator_of_subset_submoduleCore_of_not_p K
      (actualSubmoduleCore_subset K C) hp
  have hann :
      x K ∈ supportAnnihilator (skeleton K C).obj
        ((actualSubmoduleCoreData K C).core : Set Label) := by
    simpa only [skeleton] using hannObj
  have hbot : x K ∈ (⊥ : TwoSidedIdeal (B1Model K)) := by
    rw [← (actualSubmoduleCoreData K C).core_faithful]
    exact hann
  apply x_ne_zero K
  simpa using hbot

theorem s2_mem_actualSubmoduleCore (C : Classification K) :
    .s2 ∈ ((actualSubmoduleCoreData K C).core : Set Label) := by
  have hclosure :=
    s2_mem_sClosure_of_p_mem K C (p_mem_actualSubmoduleCore K C)
  rw [(actualSubmoduleCoreData K C).core.property.closure_eq] at hclosure
  exact hclosure

theorem a_mem_actualSubmoduleCore (C : Classification K) :
    .a ∈ ((actualSubmoduleCoreData K C).core : Set Label) := by
  have hclosure :=
    a_mem_sClosure_of_p_mem K C (p_mem_actualSubmoduleCore K C)
  rw [(actualSubmoduleCoreData K C).core.property.closure_eq] at hclosure
  exact hclosure

theorem actualSubmoduleCore_eq (C : Classification K) :
    ((actualSubmoduleCoreData K C).core : Set Label) = submoduleCore := by
  apply Set.Subset.antisymm (actualSubmoduleCore_subset K C)
  intro i hi
  rw [mem_submoduleCore] at hi
  rcases hi with rfl | rfl | rfl
  · exact p_mem_actualSubmoduleCore K C
  · exact s2_mem_actualSubmoduleCore K C
  · exact a_mem_actualSubmoduleCore K C

end QuotientSubmoduleEquidistribution.LollipopConcrete.B1.ModuleLayer.SevenObjectAdapter.CoreIdentification
