import OpConjecture.RepresentationTheory.LollipopB0FiveObjectAdapter
import OpConjecture.RepresentationTheory.FaithfulCoreNormalForm

noncomputable section

open Set
open CategoryTheory CategoryTheory.Limits

namespace OpConjecture.LollipopConcrete.ModuleLayer.FiveObjectAdapter.CoreIdentification

universe u

variable (K : Type u) [Field K]

open OpConjecture.AnnihilatorInflation

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

@[simp] theorem S1_action_top_fst (b : B0Model K) :
    (FiniteB0Rep.actionHom K (S1Data K) b
      (FiniteB0Rep.ofV₁ K (S1Data K) 1)).1 = b.fst.1 := by
  change
    (b0Action K K (Fin 0 → K)
      (0 : K →ₗ[K] K) (0 : K →ₗ[K] (Fin 0 → K))
      (by simp) (by simp) b (1, 0)).1 = b.fst.1
  unfold b0Action
  rw [TrivSqZeroExt.lift_def]
  simp [vertexAction, radicalAction]

@[simp] theorem X_action_top_loop (b : B0Model K) :
    (FiniteB0Rep.actionHom K (XData K) b
      (FiniteB0Rep.ofV₁ K (XData K) (1, 0))).1.2 = b.snd.x := by
  change
    (b0Action K (K × K) (Fin 0 → K)
      (jordan K).hom.hom (0 : (K × K) →ₗ[K] (Fin 0 → K))
      (by intro z; rfl) (by simp) b ((1, 0), 0)).1.2 = b.snd.x
  unfold b0Action
  rw [TrivSqZeroExt.lift_def]
  simp [vertexAction, radicalAction, jordan]
  change b.snd.x * 1 = b.snd.x
  simp

@[simp] theorem A_action_vertexTwo (b : B0Model K) :
    (FiniteB0Rep.actionHom K (AData K) b
      (FiniteB0Rep.ofV₂ K (AData K) 1)).2 = b.fst.2 := by
  change
    (b0Action K K K
      (0 : K →ₗ[K] K) LinearMap.id
      (by simp) (by simp) b (0, 1)).2 = b.fst.2
  unfold b0Action
  rw [TrivSqZeroExt.lift_def]
  simp [vertexAction, radicalAction]

@[simp] theorem A_action_top_stem (b : B0Model K) :
    (FiniteB0Rep.actionHom K (AData K) b
      (FiniteB0Rep.ofV₁ K (AData K) 1)).2 = b.snd.a := by
  change
    (b0Action K K K
      (0 : K →ₗ[K] K) LinearMap.id
      (by simp) (by simp) b (1, 0)).2 = b.snd.a
  unfold b0Action
  rw [TrivSqZeroExt.lift_def]
  simp [vertexAction, radicalAction]

@[simp] theorem P_action_top_fst (b : B0Model K) :
    (FiniteB0Rep.actionHom K (PData K) b
      (FiniteB0Rep.ofV₁ K (PData K) (1, 0))).1.1 = b.fst.1 := by
  change
    (b0Action K (K × K) K
      (jordan K).hom.hom (LinearMap.fst K K K)
      (by intro z; rfl) (by intro z; rfl) b ((1, 0), 0)).1.1 = b.fst.1
  unfold b0Action
  rw [TrivSqZeroExt.lift_def]
  simp [vertexAction, radicalAction, jordan]
  right
  rfl

@[simp] theorem P_action_top_loop (b : B0Model K) :
    (FiniteB0Rep.actionHom K (PData K) b
      (FiniteB0Rep.ofV₁ K (PData K) (1, 0))).1.2 = b.snd.x := by
  change
    (b0Action K (K × K) K
      (jordan K).hom.hom (LinearMap.fst K K K)
      (by intro z; rfl) (by intro z; rfl) b ((1, 0), 0)).1.2 = b.snd.x
  unfold b0Action
  rw [TrivSqZeroExt.lift_def]
  simp [vertexAction, radicalAction, jordan]
  change b.snd.x * 1 = b.snd.x
  simp

@[simp] theorem P_action_top_stem (b : B0Model K) :
    (FiniteB0Rep.actionHom K (PData K) b
      (FiniteB0Rep.ofV₁ K (PData K) (1, 0))).2 = b.snd.a := by
  change
    (b0Action K (K × K) K
      (jordan K).hom.hom (LinearMap.fst K K K)
      (by intro z; rfl) (by intro z; rfl) b ((1, 0), 0)).2 = b.snd.a
  unfold b0Action
  rw [TrivSqZeroExt.lift_def]
  simp [vertexAction, radicalAction, jordan]

@[simp] theorem P_action_vertexTwo (b : B0Model K) :
    (FiniteB0Rep.actionHom K (PData K) b
      (FiniteB0Rep.ofV₂ K (PData K) 1)).2 = b.fst.2 := by
  change
    (b0Action K (K × K) K
      (jordan K).hom.hom (LinearMap.fst K K K)
      (by intro z; rfl) (by intro z; rfl) b ((0, 0), 1)).2 = b.fst.2
  unfold b0Action
  rw [TrivSqZeroExt.lift_def]
  simp [vertexAction, radicalAction, jordan]

theorem S1_action_fst (b : B0Model K) (z : S1Module K) :
    (FiniteB0Rep.actionHom K (S1Data K) b z).1 =
      b.fst.1 * z.1 := by
  change
    (b0Action K K (Fin 0 → K)
      (0 : K →ₗ[K] K) (0 : K →ₗ[K] (Fin 0 → K))
      (by simp) (by simp) b z).1 = b.fst.1 * z.1
  unfold b0Action
  rw [TrivSqZeroExt.lift_def]
  simp [vertexAction, radicalAction]

def xTopQuotientLinear : XModule K →ₗ[B0Model K] S1Module K where
  toFun := fun z ↦ (z.1.1, 0)
  map_add' := by
    intro z w
    apply Prod.ext
    · rfl
    · exact Subsingleton.elim _ _
  map_smul' := by
    intro b z
    apply Prod.ext
    · change
        (FiniteB0Rep.actionHom K (S1Data K) b (z.1.1, 0)).1 =
          (FiniteB0Rep.actionHom K (XData K) b z).1.1
      rw [S1_action_fst]
      exact
        PBound.b0Action_first_eq K (Fin 0 → K)
          (XData K).loop.hom.hom (XData K).stem.hom.hom
          (XData K).loop_sq (XData K).stem_loop
          (by intro q; rfl) b z |>.symm
    · exact Subsingleton.elim _ _

def xTopQuotient : XModule K ⟶ S1Module K :=
  FGModuleCat.ofHom (xTopQuotientLinear K)

theorem xTopQuotient_surjective :
    Function.Surjective (xTopQuotient K).hom.hom := by
  intro z
  obtain ⟨t, q⟩ := z
  have hq : q = 0 := Subsingleton.elim _ _
  subst q
  exact ⟨((t, 0), 0), rfl⟩

theorem P_action_s1Socle (b : B0Model K) (t : K) :
    FiniteB0Rep.actionHom K (PData K) b ((0, t), 0) =
      ((0, b.fst.1 * t), 0) := by
  change
    b0Action K (K × K) K
      (jordan K).hom.hom (LinearMap.fst K K K)
      (by intro z; rfl) (by intro z; rfl) b ((0, t), 0) =
        ((0, b.fst.1 * t), 0)
  unfold b0Action
  rw [TrivSqZeroExt.lift_def]
  apply Prod.ext
  · apply Prod.ext
    · simp [vertexAction, radicalAction]
      right
      rfl
    · simp [vertexAction, radicalAction, jordan]
      right
      rfl
  · simp [vertexAction, radicalAction]

def s1SocleInclusionLinear : S1Module K →ₗ[B0Model K] PModule K where
  toFun := fun z ↦ ((0, z.1), 0)
  map_add' := by
    intro z w
    apply Prod.ext
    · apply Prod.ext
      · change (0 : K) = 0 + 0
        simp
      · rfl
    · change (0 : K) = 0 + 0
      simp
  map_smul' := by
    intro b z
    change
      ((0, (FiniteB0Rep.actionHom K (S1Data K) b z).1), 0) =
        FiniteB0Rep.actionHom K (PData K) b ((0, z.1), 0)
    rw [S1_action_fst, P_action_s1Socle]

def s1SocleInclusion : S1Module K ⟶ PModule K :=
  FGModuleCat.ofHom (s1SocleInclusionLinear K)

theorem s1SocleInclusion_injective :
    Function.Injective (s1SocleInclusion K).hom.hom := by
  intro z w h
  have hcoord := congrArg (fun q ↦ q.1.2) h
  apply Prod.ext
  · exact hcoord
  · exact Subsingleton.elim _ _

theorem S2_action_snd (b : B0Model K) (z : S2Module K) :
    (FiniteB0Rep.actionHom K (S2Data K) b z).2 =
      b.fst.2 * z.2 := by
  change
    (b0Action K (Fin 0 → K) K
      (0 : (Fin 0 → K) →ₗ[K] (Fin 0 → K))
      (0 : (Fin 0 → K) →ₗ[K] K)
      (by simp) (by simp) b z).2 = b.fst.2 * z.2
  unfold b0Action
  rw [TrivSqZeroExt.lift_def]
  simp [vertexAction, radicalAction]

theorem P_action_s2Socle (b : B0Model K) (t : K) :
    FiniteB0Rep.actionHom K (PData K) b ((0, 0), t) =
      ((0, 0), b.fst.2 * t) := by
  change
    b0Action K (K × K) K
      (jordan K).hom.hom (LinearMap.fst K K K)
      (by intro z; rfl) (by intro z; rfl) b ((0, 0), t) =
        ((0, 0), b.fst.2 * t)
  unfold b0Action
  rw [TrivSqZeroExt.lift_def]
  apply Prod.ext
  · apply Prod.ext
    · simp [vertexAction, radicalAction]
      right
      rfl
    · simp [vertexAction, radicalAction, jordan]
      right
      rfl
  · simp [vertexAction, radicalAction]

def s2InclusionLinear : S2Module K →ₗ[B0Model K] PModule K where
  toFun := fun z ↦ ((0, 0), z.2)
  map_add' := by
    intro z w
    apply Prod.ext
    · apply Prod.ext
      · change (0 : K) = 0 + 0
        simp
      · change (0 : K) = 0 + 0
        simp
    · rfl
  map_smul' := by
    intro b z
    change
      ((0, 0), (FiniteB0Rep.actionHom K (S2Data K) b z).2) =
        FiniteB0Rep.actionHom K (PData K) b ((0, 0), z.2)
    rw [S2_action_snd, P_action_s2Socle]

def s2Inclusion : S2Module K ⟶ PModule K :=
  FGModuleCat.ofHom (s2InclusionLinear K)

theorem s2Inclusion_injective :
    Function.Injective (s2Inclusion K).hom.hom := by
  intro z w h
  have hcoord := congrArg (fun q ↦ q.2) h
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · exact hcoord

/-! ## Singleton presentations supplied by the coordinate maps -/

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

theorem s1_mem_qClosure_of_x_mem
    (C : Classification K) {S : Set Label} (hx : .x ∈ S) :
    .s1 ∈ (skeleton K C).qClosure S := by
  letI : Epi (xTopQuotient K) :=
    (OpConjecture.IndecomposableSkeleton.fg_epi_iff_surjective
      (xTopQuotient K)).2 (xTopQuotient_surjective K)
  let f : obj K .x ⟶ obj K .s1 := xTopQuotient K
  letI : Epi f := by
    change Epi (xTopQuotient K)
    infer_instance
  exact ⟨singletonFacPresentation K C (i := .x) (j := .s1) hx f⟩

theorem s1_mem_sClosure_of_p_mem
    (C : Classification K) {S : Set Label} (hp : .p ∈ S) :
    .s1 ∈ (skeleton K C).sClosure S := by
  letI : Mono (s1SocleInclusion K) :=
    (OpConjecture.IndecomposableSkeleton.fg_mono_iff_injective
      (s1SocleInclusion K)).2 (s1SocleInclusion_injective K)
  let f : obj K .s1 ⟶ obj K .p := s1SocleInclusion K
  letI : Mono f := by
    change Mono (s1SocleInclusion K)
    infer_instance
  exact ⟨singletonSubPresentation K C (i := .p) (j := .s1) hp f⟩

theorem s2_mem_sClosure_of_p_mem
    (C : Classification K) {S : Set Label} (hp : .p ∈ S) :
    .s2 ∈ (skeleton K C).sClosure S := by
  letI : Mono (s2Inclusion K) :=
    (OpConjecture.IndecomposableSkeleton.fg_mono_iff_injective
      (s2Inclusion K)).2 (s2Inclusion_injective K)
  let f : obj K .s2 ⟶ obj K .p := s2Inclusion K
  letI : Mono f := by
    change Mono (s2Inclusion K)
    infer_instance
  exact ⟨singletonSubPresentation K C (i := .p) (j := .s2) hp f⟩

/-- The displayed quotient core acts faithfully on the coordinate algebra. -/
theorem quotientCore_faithful :
    IsFaithfulSupport (obj K) quotientCore := by
  unfold IsFaithfulSupport
  apply bot_unique
  intro b hb
  have hS1 := (mem_supportAnnihilator (X := obj K)).1 hb
    (.s1) (by simp [quotientCore])
    (FiniteB0Rep.ofV₁ K (S1Data K) 1)
  have hX := (mem_supportAnnihilator (X := obj K)).1 hb
    (.x) (by simp [quotientCore])
    (FiniteB0Rep.ofV₁ K (XData K) (1, 0))
  have hAv2 := (mem_supportAnnihilator (X := obj K)).1 hb
    (.a) (by simp [quotientCore])
    (FiniteB0Rep.ofV₂ K (AData K) 1)
  have hAv1 := (mem_supportAnnihilator (X := obj K)).1 hb
    (.a) (by simp [quotientCore])
    (FiniteB0Rep.ofV₁ K (AData K) 1)
  change FiniteB0Rep.actionHom K (S1Data K) b
    (FiniteB0Rep.ofV₁ K (S1Data K) 1) = 0 at hS1
  change FiniteB0Rep.actionHom K (XData K) b
    (FiniteB0Rep.ofV₁ K (XData K) (1, 0)) = 0 at hX
  change FiniteB0Rep.actionHom K (AData K) b
    (FiniteB0Rep.ofV₂ K (AData K) 1) = 0 at hAv2
  change FiniteB0Rep.actionHom K (AData K) b
    (FiniteB0Rep.ofV₁ K (AData K) 1) = 0 at hAv1
  have hb11 : b.fst.1 = 0 := by
    have h := congrArg Prod.fst hS1
    rw [S1_action_top_fst K b] at h
    change b.fst.1 = (0 : K) at h
    exact h
  have hbx : b.snd.x = 0 := by
    have h := congrArg (fun z ↦ z.1.2) hX
    rw [X_action_top_loop K b] at h
    change b.snd.x = (0 : K) at h
    exact h
  have hb12 : b.fst.2 = 0 := by
    have h := congrArg Prod.snd hAv2
    rw [A_action_vertexTwo K b] at h
    change b.fst.2 = (0 : K) at h
    exact h
  have hba : b.snd.a = 0 := by
    have h := congrArg Prod.snd hAv1
    rw [A_action_top_stem K b] at h
    change b.snd.a = (0 : K) at h
    exact h
  apply TrivSqZeroExt.ext
  · exact Prod.ext hb11 hb12
  · exact B0Radical.ext K hbx hba

/-- The displayed submodule core acts faithfully on the coordinate algebra. -/
theorem submoduleCore_faithful :
    IsFaithfulSupport (obj K) submoduleCore := by
  unfold IsFaithfulSupport
  apply bot_unique
  intro b hb
  have hP1 := (mem_supportAnnihilator (X := obj K)).1 hb
    (.p) (by simp [submoduleCore])
    (FiniteB0Rep.ofV₁ K (PData K) (1, 0))
  have hP2 := (mem_supportAnnihilator (X := obj K)).1 hb
    (.p) (by simp [submoduleCore])
    (FiniteB0Rep.ofV₂ K (PData K) 1)
  change FiniteB0Rep.actionHom K (PData K) b
    (FiniteB0Rep.ofV₁ K (PData K) (1, 0)) = 0 at hP1
  change FiniteB0Rep.actionHom K (PData K) b
    (FiniteB0Rep.ofV₂ K (PData K) 1) = 0 at hP2
  have hb11 : b.fst.1 = 0 := by
    have h := congrArg (fun z ↦ z.1.1) hP1
    rw [P_action_top_fst K b] at h
    change b.fst.1 = (0 : K) at h
    exact h
  have hbx : b.snd.x = 0 := by
    have h := congrArg (fun z ↦ z.1.2) hP1
    rw [P_action_top_loop K b] at h
    change b.snd.x = (0 : K) at h
    exact h
  have hba : b.snd.a = 0 := by
    have h := congrArg (fun z ↦ z.2) hP1
    rw [P_action_top_stem K b] at h
    change b.snd.a = (0 : K) at h
    exact h
  have hb12 : b.fst.2 = 0 := by
    have h := congrArg (fun z ↦ z.2) hP2
    rw [P_action_vertexTwo K b] at h
    change b.fst.2 = (0 : K) at h
    exact h
  apply TrivSqZeroExt.ext
  · exact Prod.ext hb11 hb12
  · exact B0Radical.ext K hbx hba

/-! ## Closedness of the two displayed cores -/

theorem quotientCore_hom_S2_eq_zero
    (i : Label) (hi : i ∈ quotientCore)
    (f : obj K i ⟶ S2Module K) : f = 0 := by
  cases i with
  | s1 => exact hom_S1_S2_eq_zero K f
  | s2 => simp [quotientCore] at hi
  | x => exact hom_X_S2_eq_zero K f
  | a => exact hom_A_S2_eq_zero K f
  | p => simp [quotientCore] at hi

theorem quotientCore_range_P_le
    (i : Label) (hi : i ∈ quotientCore)
    (f : obj K i ⟶ PModule K) :
    LinearMap.range f.hom.hom ≤ PBound.pRadicalBound K := by
  cases i with
  | s1 => exact PBound.range_S1_P_le K f
  | s2 => simp [quotientCore] at hi
  | x => exact PBound.range_X_P_le K f
  | a => exact PBound.range_A_P_le K f
  | p => simp [quotientCore] at hi

def quotientCore_S2_omission (C : Classification K) :
    BottomLevels.LollipopTableCertificates.Quotient.OmissionCertificate
      (skeleton K C) quotientCore .s2 :=
  BottomLevels.LollipopTableCertificates.Quotient.omissionCertificateOfHomEqZero
    (skeleton K C) (by simp [quotientCore])
      (quotientCore_hom_S2_eq_zero K)

def quotientCore_P_omission (C : Classification K) :
    BottomLevels.LollipopTableCertificates.Quotient.OmissionCertificate
      (skeleton K C) quotientCore .p :=
  PBound.omissionCertificateOfRangeBound
    (skeleton K C) (by simp [quotientCore])
      (PBound.pRadicalBound K)
      (PBound.pRadicalBound_ne_top K)
      (quotientCore_range_P_le K)

theorem quotientCore_isClosed (C : Classification K) :
    (skeleton K C).qClosure.IsClosed quotientCore := by
  apply BottomLevels.LollipopTableCertificates.Quotient.isClosed_of_omissionCertificates
  intro j hj
  cases j with
  | s1 => simp [quotientCore] at hj
  | s2 => exact quotientCore_S2_omission K C
  | x => simp [quotientCore] at hj
  | a => simp [quotientCore] at hj
  | p => exact quotientCore_P_omission K C

def submoduleCore_A_omission (C : Classification K) :
    BottomLevels.LollipopTableCertificates.Submodule.OmissionCertificate
      (skeleton K C) submoduleCore .a where
  not_mem := by simp [submoduleCore]
  witness := SubmoduleBounds.AStemLine K
  witness_ne_bot := SubmoduleBounds.AStemLine_ne_bot K
  witness_le_reject :=
    witness_le_reject_of_forall_le_ker (skeleton K C)
      (SubmoduleBounds.AStemLine K) (by
        intro i hi f
        exact aStemLine_le_ker_of_mem_submoduleX K i
          (by simp only [Set.mem_insert_iff]; exact Or.inr hi) f)

def submoduleCore_X_omission (C : Classification K) :
    BottomLevels.LollipopTableCertificates.Submodule.OmissionCertificate
      (skeleton K C) submoduleCore .x where
  not_mem := by simp [submoduleCore]
  witness := SubmoduleBounds.xSocleLine K
  witness_ne_bot := SubmoduleBounds.xSocleLine_ne_bot K
  witness_le_reject :=
    witness_le_reject_of_forall_le_ker (skeleton K C)
      (SubmoduleBounds.xSocleLine K) (by
        intro i hi f
        exact xSocleLine_le_ker_of_mem_submoduleA K i
          (by simp only [Set.mem_insert_iff]; exact Or.inr hi) f)

theorem submoduleCore_isClosed (C : Classification K) :
    (skeleton K C).sClosure.IsClosed submoduleCore := by
  apply BottomLevels.LollipopTableCertificates.Submodule.isClosed_of_omissionCertificates
  intro j hj
  cases j with
  | s1 => simp [submoduleCore] at hj
  | s2 => simp [submoduleCore] at hj
  | x => exact submoduleCore_X_omission K C
  | a => exact submoduleCore_A_omission K C
  | p => simp [submoduleCore] at hj

/-! ## Necessity of the closure-forcing labels -/

theorem x_ne_zero : x K ≠ 0 := by
  intro h
  have hcoord := congrArg (fun b : B0Model K ↦ b.snd.x) h
  change (1 : K) = 0 at hcoord
  exact one_ne_zero hcoord

theorem e2_ne_zero : e2 K ≠ 0 := by
  intro h
  have hcoord := congrArg (fun b : B0Model K ↦ b.fst.2) h
  change (1 : K) = 0 at hcoord
  exact one_ne_zero hcoord

theorem x_smul_S1_eq_zero (z : S1Module K) : x K • z = 0 := by
  rw [FiniteB0Rep.x_smul]
  rfl

theorem x_smul_S2_eq_zero (z : S2Module K) : x K • z = 0 := by
  rw [FiniteB0Rep.x_smul]
  rfl

theorem x_smul_A_eq_zero (z : AModule K) : x K • z = 0 := by
  rw [FiniteB0Rep.x_smul]
  rfl

theorem e2_smul_S1_eq_zero (z : S1Module K) : e2 K • z = 0 := by
  rw [FiniteB0Rep.e2_smul]
  apply Prod.ext
  · rfl
  · exact Subsingleton.elim _ _

theorem e2_smul_X_eq_zero (z : XModule K) : e2 K • z = 0 := by
  rw [FiniteB0Rep.e2_smul]
  apply Prod.ext
  · rfl
  · exact Subsingleton.elim _ _

theorem x_mem_supportAnnihilator_of_subset_quotientCore_of_not_x
    {S : Set Label} (hS : S ⊆ quotientCore) (hx : .x ∉ S) :
    x K ∈ supportAnnihilator (obj K) S := by
  rw [mem_supportAnnihilator]
  intro j hj z
  have hcore := hS hj
  cases j with
  | s1 =>
      change FiniteB0Rep.actionHom K (S1Data K) (x K) z = 0
      exact x_smul_S1_eq_zero K z
  | s2 => simp [quotientCore] at hcore
  | x => exact (hx hj).elim
  | a =>
      change FiniteB0Rep.actionHom K (AData K) (x K) z = 0
      exact x_smul_A_eq_zero K z
  | p => simp [quotientCore] at hcore

theorem e2_mem_supportAnnihilator_of_subset_quotientCore_of_not_a
    {S : Set Label} (hS : S ⊆ quotientCore) (ha : .a ∉ S) :
    e2 K ∈ supportAnnihilator (obj K) S := by
  rw [mem_supportAnnihilator]
  intro j hj z
  have hcore := hS hj
  cases j with
  | s1 =>
      change FiniteB0Rep.actionHom K (S1Data K) (e2 K) z = 0
      exact e2_smul_S1_eq_zero K z
  | s2 => simp [quotientCore] at hcore
  | x =>
      change FiniteB0Rep.actionHom K (XData K) (e2 K) z = 0
      exact e2_smul_X_eq_zero K z
  | a => exact (ha hj).elim
  | p => simp [quotientCore] at hcore

theorem x_mem_supportAnnihilator_of_subset_submoduleCore_of_not_p
    {S : Set Label} (hS : S ⊆ submoduleCore) (hp : .p ∉ S) :
    x K ∈ supportAnnihilator (obj K) S := by
  rw [mem_supportAnnihilator]
  intro j hj z
  have hcore := hS hj
  cases j with
  | s1 =>
      change FiniteB0Rep.actionHom K (S1Data K) (x K) z = 0
      exact x_smul_S1_eq_zero K z
  | s2 =>
      change FiniteB0Rep.actionHom K (S2Data K) (x K) z = 0
      exact x_smul_S2_eq_zero K z
  | x => simp [submoduleCore] at hcore
  | a => simp [submoduleCore] at hcore
  | p => exact (hp hj).elim

/-! ## Exact alignment with the unconditional faithful cores -/

local instance b0Model_op_isNoetherianRing :
    IsNoetherianRing (B0Model K)ᵐᵒᵖ :=
  IsNoetherianRing.of_finite K (B0Model K)ᵐᵒᵖ

def actualQuotientCoreData (C : Classification K) :=
  OpConjecture.IndecomposableSkeleton.FaithfulCore.concreteQuotientCoreData
    (K := K) (skeleton K C)

def actualSubmoduleCoreData (C : Classification K) :=
  OpConjecture.IndecomposableSkeleton.FaithfulCore.concreteSubmoduleCoreData
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

theorem x_mem_actualQuotientCore (C : Classification K) :
    .x ∈ ((actualQuotientCoreData K C).core : Set Label) := by
  by_contra hx
  have hannObj :=
    x_mem_supportAnnihilator_of_subset_quotientCore_of_not_x K
      (actualQuotientCore_subset K C) hx
  have hann :
      x K ∈ supportAnnihilator (skeleton K C).obj
        ((actualQuotientCoreData K C).core : Set Label) := by
    simpa only [skeleton] using hannObj
  have hbot : x K ∈ (⊥ : TwoSidedIdeal (B0Model K)) := by
    rw [← (actualQuotientCoreData K C).core_faithful]
    exact hann
  apply x_ne_zero K
  simpa using hbot

theorem a_mem_actualQuotientCore (C : Classification K) :
    .a ∈ ((actualQuotientCoreData K C).core : Set Label) := by
  by_contra ha
  have hannObj :=
    e2_mem_supportAnnihilator_of_subset_quotientCore_of_not_a K
      (actualQuotientCore_subset K C) ha
  have hann :
      e2 K ∈ supportAnnihilator (skeleton K C).obj
        ((actualQuotientCoreData K C).core : Set Label) := by
    simpa only [skeleton] using hannObj
  have hbot : e2 K ∈ (⊥ : TwoSidedIdeal (B0Model K)) := by
    rw [← (actualQuotientCoreData K C).core_faithful]
    exact hann
  apply e2_ne_zero K
  simpa using hbot

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
  · exact a_mem_actualQuotientCore K C
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
  have hbot : x K ∈ (⊥ : TwoSidedIdeal (B0Model K)) := by
    rw [← (actualSubmoduleCoreData K C).core_faithful]
    exact hann
  apply x_ne_zero K
  simpa using hbot

theorem s1_mem_actualSubmoduleCore (C : Classification K) :
    .s1 ∈ ((actualSubmoduleCoreData K C).core : Set Label) := by
  have hclosure :=
    s1_mem_sClosure_of_p_mem K C (p_mem_actualSubmoduleCore K C)
  rw [(actualSubmoduleCoreData K C).core.property.closure_eq] at hclosure
  exact hclosure

theorem s2_mem_actualSubmoduleCore (C : Classification K) :
    .s2 ∈ ((actualSubmoduleCoreData K C).core : Set Label) := by
  have hclosure :=
    s2_mem_sClosure_of_p_mem K C (p_mem_actualSubmoduleCore K C)
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
  · exact s1_mem_actualSubmoduleCore K C

end OpConjecture.LollipopConcrete.ModuleLayer.FiveObjectAdapter.CoreIdentification
