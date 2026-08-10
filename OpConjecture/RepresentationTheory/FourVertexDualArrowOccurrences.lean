import OpConjecture.RepresentationTheory.FourVertexSignedChannelOccurrences
import OpConjecture.RepresentationTheory.FourVertexStripReversal

/-!
# Labelled arrow occurrences under aligned duality

Aligned biduality reverses irreducible arrows.  This file packages that
operation as equivalences on actual labelled arrow occurrences, on trimmed
interior occurrences, and on the common-target/common-source pair types used
by the signed strip square shift.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace OpConjecture.IndecomposableSkeleton

universe u v w

variable {R S : Type u}
  [Ring R] [IsNoetherianRing R]
  [Ring S] [IsNoetherianRing S]
  {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)
  (τ : IndecomposableSkeleton.{u, w, u} S κ)

namespace AlignedBiduality

variable (D : AlignedBiduality σ τ)

/-- Pull a labelled irreducible arrow on the dual skeleton back to the
source skeleton, reversing its orientation. -/
def pullbackIrreduciblePair (a : τ.IrreduciblePair) :
    σ.IrreduciblePair :=
  ⟨(D.forward.labelEquiv.symm a.1.2,
    D.forward.labelEquiv.symm a.1.1),
    (D.hasIrreducibleMorphism_image_iff σ τ
      (x := D.forward.labelEquiv.symm a.1.2)
      (y := D.forward.labelEquiv.symm a.1.1)).1 (by
        simpa using a.2)⟩

/-- Push a labelled source arrow to the dual skeleton, reversing its
orientation. -/
def pushforwardIrreduciblePair (a : σ.IrreduciblePair) :
    τ.IrreduciblePair :=
  ⟨(D.forward.labelEquiv a.1.2, D.forward.labelEquiv a.1.1),
    (D.hasIrreducibleMorphism_image_iff σ τ).2 a.2⟩

/-- Aligned duality is an exact equivalence of labelled irreducible-arrow
occurrences with reversed endpoints. -/
def irreduciblePairEquiv : τ.IrreduciblePair ≃ σ.IrreduciblePair where
  toFun := D.pullbackIrreduciblePair σ τ
  invFun := D.pushforwardIrreduciblePair σ τ
  left_inv a := by
    apply Subtype.ext
    apply Prod.ext <;> simp [pullbackIrreduciblePair,
      pushforwardIrreduciblePair]
  right_inv a := by
    apply Subtype.ext
    apply Prod.ext <;> simp [pullbackIrreduciblePair,
      pushforwardIrreduciblePair]

omit [Fintype ι] [Fintype κ] in
/-- A nonprojective dual arrow target pulls back to a noninjective source. -/
theorem pullbackIrreduciblePair_source_noninjective
    (a : τ.IrreduciblePair)
    (ha : ¬ Projective (τ.obj a.1.2)) :
    ¬ Injective (σ.obj (D.pullbackIrreduciblePair σ τ a).1.1) := by
  intro hi
  apply ha
  have h := (D.forward.injective_iff_projective_image σ τ
    (D.forward.labelEquiv.symm a.1.2)).1 hi
  simpa [pullbackIrreduciblePair] using h

omit [Fintype ι] [Fintype κ] in
/-- A noninjective dual arrow source pulls back to a nonprojective target. -/
theorem pullbackIrreduciblePair_target_nonprojective
    (a : τ.IrreduciblePair)
    (ha : ¬ Injective (τ.obj a.1.1)) :
    ¬ Projective (σ.obj (D.pullbackIrreduciblePair σ τ a).1.2) := by
  intro hp
  apply ha
  have h := (D.forward.projective_iff_injective_image σ τ
    (D.forward.labelEquiv.symm a.1.1)).1 hp
  simpa [pullbackIrreduciblePair] using h

omit [Fintype ι] [Fintype κ] in
/-- A nonprojective source-arrow target pushes to a noninjective dual
source. -/
theorem pushforwardIrreduciblePair_source_noninjective
    (a : σ.IrreduciblePair)
    (ha : ¬ Projective (σ.obj a.1.2)) :
    ¬ Injective (τ.obj (D.pushforwardIrreduciblePair σ τ a).1.1) := by
  intro hi
  apply ha
  exact (D.forward.projective_iff_injective_image σ τ a.1.2).2 (by
    simpa [pushforwardIrreduciblePair] using hi)

omit [Fintype ι] [Fintype κ] in
/-- A noninjective source-arrow source pushes to a nonprojective dual
target. -/
theorem pushforwardIrreduciblePair_target_nonprojective
    (a : σ.IrreduciblePair)
    (ha : ¬ Injective (σ.obj a.1.1)) :
    ¬ Projective (τ.obj (D.pushforwardIrreduciblePair σ τ a).1.2) := by
  intro hp
  apply ha
  exact (D.forward.injective_iff_projective_image σ τ a.1.1).2 (by
    simpa [pushforwardIrreduciblePair] using hp)

/-- Full two-step source boundary on the dual arrow orbit pulls back to the
full two-step target boundary on the source arrow orbit. -/
theorem pullback_arrowOrbit_twoSource_iff_twoTarget
    (ARσ : σ.FiniteARTranslationData)
    (ARτ : τ.FiniteARTranslationData)
    (a : τ.IrreduciblePair) :
    ((ARτ.arMeshRotationData τ).arrowOrbitData τ).TwoSource a ↔
      ((ARσ.arMeshRotationData σ).arrowOrbitData σ).TwoTarget
        (D.pullbackIrreduciblePair σ τ a) := by
  rw [(ARτ.arMeshRotationData τ).arrowOrbit_twoSource_iff τ,
    (ARσ.arMeshRotationData σ).arrowOrbit_twoTarget_iff σ]
  have htarget := D.forward.injective_iff_projective_image σ τ
    (D.forward.labelEquiv.symm a.1.2)
  have hsource := D.forward.injective_iff_projective_image σ τ
    (D.forward.labelEquiv.symm a.1.1)
  simpa [pullbackIrreduciblePair] using
    (or_congr htarget hsource).symm

/-- Pulling back both arrows turns equality of dual targets into equality
of source endpoints, without trimming either arrow orbit. -/
def commonTargetEquivCommonSource :
    FiniteARTranslationData.CommonTargetArrowPair τ ≃
      FiniteARTranslationData.CommonSourceArrowPair σ where
  toFun p :=
    ⟨(D.pullbackIrreduciblePair σ τ p.1.1,
      D.pullbackIrreduciblePair σ τ p.1.2), by
        exact congrArg D.forward.labelEquiv.symm p.2⟩
  invFun p :=
    ⟨(D.pushforwardIrreduciblePair σ τ p.1.1,
      D.pushforwardIrreduciblePair σ τ p.1.2), by
        exact congrArg D.forward.labelEquiv p.2⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact (D.irreduciblePairEquiv σ τ).symm_apply_apply p.1.1
    · exact (D.irreduciblePairEquiv σ τ).symm_apply_apply p.1.2
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact (D.irreduciblePairEquiv σ τ).apply_symm_apply p.1.1
    · exact (D.irreduciblePairEquiv σ τ).apply_symm_apply p.1.2

/-- Full dual source-boundary common-target pairs are exactly source
target-boundary common-source pairs. -/
def sourceBoundaryCommonTargetEquivTargetBoundaryCommonSource
    (ARσ : σ.FiniteARTranslationData)
    (ARτ : τ.FiniteARTranslationData) :
    ARτ.SourceBoundaryCommonTargetArrowPair τ ≃
      ARσ.TargetBoundaryCommonSourceArrowPair σ := by
  let E := D.commonTargetEquivCommonSource σ τ
  apply E.subtypeEquiv
  intro p
  exact or_congr
    (pullback_arrowOrbit_twoSource_iff_twoTarget σ τ D ARσ ARτ p.1.1)
    (pullback_arrowOrbit_twoSource_iff_twoTarget σ τ D ARσ ARτ p.1.2)

/-- Full dual boundary transport followed by the source-equality square
shift puts both sides on their first-two boundary. -/
def sourceBoundaryCommonTargetEquivSourceBoundaryCommonSource
    (ARσ : σ.FiniteARTranslationData)
    (ARτ : τ.FiniteARTranslationData) :
    ARτ.SourceBoundaryCommonTargetArrowPair τ ≃
      ARσ.SourceBoundaryCommonSourceArrowPair σ :=
  (D.sourceBoundaryCommonTargetEquivTargetBoundaryCommonSource
    σ τ ARσ ARτ).trans
      (ARσ.commonSourceBoundaryEquiv σ).symm

include D in
/-- Cardinal form of full aligned source-boundary transport. -/
theorem sourceBoundaryCommonTarget_card_eq_sourceBoundaryCommonSource
    (ARσ : σ.FiniteARTranslationData)
    (ARτ : τ.FiniteARTranslationData) :
    Fintype.card (ARτ.SourceBoundaryCommonTargetArrowPair τ) =
      Fintype.card (ARσ.SourceBoundaryCommonSourceArrowPair σ) :=
  Fintype.card_congr
    (sourceBoundaryCommonTargetEquivSourceBoundaryCommonSource
      σ τ D ARσ ARτ)

section Interior

variable (ARσ : σ.FiniteARTranslationData)
  (ARτ : τ.FiniteARTranslationData)

/-- Pull back a trimmed dual arrow occurrence. -/
def pullbackInteriorArrow
    (a : (ARτ.arMeshRotationData τ).InteriorArrow τ) :
    (ARσ.arMeshRotationData σ).InteriorArrow σ :=
  ⟨D.pullbackIrreduciblePair σ τ a.1,
    D.pullbackIrreduciblePair_target_nonprojective σ τ a.1 a.2.2,
    D.pullbackIrreduciblePair_source_noninjective σ τ a.1 a.2.1⟩

/-- Push forward a trimmed source arrow occurrence. -/
def pushforwardInteriorArrow
    (a : (ARσ.arMeshRotationData σ).InteriorArrow σ) :
    (ARτ.arMeshRotationData τ).InteriorArrow τ :=
  ⟨D.pushforwardIrreduciblePair σ τ a.1,
    D.pushforwardIrreduciblePair_target_nonprojective σ τ a.1 a.2.2,
    D.pushforwardIrreduciblePair_source_noninjective σ τ a.1 a.2.1⟩

/-- Aligned duality equivalently reverses the trimmed labelled-arrow
occurrences. -/
def interiorArrowEquiv :
    (ARτ.arMeshRotationData τ).InteriorArrow τ ≃
      (ARσ.arMeshRotationData σ).InteriorArrow σ where
  toFun := D.pullbackInteriorArrow σ τ ARσ ARτ
  invFun := D.pushforwardInteriorArrow σ τ ARσ ARτ
  left_inv a := by
    apply Subtype.ext
    exact (D.irreduciblePairEquiv σ τ).symm_apply_apply a.1
  right_inv a := by
    apply Subtype.ext
    exact (D.irreduciblePairEquiv σ τ).apply_symm_apply a.1

/-- Pullback conjugates dual mesh rotation toward the projective boundary
to source mesh rotation toward the injective boundary. -/
theorem pullback_arrowOrbit_tau
    (a : {a : τ.IrreduciblePair //
      ¬ Projective (τ.obj a.1.2)}) :
    D.pullbackIrreduciblePair σ τ
        (((ARτ.arMeshRotationData τ).arrowOrbitData τ).tau a).1 =
      (((ARσ.arMeshRotationData σ).arrowOrbitData σ).tau.symm
        ⟨D.pullbackIrreduciblePair σ τ a.1,
          D.pullbackIrreduciblePair_source_noninjective
            σ τ a.1 a.2⟩).1 := by
  let Mσ := ARσ.arMeshRotationData σ
  let Mτ := ARτ.arMeshRotationData τ
  apply Subtype.ext
  have hτ := Mτ.arrowOrbitData_tau_val τ a
  have hσ := Mσ.arrowOrbitData_tau_symm_val σ
    ⟨D.pullbackIrreduciblePair σ τ a.1,
      D.pullbackIrreduciblePair_source_noninjective σ τ a.1 a.2⟩
  apply Prod.ext
  · change D.forward.labelEquiv.symm
        (((Mτ.arrowOrbitData τ).tau a).1.1.2) =
      (((Mσ.arrowOrbitData σ).tau.symm
        ⟨D.pullbackIrreduciblePair σ τ a.1,
          D.pullbackIrreduciblePair_source_noninjective
            σ τ a.1 a.2⟩).1.1.1)
    rw [congrArg Prod.snd hτ, congrArg Prod.fst hσ]
    rfl
  · change D.forward.labelEquiv.symm
        (((Mτ.arrowOrbitData τ).tau a).1.1.1) =
      (((Mσ.arrowOrbitData σ).tau.symm
        ⟨D.pullbackIrreduciblePair σ τ a.1,
          D.pullbackIrreduciblePair_source_noninjective
            σ τ a.1 a.2⟩).1.1.2)
    rw [congrArg Prod.fst hτ, congrArg Prod.snd hσ]
    have hdual :=
      D.forward_symm_arTranslation_eq_inverse σ τ ARσ ARτ
        ⟨a.1.1.2, a.2⟩
    change D.forward.labelEquiv.symm
        (Mτ.tau ⟨a.1.1.2, a.2⟩).1 =
      (Mσ.tau.symm
        ⟨D.forward.labelEquiv.symm a.1.1.2,
          D.pullbackIrreduciblePair_source_noninjective
            σ τ a.1 a.2⟩).1 at hdual
    exact hdual

omit [Fintype ι] [Fintype κ] in
/-- A dual projective-target boundary pulls back to the source
injective-source boundary. -/
theorem pullback_arrowOrbit_source_iff_target
    (a : τ.IrreduciblePair) :
    Projective (τ.obj a.1.2) ↔
      Injective
        (σ.obj (D.pullbackIrreduciblePair σ τ a).1.1) := by
  simpa [pullbackIrreduciblePair] using
    (D.forward.injective_iff_projective_image σ τ
      (D.forward.labelEquiv.symm a.1.2)).symm

omit [Fintype ι] [Fintype κ] in
/-- A dual injective-source boundary pulls back to the source
projective-target boundary. -/
theorem pullback_arrowOrbit_target_iff_source
    (a : τ.IrreduciblePair) :
    Injective (τ.obj a.1.1) ↔
      Projective
        (σ.obj (D.pullbackIrreduciblePair σ τ a).1.2) := by
  simpa [pullbackIrreduciblePair] using
    (D.forward.projective_iff_injective_image σ τ
      (D.forward.labelEquiv.symm a.1.1)).symm

/-- Pullback also conjugates inverse dual mesh rotation to forward source
mesh rotation on all labelled arrow occurrences. -/
theorem pullback_arrowOrbit_tau_symm
    (a : {a : τ.IrreduciblePair //
      ¬ Injective (τ.obj a.1.1)}) :
    D.pullbackIrreduciblePair σ τ
        (((ARτ.arMeshRotationData τ).arrowOrbitData τ).tau.symm a).1 =
      (((ARσ.arMeshRotationData σ).arrowOrbitData σ).tau
        ⟨D.pullbackIrreduciblePair σ τ a.1,
          D.pullbackIrreduciblePair_target_nonprojective
            σ τ a.1 a.2⟩).1 := by
  let Oσ := (ARσ.arMeshRotationData σ).arrowOrbitData σ
  let Oτ := (ARτ.arMeshRotationData τ).arrowOrbitData τ
  let b := Oτ.tau.symm a
  have hbTarget : ¬ Injective
      (σ.obj (D.pullbackIrreduciblePair σ τ b.1).1.1) :=
    D.pullbackIrreduciblePair_source_noninjective σ τ b.1 b.2
  have haSource : ¬ Projective
      (σ.obj (D.pullbackIrreduciblePair σ τ a.1).1.2) :=
    D.pullbackIrreduciblePair_target_nonprojective σ τ a.1 a.2
  have hforward := D.pullback_arrowOrbit_tau σ τ ARσ ARτ
    ⟨b.1, b.2⟩
  have hsub : Oσ.tau.symm
      ⟨D.pullbackIrreduciblePair σ τ b.1, hbTarget⟩ =
      ⟨D.pullbackIrreduciblePair σ τ a.1, haSource⟩ := by
    apply Subtype.ext
    rw [← hforward]
    exact congrArg (D.pullbackIrreduciblePair σ τ)
      (congrArg Subtype.val (Oτ.tau.apply_symm_apply a))
  have hback := congrArg Oσ.tau hsub
  simpa only [Oσ.tau.apply_symm_apply] using congrArg Subtype.val hback

/-- Pullback conjugates dual successor to reversed source successor on all
labelled arrow occurrences. -/
theorem pullback_arrowOrbit_successor
    [DecidableEq ι] [DecidableEq κ]
    (a : τ.IrreduciblePair) :
    D.pullbackIrreduciblePair σ τ
        (((ARτ.arMeshRotationData τ).arrowOrbitData τ).successor a) =
      ((ARσ.arMeshRotationData σ).arrowOrbitData σ).reverse.successor
        (D.pullbackIrreduciblePair σ τ a) := by
  classical
  let Oσ := (ARσ.arMeshRotationData σ).arrowOrbitData σ
  let Oτ := (ARτ.arMeshRotationData τ).arrowOrbitData τ
  by_cases ha : Injective (τ.obj a.1.1)
  · have htarget : Projective
      (σ.obj (D.pullbackIrreduciblePair σ τ a).1.2) :=
      (D.pullback_arrowOrbit_target_iff_source σ τ a).1 ha
    rw [Oτ.successor_eq_self_of_mem_target ha,
      Oσ.reverse.successor_eq_self_of_mem_target htarget]
  · have hsource : ¬ Projective
        (σ.obj (D.pullbackIrreduciblePair σ τ a).1.2) :=
      D.pullbackIrreduciblePair_target_nonprojective σ τ a ha
    rw [show Oτ.successor a = (Oτ.tau.symm ⟨a, ha⟩).1 by
      change (if hx : Injective (τ.obj a.1.1) then a
        else (Oτ.tau.symm ⟨a, hx⟩).1) = _
      rw [dif_neg ha],
      show Oσ.reverse.successor
          (D.pullbackIrreduciblePair σ τ a) =
        (Oσ.tau
          ⟨D.pullbackIrreduciblePair σ τ a, hsource⟩).1 by
        change (if hx : Projective
            (σ.obj (D.pullbackIrreduciblePair σ τ a).1.2) then
          D.pullbackIrreduciblePair σ τ a
        else (Oσ.tau
          ⟨D.pullbackIrreduciblePair σ τ a, hx⟩).1) = _
        rw [dif_neg hsource]]
    exact D.pullback_arrowOrbit_tau_symm σ τ ARσ ARτ ⟨a, ha⟩

/-- Arrow reversal preserves and reflects the intrinsic successor component
of every labelled arrow occurrence. -/
theorem pullback_arrowOrbit_sameSuccessorOrbit_iff
    [DecidableEq ι] [DecidableEq κ]
    (a b : τ.IrreduciblePair) :
    let Oτ := (ARτ.arMeshRotationData τ).arrowOrbitData τ
    let Oσ := (ARσ.arMeshRotationData σ).arrowOrbitData σ
    Oτ.SameSuccessorOrbit a b ↔
      Oσ.SameSuccessorOrbit
        (D.pullbackIrreduciblePair σ τ a)
        (D.pullbackIrreduciblePair σ τ b) := by
  let Oτ := (ARτ.arMeshRotationData τ).arrowOrbitData τ
  let Oσ := (ARσ.arMeshRotationData σ).arrowOrbitData σ
  let E := D.irreduciblePairEquiv σ τ
  exact (Oτ.sameSuccessorOrbit_congr Oσ.reverse E
    (D.pullback_arrowOrbit_successor σ τ ARσ ARτ) a b).trans
      (Oσ.reverse_sameSuccessorOrbit_iff (E a) (E b))

/-- Full aligned target-to-source boundary transport restricts exactly to
pairs from different intrinsic labelled arrow components. -/
def differentOrbitSourceBoundaryCommonTargetEquivTargetBoundaryCommonSource
    [DecidableEq ι] [DecidableEq κ] :
    ARτ.DifferentOrbitSourceBoundaryCommonTargetArrowPair τ ≃
      ARσ.DifferentOrbitTargetBoundaryCommonSourceArrowPair σ := by
  let E := D.sourceBoundaryCommonTargetEquivTargetBoundaryCommonSource
    σ τ ARσ ARτ
  apply E.subtypeEquiv
  intro p
  change (¬ ((ARτ.arMeshRotationData τ).arrowOrbitData τ).SameSuccessorOrbit
      p.1.1.1 p.1.1.2) ↔
    ¬ ((ARσ.arMeshRotationData σ).arrowOrbitData σ).SameSuccessorOrbit
      (D.pullbackIrreduciblePair σ τ p.1.1.1)
      (D.pullbackIrreduciblePair σ τ p.1.1.2)
  exact not_congr <|
    D.pullback_arrowOrbit_sameSuccessorOrbit_iff σ τ ARσ ARτ
      p.1.1.1 p.1.1.2

/-- Exact full cross-side square shift for two different labelled arrow
components. -/
def differentOrbitSourceBoundaryCommonTargetEquivSourceBoundaryCommonSource
    [DecidableEq ι] [DecidableEq κ] :
    ARτ.DifferentOrbitSourceBoundaryCommonTargetArrowPair τ ≃
      ARσ.DifferentOrbitSourceBoundaryCommonSourceArrowPair σ :=
  (D.differentOrbitSourceBoundaryCommonTargetEquivTargetBoundaryCommonSource
    σ τ ARσ ARτ).trans
      (ARσ.differentOrbitCommonSourceBoundaryEquiv σ).symm

include D in
/-- Cardinal form of the manuscript's untrimmed preliminary
different-orbit cross-side square-shift equality. -/
theorem differentOrbitSourceBoundaryCommonTarget_card_eq_sourceBoundaryCommonSource
    [DecidableEq ι] [DecidableEq κ] :
    Fintype.card
        (ARτ.DifferentOrbitSourceBoundaryCommonTargetArrowPair τ) =
      Fintype.card
        (ARσ.DifferentOrbitSourceBoundaryCommonSourceArrowPair σ) :=
  Fintype.card_congr
    (D.differentOrbitSourceBoundaryCommonTargetEquivSourceBoundaryCommonSource
      σ τ ARσ ARτ)

/-- The shifted source predicate on a dual interior arrow is the shifted
target predicate on its pulled-back source arrow. -/
theorem pullbackInterior_source_iff_target
    (a : (ARτ.arMeshRotationData τ).InteriorArrow τ) :
    ((ARτ.arMeshRotationData τ).arrowOrbitData τ).InteriorSource a ↔
      ((ARσ.arMeshRotationData σ).arrowOrbitData σ).InteriorTarget
        (D.pullbackInteriorArrow σ τ ARσ ARτ a) := by
  rw [(ARτ.arMeshRotationData τ).arrowInterior_source_iff τ a,
    (ARσ.arMeshRotationData σ).arrowInterior_target_iff σ]
  simpa [pullbackInteriorArrow, pullbackIrreduciblePair] using
    (D.forward.injective_iff_projective_image σ τ
      (D.forward.labelEquiv.symm a.1.1.1)).symm

/-- The shifted target predicate on a dual interior arrow is the shifted
source predicate on its pulled-back source arrow. -/
theorem pullbackInterior_target_iff_source
    (a : (ARτ.arMeshRotationData τ).InteriorArrow τ) :
    ((ARτ.arMeshRotationData τ).arrowOrbitData τ).InteriorTarget a ↔
      ((ARσ.arMeshRotationData σ).arrowOrbitData σ).InteriorSource
        (D.pullbackInteriorArrow σ τ ARσ ARτ a) := by
  rw [(ARτ.arMeshRotationData τ).arrowInterior_target_iff τ a,
    (ARσ.arMeshRotationData σ).arrowInterior_source_iff σ]
  simpa [pullbackInteriorArrow, pullbackIrreduciblePair] using
    (D.forward.projective_iff_injective_image σ τ
      (D.forward.labelEquiv.symm a.1.1.2)).symm

/-- Interior mesh rotation is likewise conjugated to inverse interior mesh
rotation by arrow reversal. -/
theorem pullbackInterior_tau
    (a : {a : (ARτ.arMeshRotationData τ).InteriorArrow τ //
      ¬ ((ARτ.arMeshRotationData τ).arrowOrbitData τ).InteriorSource a}) :
    D.pullbackInteriorArrow σ τ ARσ ARτ
        (((ARτ.arMeshRotationData τ).arrowInteriorOrbitData τ).tau a).1 =
      (((ARσ.arMeshRotationData σ).arrowInteriorOrbitData σ).tau.symm
        ⟨D.pullbackInteriorArrow σ τ ARσ ARτ a.1, by
          intro h
          exact a.2
            ((AlignedBiduality.pullbackInterior_source_iff_target
              σ τ D ARσ ARτ a.1).2 h)⟩).1 := by
  apply Subtype.ext
  have h := D.pullback_arrowOrbit_tau σ τ ARσ ARτ
    ⟨a.1.1, a.1.2.1⟩
  simpa [pullbackInteriorArrow,
    ARMeshRotationData.arrowInteriorOrbitData,
    OpConjecture.BoundaryTranslationChains.Data.interior] using h

/-- Pullback also conjugates inverse dual interior rotation to forward
source interior rotation. -/
theorem pullbackInterior_tau_symm
    (a : {a : (ARτ.arMeshRotationData τ).InteriorArrow τ //
      ¬ ((ARτ.arMeshRotationData τ).arrowOrbitData τ).InteriorTarget a}) :
    D.pullbackInteriorArrow σ τ ARσ ARτ
        (((ARτ.arMeshRotationData τ).arrowInteriorOrbitData τ).tau.symm a).1 =
      (((ARσ.arMeshRotationData σ).arrowInteriorOrbitData σ).tau
        ⟨D.pullbackInteriorArrow σ τ ARσ ARτ a.1, by
          intro h
          exact a.2 ((D.pullbackInterior_target_iff_source
            σ τ ARσ ARτ a.1).2 h)⟩).1 := by
  let Uσ := (ARσ.arMeshRotationData σ).arrowInteriorOrbitData σ
  let Uτ := (ARτ.arMeshRotationData τ).arrowInteriorOrbitData τ
  let Oσ := (ARσ.arMeshRotationData σ).arrowOrbitData σ
  let b := Uτ.tau.symm a
  have hbTarget : ¬ Oσ.InteriorTarget
      (D.pullbackInteriorArrow σ τ ARσ ARτ b.1) := by
    intro h
    exact b.2 ((D.pullbackInterior_source_iff_target
      σ τ ARσ ARτ b.1).2 h)
  have haSource : ¬ Oσ.InteriorSource
      (D.pullbackInteriorArrow σ τ ARσ ARτ a.1) := by
    intro h
    exact a.2 ((D.pullbackInterior_target_iff_source
      σ τ ARσ ARτ a.1).2 h)
  have hforward := D.pullbackInterior_tau σ τ ARσ ARτ
    ⟨b.1, b.2⟩
  have hsub : Uσ.tau.symm
      ⟨D.pullbackInteriorArrow σ τ ARσ ARτ b.1, hbTarget⟩ =
      ⟨D.pullbackInteriorArrow σ τ ARσ ARτ a.1, haSource⟩ := by
    apply Subtype.ext
    rw [← hforward]
    exact congrArg (D.pullbackInteriorArrow σ τ ARσ ARτ)
      (congrArg Subtype.val (Uτ.tau.apply_symm_apply a))
  have hback := congrArg Uσ.tau hsub
  simpa only [Uσ.tau.apply_symm_apply] using congrArg Subtype.val hback

/-- Pullback conjugates dual successor to reversed source successor on
trimmed labelled arrow occurrences. -/
theorem pullbackInterior_successor
    [DecidableEq ι] [DecidableEq κ]
    (a : (ARτ.arMeshRotationData τ).InteriorArrow τ) :
    D.pullbackInteriorArrow σ τ ARσ ARτ
        (((ARτ.arMeshRotationData τ).arrowInteriorOrbitData τ).successor a) =
      ((ARσ.arMeshRotationData σ).arrowInteriorOrbitData σ).reverse.successor
        (D.pullbackInteriorArrow σ τ ARσ ARτ a) := by
  classical
  let Uσ := (ARσ.arMeshRotationData σ).arrowInteriorOrbitData σ
  let Uτ := (ARτ.arMeshRotationData τ).arrowInteriorOrbitData τ
  let Oσ := (ARσ.arMeshRotationData σ).arrowOrbitData σ
  let Oτ := (ARτ.arMeshRotationData τ).arrowOrbitData τ
  by_cases ha : Oτ.InteriorTarget a
  · have hsource : Oσ.InteriorSource
        (D.pullbackInteriorArrow σ τ ARσ ARτ a) :=
      (D.pullbackInterior_target_iff_source σ τ ARσ ARτ a).1 ha
    rw [Uτ.successor_eq_self_of_mem_target ha,
      Uσ.reverse.successor_eq_self_of_mem_target hsource]
  · have hsource : ¬ Oσ.InteriorSource
        (D.pullbackInteriorArrow σ τ ARσ ARτ a) := by
      intro h
      exact ha ((D.pullbackInterior_target_iff_source
        σ τ ARσ ARτ a).2 h)
    rw [show Uτ.successor a = (Uτ.tau.symm ⟨a, ha⟩).1 by
      change (if hx : Oτ.InteriorTarget a then a
        else (Uτ.tau.symm ⟨a, hx⟩).1) = _
      rw [dif_neg ha],
      show Uσ.reverse.successor
          (D.pullbackInteriorArrow σ τ ARσ ARτ a) =
        (Uσ.tau
          ⟨D.pullbackInteriorArrow σ τ ARσ ARτ a, hsource⟩).1 by
        change (if hx : Oσ.InteriorSource
            (D.pullbackInteriorArrow σ τ ARσ ARτ a) then
          D.pullbackInteriorArrow σ τ ARσ ARτ a
        else (Uσ.tau
          ⟨D.pullbackInteriorArrow σ τ ARσ ARτ a, hx⟩).1) = _
        rw [dif_neg hsource]]
    exact D.pullbackInterior_tau_symm σ τ ARσ ARτ ⟨a, ha⟩

/-- Arrow reversal preserves and reflects the intrinsic component of a
trimmed labelled arrow occurrence. -/
theorem pullbackInterior_sameSuccessorOrbit_iff
    [DecidableEq ι] [DecidableEq κ]
    (a b : (ARτ.arMeshRotationData τ).InteriorArrow τ) :
    let Uτ := (ARτ.arMeshRotationData τ).arrowInteriorOrbitData τ
    let Uσ := (ARσ.arMeshRotationData σ).arrowInteriorOrbitData σ
    Uτ.SameSuccessorOrbit a b ↔
      Uσ.SameSuccessorOrbit
        (D.pullbackInteriorArrow σ τ ARσ ARτ a)
        (D.pullbackInteriorArrow σ τ ARσ ARτ b) := by
  let Uτ := (ARτ.arMeshRotationData τ).arrowInteriorOrbitData τ
  let Uσ := (ARσ.arMeshRotationData σ).arrowInteriorOrbitData σ
  let E := D.interiorArrowEquiv σ τ ARσ ARτ
  exact (Uτ.sameSuccessorOrbit_congr Uσ.reverse E
    (D.pullbackInterior_successor σ τ ARσ ARτ) a b).trans
      (Uσ.reverse_sameSuccessorOrbit_iff (E a) (E b))

/-- The first-two shifted boundary on the dual arrow orbit is exactly the
last-two shifted boundary on the pulled-back source arrow orbit. -/
theorem pullbackInterior_twoSource_iff_twoTarget
    (a : (ARτ.arMeshRotationData τ).InteriorArrow τ) :
    ((ARτ.arMeshRotationData τ).arrowInteriorOrbitData τ).TwoSource a ↔
      ((ARσ.arMeshRotationData σ).arrowInteriorOrbitData σ).TwoTarget
        (D.pullbackInteriorArrow σ τ ARσ ARτ a) := by
  let Uτ := (ARτ.arMeshRotationData τ).arrowInteriorOrbitData τ
  let Uσ := (ARσ.arMeshRotationData σ).arrowInteriorOrbitData σ
  let Fa := D.pullbackInteriorArrow σ τ ARσ ARτ a
  constructor
  · rintro (ha | ha)
    · exact Or.inl
        ((AlignedBiduality.pullbackInterior_source_iff_target
          σ τ D ARσ ARτ a).1 ha)
    · right
      intro hFa
      have haSource : ¬
          ((ARτ.arMeshRotationData τ).arrowOrbitData τ).InteriorSource a := by
        intro h
        exact hFa
          ((AlignedBiduality.pullbackInterior_source_iff_target
            σ τ D ARσ ARτ a).1 h)
      have hsource := ha haSource
      have htarget :=
        (AlignedBiduality.pullbackInterior_source_iff_target
          σ τ D ARσ ARτ (Uτ.tau ⟨a, haSource⟩).1).1 hsource
      have hrotate := D.pullbackInterior_tau σ τ ARσ ARτ
        ⟨a, haSource⟩
      change ((ARσ.arMeshRotationData σ).arrowOrbitData σ).InteriorTarget
        (Uσ.tau.symm ⟨Fa, hFa⟩).1
      rw [← hrotate]
      exact htarget
  · rintro (ha | ha)
    · exact Or.inl
        ((AlignedBiduality.pullbackInterior_source_iff_target
          σ τ D ARσ ARτ a).2 ha)
    · right
      intro haSource
      have hFa : ¬
          ((ARσ.arMeshRotationData σ).arrowOrbitData σ).InteriorTarget Fa := by
        intro h
        exact haSource
          ((AlignedBiduality.pullbackInterior_source_iff_target
            σ τ D ARσ ARτ a).2 h)
      have htarget := ha hFa
      apply (AlignedBiduality.pullbackInterior_source_iff_target
        σ τ D ARσ ARτ (Uτ.tau ⟨a, haSource⟩).1).2
      have hrotate := D.pullbackInterior_tau σ τ ARσ ARτ
        ⟨a, haSource⟩
      rw [hrotate]
      exact htarget

/-- Pulling back both arrows turns equality of dual targets into equality
of source endpoints. -/
def interiorCommonTargetEquivCommonSource :
    ARτ.InteriorCommonTargetArrowPair τ ≃
      ARσ.InteriorCommonSourceArrowPair σ where
  toFun p :=
    ⟨(D.pullbackInteriorArrow σ τ ARσ ARτ p.1.1,
      D.pullbackInteriorArrow σ τ ARσ ARτ p.1.2), by
      change D.forward.labelEquiv.symm p.1.1.1.1.2 =
        D.forward.labelEquiv.symm p.1.2.1.1.2
      exact congrArg D.forward.labelEquiv.symm p.2⟩
  invFun p :=
    ⟨(D.pushforwardInteriorArrow σ τ ARσ ARτ p.1.1,
      D.pushforwardInteriorArrow σ τ ARσ ARτ p.1.2), by
      change D.forward.labelEquiv p.1.1.1.1.1 =
        D.forward.labelEquiv p.1.2.1.1.1
      exact congrArg D.forward.labelEquiv p.2⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> exact
      (D.interiorArrowEquiv σ τ ARσ ARτ).symm_apply_apply _
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> exact
      (D.interiorArrowEquiv σ τ ARσ ARτ).apply_symm_apply _

/-- The common-target/common-source equivalence restricts to the shifted
source boundary on the dual side and the shifted target boundary on the
source side. -/
def interiorSourceBoundaryCommonTargetEquivTargetBoundaryCommonSource :
    ARτ.InteriorSourceBoundaryCommonTargetArrowPair τ ≃
      ARσ.InteriorTargetBoundaryCommonSourceArrowPair σ := by
  let E := D.interiorCommonTargetEquivCommonSource σ τ ARσ ARτ
  apply E.subtypeEquiv
  intro p
  change
    ((ARτ.arMeshRotationData τ).arrowInteriorOrbitData τ).TwoSource p.1.1 ∨
        ((ARτ.arMeshRotationData τ).arrowInteriorOrbitData τ).TwoSource p.1.2 ↔
      ((ARσ.arMeshRotationData σ).arrowInteriorOrbitData σ).TwoTarget
          (D.pullbackInteriorArrow σ τ ARσ ARτ p.1.1) ∨
        ((ARσ.arMeshRotationData σ).arrowInteriorOrbitData σ).TwoTarget
          (D.pullbackInteriorArrow σ τ ARσ ARτ p.1.2)
  exact or_congr
    (AlignedBiduality.pullbackInterior_twoSource_iff_twoTarget
      σ τ D ARσ ARτ p.1.1)
    (AlignedBiduality.pullbackInterior_twoSource_iff_twoTarget
      σ τ D ARσ ARτ p.1.2)

/-- The aligned target-to-source boundary equivalence restricts exactly to
pairs of different intrinsic trimmed arrow-orbit components. -/
def interiorDifferentOrbitSourceBoundaryCommonTargetEquivTargetBoundaryCommonSource
    [DecidableEq ι] [DecidableEq κ] :
    ARτ.InteriorDifferentOrbitSourceBoundaryCommonTargetArrowPair τ ≃
      ARσ.InteriorDifferentOrbitTargetBoundaryCommonSourceArrowPair σ := by
  let E := D.interiorSourceBoundaryCommonTargetEquivTargetBoundaryCommonSource
    σ τ ARσ ARτ
  apply E.subtypeEquiv
  intro p
  change (¬ ((ARτ.arMeshRotationData τ).arrowInteriorOrbitData τ).SameSuccessorOrbit
      p.1.1.1 p.1.1.2) ↔
    ¬ ((ARσ.arMeshRotationData σ).arrowInteriorOrbitData σ).SameSuccessorOrbit
      (D.pullbackInteriorArrow σ τ ARσ ARτ p.1.1.1)
      (D.pullbackInteriorArrow σ τ ARσ ARτ p.1.1.2)
  exact not_congr <|
    D.pullbackInterior_sameSuccessorOrbit_iff σ τ ARσ ARτ
      p.1.1.1 p.1.1.2

/-- Exact raw cross-side square shift: dual incoming pairs on the shifted
source boundary correspond to source outgoing-incidence pairs on that same
shifted boundary. -/
def interiorSourceBoundaryCommonTargetEquivSourceBoundaryCommonSource
    [DecidableEq ι] :
    ARτ.InteriorSourceBoundaryCommonTargetArrowPair τ ≃
      ARσ.InteriorSourceBoundaryCommonSourceArrowPair σ :=
  (AlignedBiduality.interiorSourceBoundaryCommonTargetEquivTargetBoundaryCommonSource
    σ τ D ARσ ARτ).trans
      (ARσ.interiorCommonSourceBoundaryEquiv σ).symm

/-- Exact cross-side raw square shift for two different trimmed labelled
arrow-orbit components. -/
def interiorDifferentOrbitSourceBoundaryCommonTargetEquivSourceBoundaryCommonSource
    [DecidableEq ι] [DecidableEq κ] :
    ARτ.InteriorDifferentOrbitSourceBoundaryCommonTargetArrowPair τ ≃
      ARσ.InteriorDifferentOrbitSourceBoundaryCommonSourceArrowPair σ :=
  (D.interiorDifferentOrbitSourceBoundaryCommonTargetEquivTargetBoundaryCommonSource
    σ τ ARσ ARτ).trans
      (ARσ.interiorDifferentOrbitCommonSourceBoundaryEquiv σ).symm

include D in
/-- Cardinal form of the manuscript's preliminary different-orbit
cross-side square-shift equality. -/
theorem interiorDifferentOrbitSourceBoundaryCommonTarget_card_eq_sourceBoundaryCommonSource
    [DecidableEq ι] [DecidableEq κ] :
    Fintype.card
        (ARτ.InteriorDifferentOrbitSourceBoundaryCommonTargetArrowPair τ) =
      Fintype.card
        (ARσ.InteriorDifferentOrbitSourceBoundaryCommonSourceArrowPair σ) :=
  Fintype.card_congr
    (D.interiorDifferentOrbitSourceBoundaryCommonTargetEquivSourceBoundaryCommonSource
      σ τ ARσ ARτ)

include D in
/-- Raw dual incoming-boundary pairs and source outgoing-boundary pairs have
the same cardinality. -/
theorem interiorSourceBoundaryCommonTarget_card_eq_targetBoundaryCommonSource :
    Fintype.card (ARτ.InteriorSourceBoundaryCommonTargetArrowPair τ) =
      Fintype.card (ARσ.InteriorTargetBoundaryCommonSourceArrowPair σ) :=
  Fintype.card_congr
    (AlignedBiduality.interiorSourceBoundaryCommonTargetEquivTargetBoundaryCommonSource
      σ τ D ARσ ARτ)

include D in
/-- Combining dual pullback with the source-equality square shift converts
dual incoming-boundary pairs into source outgoing-incidence pairs on the
first shifted boundary. -/
theorem interiorSourceBoundaryCommonTarget_card_eq_sourceBoundaryCommonSource
    [DecidableEq ι] :
    Fintype.card (ARτ.InteriorSourceBoundaryCommonTargetArrowPair τ) =
      Fintype.card (ARσ.InteriorSourceBoundaryCommonSourceArrowPair σ) := by
  exact Fintype.card_congr
    (D.interiorSourceBoundaryCommonTargetEquivSourceBoundaryCommonSource
      σ τ ARσ ARτ)

end Interior

end AlignedBiduality

end OpConjecture.IndecomposableSkeleton
