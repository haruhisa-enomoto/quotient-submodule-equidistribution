import OpConjecture.RepresentationTheory.FourVertexDiagonalM4CutOccurrences
import OpConjecture.RepresentationTheory.FourVertexBoundaryChannelClassification

/-!
# Diagonal cuts as genuine `M6` occurrences or reverse-last exceptions

This file refines the long-chain diagonal-cut occurrence adapter.  A cut is
made into an interior common-target pair, and the exact reverse-last
condition required by `boundaryM6Reconstruction` is retained as a subtype
hypothesis. Regular cuts reconstruct genuine `HookM6` terms, while the
complement maps to the existing reverse-last correction stratum. Both maps,
and their combined classification, preserve the labelled cut injectively.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace OpConjecture.IndecomposableSkeleton.FiniteARTranslationData

universe u v

variable {K R : Type u} [Field K] [Ring R] [Algebra K R]
  [FiniteDimensional K R] [IsNoetherianRing R]
  {ι : Type v} [Fintype ι] [DecidableEq ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)
  (AR : σ.FiniteARTranslationData)

/-- A quotient-side long-chain diagonal cut as an interior common-target
pair. -/
def longArrowChainFirstDiagonalCutInteriorPair
    (q : AR.LongArrowChainFirstDiagonalCut σ) :
    AR.InteriorCommonTargetArrowPair σ := by
  let M := AR.arMeshRotationData σ
  let a := q.1.1.1
  let ha := q.1.1.2
  let n := M.arrowChainLength σ a ha
  let e := q.2.1.1
  let A := M.arrowChainAt σ a 1
  let B := M.arrowChainAt σ a (e - 1)
  have hlen : 4 ≤ M.arrowChainLength σ a ha := q.1.2
  have heLower : 2 ≤ e := q.2.1.2.1
  have heBounds := q.2.1.2
  change 2 ≤ e ∧ e ≤ M.arrowChainLength σ a ha + 1 - 2 at heBounds
  have heUpper : e ≤ M.arrowChainLength σ a ha - 1 := by omega
  have hANP : ¬ Projective (σ.obj A.1.2) :=
    M.arrowChainAt_succ_target_nonprojective σ a ha (n := 0) (by omega)
  have hANI : ¬ Injective (σ.obj A.1.1) :=
    M.arrowChainAt_not_injectiveSource_of_lt σ a ha (n := 1) (by omega)
  have hBNP : ¬ Projective (σ.obj B.1.2) := by
    have heLt : e - 2 < M.arrowChainLength σ a ha := by omega
    have h := M.arrowChainAt_succ_target_nonprojective σ a ha
      (n := e - 2) heLt
    have hind : e - 2 + 1 = e - 1 := by omega
    simpa only [B, hind] using h
  have hBNI : ¬ Injective (σ.obj B.1.1) :=
    M.arrowChainAt_not_injectiveSource_of_lt σ a ha
      (n := e - 1) (by omega)
  let AI := toInteriorArrow σ AR A ⟨hANP, hANI⟩
  let BI := toInteriorArrow σ AR B ⟨hBNP, hBNI⟩
  refine ⟨(AI, BI), ?_⟩
  exact (AR.longArrowChainFirstDiagonalCutCommonTargetPair σ q).2

omit [DecidableEq ι] in
/-- Forgetting the interior witnesses recovers the original labelled cut
occurrence. -/
theorem forget_longArrowChainFirstDiagonalCutInteriorPair
    (q : AR.LongArrowChainFirstDiagonalCut σ) :
    forgetInteriorCommonTarget σ AR
        (AR.longArrowChainFirstDiagonalCutInteriorPair σ q) =
      AR.longArrowChainFirstDiagonalCutCommonTargetPair σ q := by
  apply Subtype.ext
  rfl

omit [DecidableEq ι] in
/-- The common target of a long-chain diagonal cut is noninjective. -/
theorem longArrowChainFirstDiagonalCut_target_noninjective
    (q : AR.LongArrowChainFirstDiagonalCut σ) :
    ¬ Injective
      (σ.obj (AR.longArrowChainFirstDiagonalCutInteriorPair σ q).1.2.1.1.2) := by
  let M := AR.arMeshRotationData σ
  let a := q.1.1.1
  let ha := q.1.1.2
  have hlen : 4 ≤ M.arrowChainLength σ a ha := q.1.2
  have htarget : ¬ Injective (σ.obj (M.arrowChainAt σ a 1).1.2) := by
    rw [← M.arrowChainAt_succ_source_eq_target σ a ha (n := 1) (by omega)]
    exact M.arrowChainAt_not_injectiveSource_of_lt σ a ha
      (n := 2) (by omega)
  rw [← (AR.longArrowChainFirstDiagonalCutInteriorPair σ q).2]
  change ¬ Injective (σ.obj (M.arrowChainAt σ a 1).1.2)
  exact htarget

omit [DecidableEq ι] in
/-- The first occurrence of a long-chain diagonal cut is on the trimmed
source boundary. -/
theorem longArrowChainFirstDiagonalCut_first_interiorSource
    (q : AR.LongArrowChainFirstDiagonalCut σ) :
    ((AR.arMeshRotationData σ).arrowOrbitData σ).InteriorSource
      (AR.longArrowChainFirstDiagonalCutInteriorPair σ q).1.1 := by
  let M := AR.arMeshRotationData σ
  let a := q.1.1.1
  let ha := q.1.1.2
  have hlen : 4 ≤ M.arrowChainLength σ a ha := q.1.2
  let A := M.arrowChainAt σ a 1
  have hprojective : Projective (σ.obj A.1.1) := by
    rw [M.arrowChainAt_succ_source_eq_target σ a ha (n := 0) (by omega)]
    exact ha
  rw [M.arrowInterior_source_iff σ
    (AR.longArrowChainFirstDiagonalCutInteriorPair σ q).1.1]
  change Projective (σ.obj A.1.1)
  exact hprojective

omit [DecidableEq ι] in
/-- The two labelled occurrences of an actual long-chain diagonal cut lie
in one intrinsic successor component of the trimmed arrow translation. -/
theorem longArrowChainFirstDiagonalCut_sameSuccessorOrbit
    (q : AR.LongArrowChainFirstDiagonalCut σ) :
    let U := (AR.arMeshRotationData σ).arrowInteriorOrbitData σ
    let p := AR.longArrowChainFirstDiagonalCutInteriorPair σ q
    U.SameSuccessorOrbit p.1.1 p.1.2 := by
  let M := AR.arMeshRotationData σ
  let O := M.arrowOrbitData σ
  let U := M.arrowInteriorOrbitData σ
  let a := q.1.1.1
  let ha := q.1.1.2
  let n := M.arrowChainLength σ a ha
  let e := q.2.1.1
  let p := AR.longArrowChainFirstDiagonalCutInteriorPair σ q
  let A := p.1.1
  let B := p.1.2
  have hlen : 4 ≤ n := q.1.2
  have heLower : 2 ≤ e := q.2.1.2.1
  have heBounds := q.2.1.2
  change 2 ≤ e ∧ e ≤ n + 1 - 2 at heBounds
  have heUpper : e ≤ n - 1 := by omega
  have hAVal : A.1 = M.arrowChainAt σ a 1 := rfl
  have hBVal : B.1 = M.arrowChainAt σ a (e - 1) := rfl
  have hbeforeTarget :
      ∀ i < e - 2, ¬ Injective
        (σ.obj (((O.successor^[i + 1]) A.1).1.1)) := by
    intro i hi
    have hindex : i + 2 < n := by omega
    have hnotInjective :=
      M.arrowChainAt_not_injectiveSource_of_lt σ a ha hindex
    change ¬ Injective
      (σ.obj (((O.successor^[i + 2]) a).1.1)) at hnotInjective
    rw [hAVal]
    change ¬ Injective
      (σ.obj (((O.successor^[i + 1])
        ((O.successor^[1]) a)).1.1))
    rw [← Function.iterate_add_apply]
    simpa only [show i + 1 + 1 = i + 2 by omega] using hnotInjective
  have hiterate := O.interior_iterate_successor_val A (e - 2)
    hbeforeTarget
  refine ⟨e - 2, 0, ?_⟩
  simp only [Function.iterate_zero, id_eq]
  apply Subtype.ext
  calc
    ((U.successor^[e - 2]) A).1 =
        (O.successor^[e - 2]) A.1 := hiterate
    _ = (O.successor^[e - 2]) ((O.successor^[1]) a) := by
      rw [hAVal]
      rfl
    _ = (O.successor^[e - 1]) a := by
      rw [← Function.iterate_add_apply]
      congr 2
      omega
    _ = B.1 := hBVal.symm

/-- The exact reverse-last-arrow predicate on a long-chain diagonal cut. -/
def longArrowChainFirstDiagonalCutHasReverseLast
    (q : AR.LongArrowChainFirstDiagonalCut σ) : Prop :=
  HasIrreducibleMorphism
    (σ.obj (AR.boundaryM6Last σ
      (AR.longArrowChainFirstDiagonalCutInteriorPair σ q)
      (AR.longArrowChainFirstDiagonalCut_target_noninjective σ q)))
    (σ.obj (AR.boundaryM6FirstArrow σ
      (AR.longArrowChainFirstDiagonalCutInteriorPair σ q)).1.2)

omit [DecidableEq ι] in
/-- Advancing the second occurrence of a diagonal cut gives the arrow at
the cut index itself. -/
theorem boundaryM6FirstArrow_longArrowChainFirstDiagonalCut
    (q : AR.LongArrowChainFirstDiagonalCut σ) :
    let M := AR.arMeshRotationData σ
    let a := q.1.1.1
    let e := q.2.1.1
    AR.boundaryM6FirstArrow σ
        (AR.longArrowChainFirstDiagonalCutInteriorPair σ q) =
      M.arrowChainAt σ a e := by
  let M := AR.arMeshRotationData σ
  let O := M.arrowOrbitData σ
  let a := q.1.1.1
  let ha := q.1.1.2
  let e := q.2.1.1
  let B := M.arrowChainAt σ a (e - 1)
  have hlen : 4 ≤ M.arrowChainLength σ a ha := q.1.2
  have heLower : 2 ≤ e := q.2.1.2.1
  have heUpper : e ≤ M.arrowChainLength σ a ha - 1 := by
    have h := q.2.1.2.2
    change e ≤ M.arrowChainLength σ a ha + 1 - 2 at h
    omega
  have hBNI : ¬ Injective (σ.obj B.1.1) :=
    M.arrowChainAt_not_injectiveSource_of_lt σ a ha
      (n := e - 1) (by omega)
  change (O.tau.symm ⟨B, hBNI⟩).1 = M.arrowChainAt σ a e
  have hsuccessor : O.successor B = (O.tau.symm ⟨B, hBNI⟩).1 := by
    simp [OpConjecture.BoundaryTranslationChains.Data.successor, hBNI]
  rw [← hsuccessor]
  change O.successor ((O.successor^[e - 1]) a) = (O.successor^[e]) a
  rw [← Function.iterate_succ_apply' O.successor (e - 1) a]
  congr 2
  omega

omit [DecidableEq ι] in
/-- The canonical last label reconstructed from a diagonal cut is chain
vertex `4`. -/
theorem boundaryM6Last_longArrowChainFirstDiagonalCut
    (q : AR.LongArrowChainFirstDiagonalCut σ) :
    let a := q.1.1.1
    let ha := q.1.1.2
    AR.boundaryM6Last σ
        (AR.longArrowChainFirstDiagonalCutInteriorPair σ q)
        (AR.longArrowChainFirstDiagonalCut_target_noninjective σ q) =
      AR.arrowChainVertexNat σ a ha 4 := by
  let M := AR.arMeshRotationData σ
  let a := q.1.1.1
  let ha := q.1.1.2
  let A := M.arrowChainAt σ a 1
  let B := M.arrowChainAt σ a (q.2.1.1 - 1)
  have hlen : 4 ≤ M.arrowChainLength σ a ha := q.1.2
  have hAcommon : A.1.2 = B.1.2 :=
    (AR.longArrowChainFirstDiagonalCutCommonTargetPair σ q).2
  have hAtoTwo : (M.arrowChainAt σ a 2).1.1 = A.1.2 :=
    M.arrowChainAt_succ_source_eq_target σ a ha (n := 1) (by omega)
  let z : σ.NonprojectiveLabel :=
    ⟨(M.arrowChainAt σ a 3).1.2,
      M.arrowChainAt_succ_target_nonprojective σ a ha
        (n := 2) (by omega)⟩
  have hzTau : M.tau z =
      ⟨(M.arrowChainAt σ a 2).1.1,
        M.arrowChainAt_not_injectiveSource_of_lt σ a ha
          (n := 2) (by omega)⟩ := by
    apply Subtype.ext
    exact M.arTranslation_arrowChainAt_succ_target_eq_source
      σ a ha (n := 2) (by omega)
  change
    (M.tau.symm
      ⟨B.1.2,
        AR.longArrowChainFirstDiagonalCut_target_noninjective σ q⟩).1 =
      AR.arrowChainVertexNat σ a ha 4
  have hinput :
      (⟨B.1.2,
        AR.longArrowChainFirstDiagonalCut_target_noninjective σ q⟩ :
          σ.NoninjectiveLabel) = M.tau z := by
    rw [hzTau]
    apply Subtype.ext
    exact hAcommon.symm.trans hAtoTwo.symm
  rw [hinput, M.tau.symm_apply_apply]
  exact AR.arrowChainAt_target_eq_vertexNat_succ
    σ a ha (n := 3) (by
      simpa only [M] using (show 3 ≤ M.arrowChainLength σ a ha by omega))

omit [DecidableEq ι] in
/-- In literal chain coordinates, the reverse-last obstruction is exactly
the extra arrow from vertex `4` to the vertex immediately after the cut.
This is the local predicate used in the manuscript's diagonal correction. -/
theorem longArrowChainFirstDiagonalCutHasReverseLast_iff
    (q : AR.LongArrowChainFirstDiagonalCut σ) :
    AR.longArrowChainFirstDiagonalCutHasReverseLast σ q ↔
      HasIrreducibleMorphism
        (σ.obj (AR.arrowChainVertexNat σ q.1.1.1 q.1.1.2 4))
        (σ.obj (AR.arrowChainVertexNat σ q.1.1.1 q.1.1.2
          (q.2.1.1 + 1))) := by
  let M := AR.arMeshRotationData σ
  let a := q.1.1.1
  let ha := q.1.1.2
  let e := q.2.1.1
  have hlen : 4 ≤ M.arrowChainLength σ a ha := q.1.2
  have heUpper : e ≤ M.arrowChainLength σ a ha - 1 := by
    have h := q.2.1.2.2
    change e ≤ M.arrowChainLength σ a ha + 1 - 2 at h
    omega
  rw [longArrowChainFirstDiagonalCutHasReverseLast,
    AR.boundaryM6Last_longArrowChainFirstDiagonalCut σ q,
    AR.boundaryM6FirstArrow_longArrowChainFirstDiagonalCut σ q,
    AR.arrowChainAt_target_eq_vertexNat_succ
      σ a ha (n := e) (by
        simpa only [M] using
          (show e ≤ M.arrowChainLength σ a ha by omega))]

/-- Long-chain diagonal cuts satisfying the one remaining local
admissibility condition for regular `M6` reconstruction. -/
abbrev LongArrowChainFirstDiagonalRegularCut :=
  {q : AR.LongArrowChainFirstDiagonalCut σ //
    ¬ AR.longArrowChainFirstDiagonalCutHasReverseLast σ q}

/-- The complementary diagonal cuts carrying the reverse-last-arrow
exception. -/
abbrev LongArrowChainFirstDiagonalReverseLastCut :=
  {q : AR.LongArrowChainFirstDiagonalCut σ //
    AR.longArrowChainFirstDiagonalCutHasReverseLast σ q}

noncomputable instance longArrowChainFirstDiagonalRegularCutFintype :
    Fintype (AR.LongArrowChainFirstDiagonalRegularCut σ) :=
  Fintype.ofFinite _

noncomputable instance longArrowChainFirstDiagonalReverseLastCutFintype :
    Fintype (AR.LongArrowChainFirstDiagonalReverseLastCut σ) :=
  Fintype.ofFinite _

omit [DecidableEq ι] in
/-- Every diagonal cut is uniquely either regular or a reverse-last-arrow
exception. -/
def longArrowChainFirstDiagonalCutEquivRegularSumReverseLast :
    AR.LongArrowChainFirstDiagonalCut σ ≃
      AR.LongArrowChainFirstDiagonalRegularCut σ ⊕
        AR.LongArrowChainFirstDiagonalReverseLastCut σ where
  toFun q := by
    classical
    by_cases h : AR.longArrowChainFirstDiagonalCutHasReverseLast σ q
    · exact Sum.inr ⟨q, h⟩
    · exact Sum.inl ⟨q, h⟩
  invFun q := q.elim Subtype.val Subtype.val
  left_inv q := by
    classical
    by_cases h : AR.longArrowChainFirstDiagonalCutHasReverseLast σ q
    · simp [h]
    · simp [h]
  right_inv q := by
    classical
    rcases q with q | q
    · simp [q.2]
    · simp [q.2]

omit [DecidableEq ι] in
/-- Cardinal form of the exact regular/reverse-last partition. -/
theorem longArrowChainFirstDiagonalCut_card_eq_regular_add_reverseLast :
    Fintype.card (AR.LongArrowChainFirstDiagonalCut σ) =
      Fintype.card (AR.LongArrowChainFirstDiagonalRegularCut σ) +
        Fintype.card (AR.LongArrowChainFirstDiagonalReverseLastCut σ) := by
  rw [Fintype.card_congr
    (AR.longArrowChainFirstDiagonalCutEquivRegularSumReverseLast σ)]
  exact Fintype.card_sum

omit [DecidableEq ι] in
/-- Package a regular cut as the exact boundary type reconstructed by the
global `M6` classification. -/
def LongArrowChainFirstDiagonalRegularCut.toBoundaryM6RegularPair
    (q : AR.LongArrowChainFirstDiagonalRegularCut σ) :
    AR.BoundaryM6RegularPair σ where
  pair := AR.longArrowChainFirstDiagonalCutInteriorPair σ q.1
  first_source :=
    AR.longArrowChainFirstDiagonalCut_first_interiorSource σ q.1
  target_noninjective :=
    AR.longArrowChainFirstDiagonalCut_target_noninjective σ q.1
  last_not_to_middle := q.2

omit [DecidableEq ι] in
/-- Package an exceptional cut as the reverse-last correction type in the
exhaustive first-boundary classification. -/
def LongArrowChainFirstDiagonalReverseLastCut.toBoundaryM6ReverseLastPair
    (q : AR.LongArrowChainFirstDiagonalReverseLastCut σ) :
    AR.BoundaryM6ReverseLastPair σ where
  pair := AR.longArrowChainFirstDiagonalCutInteriorPair σ q.1
  first_source :=
    AR.longArrowChainFirstDiagonalCut_first_interiorSource σ q.1
  target_noninjective :=
    AR.longArrowChainFirstDiagonalCut_target_noninjective σ q.1
  last_to_middle := q.2

omit [DecidableEq ι] in
/-- The regular-cut boundary encoding is injective. -/
theorem longArrowChainFirstDiagonalRegularCut_toBoundary_injective :
    Function.Injective
      (LongArrowChainFirstDiagonalRegularCut.toBoundaryM6RegularPair σ AR) := by
  intro q r h
  apply Subtype.ext
  apply AR.longArrowChainFirstDiagonalCutCommonTargetPair_injective σ
  have hp := congrArg BoundaryM6RegularPair.pair h
  have hforget := congrArg (forgetInteriorCommonTarget σ AR) hp
  simpa only [LongArrowChainFirstDiagonalRegularCut.toBoundaryM6RegularPair,
    AR.forget_longArrowChainFirstDiagonalCutInteriorPair σ] using hforget

omit [DecidableEq ι] in
/-- The reverse-last correction occurrence also remembers its cut. -/
theorem longArrowChainFirstDiagonalReverseLastCut_toBoundary_injective :
    Function.Injective
      (LongArrowChainFirstDiagonalReverseLastCut.toBoundaryM6ReverseLastPair
        σ AR) := by
  intro q r h
  apply Subtype.ext
  apply AR.longArrowChainFirstDiagonalCutCommonTargetPair_injective σ
  have hp := congrArg BoundaryM6ReverseLastPair.pair h
  have hforget := congrArg (forgetInteriorCommonTarget σ AR) hp
  simpa only [
    LongArrowChainFirstDiagonalReverseLastCut.toBoundaryM6ReverseLastPair,
    AR.forget_longArrowChainFirstDiagonalCutInteriorPair σ] using hforget

include K AR in
/-- Reconstruct the genuine interior `M6` term represented by a regular
long-chain diagonal cut. -/
def LongArrowChainFirstDiagonalRegularCut.toHookM6Interior
    (q : AR.LongArrowChainFirstDiagonalRegularCut σ) :
    HookM6Channel.InteriorChannel σ AR :=
  (AR.boundaryM6Reconstruction (k := K) σ
    (q.toBoundaryM6RegularPair σ AR)).term

include K AR in
/-- Reconstruction preserves the actual labelled common-target occurrence. -/
theorem LongArrowChainFirstDiagonalRegularCut.toHookM6Interior_occurrence
    (q : AR.LongArrowChainFirstDiagonalRegularCut σ) :
    HookM6Channel.interiorCommonTargetPair σ AR
        (q.toHookM6Interior (K := K) σ AR) =
      AR.longArrowChainFirstDiagonalCutInteriorPair σ q.1 :=
  (AR.boundaryM6Reconstruction (k := K) σ
    (q.toBoundaryM6RegularPair σ AR)).occurrence_eq

include K AR in
/-- The resulting genuine `M6` occurrence still remembers its cut. -/
theorem longArrowChainFirstDiagonalRegularCut_toHookM6Interior_injective :
    Function.Injective
      (LongArrowChainFirstDiagonalRegularCut.toHookM6Interior
        (K := K) σ AR) := by
  intro q r h
  apply AR.longArrowChainFirstDiagonalRegularCut_toBoundary_injective σ
  apply BoundaryM6RegularPair.ext
  calc
    (q.toBoundaryM6RegularPair σ AR).pair =
        HookM6Channel.interiorCommonTargetPair σ AR
          (q.toHookM6Interior (K := K) σ AR) :=
      (q.toHookM6Interior_occurrence (K := K) σ AR).symm
    _ = HookM6Channel.interiorCommonTargetPair σ AR
          (r.toHookM6Interior (K := K) σ AR) := congrArg _ h
    _ = (r.toBoundaryM6RegularPair σ AR).pair :=
      r.toHookM6Interior_occurrence (K := K) σ AR

include K AR in
/-- Classify every long-chain diagonal cut as either a genuine interior
`M6` term or an occurrence in the existing reverse-last correction
stratum. -/
def longArrowChainFirstDiagonalCutToHookM6OrReverseLast :
    AR.LongArrowChainFirstDiagonalCut σ →
      HookM6Channel.InteriorChannel σ AR ⊕
        AR.BoundaryM6ReverseLastPair σ :=
  fun q ↦ Sum.map
    (LongArrowChainFirstDiagonalRegularCut.toHookM6Interior
      (K := K) σ AR)
    (LongArrowChainFirstDiagonalReverseLastCut.toBoundaryM6ReverseLastPair
      σ AR)
    (AR.longArrowChainFirstDiagonalCutEquivRegularSumReverseLast σ q)

include K AR in
/-- The genuine/exceptional classification retains the maximal chain and
the cut index. -/
theorem longArrowChainFirstDiagonalCutToHookM6OrReverseLast_injective :
    Function.Injective
      (AR.longArrowChainFirstDiagonalCutToHookM6OrReverseLast
        (K := K) σ) :=
  ((AR.longArrowChainFirstDiagonalRegularCut_toHookM6Interior_injective
      (K := K) σ).sumMap
    (AR.longArrowChainFirstDiagonalReverseLastCut_toBoundary_injective σ)).comp
    (AR.longArrowChainFirstDiagonalCutEquivRegularSumReverseLast σ).injective

/-- First trimmed source-boundary occurrences with noninjective common
target.  This is the occurrence-level ambient type for the regular `M6`
and reverse-last branches together. -/
abbrev FirstSourceNoninjectiveTargetPair :=
  {p : AR.FirstSourceBoundaryPair σ //
    ¬ Injective (σ.obj p.1.1.2.1.1.2)}

noncomputable instance firstSourceNoninjectiveTargetPairFintype :
    Fintype (AR.FirstSourceNoninjectiveTargetPair σ) :=
  Fintype.ofFinite _

/-- Splitting by the reverse-last predicate classifies the noninjective
part of the first source boundary as regular or exceptional. -/
def firstSourceNoninjectiveTargetPairEquivRegularSumReverseLast :
    AR.FirstSourceNoninjectiveTargetPair σ ≃
      AR.BoundaryM6RegularPair σ ⊕
        AR.BoundaryM6ReverseLastPair σ where
  toFun p := by
    classical
    by_cases hlast : HasIrreducibleMorphism
        (σ.obj (AR.boundaryM6Last σ p.1.1 p.2))
        (σ.obj (AR.boundaryM6FirstArrow σ p.1.1).1.2)
    · exact Sum.inr
        { pair := p.1.1
          first_source := p.1.2
          target_noninjective := p.2
          last_to_middle := hlast }
    · exact Sum.inl
        { pair := p.1.1
          first_source := p.1.2
          target_noninjective := p.2
          last_not_to_middle := hlast }
  invFun p := by
    rcases p with p | p
    · exact ⟨⟨p.pair, p.first_source⟩, p.target_noninjective⟩
    · exact ⟨⟨p.pair, p.first_source⟩, p.target_noninjective⟩
  left_inv p := by
    classical
    by_cases hlast : HasIrreducibleMorphism
        (σ.obj (AR.boundaryM6Last σ p.1.1 p.2))
        (σ.obj (AR.boundaryM6FirstArrow σ p.1.1).1.2)
    · simp [hlast]
    · simp [hlast]
  right_inv p := by
    classical
    rcases p with p | p
    · simp [p.last_not_to_middle]
    · simp [p.last_to_middle]

include K AR in
/-- The native `M6`/reverse-last sum is exactly the noninjective-target
part of the literal first source boundary. -/
def hookM6OrReverseLastEquivFirstSourceNoninjectiveTarget :
    HookM6Channel.InteriorChannel σ AR ⊕
        AR.BoundaryM6ReverseLastPair σ ≃
      AR.FirstSourceNoninjectiveTargetPair σ :=
  (Equiv.sumCongr
      (AR.boundaryM6RegularPairEquiv (k := K) σ)
      (Equiv.refl _)).trans
    (AR.firstSourceNoninjectiveTargetPairEquivRegularSumReverseLast σ).symm

/-- A diagonal cut viewed directly as a noninjective-target occurrence on
the literal first source boundary. -/
def longArrowChainFirstDiagonalCutToFirstSourceNoninjectiveTarget
    (q : AR.LongArrowChainFirstDiagonalCut σ) :
    AR.FirstSourceNoninjectiveTargetPair σ :=
  ⟨⟨AR.longArrowChainFirstDiagonalCutInteriorPair σ q,
      AR.longArrowChainFirstDiagonalCut_first_interiorSource σ q⟩,
    AR.longArrowChainFirstDiagonalCut_target_noninjective σ q⟩

omit [DecidableEq ι] in
/-- The direct first-boundary occurrence retains the chain and cut index. -/
theorem longArrowChainFirstDiagonalCutToFirstSourceNoninjectiveTarget_injective :
    Function.Injective
      (AR.longArrowChainFirstDiagonalCutToFirstSourceNoninjectiveTarget σ) := by
  intro q r h
  apply AR.longArrowChainFirstDiagonalCutCommonTargetPair_injective σ
  have hinterior := congrArg
    (fun p : AR.FirstSourceNoninjectiveTargetPair σ ↦ p.1.1) h
  have hforget := congrArg (forgetInteriorCommonTarget σ AR) hinterior
  simpa only [longArrowChainFirstDiagonalCutToFirstSourceNoninjectiveTarget,
    AR.forget_longArrowChainFirstDiagonalCutInteriorPair σ] using hforget

include K AR in
/-- The channel classifier and the direct first-boundary encoding carry
exactly the same labelled occurrence. -/
theorem hookM6OrReverseLastEquiv_firstDiagonalCut
    (q : AR.LongArrowChainFirstDiagonalCut σ) :
    AR.hookM6OrReverseLastEquivFirstSourceNoninjectiveTarget
        (K := K) σ
        (AR.longArrowChainFirstDiagonalCutToHookM6OrReverseLast
          (K := K) σ q) =
      AR.longArrowChainFirstDiagonalCutToFirstSourceNoninjectiveTarget σ q := by
  classical
  by_cases h : AR.longArrowChainFirstDiagonalCutHasReverseLast σ q
  · simp [longArrowChainFirstDiagonalCutToHookM6OrReverseLast,
      longArrowChainFirstDiagonalCutEquivRegularSumReverseLast, h,
      hookM6OrReverseLastEquivFirstSourceNoninjectiveTarget,
      firstSourceNoninjectiveTargetPairEquivRegularSumReverseLast,
      longArrowChainFirstDiagonalCutToFirstSourceNoninjectiveTarget]
    rfl
  · apply Subtype.ext
    apply Subtype.ext
    simpa [longArrowChainFirstDiagonalCutToHookM6OrReverseLast,
      longArrowChainFirstDiagonalCutEquivRegularSumReverseLast, h,
      hookM6OrReverseLastEquivFirstSourceNoninjectiveTarget,
      firstSourceNoninjectiveTargetPairEquivRegularSumReverseLast,
      boundaryM6RegularPairEquiv,
      HookM6Channel.toBoundaryM6RegularPair,
      longArrowChainFirstDiagonalCutToFirstSourceNoninjectiveTarget] using
        (show HookM6Channel.interiorCommonTargetPair σ AR
            (LongArrowChainFirstDiagonalRegularCut.toHookM6Interior
              (K := K) σ AR ⟨q, h⟩) =
          AR.longArrowChainFirstDiagonalCutInteriorPair σ q from
        LongArrowChainFirstDiagonalRegularCut.toHookM6Interior_occurrence
          (K := K) σ AR ⟨q, h⟩)

/-- Exact image of diagonal cuts inside the noninjective-target first source
boundary. -/
abbrev LongArrowChainFirstDiagonalFirstBoundaryImage :=
  Set.range
    (AR.longArrowChainFirstDiagonalCutToFirstSourceNoninjectiveTarget σ)

/-- The different-chain part of the same boundary: noninjective-target first
source occurrences not represented by a same-chain diagonal cut. -/
abbrev LongArrowChainFirstDiagonalFirstBoundaryComplement :=
  {p : AR.FirstSourceNoninjectiveTargetPair σ //
    p ∉ AR.LongArrowChainFirstDiagonalFirstBoundaryImage σ}

noncomputable instance
    longArrowChainFirstDiagonalFirstBoundaryComplementFintype :
    Fintype (AR.LongArrowChainFirstDiagonalFirstBoundaryComplement σ) :=
  Fintype.ofFinite _

/-- Intrinsic different-component part of the noninjective literal first
source boundary. -/
abbrev DifferentOrbitFirstSourceNoninjectiveTargetPair :=
  {p : AR.FirstSourceNoninjectiveTargetPair σ //
    InteriorCommonTargetArrowPair.DifferentOrbit σ AR p.1.1}

/-- Intrinsic different-component part of the diagonal-cut-image
complement. -/
abbrev LongArrowChainFirstDiagonalFirstBoundaryDifferentOrbitComplement :=
  {p : AR.LongArrowChainFirstDiagonalFirstBoundaryComplement σ //
    InteriorCommonTargetArrowPair.DifferentOrbit σ AR p.1.1.1}

/-- The part of the diagonal-cut-image complement which still lies in one
intrinsic successor component.  This is kept explicit until its short-chain
classification is proved. -/
abbrev LongArrowChainFirstDiagonalFirstBoundarySameOrbitRemainder :=
  {p : AR.LongArrowChainFirstDiagonalFirstBoundaryComplement σ //
    let U := (AR.arMeshRotationData σ).arrowInteriorOrbitData σ
    U.SameSuccessorOrbit p.1.1.1.1.1 p.1.1.1.1.2}

/-- Maximal labelled arrow chains with exactly three mesh-rotation steps.
These are the short chains which can contribute a same-orbit noninjective
first-boundary pair outside the long diagonal-cut image. -/
abbrev LengthThreeArrowChainStart :=
  {a : {q : σ.IrreduciblePair // Projective (σ.obj q.1.2)} //
    (AR.arMeshRotationData σ).arrowChainLength σ a.1 a.2 = 3}

noncomputable instance
    differentOrbitFirstSourceNoninjectiveTargetPairFintype :
    Fintype (AR.DifferentOrbitFirstSourceNoninjectiveTargetPair σ) :=
  Fintype.ofFinite _

noncomputable instance
    longArrowChainFirstDiagonalFirstBoundaryDifferentOrbitComplementFintype :
    Fintype
      (AR.LongArrowChainFirstDiagonalFirstBoundaryDifferentOrbitComplement
        σ) :=
  Fintype.ofFinite _

noncomputable instance
    longArrowChainFirstDiagonalFirstBoundarySameOrbitRemainderFintype :
    Fintype
      (AR.LongArrowChainFirstDiagonalFirstBoundarySameOrbitRemainder σ) :=
  Fintype.ofFinite _

noncomputable instance lengthThreeArrowChainStartFintype :
    Fintype (AR.LengthThreeArrowChainStart σ) :=
  Fintype.ofFinite _

omit [DecidableEq ι] in
/-- A pair from different intrinsic components cannot belong to the actual
long-chain diagonal-cut image. -/
theorem differentOrbitFirstSourceNoninjectiveTarget_not_mem_diagonalImage
    (p : AR.DifferentOrbitFirstSourceNoninjectiveTargetPair σ) :
    p.1 ∉ AR.LongArrowChainFirstDiagonalFirstBoundaryImage σ := by
  rintro ⟨q, hq⟩
  apply p.2
  have hsame := AR.longArrowChainFirstDiagonalCut_sameSuccessorOrbit σ q
  rw [← hq]
  exact hsame

omit [DecidableEq ι] in
/-- Thus the different-orbit part of the full noninjective first boundary
is exactly the different-orbit part of the diagonal-image complement. -/
def differentOrbitFirstSourceNoninjectiveTargetEquivDiagonalComplement :
    AR.DifferentOrbitFirstSourceNoninjectiveTargetPair σ ≃
      AR.LongArrowChainFirstDiagonalFirstBoundaryDifferentOrbitComplement
        σ where
  toFun p :=
    ⟨⟨p.1,
      AR.differentOrbitFirstSourceNoninjectiveTarget_not_mem_diagonalImage
        σ p⟩, p.2⟩
  invFun p := ⟨p.1.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The diagonal-cut-image complement splits exactly into its intrinsic
different-orbit part and the retained same-orbit remainder. -/
def longArrowChainFirstDiagonalFirstBoundaryComplementEquivDifferentOrbitSumSameOrbit :
    AR.LongArrowChainFirstDiagonalFirstBoundaryComplement σ ≃
      AR.LongArrowChainFirstDiagonalFirstBoundaryDifferentOrbitComplement σ ⊕
        AR.LongArrowChainFirstDiagonalFirstBoundarySameOrbitRemainder σ := by
  classical
  let P : AR.LongArrowChainFirstDiagonalFirstBoundaryComplement σ → Prop :=
    fun p ↦ InteriorCommonTargetArrowPair.DifferentOrbit σ AR p.1.1.1
  let E := (Equiv.sumCompl P).symm
  let S : {p : AR.LongArrowChainFirstDiagonalFirstBoundaryComplement σ //
      ¬ P p} ≃
      AR.LongArrowChainFirstDiagonalFirstBoundarySameOrbitRemainder σ := by
    apply (Equiv.refl _).subtypeEquiv
    intro p
    simp [P, InteriorCommonTargetArrowPair.DifferentOrbit]
  exact E.trans (Equiv.sumCongr (Equiv.refl _) S)

omit [DecidableEq ι] in
/-- Cardinal form of the intrinsic different/same-component split of the
diagonal-cut-image complement. -/
theorem longArrowChainFirstDiagonalFirstBoundaryComplement_card_eq_differentOrbit_add_sameOrbit :
    Fintype.card
        (AR.LongArrowChainFirstDiagonalFirstBoundaryComplement σ) =
      Fintype.card (AR.DifferentOrbitFirstSourceNoninjectiveTargetPair σ) +
        Fintype.card
          (AR.LongArrowChainFirstDiagonalFirstBoundarySameOrbitRemainder
            σ) := by
  have hsplit := Fintype.card_congr
    (AR.longArrowChainFirstDiagonalFirstBoundaryComplementEquivDifferentOrbitSumSameOrbit
      σ)
  have hdifferent := Fintype.card_congr
    (AR.differentOrbitFirstSourceNoninjectiveTargetEquivDiagonalComplement
      σ)
  simp only [Fintype.card_sum] at hsplit
  omega

omit [DecidableEq ι] in
/-- The retained same-component remainder is genuinely short: its two
labelled occurrences are equal.  If they were distinct, their common-target
equality would give an actual cut on a long maximal chain; the only remaining
chain length is three, where the second interior occurrence already has an
injective target. -/
theorem LongArrowChainFirstDiagonalFirstBoundarySameOrbitRemainder.pair_eq_and_chainLength_eq_three
    (p : AR.LongArrowChainFirstDiagonalFirstBoundarySameOrbitRemainder σ) :
    let M := AR.arMeshRotationData σ
    let O := M.arrowOrbitData σ
    let A := p.1.1.1.1.1.1
    let a := (O.tau ⟨A.1, A.2.1⟩).1
    let ha : Projective (σ.obj a.1.2) := p.1.1.1.2
    A = p.1.1.1.1.1.2 ∧ M.arrowChainLength σ a ha = 3 := by
  let M := AR.arMeshRotationData σ
  let O := M.arrowOrbitData σ
  let U := M.arrowInteriorOrbitData σ
  let pair := p.1.1.1.1
  let A := pair.1.1
  let B := pair.1.2
  have hASource : O.InteriorSource A := p.1.1.1.2
  have hTargetNI : ¬ Injective (σ.obj B.1.1.2) := p.1.1.2
  have hBTarget : ¬ O.InteriorTarget B := by
    intro h
    exact hTargetNI ((M.arrowInterior_target_iff σ B).1 h)
  have hsame : U.SameSuccessorOrbit A B := p.2
  obtain ⟨r, hr⟩ :=
    U.exists_iterate_eq_of_mem_source_of_sameSuccessorOrbit hASource hsame
  let aSub := O.tau ⟨A.1, A.2.1⟩
  let a := aSub.1
  have ha : Projective (σ.obj a.1.2) := by
    exact hASource
  let n := M.arrowChainLength σ a ha
  have haNotTarget : ¬ Injective (σ.obj a.1.1) := aSub.2
  have hstart : O.successor a = A.1 := by
    rw [show O.successor a = (O.tau.symm ⟨a, haNotTarget⟩).1 by
      classical
      simp [OpConjecture.BoundaryTranslationChains.Data.successor,
        haNotTarget]]
    exact congrArg Subtype.val (O.tau.symm_apply_apply ⟨A.1, A.2.1⟩)
  have hAChain : M.arrowChainAt σ a 1 = A.1 := by
    simpa only [ARMeshRotationData.arrowChainAt,
      Function.iterate_one] using hstart
  have hbefore : ∀ i < r,
      ¬ O.InteriorTarget ((U.successor^[i]) A) := by
    intro i hi htarget
    have hfixed := U.iterate_eq_self_of_mem_target
      ((U.successor^[i]) A) htarget (r - i)
    have hir : i + (r - i) = r := by omega
    have hri : (U.successor^[r]) A = (U.successor^[i]) A := by
      calc
        (U.successor^[r]) A =
            (U.successor^[(r - i) + i]) A := by
          congr 2
          omega
        _ = (U.successor^[r - i]) ((U.successor^[i]) A) :=
          Function.iterate_add_apply U.successor (r - i) i A
        _ = (U.successor^[i]) A := hfixed
    apply hBTarget
    rw [← hr, hri]
    exact htarget
  have hUVal := O.interior_iterate_successor_val_of_not_interiorTarget
    A r hbefore
  have hBChain : M.arrowChainAt σ a (r + 1) = B.1 := by
    change (O.successor^[r + 1]) a = B.1
    calc
      (O.successor^[r + 1]) a =
          (O.successor^[r]) ((O.successor^[1]) a) :=
        Function.iterate_add_apply O.successor r 1 a
      _ = (O.successor^[r]) A.1 := by
        rw [show (O.successor^[1]) a = A.1 by
          simpa only [Function.iterate_one] using hstart]
      _ = ((U.successor^[r]) A).1 := hUVal.symm
      _ = B.1 := congrArg Subtype.val hr
  have hr1n : r + 1 < n := by
    by_contra hnot
    have hnle : n ≤ r + 1 := by omega
    have hnTarget : Injective
        (σ.obj ((M.arrowChainAt σ a n).1.1)) :=
      M.arrowChainAt_length_injectiveSource σ a ha
    have hlate : M.arrowChainAt σ a (r + 1) =
        M.arrowChainAt σ a n := by
      change (O.successor^[r + 1]) a = (O.successor^[n]) a
      calc
        (O.successor^[r + 1]) a =
            (O.successor^[(r + 1 - n) + n]) a := by
          rw [Nat.sub_add_cancel hnle]
        _ =
            (O.successor^[r + 1 - n]) ((O.successor^[n]) a) := by
          exact Function.iterate_add_apply O.successor (r + 1 - n) n a
        _ = (O.successor^[n]) a :=
          O.iterate_eq_self_of_mem_target
            ((O.successor^[n]) a)
            (M.arrowChainAt_length_injectiveSource σ a ha)
            (r + 1 - n)
    apply B.2.2
    rw [← hBChain, hlate]
    exact hnTarget
  have hr2n : r + 2 < n := by
    by_contra hnot
    have hre : r + 2 = n := by omega
    have hstep := M.arrowChainAt_succ_source_eq_target σ a ha hr1n
    have hnTarget := M.arrowChainAt_length_injectiveSource σ a ha
    apply hTargetNI
    rw [← hBChain, ← hstep, hre]
    exact hnTarget
  have hnThree : 3 ≤ n := by omega
  have hnNotLong : ¬ 4 ≤ n := by
    intro hnLong
    let e := r + 2
    have heBounds : 2 ≤ e ∧ e ≤ n + 1 - 2 := by
      constructor <;> omega
    have hfirstVertex := AR.arrowChainAt_target_eq_vertexNat_succ
      σ a ha (n := 1) (by omega : 1 ≤ n)
    have hsecondVertex := AR.arrowChainAt_target_eq_vertexNat_succ
      σ a ha (n := r + 1) (by omega : r + 1 ≤ n)
    have heq : AR.arrowChainVertexNat σ a ha 2 =
        AR.arrowChainVertexNat σ a ha e := by
      calc
        AR.arrowChainVertexNat σ a ha 2 =
            (M.arrowChainAt σ a 1).1.2 := hfirstVertex.symm
        _ = A.1.1.2 := congrArg (fun q : σ.IrreduciblePair ↦ q.1.2)
          hAChain
        _ = B.1.1.2 := pair.2
        _ = (M.arrowChainAt σ a (r + 1)).1.2 :=
          congrArg (fun q : σ.IrreduciblePair ↦ q.1.2) hBChain.symm
        _ = AR.arrowChainVertexNat σ a ha e := by
          simpa only [e, show r + 1 + 1 = r + 2 by omega] using
            hsecondVertex
    let q : AR.LongArrowChainFirstDiagonalCut σ :=
      ⟨⟨⟨a, ha⟩, hnLong⟩, ⟨⟨e, heBounds⟩, heq⟩⟩
    apply p.1.2
    refine ⟨q, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact hAChain
    · apply Subtype.ext
      change M.arrowChainAt σ a (r + 2 - 1) = B.1
      simpa only [show r + 2 - 1 = r + 1 by omega] using hBChain
  have hnEq : n = 3 := by omega
  have hrEq : r = 0 := by omega
  subst r
  have hpair : A = B := by
    simpa only [Function.iterate_zero, id_eq] using hr
  exact ⟨hpair, hnEq⟩

omit [DecidableEq ι] in
/-- In particular, the retained short same-component remainder is diagonal
as a labelled occurrence pair. -/
theorem LongArrowChainFirstDiagonalFirstBoundarySameOrbitRemainder.pair_eq
    (p : AR.LongArrowChainFirstDiagonalFirstBoundarySameOrbitRemainder σ) :
    p.1.1.1.1.1.1 = p.1.1.1.1.1.2 :=
  (p.pair_eq_and_chainLength_eq_three σ AR).1

omit [DecidableEq ι] in
/-- A length-three maximal arrow chain supplies its unique diagonal
noninjective first-boundary occurrence outside the long-cut image. -/
def lengthThreeArrowChainStartToSameOrbitRemainder
    (a₀ : AR.LengthThreeArrowChainStart σ) :
    AR.LongArrowChainFirstDiagonalFirstBoundarySameOrbitRemainder σ := by
  let M := AR.arMeshRotationData σ
  let O := M.arrowOrbitData σ
  let U := M.arrowInteriorOrbitData σ
  let a := a₀.1.1
  let ha := a₀.1.2
  have hlen : M.arrowChainLength σ a ha = 3 := a₀.2
  let A₀ := M.arrowChainAt σ a 1
  have hANP : ¬ Projective (σ.obj A₀.1.2) :=
    M.arrowChainAt_succ_target_nonprojective σ a ha (n := 0) (by omega)
  have hANI : ¬ Injective (σ.obj A₀.1.1) :=
    M.arrowChainAt_not_injectiveSource_of_lt σ a ha (n := 1) (by omega)
  let A := toInteriorArrow σ AR A₀ ⟨hANP, hANI⟩
  let pair : AR.InteriorCommonTargetArrowPair σ := ⟨(A, A), rfl⟩
  have hsource : O.InteriorSource A := by
    rw [M.arrowInterior_source_iff σ A]
    have hstep := M.arrowChainAt_succ_source_eq_target σ a ha
      (n := 0) (by omega)
    rw [show A.1.1.1 = A₀.1.1 by rfl, hstep]
    exact ha
  have htargetNI : ¬ Injective (σ.obj A.1.1.2) := by
    have hstep := M.arrowChainAt_succ_source_eq_target σ a ha
      (n := 1) (by omega)
    have hnot := M.arrowChainAt_not_injectiveSource_of_lt σ a ha
      (n := 2) (by omega)
    rw [show A.1.1.2 = A₀.1.2 by rfl, ← hstep]
    exact hnot
  let first : AR.FirstSourceNoninjectiveTargetPair σ :=
    ⟨⟨pair, hsource⟩, htargetNI⟩
  have hnotImage :
      first ∉ AR.LongArrowChainFirstDiagonalFirstBoundaryImage σ := by
    rintro ⟨q, hq⟩
    let b := q.1.1.1
    let hb := q.1.1.2
    have hbLong : 4 ≤ M.arrowChainLength σ b hb := q.1.2
    have hfirstArrow : M.arrowChainAt σ b 1 =
        M.arrowChainAt σ a 1 := by
      have h := congrArg
        (fun z : AR.FirstSourceNoninjectiveTargetPair σ ↦ z.1.1.1.1.1)
        hq
      exact h
    have haNotTarget : ¬ Injective (σ.obj a.1.1) :=
      M.arrowChainAt_not_injectiveSource_of_lt σ a ha (n := 0) (by omega)
    have hbNotTarget : ¬ Injective (σ.obj b.1.1) :=
      M.arrowChainAt_not_injectiveSource_of_lt σ b hb (n := 0) (by omega)
    have hstart : b = a := by
      apply O.successor_left_injective hbNotTarget haNotTarget
      simpa only [ARMeshRotationData.arrowChainAt,
        Function.iterate_one] using hfirstArrow
    have hstartSubtype :
        (⟨b, hb⟩ : {q : σ.IrreduciblePair // Projective (σ.obj q.1.2)}) =
          ⟨a, ha⟩ := by
      apply Subtype.ext
      exact hstart
    have hlength := congrArg
      (fun c : {q : σ.IrreduciblePair // Projective (σ.obj q.1.2)} ↦
        M.arrowChainLength σ c.1 c.2) hstartSubtype
    have hlengthB : M.arrowChainLength σ b hb = 3 :=
      hlength.trans hlen
    omega
  exact ⟨⟨first, hnotImage⟩, U.sameSuccessorOrbit_refl A⟩

omit [DecidableEq ι] in
/-- The length-three chain is retained by its short diagonal occurrence. -/
theorem lengthThreeArrowChainStartToSameOrbitRemainder_injective :
    Function.Injective
      (AR.lengthThreeArrowChainStartToSameOrbitRemainder σ) := by
  intro a₀ b₀ h
  let M := AR.arMeshRotationData σ
  let O := M.arrowOrbitData σ
  have hfirst := congrArg
    (fun p : AR.LongArrowChainFirstDiagonalFirstBoundarySameOrbitRemainder σ ↦
      p.1.1.1.1.1.1.1) h
  change M.arrowChainAt σ a₀.1.1 1 =
    M.arrowChainAt σ b₀.1.1 1 at hfirst
  have haLen : M.arrowChainLength σ a₀.1.1 a₀.1.2 = 3 := a₀.2
  have hbLen : M.arrowChainLength σ b₀.1.1 b₀.1.2 = 3 := b₀.2
  have haNotTarget : ¬ Injective (σ.obj a₀.1.1.1.1) :=
    M.arrowChainAt_not_injectiveSource_of_lt σ a₀.1.1 a₀.1.2
      (n := 0) (by omega)
  have hbNotTarget : ¬ Injective (σ.obj b₀.1.1.1.1) :=
    M.arrowChainAt_not_injectiveSource_of_lt σ b₀.1.1 b₀.1.2
      (n := 0) (by omega)
  have hstart : a₀.1.1 = b₀.1.1 := by
    apply O.successor_left_injective haNotTarget hbNotTarget
    simpa only [ARMeshRotationData.arrowChainAt,
      Function.iterate_one] using hfirst
  apply Subtype.ext
  apply Subtype.ext
  exact hstart

omit [DecidableEq ι] in
/-- Every same-orbit complement occurrence comes from its unique
length-three maximal arrow chain. -/
theorem lengthThreeArrowChainStartToSameOrbitRemainder_surjective :
    Function.Surjective
      (AR.lengthThreeArrowChainStartToSameOrbitRemainder σ) := by
  intro p
  let M := AR.arMeshRotationData σ
  let O := M.arrowOrbitData σ
  let A := p.1.1.1.1.1.1
  let aSub := O.tau ⟨A.1, A.2.1⟩
  let a := aSub.1
  have ha : Projective (σ.obj a.1.2) := p.1.1.1.2
  have hclassification := p.pair_eq_and_chainLength_eq_three σ AR
  let a₀ : AR.LengthThreeArrowChainStart σ :=
    ⟨⟨a, ha⟩, hclassification.2⟩
  refine ⟨a₀, ?_⟩
  have haNotTarget : ¬ Injective (σ.obj a.1.1) := aSub.2
  have hstart : O.successor a = A.1 := by
    rw [show O.successor a = (O.tau.symm ⟨a, haNotTarget⟩).1 by
      classical
      simp [OpConjecture.BoundaryTranslationChains.Data.successor,
        haNotTarget]]
    exact congrArg Subtype.val (O.tau.symm_apply_apply ⟨A.1, A.2.1⟩)
  have hchain : M.arrowChainAt σ a 1 = A.1 := by
    simpa only [ARMeshRotationData.arrowChainAt,
      Function.iterate_one] using hstart
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact hchain
  · apply Subtype.ext
    exact hchain.trans (congrArg Subtype.val hclassification.1)

omit [DecidableEq ι] in
/-- Exact classification of the formerly unnamed same-orbit complement:
it is the type of maximal labelled arrow chains of length three. -/
def lengthThreeArrowChainStartEquivSameOrbitRemainder :
    AR.LengthThreeArrowChainStart σ ≃
      AR.LongArrowChainFirstDiagonalFirstBoundarySameOrbitRemainder σ :=
  Equiv.ofBijective
    (AR.lengthThreeArrowChainStartToSameOrbitRemainder σ)
    ⟨AR.lengthThreeArrowChainStartToSameOrbitRemainder_injective σ,
      AR.lengthThreeArrowChainStartToSameOrbitRemainder_surjective σ⟩

/-- Exact image of the native diagonal-cut classification in the actual
`M6`/reverse-last signed-channel occurrence sum. -/
abbrev LongArrowChainFirstDiagonalChannelImage :=
  Set.range
    (AR.longArrowChainFirstDiagonalCutToHookM6OrReverseLast
      (K := K) σ)

noncomputable instance longArrowChainFirstDiagonalChannelImageFintype :
    Fintype (AR.LongArrowChainFirstDiagonalChannelImage (K := K) σ) :=
  Fintype.ofFinite _

include K AR in
/-- Native diagonal cuts are exactly equivalent to their labelled image in
the `M6`/reverse-last occurrence sum. -/
def longArrowChainFirstDiagonalCutEquivChannelImage :
    AR.LongArrowChainFirstDiagonalCut σ ≃
      AR.LongArrowChainFirstDiagonalChannelImage (K := K) σ :=
  Equiv.ofInjective
    (AR.longArrowChainFirstDiagonalCutToHookM6OrReverseLast
      (K := K) σ)
    (AR.longArrowChainFirstDiagonalCutToHookM6OrReverseLast_injective
      (K := K) σ)

/-- The part of the actual `M6`/reverse-last occurrence sum not represented
by a native diagonal cut. -/
abbrev LongArrowChainFirstDiagonalChannelComplement :=
  {p : HookM6Channel.InteriorChannel σ AR ⊕
      AR.BoundaryM6ReverseLastPair σ //
    p ∉ AR.LongArrowChainFirstDiagonalChannelImage (K := K) σ}

noncomputable instance longArrowChainFirstDiagonalChannelComplementFintype :
    Fintype
      (AR.LongArrowChainFirstDiagonalChannelComplement (K := K) σ) :=
  Fintype.ofFinite _

include K AR in
/-- The occurrence equivalence carries the native diagonal channel image
exactly to the same-chain image in the noninjective first source boundary. -/
theorem mem_longArrowChainFirstDiagonalChannelImage_iff_firstBoundaryImage
    (p : HookM6Channel.InteriorChannel σ AR ⊕
      AR.BoundaryM6ReverseLastPair σ) :
    p ∈ AR.LongArrowChainFirstDiagonalChannelImage (K := K) σ ↔
      AR.hookM6OrReverseLastEquivFirstSourceNoninjectiveTarget
          (K := K) σ p ∈
        AR.LongArrowChainFirstDiagonalFirstBoundaryImage σ := by
  let E := AR.hookM6OrReverseLastEquivFirstSourceNoninjectiveTarget
    (K := K) σ
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨q, ?_⟩
    rw [← hq]
    exact (AR.hookM6OrReverseLastEquiv_firstDiagonalCut
      (K := K) σ q).symm
  · rintro ⟨q, hq⟩
    refine ⟨q, ?_⟩
    apply E.injective
    calc
      E (AR.longArrowChainFirstDiagonalCutToHookM6OrReverseLast
          (K := K) σ q) =
          AR.longArrowChainFirstDiagonalCutToFirstSourceNoninjectiveTarget
            σ q :=
        AR.hookM6OrReverseLastEquiv_firstDiagonalCut
          (K := K) σ q
      _ = E p := hq

include K AR in
/-- Thus the native diagonal channel complement is exactly the
different-chain part of the noninjective first source boundary. -/
def longArrowChainFirstDiagonalChannelComplementEquivFirstBoundaryComplement :
    AR.LongArrowChainFirstDiagonalChannelComplement (K := K) σ ≃
      AR.LongArrowChainFirstDiagonalFirstBoundaryComplement σ := by
  let E := AR.hookM6OrReverseLastEquivFirstSourceNoninjectiveTarget
    (K := K) σ
  apply E.subtypeEquiv
  intro p
  exact not_congr
    (AR.mem_longArrowChainFirstDiagonalChannelImage_iff_firstBoundaryImage
      (K := K) σ p)

include K AR in
/-- Cardinal form of the exact same-chain/different-chain complement
identification. -/
theorem longArrowChainFirstDiagonalChannelComplement_card_eq_firstBoundary :
    Fintype.card
        (AR.LongArrowChainFirstDiagonalChannelComplement (K := K) σ) =
      Fintype.card
        (AR.LongArrowChainFirstDiagonalFirstBoundaryComplement σ) :=
  Fintype.card_congr
    (AR.longArrowChainFirstDiagonalChannelComplementEquivFirstBoundaryComplement
      (K := K) σ)

include K AR in
/-- The ambient signed-channel occurrence sum splits exactly into the
diagonal image and its occurrence complement. -/
def longArrowChainFirstDiagonalChannelEquivImageSumComplement :
    HookM6Channel.InteriorChannel σ AR ⊕
        AR.BoundaryM6ReverseLastPair σ ≃
      AR.LongArrowChainFirstDiagonalChannelImage (K := K) σ ⊕
        AR.LongArrowChainFirstDiagonalChannelComplement (K := K) σ := by
  classical
  exact (Equiv.sumCompl
    (fun p : HookM6Channel.InteriorChannel σ AR ⊕
      AR.BoundaryM6ReverseLastPair σ ↦
        p ∈ AR.LongArrowChainFirstDiagonalChannelImage (K := K) σ)).symm

end OpConjecture.IndecomposableSkeleton.FiniteARTranslationData
