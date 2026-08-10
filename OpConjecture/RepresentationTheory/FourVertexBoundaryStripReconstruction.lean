import OpConjecture.RepresentationTheory.FourVertexShortStripReversal

/-!
# Reconstructing strips from shifted source-boundary arrows

The regular boundary classification needs to recover the admissible hook
whose first or second displayed arrow occurs in the first two layers of a
trimmed mesh-rotation chain.  This file gives that reconstruction directly
from finite AR-translation data, without choosing orbit coordinates.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace OpConjecture.IndecomposableSkeleton

universe u v

variable {k R : Type u} [Field k]
  [Ring R] [Algebra k R] [FiniteDimensional k R]
  [IsNoetherianRing R]
  {iota : Type v} [Fintype iota] [DecidableEq iota]
  (sigma : IndecomposableSkeleton.{u, v, u} R iota)

namespace FiniteARTranslationData

variable (AR : sigma.FiniteARTranslationData)

omit [Fintype iota] [DecidableEq iota] in
include k in
/-- An interior irreducible arrow with projective source canonically
extends by one mesh to an admissible strip triple. -/
def stripTripleOfProjectiveArrow
    (q : sigma.IrreduciblePair)
    (hsourceP : Projective (sigma.obj q.1.1))
    (hsourceNI : ¬ Injective (sigma.obj q.1.1))
    (htargetNP : ¬ Projective (sigma.obj q.1.2)) :
    AR.StripAdmissibleTriple sigma := by
  let a := q.1.1
  let u := q.1.2
  let bLabel : sigma.NonprojectiveLabel :=
    (AR.arTranslationEquiv sigma).symm ⟨a, hsourceNI⟩
  let b := bLabel.1
  have hbNP : ¬ Projective (sigma.obj b) := bLabel.2
  have htauB : (AR.arTranslation sigma bLabel).1 = a := by
    exact congrArg Subtype.val
      ((AR.arTranslationEquiv sigma).apply_symm_apply
        ⟨a, hsourceNI⟩)
  have huB : HasIrreducibleMorphism (sigma.obj u) (sigma.obj b) := by
    apply (AR.arTranslation_incidence sigma bLabel u).2
    simpa only [htauB] using q.2
  have hBnotU :
      ¬ HasIrreducibleMorphism (sigma.obj b) (sigma.obj u) := by
    intro hBu
    rcases AR.exists_arTranslation_eq_self_of_two_cycle
        (K := k) sigma b u hBu huB with hbFixed | huFixed
    · obtain ⟨hbNP', htauB'⟩ := hbFixed
      have hab : a = b := by
        calc
          a = (AR.arTranslation sigma bLabel).1 := htauB.symm
          _ = (AR.arTranslation sigma ⟨b, hbNP'⟩).1 := by congr
          _ = b := htauB'
      exact hbNP (hab.symm ▸ hsourceP)
    · obtain ⟨huNP, htauU⟩ := huFixed
      have huA : HasIrreducibleMorphism (sigma.obj u) (sigma.obj a) := by
        have h := (AR.arTranslation_incidence sigma
          ⟨u, huNP⟩ a).1 q.2
        simpa only [htauU] using h
      have haI := AR.injective_of_projective_two_cycle
        (K := k) sigma a u hsourceP q.2 huA
      exact hsourceNI haI
  have hAnotB :
      ¬ HasIrreducibleMorphism (sigma.obj a) (sigma.obj b) :=
    AR.no_irreducible_transitiveTriangle (K := k) sigma q.2 huB
  exact
    { a := a
      u := u
      b := b
      a_ne_u := by
        change q.1.1 ≠ q.1.2
        intro h
        exact sigma.hasNoIrreducibleEndomorphism_obj q.1.2
          (h ▸ q.2)
      a_ne_b := by
        intro h
        exact hbNP (h.symm ▸ hsourceP)
      u_ne_b := by
        intro h
        exact sigma.hasNoIrreducibleEndomorphism_obj u (by
          simpa only [h] using huB)
      u_nonprojective := htargetNP
      b_nonprojective := hbNP
      a_to_u := q.2
      u_to_b := huB
      b_not_to_u := hBnotU
      a_not_to_b := hAnotB
      tau_b := htauB }

omit [DecidableEq iota] in
include k in
@[simp]
theorem stripTripleOfProjectiveArrow_firstArrow
    (q : sigma.IrreduciblePair)
    (hsourceP : Projective (sigma.obj q.1.1))
    (hsourceNI : ¬ Injective (sigma.obj q.1.1))
    (htargetNP : ¬ Projective (sigma.obj q.1.2)) :
    (stripTripleOfProjectiveArrow (k := k) sigma AR q
      hsourceP hsourceNI htargetNP).firstArrow sigma AR = q := by
  apply Subtype.ext
  rfl

/-- A projective strip together with the assertion that a selected
interior occurrence is its first or second displayed arrow. -/
structure SourceBoundaryHook
    (H : (AR.arMeshRotationData sigma).InteriorArrow sigma) where
  triple : AR.StripAdmissibleTriple sigma
  a_projective : Projective (sigma.obj triple.a)
  hookArrow_eq :
    H.1 = triple.firstArrow sigma AR ∨
      H.1 = triple.secondArrow sigma AR

omit [DecidableEq iota] in
include AR in
/-- Every occurrence in the first two layers of a trimmed arrow chain is
canonically the first or second displayed arrow of a projectively based
admissible strip. -/
def sourceBoundaryHook
    (H : (AR.arMeshRotationData sigma).InteriorArrow sigma)
    (hH : ((AR.arMeshRotationData sigma).arrowInteriorOrbitData sigma).TwoSource
      H) : AR.SourceBoundaryHook sigma H := by
  classical
  let M := AR.arMeshRotationData sigma
  let O := M.arrowOrbitData sigma
  let U := M.arrowInteriorOrbitData sigma
  by_cases hfirst : O.InteriorSource H
  · have hsourceP : Projective (sigma.obj H.1.1.1) :=
      (M.arrowInterior_source_iff sigma H).1 hfirst
    let T := stripTripleOfProjectiveArrow (k := k) sigma AR H.1
      hsourceP H.2.2 H.2.1
    exact
      { triple := T
        a_projective := hsourceP
        hookArrow_eq := Or.inl (by
          exact (stripTripleOfProjectiveArrow_firstArrow
            (k := k) sigma AR H.1 hsourceP H.2.2 H.2.1).symm) }
  · have hsecond : O.InteriorSource
        (U.tau ⟨H, hfirst⟩).1 := by
      rcases hH with h | h
      · exact (hfirst h).elim
      · exact h hfirst
    let Qsub := U.tau ⟨H, hfirst⟩
    let Q : M.InteriorArrow sigma := Qsub.1
    have hsourceP : Projective (sigma.obj Q.1.1.1) :=
      (M.arrowInterior_source_iff sigma Q).1 hsecond
    let T := stripTripleOfProjectiveArrow (k := k) sigma AR Q.1
      hsourceP Q.2.2 Q.2.1
    have hUback : U.successor Q = H := by
      have hback := U.tau.symm_apply_apply ⟨H, hfirst⟩
      change (if htarget : O.InteriorTarget Q then Q
        else (U.tau.symm ⟨Q, htarget⟩).1) = H
      rw [dif_neg Qsub.2]
      exact congrArg Subtype.val hback
    have hOriginalSucc :
        (M.arrowOrbitData sigma).successor Q.1 = H.1 := by
      have hval := (M.arrowOrbitData sigma).interior_successor_val
        Q Qsub.2
      exact hval.symm.trans (congrArg Subtype.val hUback)
    have hsecondArrow : T.secondArrow sigma AR = H.1 := by
      calc
        T.secondArrow sigma AR =
            (M.arrowOrbitData sigma).successor
              (T.firstArrow sigma AR) :=
          (T.firstArrow_successor sigma AR).symm
        _ = (M.arrowOrbitData sigma).successor Q.1 := by
          rw [stripTripleOfProjectiveArrow_firstArrow]
        _ = H.1 := hOriginalSucc
    exact
      { triple := T
        a_projective := hsourceP
        hookArrow_eq := Or.inr hsecondArrow.symm }

/-- First-layer arrows of the trimmed source boundary. -/
abbrev FirstInteriorSourceArrow :=
  {H : (AR.arMeshRotationData sigma).InteriorArrow sigma //
    (AR.arMeshRotationData sigma).arrowOrbitData sigma |>.InteriorSource H}

/-- Second-layer arrows which are not already in the first layer. -/
abbrev SecondOnlyInteriorSourceArrow :=
  {H : (AR.arMeshRotationData sigma).InteriorArrow sigma //
    ¬ ((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorSource H ∧
      ((AR.arMeshRotationData sigma).arrowInteriorOrbitData sigma).TwoSource H}

omit [DecidableEq iota] in
include k AR in
/-- First-layer trimmed arrows are exactly projectively based admissible
strip triples, reconstructed from the arrow itself. -/
def firstInteriorSourceArrowEquivProjectiveStrip :
    AR.FirstInteriorSourceArrow sigma ≃
      {T : AR.StripAdmissibleTriple sigma //
        Projective (sigma.obj T.a)} where
  toFun H := by
    have hP : Projective (sigma.obj H.1.1.1.1) :=
      ((AR.arMeshRotationData sigma).arrowInterior_source_iff
        sigma H.1).1 H.2
    exact ⟨stripTripleOfProjectiveArrow (k := k) sigma AR H.1.1
      hP H.1.2.2 H.1.2.1, hP⟩
  invFun T := by
    let H : (AR.arMeshRotationData sigma).InteriorArrow sigma :=
      ⟨T.1.firstArrow sigma AR, by
        exact ⟨by
          simpa [StripAdmissibleTriple.firstArrow] using
            T.1.u_nonprojective,
          by simpa [StripAdmissibleTriple.firstArrow] using
            T.1.a_noninjective sigma AR⟩⟩
    exact ⟨H, ((AR.arMeshRotationData sigma).arrowInterior_source_iff
      sigma H).2 (by
        simpa [H, StripAdmissibleTriple.firstArrow] using T.2)⟩
  left_inv H := by
    apply Subtype.ext
    apply Subtype.ext
    exact stripTripleOfProjectiveArrow_firstArrow
      (k := k) sigma AR H.1.1
        (((AR.arMeshRotationData sigma).arrowInterior_source_iff
          sigma H.1).1 H.2) H.1.2.2 H.1.2.1
  right_inv T := by
    apply Subtype.ext
    apply StripAdmissibleTriple.firstArrow_injective sigma AR
    exact stripTripleOfProjectiveArrow_firstArrow
      (k := k) sigma AR (T.1.firstArrow sigma AR) T.2
        (T.1.a_noninjective sigma AR) T.1.u_nonprojective

omit [DecidableEq iota] in
include k AR in
/-- A genuine second-layer trimmed arrow is exactly the second displayed
arrow of a projective-end diagonal candidate. -/
def secondOnlyInteriorSourceArrowEquivDiagonalCandidate :
    AR.SecondOnlyInteriorSourceArrow sigma ≃
      AR.HookDiagonalCandidate sigma where
  toFun H := by
    let S := AR.sourceBoundaryHook (k := k) sigma H.1 H.2.2
    have hsecond : H.1.1 = S.triple.secondArrow sigma AR := by
      rcases S.hookArrow_eq with hfirst | hsecond
      · exfalso
        apply H.2.1
        apply ((AR.arMeshRotationData sigma).arrowInterior_source_iff
          sigma H.1).2
        simpa [StripAdmissibleTriple.firstArrow, hfirst] using
          S.a_projective
      · exact hsecond
    have huNI : ¬ Injective (sigma.obj S.triple.u) := by
      have h := H.1.2.2
      rw [hsecond] at h
      simpa [StripAdmissibleTriple.secondArrow] using h
    exact ⟨S.triple, S.a_projective, huNI⟩
  invFun C := by
    let M := AR.arMeshRotationData sigma
    let O := M.arrowOrbitData sigma
    let U := M.arrowInteriorOrbitData sigma
    let H : M.InteriorArrow sigma :=
      ⟨C.1.secondArrow sigma AR, by
        exact ⟨by
          simpa [StripAdmissibleTriple.secondArrow] using
            C.1.b_nonprojective,
          by simpa [StripAdmissibleTriple.secondArrow] using C.2.2⟩⟩
    have hnot : ¬ O.InteriorSource H := by
      intro h
      have hP := (M.arrowInterior_source_iff sigma H).1 h
      exact C.1.u_nonprojective (by
        simpa [H, StripAdmissibleTriple.secondArrow] using hP)
    refine ⟨H, hnot, Or.inr ?_⟩
    intro _hnot
    apply (M.arrowInterior_source_iff sigma (U.tau ⟨H, hnot⟩).1).2
    have hval : (U.tau ⟨H, hnot⟩).1.1 =
        C.1.firstArrow sigma AR := by
      have hpred := congrArg Subtype.val
        (C.1.secondArrow_predecessor sigma AR)
      simpa [U, M, O, H, ARMeshRotationData.arrowInteriorOrbitData,
        OpConjecture.BoundaryTranslationChains.Data.interior] using hpred
    rw [hval]
    simpa [StripAdmissibleTriple.firstArrow] using C.2.1
  left_inv H := by
    apply Subtype.ext
    apply Subtype.ext
    let S := AR.sourceBoundaryHook (k := k) sigma H.1 H.2.2
    have hsecond : H.1.1 = S.triple.secondArrow sigma AR := by
      rcases S.hookArrow_eq with hfirst | hsecond
      · exfalso
        apply H.2.1
        apply ((AR.arMeshRotationData sigma).arrowInterior_source_iff
          sigma H.1).2
        simpa [StripAdmissibleTriple.firstArrow, hfirst] using
          S.a_projective
      · exact hsecond
    exact hsecond.symm
  right_inv C := by
    apply Subtype.ext
    let M := AR.arMeshRotationData sigma
    let O := M.arrowOrbitData sigma
    let U := M.arrowInteriorOrbitData sigma
    let H : M.InteriorArrow sigma :=
      ⟨C.1.secondArrow sigma AR, by
        exact ⟨by
          simpa [StripAdmissibleTriple.secondArrow] using
            C.1.b_nonprojective,
          by simpa [StripAdmissibleTriple.secondArrow] using C.2.2⟩⟩
    have hnot : ¬ O.InteriorSource H := by
      intro h
      have hP := (M.arrowInterior_source_iff sigma H).1 h
      exact C.1.u_nonprojective (by
        simpa [H, StripAdmissibleTriple.secondArrow] using hP)
    have htwo : U.TwoSource H := by
      right
      intro _
      apply (M.arrowInterior_source_iff sigma (U.tau ⟨H, hnot⟩).1).2
      have hval : (U.tau ⟨H, hnot⟩).1.1 =
          C.1.firstArrow sigma AR := by
        have hpred := congrArg Subtype.val
          (C.1.secondArrow_predecessor sigma AR)
        simpa [U, M, O, H, ARMeshRotationData.arrowInteriorOrbitData,
          OpConjecture.BoundaryTranslationChains.Data.interior] using hpred
      rw [hval]
      simpa [StripAdmissibleTriple.firstArrow] using C.2.1
    let S := AR.sourceBoundaryHook (k := k) sigma H htwo
    apply StripAdmissibleTriple.secondArrow_injective sigma AR
    have hsecond : H.1 = S.triple.secondArrow sigma AR := by
      rcases S.hookArrow_eq with hfirst | hsecond
      · exfalso
        apply hnot
        apply (M.arrowInterior_source_iff sigma H).2
        rw [congrArg (fun q : sigma.IrreduciblePair ↦ q.1.1) hfirst]
        simpa [StripAdmissibleTriple.firstArrow] using S.a_projective
      · exact hsecond
    exact hsecond.symm

/-- All first-two-layer trimmed source arrows. -/
abbrev TwoSourceInteriorArrow :=
  {H : (AR.arMeshRotationData sigma).InteriorArrow sigma //
    ((AR.arMeshRotationData sigma).arrowInteriorOrbitData sigma).TwoSource H}

/-- The two shifted source layers split into the literal first layer and
the genuine second layer. -/
def twoSourceInteriorArrowEquivFirstSumSecondOnly :
    AR.TwoSourceInteriorArrow sigma ≃
      AR.FirstInteriorSourceArrow sigma ⊕
        AR.SecondOnlyInteriorSourceArrow sigma where
  toFun H := by
    classical
    by_cases hfirst :
        ((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorSource
          H.1
    · exact Sum.inl ⟨H.1, hfirst⟩
    · exact Sum.inr ⟨H.1, hfirst, H.2⟩
  invFun H := by
    rcases H with H | H
    · exact ⟨H.1, Or.inl H.2⟩
    · exact ⟨H.1, H.2.2⟩
  left_inv H := by
    classical
    by_cases hfirst :
        ((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorSource
          H.1
    · simp [hfirst]
    · simp [hfirst]
  right_inv H := by
    classical
    rcases H with H | H
    · simp [H.2]
    · simp [H.2.1]

/-- Diagonal common-target pairs on the shifted source boundary. -/
abbrev InteriorSourceBoundaryDiagonalCommonTargetPair :=
  {p : AR.InteriorSourceBoundaryCommonTargetArrowPair sigma //
    p.1.1.1 = p.1.1.2}

/-- Forgetting the repeated coordinate identifies diagonal boundary pairs
with first-two-layer trimmed arrows. -/
def interiorSourceBoundaryDiagonalCommonTargetEquivTwoSourceArrow :
    AR.InteriorSourceBoundaryDiagonalCommonTargetPair sigma ≃
      AR.TwoSourceInteriorArrow sigma where
  toFun p := ⟨p.1.1.1.1, by
    rcases p.1.2 with h | h
    · exact h
    · rw [p.2]
      exact h⟩
  invFun H := ⟨⟨⟨(H.1, H.1), rfl⟩, Or.inl H.2⟩, rfl⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact p.2
  right_inv H := by
    apply Subtype.ext
    rfl

noncomputable instance twoSourceInteriorArrowFintype :
    Fintype (AR.TwoSourceInteriorArrow sigma) := Fintype.ofFinite _

noncomputable instance firstInteriorSourceArrowFintype :
    Fintype (AR.FirstInteriorSourceArrow sigma) := Fintype.ofFinite _

noncomputable instance secondOnlyInteriorSourceArrowFintype :
    Fintype (AR.SecondOnlyInteriorSourceArrow sigma) := Fintype.ofFinite _

noncomputable instance
    interiorSourceBoundaryDiagonalCommonTargetPairFintype :
    Fintype (AR.InteriorSourceBoundaryDiagonalCommonTargetPair sigma) :=
  Fintype.ofFinite _

omit [DecidableEq iota] in
include k AR in
/-- The diagonal shifted-source boundary consists of one copy of all
projective strips and one further copy of the continuing candidates.
Equivalently its cardinality is two candidate copies plus the short-strip
endpoint correction. -/
theorem interiorSourceBoundaryDiagonalCommonTarget_card_eq :
    Fintype.card
        (AR.InteriorSourceBoundaryDiagonalCommonTargetPair sigma) =
      2 * Fintype.card (AR.HookDiagonalCandidate sigma) +
        Fintype.card (AR.HookShortStrip sigma) := by
  have hsplit :
      Fintype.card (AR.TwoSourceInteriorArrow sigma) =
        Fintype.card (AR.FirstInteriorSourceArrow sigma) +
          Fintype.card (AR.SecondOnlyInteriorSourceArrow sigma) := by
    rw [Fintype.card_congr
      (AR.twoSourceInteriorArrowEquivFirstSumSecondOnly sigma)]
    exact Fintype.card_sum
  have hfirst :
      Fintype.card (AR.FirstInteriorSourceArrow sigma) =
        Fintype.card
          {T : AR.StripAdmissibleTriple sigma //
            Projective (sigma.obj T.a)} :=
    Fintype.card_congr
      (AR.firstInteriorSourceArrowEquivProjectiveStrip (k := k) sigma)
  have hsecond :
      Fintype.card (AR.SecondOnlyInteriorSourceArrow sigma) =
        Fintype.card (AR.HookDiagonalCandidate sigma) :=
    Fintype.card_congr
      (AR.secondOnlyInteriorSourceArrowEquivDiagonalCandidate
        (k := k) sigma)
  have hprojective :
      Fintype.card
          {T : AR.StripAdmissibleTriple sigma //
            Projective (sigma.obj T.a)} =
        Fintype.card (AR.HookDiagonalCandidate sigma) +
          Fintype.card (AR.HookShortStrip sigma) := by
    rw [Fintype.card_congr
      (projectiveStripEquivDiagonalCandidateSumShort sigma AR)]
    exact Fintype.card_sum
  rw [Fintype.card_congr
    (AR.interiorSourceBoundaryDiagonalCommonTargetEquivTwoSourceArrow
      sigma)]
  omega

/-- A trimmed common-target pair whose second occurrence lies on the
shifted source boundary and whose two labelled occurrences are distinct. -/
abbrev SecondSourceBoundaryOffDiagonalPair :=
  {p : AR.InteriorCommonTargetArrowPair sigma //
    ((AR.arMeshRotationData sigma).arrowInteriorOrbitData sigma).TwoSource
        p.1.2 ∧
      p.1.1 ≠ p.1.2}

/-- The reconstructed preliminary term together with the fact that its
canonical labelled occurrence is the original boundary pair. -/
structure PreliminarySecondBoundaryReconstruction
    (p : AR.SecondSourceBoundaryOffDiagonalPair sigma) where
  term : HookM5Preliminary.InteriorChannel sigma AR
  occurrence_eq :
    HookM5Preliminary.interiorCommonTargetPair sigma AR term = p.1

omit [DecidableEq iota] in
include k AR in
/-- Rotate the first occurrence of a non-diagonal common-target pair one
step forward.  Reconstructing the projective hook from the second
occurrence then produces the unique preliminary `M5` term represented by
the pair. -/
def preliminaryInteriorOfSecondSourceBoundaryPair
    (p : AR.SecondSourceBoundaryOffDiagonalPair sigma) :
    AR.PreliminarySecondBoundaryReconstruction sigma p := by
  classical
  let M := AR.arMeshRotationData sigma
  let O := M.arrowOrbitData sigma
  let C : M.InteriorArrow sigma := p.1.1.1
  let H : M.InteriorArrow sigma := p.1.1.2
  let S := AR.sourceBoundaryHook (k := k) sigma H p.2.1
  let T := S.triple
  let qsub := O.tau.symm ⟨C.1, C.2.2⟩
  let q : sigma.IrreduciblePair := qsub.1
  have hqSource : q.1.1 = C.1.1.2 := by
    have hval := M.arrowOrbitData_tau_symm_val sigma ⟨C.1, C.2.2⟩
    exact congrArg Prod.fst hval
  have hqSourceH : q.1.1 = H.1.1.2 :=
    hqSource.trans p.1.2
  have hzNP : ¬ Projective (sigma.obj q.1.2) := qsub.2
  by_cases hfirst : H.1 = T.firstArrow sigma AR
  · have hqSourceU : q.1.1 = T.u := by
      exact hqSourceH.trans (congrArg
        (fun r : sigma.IrreduciblePair ↦ r.1.2) hfirst)
    have hqArrow : HasIrreducibleMorphism
        (sigma.obj T.u) (sigma.obj q.1.2) := by
      simpa only [hqSourceU] using q.2
    have hzNot : q.1.2 ∉ T.support := by
      simp only [StripAdmissibleTriple.support, Finset.mem_insert,
        Finset.mem_singleton, not_or]
      refine ⟨?_, ?_, ?_⟩
      · intro hza
        exact hzNP (hza ▸ S.a_projective)
      · intro hzu
        exact sigma.hasNoIrreducibleEndomorphism_obj T.u (by
          simpa only [hqSourceU, hzu] using q.2)
      · intro hzb
        have hqSecond : q = T.secondArrow sigma AR := by
          apply Subtype.ext
          apply Prod.ext
          · exact hqSourceU
          · exact hzb
        have hsub : qsub =
            ⟨T.secondArrow sigma AR, T.b_nonprojective⟩ := by
          apply Subtype.ext
          exact hqSecond
        have hCfirst : C.1 = T.firstArrow sigma AR := by
          have hleft := congrArg Subtype.val
            (O.tau.apply_symm_apply ⟨C.1, C.2.2⟩)
          have hright := congrArg Subtype.val
            (T.secondArrow_predecessor sigma AR)
          exact hleft.symm.trans ((congrArg
            (fun s : {r : sigma.IrreduciblePair //
                ¬ Projective (sigma.obj r.1.2)} ↦ (O.tau s).1)
              hsub).trans hright)
        apply p.2.2
        apply Subtype.ext
        exact hCfirst.trans hfirst.symm
    let P : AR.HookM5Preliminary sigma :=
      { triple := T
        a_projective := S.a_projective
        z := q.1.2
        z_not_mem := hzNot
        z_nonprojective := hzNP
        outgoing_to_z := Or.inl hqArrow }
    have hassociated : P.associatedArrow sigma AR = q := by
      apply Subtype.ext
      apply Prod.ext
      · simpa only [HookM5Preliminary.associatedArrow, P, hqArrow,
          dite_true] using hqSourceU.symm
      · exact P.associatedArrow_target sigma AR
    have hrotated : P.rotatedAssociatedArrow sigma AR = C.1 := by
      change (O.tau ⟨P.associatedArrow sigma AR, ?_⟩).1 = C.1
      have harg : (⟨P.associatedArrow sigma AR, by
          simpa only [P.associatedArrow_target sigma AR] using
            P.z_nonprojective⟩ : {r : sigma.IrreduciblePair //
              ¬ Projective (sigma.obj r.1.2)}) = qsub := by
        apply Subtype.ext
        exact hassociated
      rw [harg]
      exact congrArg Subtype.val (O.tau.apply_symm_apply ⟨C.1, C.2.2⟩)
    have hhook : P.hookArrow sigma AR = H.1 := by
      simpa [HookM5Preliminary.hookArrow, P, hqArrow] using hfirst.symm
    let X : HookM5Preliminary.InteriorChannel sigma AR := ⟨P, by
      constructor
      · simpa only [hrotated, IsInteriorArrow] using C.2
      · simpa only [hhook, IsInteriorArrow] using H.2⟩
    refine ⟨X, ?_⟩
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext
    · exact hrotated
    · exact hhook
  · have hsecond : H.1 = T.secondArrow sigma AR :=
      S.hookArrow_eq.resolve_left hfirst
    have hqSourceB : q.1.1 = T.b := by
      exact hqSourceH.trans (congrArg
        (fun r : sigma.IrreduciblePair ↦ r.1.2) hsecond)
    have hqArrow : HasIrreducibleMorphism
        (sigma.obj T.b) (sigma.obj q.1.2) := by
      simpa only [hqSourceB] using q.2
    have huNot : ¬ HasIrreducibleMorphism
        (sigma.obj T.u) (sigma.obj q.1.2) :=
      AR.no_irreducible_transitiveTriangle
        (K := k) sigma T.u_to_b hqArrow
    have hzNot : q.1.2 ∉ T.support := by
      simp only [StripAdmissibleTriple.support, Finset.mem_insert,
        Finset.mem_singleton, not_or]
      refine ⟨?_, ?_, ?_⟩
      · intro hza
        exact hzNP (hza ▸ S.a_projective)
      · intro hzu
        exact T.b_not_to_u (by simpa only [hqSourceB, hzu] using q.2)
      · intro hzb
        exact sigma.hasNoIrreducibleEndomorphism_obj T.b (by
          simpa only [hqSourceB, hzb] using q.2)
    let P : AR.HookM5Preliminary sigma :=
      { triple := T
        a_projective := S.a_projective
        z := q.1.2
        z_not_mem := hzNot
        z_nonprojective := hzNP
        outgoing_to_z := Or.inr hqArrow }
    have hassociated : P.associatedArrow sigma AR = q := by
      apply Subtype.ext
      apply Prod.ext
      · simpa [HookM5Preliminary.associatedArrow, P, huNot] using
          hqSourceB.symm
      · exact P.associatedArrow_target sigma AR
    have hrotated : P.rotatedAssociatedArrow sigma AR = C.1 := by
      change (O.tau ⟨P.associatedArrow sigma AR, ?_⟩).1 = C.1
      have harg : (⟨P.associatedArrow sigma AR, by
          simpa only [P.associatedArrow_target sigma AR] using
            P.z_nonprojective⟩ : {r : sigma.IrreduciblePair //
              ¬ Projective (sigma.obj r.1.2)}) = qsub := by
        apply Subtype.ext
        exact hassociated
      rw [harg]
      exact congrArg Subtype.val (O.tau.apply_symm_apply ⟨C.1, C.2.2⟩)
    have hhook : P.hookArrow sigma AR = H.1 := by
      simpa [HookM5Preliminary.hookArrow, P, huNot] using hsecond.symm
    let X : HookM5Preliminary.InteriorChannel sigma AR := ⟨P, by
      constructor
      · simpa only [hrotated, IsInteriorArrow] using C.2
      · simpa only [hhook, IsInteriorArrow] using H.2⟩
    refine ⟨X, ?_⟩
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext
    · exact hrotated
    · exact hhook

namespace HookM5Preliminary

/-- The hook occurrence (the second coordinate of the preliminary labelled
pair) always lies in the first two layers of the trimmed source boundary. -/
theorem interiorCommonTargetPair_second_twoSource
    (X : HookM5Preliminary.InteriorChannel sigma AR) :
    ((AR.arMeshRotationData sigma).arrowInteriorOrbitData sigma).TwoSource
      (HookM5Preliminary.interiorCommonTargetPair sigma AR X).1.2 := by
  classical
  let M := AR.arMeshRotationData sigma
  let O := M.arrowOrbitData sigma
  let U := M.arrowInteriorOrbitData sigma
  let H := toInteriorArrow sigma AR (X.1.hookArrow sigma AR) X.2.2
  change U.TwoSource H
  by_cases h : HasIrreducibleMorphism
      (sigma.obj X.1.triple.u) (sigma.obj X.1.z)
  · left
    apply (M.arrowInterior_source_iff sigma H).2
    simpa [H, toInteriorArrow, HookM5Preliminary.hookArrow, h,
      StripAdmissibleTriple.firstArrow] using X.1.a_projective
  · right
    intro hnot
    apply (M.arrowInterior_source_iff sigma (U.tau ⟨H, hnot⟩).1).2
    have hval : (U.tau ⟨H, hnot⟩).1.1 =
        X.1.triple.firstArrow sigma AR := by
      have hpred := congrArg Subtype.val
        (X.1.triple.secondArrow_predecessor sigma AR)
      simpa [U, M, O, H, ARMeshRotationData.arrowInteriorOrbitData,
        OpConjecture.BoundaryTranslationChains.Data.interior,
        toInteriorArrow, HookM5Preliminary.hookArrow, h] using hpred
    rw [hval]
    simpa [StripAdmissibleTriple.firstArrow] using X.1.a_projective

/-- Interior preliminary terms whose two assigned labelled occurrences are
not the same occurrence. -/
abbrev OffDiagonalInteriorChannel :=
  {X : HookM5Preliminary.InteriorChannel sigma AR //
    (HookM5Preliminary.interiorCommonTargetPair sigma AR X).1.1 ≠
      (HookM5Preliminary.interiorCommonTargetPair sigma AR X).1.2}

/-- Non-diagonal preliminary occurrences are exactly the non-diagonal
common-target pairs with the second occurrence on the shifted source
boundary. -/
def offDiagonalInteriorChannelEquivSecondSourceBoundaryPair :
    HookM5Preliminary.OffDiagonalInteriorChannel sigma AR ≃
      AR.SecondSourceBoundaryOffDiagonalPair sigma where
  toFun X := ⟨HookM5Preliminary.interiorCommonTargetPair sigma AR X.1,
    HookM5Preliminary.interiorCommonTargetPair_second_twoSource
      sigma AR X.1, X.2⟩
  invFun p := ⟨
    (AR.preliminaryInteriorOfSecondSourceBoundaryPair
      (k := k) sigma p).term,
    by
      intro h
      apply p.2.2
      have hp := (AR.preliminaryInteriorOfSecondSourceBoundaryPair
        (k := k) sigma p).occurrence_eq
      have hfirst := congrArg
        (fun q : AR.InteriorCommonTargetArrowPair sigma ↦ q.1.1) hp
      have hsecond := congrArg
        (fun q : AR.InteriorCommonTargetArrowPair sigma ↦ q.1.2) hp
      exact hfirst.symm.trans (h.trans hsecond)⟩
  left_inv X := by
    apply Subtype.ext
    apply HookM5Preliminary.interiorCommonTargetPair_injective sigma AR
    exact (AR.preliminaryInteriorOfSecondSourceBoundaryPair
      (k := k) sigma _).occurrence_eq
  right_inv p := by
    apply Subtype.ext
    exact (AR.preliminaryInteriorOfSecondSourceBoundaryPair
      (k := k) sigma p).occurrence_eq

/-- Interior preliminary terms whose two assigned labelled occurrences
coincide. -/
abbrev DiagonalInteriorChannel :=
  {X : HookM5Preliminary.InteriorChannel sigma AR //
    (HookM5Preliminary.interiorCommonTargetPair sigma AR X).1.1 =
      (HookM5Preliminary.interiorCommonTargetPair sigma AR X).1.2}

omit [DecidableEq iota] in
include k AR in
/-- A projective-end diagonal candidate gives the diagonal preliminary
occurrence obtained from its canonical next arrow `b → z`. -/
def diagonalInteriorChannelOfCandidate
    (C : AR.HookDiagonalCandidate sigma) :
    HookM5Preliminary.DiagonalInteriorChannel sigma AR := by
  classical
  let M := AR.arMeshRotationData sigma
  let O := M.arrowOrbitData sigma
  let P := C.preliminary sigma AR
  have hassociated : P.associatedArrow sigma AR =
      ⟨(C.1.b, C.z sigma AR), C.b_to_z sigma AR⟩ := by
    apply Subtype.ext
    simp [P, HookDiagonalCandidate.preliminary,
      HookM5Preliminary.associatedArrow, C.u_not_to_z sigma AR]
  have hrotated : P.rotatedAssociatedArrow sigma AR =
      C.1.secondArrow sigma AR := by
    let q : {r : sigma.IrreduciblePair //
        ¬ Projective (sigma.obj r.1.2)} :=
      ⟨P.associatedArrow sigma AR, by
        simpa only [P.associatedArrow_target sigma AR] using
          P.z_nonprojective⟩
    change (O.tau q).1 = C.1.secondArrow sigma AR
    have hval := M.arrowOrbitData_tau_val sigma q
    apply Subtype.ext
    apply Prod.ext
    · calc
        (O.tau q).1.1.1 =
            (M.tau ⟨q.1.1.2, q.2⟩).1 := congrArg Prod.fst hval
        _ = (M.tau
            ⟨C.z sigma AR, C.z_nonprojective sigma AR⟩).1 := by
          congr 2
          apply Subtype.ext
          exact P.associatedArrow_target sigma AR
        _ = C.1.u := C.tau_z sigma AR
    · have htarget := congrArg Prod.snd hval
      exact htarget.trans (congrArg
        (fun r : sigma.IrreduciblePair ↦ r.1.1) hassociated)
  have hhook : P.hookArrow sigma AR = C.1.secondArrow sigma AR := by
    simp [P, HookDiagonalCandidate.preliminary,
      HookM5Preliminary.hookArrow, C.u_not_to_z sigma AR]
  have hInterior : IsInteriorArrow sigma (C.1.secondArrow sigma AR) := by
    exact ⟨by
      simpa [StripAdmissibleTriple.secondArrow] using C.1.b_nonprojective,
      by simpa [StripAdmissibleTriple.secondArrow] using C.2.2⟩
  let X : HookM5Preliminary.InteriorChannel sigma AR :=
    ⟨P, by
      constructor
      · simpa only [hrotated] using hInterior
      · simpa only [hhook] using hInterior⟩
  refine ⟨X, ?_⟩
  apply Subtype.ext
  exact hrotated.trans hhook.symm

omit [DecidableEq iota] in
include AR in
/-- A diagonal interior preliminary occurrence recovers its unique
projective-end candidate. -/
def diagonalCandidateOfInteriorChannel
    (X : HookM5Preliminary.DiagonalInteriorChannel sigma AR) :
    AR.HookDiagonalCandidate sigma := by
  classical
  let P := X.1.1
  let T := P.triple
  have hpair : P.rotatedAssociatedArrow sigma AR =
      P.hookArrow sigma AR := by
    exact congrArg Subtype.val X.2
  have huNot : ¬ HasIrreducibleMorphism
      (sigma.obj T.u) (sigma.obj P.z) := by
    intro hu
    have hsucc := congrArg
      ((AR.arMeshRotationData sigma).arrowOrbitData sigma).successor hpair
    have hassociated : P.associatedArrow sigma AR =
        T.secondArrow sigma AR := by
      simpa [P, T, HookM5Preliminary.hookArrow, hu,
        P.rotatedAssociatedArrow_successor sigma AR,
        T.firstArrow_successor sigma AR] using hsucc
    have hz : P.z = T.b := by
      have ht := congrArg
        (fun q : sigma.IrreduciblePair ↦ q.1.2) hassociated
      simpa only [P.associatedArrow_target sigma AR,
        StripAdmissibleTriple.secondArrow] using ht
    exact P.z_not_mem (by
      simpa only [hz] using T.mem_support_b)
  have hhook : P.hookArrow sigma AR = T.secondArrow sigma AR := by
    simp [P, T, HookM5Preliminary.hookArrow, huNot]
  have huNI : ¬ Injective (sigma.obj T.u) := by
    have hInterior := X.1.2.2
    rw [hhook] at hInterior
    simpa [T, StripAdmissibleTriple.secondArrow, IsInteriorArrow] using
      hInterior.2
  exact ⟨T, P.a_projective, huNI⟩

/-- The preliminary term reconstructed from a diagonal occurrence's
candidate is the original preliminary term. -/
theorem diagonalCandidateOfInteriorChannel_preliminary
    (X : HookM5Preliminary.DiagonalInteriorChannel sigma AR) :
    (diagonalCandidateOfInteriorChannel sigma AR X).preliminary
        sigma AR = X.1.1 := by
  classical
  let P := X.1.1
  let T := P.triple
  let C := diagonalCandidateOfInteriorChannel sigma AR X
  have hpair : P.rotatedAssociatedArrow sigma AR =
      P.hookArrow sigma AR := congrArg Subtype.val X.2
  have huNot : ¬ HasIrreducibleMorphism
      (sigma.obj T.u) (sigma.obj P.z) := by
    intro hu
    have hsucc := congrArg
      ((AR.arMeshRotationData sigma).arrowOrbitData sigma).successor hpair
    have hassociated : P.associatedArrow sigma AR =
        T.secondArrow sigma AR := by
      simpa [P, T, HookM5Preliminary.hookArrow, hu,
        P.rotatedAssociatedArrow_successor sigma AR,
        T.firstArrow_successor sigma AR] using hsucc
    have hz : P.z = T.b := by
      have ht := congrArg
        (fun q : sigma.IrreduciblePair ↦ q.1.2) hassociated
      simpa only [P.associatedArrow_target sigma AR,
        StripAdmissibleTriple.secondArrow] using ht
    exact P.z_not_mem (by simpa only [hz] using T.mem_support_b)
  have hhook : P.hookArrow sigma AR = T.secondArrow sigma AR := by
    simp [P, T, HookM5Preliminary.hookArrow, huNot]
  have hrotated : P.rotatedAssociatedArrow sigma AR =
      T.secondArrow sigma AR := hpair.trans hhook
  have htau : (AR.arTranslation sigma
      ⟨P.z, P.z_nonprojective⟩).1 = T.u := by
    let M := AR.arMeshRotationData sigma
    let O := M.arrowOrbitData sigma
    let q : {r : sigma.IrreduciblePair //
        ¬ Projective (sigma.obj r.1.2)} :=
      ⟨P.associatedArrow sigma AR, by
        simpa only [P.associatedArrow_target sigma AR] using
          P.z_nonprojective⟩
    have hval := M.arrowOrbitData_tau_val sigma q
    have hsource := congrArg Prod.fst hval
    change (O.tau q).1 = T.secondArrow sigma AR at hrotated
    rw [hrotated] at hsource
    calc
      (AR.arTranslation sigma ⟨P.z, P.z_nonprojective⟩).1 =
          (M.tau ⟨q.1.1.2, q.2⟩).1 := by
        congr 2
        apply Subtype.ext
        exact (P.associatedArrow_target sigma AR).symm
      _ = T.u := by
        simpa only [StripAdmissibleTriple.secondArrow] using hsource.symm
  have hz : C.z sigma AR = P.z := by
    have hinputs : (AR.arTranslationEquiv sigma)
        ⟨P.z, P.z_nonprojective⟩ =
          ⟨T.u, C.2.2⟩ := by
      apply Subtype.ext
      exact htau
    have hinv := congrArg (AR.arTranslationEquiv sigma).symm hinputs
    have hz' : P.z = C.z sigma AR := congrArg Subtype.val
      ((AR.arTranslationEquiv sigma).symm_apply_apply
        ⟨P.z, P.z_nonprojective⟩ |>.symm.trans hinv)
    exact hz'.symm
  apply HookM5Preliminary.ext
  · rfl
  · exact hz

/-- Diagonal interior preliminary occurrences are exactly projective-end
diagonal candidates. -/
def diagonalInteriorChannelEquivDiagonalCandidate :
    HookM5Preliminary.DiagonalInteriorChannel sigma AR ≃
      AR.HookDiagonalCandidate sigma where
  toFun := diagonalCandidateOfInteriorChannel sigma AR
  invFun := diagonalInteriorChannelOfCandidate sigma AR
  left_inv X := by
    apply Subtype.ext
    apply Subtype.ext
    exact diagonalCandidateOfInteriorChannel_preliminary
      sigma AR X
  right_inv C := by
    apply Subtype.ext
    rfl

end HookM5Preliminary

end FiniteARTranslationData

end OpConjecture.IndecomposableSkeleton
