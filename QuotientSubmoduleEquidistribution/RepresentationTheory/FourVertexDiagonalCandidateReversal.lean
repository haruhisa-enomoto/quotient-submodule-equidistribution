import QuotientSubmoduleEquidistribution.RepresentationTheory.FourVertexDiagonalReturnCorrection
import QuotientSubmoduleEquidistribution.RepresentationTheory.FourVertexStripReversal

/-!
# Reversal of the canonical diagonal candidates

The local diagonal/double-hook correction is indexed by projectively based
strip triples whose middle vertex is noninjective.  Equivalently, their
canonical labelled arrow chain has at least one occurrence after the two
displayed hook arrows.  Reflection to the injective end preserves that
extra occurrence, and aligned duality turns the reflected reverse triple
into the corresponding projectively based candidate on the dual skeleton.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe u v w

variable {k R S : Type u} [Field k]
  [Ring R] [Algebra k R] [FiniteDimensional k R]
  [Ring S] [Algebra k S] [FiniteDimensional k S]
  [IsNoetherianRing R] [IsNoetherianRing S]
  {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)
  (τ : IndecomposableSkeleton.{u, w, u} S κ)

namespace FiniteARTranslationData

variable (ARσ : σ.FiniteARTranslationData)
  (ARτ : τ.FiniteARTranslationData)
  (D : AlignedBiduality σ τ)

namespace HookDiagonalCandidate

variable (C : ARσ.HookDiagonalCandidate σ)

omit [DecidableEq ι] in
include k ARσ in
/-- The noninjectivity of the hook middle label says that the canonical
projective-target arrow chain continues for at least one occurrence after
the two displayed hook arrows. -/
theorem three_le_projectiveChainStart_length :
    let M := ARσ.arMeshRotationData σ
    let q := C.1.projectiveChainStart σ ARσ C.2.1
    let hqP : Projective (σ.obj q.1.2) :=
      C.1.projectiveChainStart_target σ ARσ C.2.1 ▸ C.2.1
    3 ≤ M.arrowChainLength σ q hqP := by
  let M := ARσ.arMeshRotationData σ
  let O := M.arrowOrbitData σ
  let q := C.1.projectiveChainStart σ ARσ C.2.1
  let hqP : Projective (σ.obj q.1.2) :=
    C.1.projectiveChainStart_target σ ARσ C.2.1 ▸ C.2.1
  let N := M.arrowChainLength σ q hqP
  have htwo : 2 ≤ N := by
    simpa [M, q, hqP, N] using
      C.1.two_le_projectiveChainStart_length (K := k) σ ARσ C.2.1
  by_contra hthree
  change ¬ 3 ≤ N at hthree
  have hN : N = 2 := by omega
  have hoccurrence : M.arrowChainAt σ q 2 =
      C.1.secondArrow σ ARσ := by
    change O.successor
      (O.successor (C.1.hookOrbitAnchor σ ARσ)) =
        C.1.secondArrow σ ARσ
    rw [C.1.hookOrbitAnchor_successor σ ARσ,
      C.1.firstArrow_successor σ ARσ]
  have hterminal := M.arrowChainAt_length_injectiveSource σ q hqP
  change Injective
    (σ.obj (M.arrowChainAt σ q (M.arrowChainLength σ q hqP)).1.1)
      at hterminal
  rw [show M.arrowChainLength σ q hqP = 2 by exact hN,
    hoccurrence] at hterminal
  exact C.2.2 (by
    simpa [StripAdmissibleTriple.secondArrow] using hterminal)

include k ARσ τ D ARτ in
/-- Reflecting a diagonal candidate to the injective end produces a
reverse strip triple whose middle label is still nonprojective. -/
def projectiveChainEndReverseCandidate :
    {U : ARσ.ReverseStripAdmissibleTriple σ //
      Injective (σ.obj U.a) ∧ ¬ Projective (σ.obj U.u)} := by
  let U := C.1.projectiveChainEndReverseTriple
    (K := k) σ ARσ τ D ARτ C.2.1
  refine ⟨U.1, U.2, ?_⟩
  let M := ARσ.arMeshRotationData σ
  let q := C.1.projectiveChainStart σ ARσ C.2.1
  let hqP : Projective (σ.obj q.1.2) :=
    C.1.projectiveChainStart_target σ ARσ C.2.1 ▸ C.2.1
  let N := M.arrowChainLength σ q hqP
  have hthree : 3 ≤ N := by
    simpa [M, q, hqP, N] using
      C.three_le_projectiveChainStart_length (k := k) σ ARσ
  have hNm2 : N - 2 < N := by omega
  have hNm3 : N - 3 < N := by omega
  have hsource := M.arrowChainAt_succ_source_eq_target
    σ q hqP (n := N - 2) hNm2
  have hnp := M.arrowChainAt_succ_target_nonprojective
    σ q hqP (n := N - 3) hNm3
  change ¬ Projective (σ.obj U.1.u)
  rw [C.1.projectiveChainEndReverseTriple_u
    (K := k) σ ARσ τ D ARτ C.2.1]
  have hind₁ : N - 2 + 1 = N - 1 := by omega
  have hind₂ : N - 3 + 1 = N - 2 := by omega
  rw [hind₁] at hsource
  rw [hsource]
  simpa only [hind₂] using hnp

end HookDiagonalCandidate

omit [DecidableEq ι] [DecidableEq κ] in
include k D in
/-- Push the reflected source-coordinate reverse candidate through aligned
duality to a genuine projective-end candidate on the dual skeleton. -/
def diagonalCandidateToDual
    (C : ARσ.HookDiagonalCandidate σ) :
    ARτ.HookDiagonalCandidate τ := by
  let U := C.projectiveChainEndReverseCandidate
    (k := k) σ τ ARσ ARτ D
  let T := pushforwardReverseStripAdmissibleTriple σ τ ARσ ARτ D U.1
  refine ⟨T, ?_, ?_⟩
  · exact (D.forward.injective_iff_projective_image σ τ U.1.a).1 U.2.1
  · intro hI
    apply U.2.2
    exact (D.forward.projective_iff_injective_image σ τ U.1.u).2 hI

omit [DecidableEq ι] [DecidableEq κ] in
include k ARσ D in
/-- Reflection followed by aligned duality is injective on canonical
diagonal candidates. -/
theorem diagonalCandidateToDual_injective
    {C₁ C₂ : ARσ.HookDiagonalCandidate σ}
    (h : diagonalCandidateToDual (k := k) σ τ ARσ ARτ D C₁ =
      diagonalCandidateToDual (k := k) σ τ ARσ ARτ D C₂) :
    C₁ = C₂ := by
  let U₁ := C₁.projectiveChainEndReverseCandidate
    (k := k) σ τ ARσ ARτ D
  let U₂ := C₂.projectiveChainEndReverseCandidate
    (k := k) σ τ ARσ ARτ D
  have hU : U₁.1 = U₂.1 := by
    apply (stripAdmissibleTripleEquivReverse σ τ ARσ ARτ D).symm.injective
    exact congrArg Subtype.val h
  have hend :
      C₁.1.projectiveChainEndReverseTriple
          (K := k) σ ARσ τ D ARτ C₁.2.1 =
        C₂.1.projectiveChainEndReverseTriple
          (K := k) σ ARσ τ D ARτ C₂.2.1 := by
    apply Subtype.ext
    exact hU
  have hstart :
      (⟨C₁.1, C₁.2.1⟩ : {T : ARσ.StripAdmissibleTriple σ //
        Projective (σ.obj T.a)}) =
      ⟨C₂.1, C₂.2.1⟩ :=
    StripAdmissibleTriple.projectiveChainEndReverseTriple_injective
      (K := k) σ ARσ τ D ARτ hend
  exact Subtype.ext (congrArg
    (fun X : {T : ARσ.StripAdmissibleTriple σ //
      Projective (σ.obj T.a)} ↦ X.1) hstart)

omit [DecidableEq ι] [DecidableEq κ] in
include k D in
/-- The canonical diagonal-candidate count is invariant under aligned
reversal. -/
theorem hookDiagonalCandidate_card_eq :
    Fintype.card (ARσ.HookDiagonalCandidate σ) =
      Fintype.card (ARτ.HookDiagonalCandidate τ) := by
  let D' : AlignedBiduality τ σ := D.swap σ τ
  have hστ : Fintype.card (ARσ.HookDiagonalCandidate σ) ≤
      Fintype.card (ARτ.HookDiagonalCandidate τ) := by
    exact Fintype.card_le_of_injective
      (diagonalCandidateToDual (k := k) σ τ ARσ ARτ D)
      (fun _ _ h ↦ diagonalCandidateToDual_injective
        (k := k) σ τ ARσ ARτ D h)
  have hτσ : Fintype.card (ARτ.HookDiagonalCandidate τ) ≤
      Fintype.card (ARσ.HookDiagonalCandidate σ) := by
    exact Fintype.card_le_of_injective
      (diagonalCandidateToDual (k := k) τ σ ARτ ARσ D')
      (fun _ _ h ↦ diagonalCandidateToDual_injective
        (k := k) τ σ ARτ ARσ D' h)
  omega

include D in
/-- Combining candidate reversal with the exact local split proves the
required invariance of `diagonal return + double-hook support`. -/
theorem diagonalReturn_add_doubleHook_card_eq :
    Fintype.card
          ((σ.finiteDimensionalARTranslationData k R).HookM5DiagonalReturn
            σ) +
        Fintype.card (QuotientDoubleHookFour (k := k) (R := R) σ) =
      Fintype.card
          ((τ.finiteDimensionalARTranslationData k S).HookM5DiagonalReturn
            τ) +
        Fintype.card (QuotientDoubleHookFour (k := k) (R := S) τ) := by
  rw [← hookDiagonalCandidate_card_eq_diagonalReturn_add_doubleHookFour
      (k := k) (R := R) σ,
    ← hookDiagonalCandidate_card_eq_diagonalReturn_add_doubleHookFour
      (k := k) (R := S) τ]
  exact hookDiagonalCandidate_card_eq (k := k) σ τ
    (σ.finiteDimensionalARTranslationData k R)
    (τ.finiteDimensionalARTranslationData k S) D

end FiniteARTranslationData

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
