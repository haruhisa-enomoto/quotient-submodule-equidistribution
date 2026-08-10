import QuotientSubmoduleEquidistribution.RepresentationTheory.FourVertexDiagonalCandidateReversal

/-!
# Reversal of short projective strips

A projectively based admissible strip either continues past its two
displayed hook arrows or its middle vertex is already injective.  The first
class is the canonical diagonal-candidate type.  This file packages the
complementary short class and obtains its reversal invariance by subtracting
the already invariant candidate count from the invariant count of all
projective strips.
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
  {iota : Type v} {kappa : Type w} [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  (sigma : IndecomposableSkeleton.{u, v, u} R iota)
  (tau : IndecomposableSkeleton.{u, w, u} S kappa)

namespace FiniteARTranslationData

variable (ARsigma : sigma.FiniteARTranslationData)
  (ARtau : tau.FiniteARTranslationData)
  (D : AlignedBiduality sigma tau)

/-- A projectively based admissible strip whose middle label is already
injective.  Equivalently, its canonical arrow chain stops at the second
displayed hook arrow. -/
abbrev HookShortStrip :=
  {T : ARsigma.StripAdmissibleTriple sigma //
    Projective (sigma.obj T.a) ∧ Injective (sigma.obj T.u)}

noncomputable instance hookShortStripFintype :
    Fintype (ARsigma.HookShortStrip sigma) := Fintype.ofFinite _

/-- Projective strips split exactly into continuing diagonal candidates
and short strips. -/
def projectiveStripEquivDiagonalCandidateSumShort :
    {T : ARsigma.StripAdmissibleTriple sigma //
        Projective (sigma.obj T.a)} ≃
      ARsigma.HookDiagonalCandidate sigma ⊕ ARsigma.HookShortStrip sigma where
  toFun T := by
    classical
    by_cases hu : Injective (sigma.obj T.1.u)
    · exact Sum.inr ⟨T.1, T.2, hu⟩
    · exact Sum.inl ⟨T.1, T.2, hu⟩
  invFun X := by
    rcases X with T | T
    · exact ⟨T.1, T.2.1⟩
    · exact ⟨T.1, T.2.1⟩
  left_inv T := by
    classical
    by_cases hu : Injective (sigma.obj T.1.u)
    · simp [hu]
    · simp [hu]
  right_inv X := by
    classical
    rcases X with T | T
    · simp [T.2.2]
    · simp [T.2.2]

omit [DecidableEq iota] in
include k ARsigma in
/-- A short strip has canonical projective-start arrow-chain length
exactly two. -/
theorem HookShortStrip.arrowChainLength_eq_two
    (T : ARsigma.HookShortStrip sigma) :
    let M := ARsigma.arMeshRotationData sigma
    let q := T.1.projectiveChainStart sigma ARsigma T.2.1
    let hqP : Projective (sigma.obj q.1.2) :=
      T.1.projectiveChainStart_target sigma ARsigma T.2.1 ▸ T.2.1
    M.arrowChainLength sigma q hqP = 2 := by
  let M := ARsigma.arMeshRotationData sigma
  let q := T.1.projectiveChainStart sigma ARsigma T.2.1
  let hqP : Projective (sigma.obj q.1.2) :=
    T.1.projectiveChainStart_target sigma ARsigma T.2.1 ▸ T.2.1
  let N := M.arrowChainLength sigma q hqP
  have htwo : 2 ≤ N := by
    simpa [M, q, hqP, N] using
      T.1.two_le_projectiveChainStart_length
        (K := k) sigma ARsigma T.2.1
  by_contra hne
  have hlt : 2 < N := lt_of_le_of_ne htwo (Ne.symm hne)
  have hnotI := M.arrowChainAt_not_injectiveSource_of_lt
    sigma q hqP hlt
  have hsource := M.arrowChainAt_succ_source_eq_target
    sigma q hqP (n := 1) (by omega)
  have hone := T.1.arrowChainAt_projectiveChainStart_one
    sigma ARsigma T.2.1
  apply hnotI
  rw [show 1 + 1 = 2 by omega] at hsource
  rw [hsource, hone]
  simpa [StripAdmissibleTriple.firstArrow] using T.2.2

omit [DecidableEq iota] [DecidableEq kappa] in
include k D in
/-- Short projective strips have the same cardinality on aligned opposite
skeletons. -/
theorem hookShortStrip_card_eq :
    Fintype.card (ARsigma.HookShortStrip sigma) =
      Fintype.card (ARtau.HookShortStrip tau) := by
  have hsplitSigma :
      Fintype.card
          {T : ARsigma.StripAdmissibleTriple sigma //
            Projective (sigma.obj T.a)} =
        Fintype.card (ARsigma.HookDiagonalCandidate sigma) +
          Fintype.card (ARsigma.HookShortStrip sigma) := by
    rw [Fintype.card_congr
      (projectiveStripEquivDiagonalCandidateSumShort sigma ARsigma)]
    exact Fintype.card_sum
  have hsplitTau :
      Fintype.card
          {T : ARtau.StripAdmissibleTriple tau //
            Projective (tau.obj T.a)} =
        Fintype.card (ARtau.HookDiagonalCandidate tau) +
          Fintype.card (ARtau.HookShortStrip tau) := by
    rw [Fintype.card_congr
      (projectiveStripEquivDiagonalCandidateSumShort tau ARtau)]
    exact Fintype.card_sum
  have hprojective := projectiveStrip_card_eq
    (K := k) sigma tau ARsigma ARtau D
  have hcandidate := hookDiagonalCandidate_card_eq
    (k := k) sigma tau ARsigma ARtau D
  omega

end FiniteARTranslationData

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
