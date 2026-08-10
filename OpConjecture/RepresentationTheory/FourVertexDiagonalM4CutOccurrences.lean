import OpConjecture.RepresentationTheory.FourVertexSignedChannelOccurrences

/-!
# Long-chain diagonal cuts as labelled arrow occurrences

The corrected diagonal cut count is initially stated in vertex coordinates.
This file sends every quotient-side long-chain cut to its actual ordered pair
of irreducible-arrow occurrences on the full common-target source boundary and
proves that the encoding is injective.  Its exact range is therefore
equivalent to the coordinate type.

The further identification of this occurrence image with the admissible
diagonal `M4`/`HookM6Channel` subtype is deliberately left explicit rather
than assumed here.
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

/-- The actual ordered common-target arrow occurrence encoded by one
quotient-side long-chain diagonal cut. -/
def longArrowChainFirstDiagonalCutCommonTargetPair
    (q : AR.LongArrowChainFirstDiagonalCut σ) :
    CommonTargetArrowPair σ := by
  let M := AR.arMeshRotationData σ
  let a := q.1.1.1
  let ha := q.1.1.2
  let n := M.arrowChainLength σ a ha
  let e := q.2.1.1
  let A := M.arrowChainAt σ a 1
  let B := M.arrowChainAt σ a (e - 1)
  refine ⟨(A, B), ?_⟩
  have hlen : 4 ≤ M.arrowChainLength σ a ha := q.1.2
  have heLower : 2 ≤ e := q.2.1.2.1
  have heBounds := q.2.1.2
  change 2 ≤ e ∧
    e ≤ M.arrowChainLength σ a ha + 1 - 2 at heBounds
  have heUpper : e ≤ n - 1 := by
    change e ≤ M.arrowChainLength σ a ha - 1
    have := heBounds.2
    omega
  have hAvertex := M.arrowChainVertexAt_positionSucc σ a ha
    (⟨1, by omega⟩ : Fin (n + 1))
  have hBvertex := M.arrowChainVertexAt_positionSucc σ a ha
    (⟨e - 1, by omega⟩ : Fin (n + 1))
  have hcut := q.2.2
  change AR.arrowChainVertexNat σ a ha 2 =
    AR.arrowChainVertexNat σ a ha e at hcut
  have htwoLt : 2 < M.arrowChainLength σ a ha + 2 := by omega
  have heUpper' : e ≤ M.arrowChainLength σ a ha - 1 := by
    simpa only [n] using heUpper
  have heLt : e < M.arrowChainLength σ a ha + 2 := by omega
  calc
    A.1.2 = AR.arrowChainVertexNat σ a ha 2 := by
      rw [AR.arrowChainVertexNat_of_lt σ a ha 2 htwoLt]
      exact hAvertex.symm
    _ = AR.arrowChainVertexNat σ a ha e := hcut
    _ = B.1.2 := by
      rw [AR.arrowChainVertexNat_of_lt σ a ha e heLt]
      change M.arrowChainVertexAt σ a ha ⟨e, heLt⟩ =
        (M.arrowChainAt σ a (e - 1)).1.2
      calc
        M.arrowChainVertexAt σ a ha ⟨e, heLt⟩ =
            M.arrowChainVertexAt σ a ha
              (M.arrowChainPositionSuccVertex σ a ha
                (⟨e - 1, by omega⟩ : Fin (n + 1))) := by
          congr 1
          apply Fin.ext
          simp [ARMeshRotationData.arrowChainPositionSuccVertex]
          omega
        _ = (M.arrowChainAt σ a (e - 1)).1.2 := hBvertex

/-- The preceding common-target pair lies on the full source boundary,
because its distinguished first occurrence starts at the projective chain
vertex. -/
def longArrowChainFirstDiagonalCutSourceBoundaryPair
    (q : AR.LongArrowChainFirstDiagonalCut σ) :
    AR.SourceBoundaryCommonTargetArrowPair σ := by
  let M := AR.arMeshRotationData σ
  let a := q.1.1.1
  let ha := q.1.1.2
  let n := M.arrowChainLength σ a ha
  let A := M.arrowChainAt σ a 1
  let P := AR.longArrowChainFirstDiagonalCutCommonTargetPair σ q
  have hlen : 4 ≤ M.arrowChainLength σ a ha := q.1.2
  have hsource : A.1.1 = a.1.2 := by
    exact M.arrowChainAt_succ_source_eq_target σ a ha (n := 0) (by omega)
  have hprojective : Projective (σ.obj A.1.1) := by
    rw [hsource]
    exact ha
  exact ⟨P, Or.inl <|
    (M.arrowOrbit_twoSource_iff σ A).2 (Or.inr hprojective)⟩

omit [DecidableEq ι] in
/-- The labelled common-target occurrence remembers both its maximal
chain and its reflected cut index. -/
theorem longArrowChainFirstDiagonalCutCommonTargetPair_injective :
    Function.Injective
      (AR.longArrowChainFirstDiagonalCutCommonTargetPair σ) := by
  intro q r hpair
  rcases q with ⟨qstart, qcut⟩
  rcases r with ⟨rstart, rcut⟩
  let M := AR.arMeshRotationData σ
  let O := M.arrowOrbitData σ
  let a := qstart.1.1
  let ha := qstart.1.2
  let b := rstart.1.1
  let hb := rstart.1.2
  let A := M.arrowChainAt σ a 1
  let B := M.arrowChainAt σ b 1
  have hlenA : 4 ≤ M.arrowChainLength σ a ha := qstart.2
  have hlenB : 4 ≤ M.arrowChainLength σ b hb := rstart.2
  have haNI : ¬ Injective (σ.obj a.1.1) :=
    M.arrowChainAt_not_injectiveSource_of_lt σ a ha (n := 0) (by omega)
  have hbNI : ¬ Injective (σ.obj b.1.1) :=
    M.arrowChainAt_not_injectiveSource_of_lt σ b hb (n := 0) (by omega)
  have hANP : ¬ Projective (σ.obj A.1.2) :=
    M.arrowChainAt_succ_target_nonprojective σ a ha (n := 0) (by omega)
  have hBNP : ¬ Projective (σ.obj B.1.2) :=
    M.arrowChainAt_succ_target_nonprojective σ b hb (n := 0) (by omega)
  have hfirst : A = B := by
    exact congrArg
      (fun p : CommonTargetArrowPair σ ↦ p.1.1) hpair
  have hbackA : O.tau ⟨A, hANP⟩ = ⟨a, haNI⟩ := by
    have hsucc : A = O.successor a := by
      simp [A, O, M, ARMeshRotationData.arrowChainAt]
    have hsuccSub : (⟨A, hANP⟩ : {x : σ.IrreduciblePair //
        ¬ Projective (σ.obj x.1.2)}) =
        ⟨O.successor a,
          O.successor_not_mem_source_of_not_mem_target haNI⟩ :=
      Subtype.ext hsucc
    rw [hsuccSub]
    exact O.tau_successor_of_not_mem_target haNI
  have hbackB : O.tau ⟨B, hBNP⟩ = ⟨b, hbNI⟩ := by
    have hsucc : B = O.successor b := by
      simp [B, O, M, ARMeshRotationData.arrowChainAt]
    have hsuccSub : (⟨B, hBNP⟩ : {x : σ.IrreduciblePair //
        ¬ Projective (σ.obj x.1.2)}) =
        ⟨O.successor b,
          O.successor_not_mem_source_of_not_mem_target hbNI⟩ :=
      Subtype.ext hsucc
    rw [hsuccSub]
    exact O.tau_successor_of_not_mem_target hbNI
  have hab : a = b := by
    have hsub : (⟨A, hANP⟩ : {x : σ.IrreduciblePair //
        ¬ Projective (σ.obj x.1.2)}) = ⟨B, hBNP⟩ :=
      Subtype.ext hfirst
    have htau := congrArg O.tau hsub
    rw [hbackA, hbackB] at htau
    exact congrArg
      (fun x : {x : σ.IrreduciblePair //
        ¬ Injective (σ.obj x.1.1)} ↦ x.1) htau
  have hstart : qstart = rstart := by
    apply Subtype.ext
    apply Subtype.ext
    simpa only [a, b] using hab
  subst rstart
  apply congrArg (Sigma.mk qstart)
  apply Subtype.ext
  apply Subtype.ext
  let e := qcut.1.1
  let f := rcut.1.1
  have heLower : 2 ≤ e := qcut.1.2.1
  have hfLower : 2 ≤ f := rcut.1.2.1
  have heUpperRaw := qcut.1.2.2
  have hfUpperRaw := rcut.1.2.2
  change e ≤ M.arrowChainLength σ a ha + 1 - 2 at heUpperRaw
  change f ≤ M.arrowChainLength σ a ha + 1 - 2 at hfUpperRaw
  have hsecond : M.arrowChainAt σ a (e - 1) =
      M.arrowChainAt σ a (f - 1) := by
    exact congrArg
      (fun p : CommonTargetArrowPair σ ↦ p.1.2) hpair
  have hindices : e - 1 = f - 1 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (M.arrowChainAt_ne_of_lt_le σ a ha hlt (by omega)) hsecond
    · exact (M.arrowChainAt_ne_of_lt_le σ a ha hgt (by omega)) hsecond.symm
  omega

omit [DecidableEq ι] in
/-- The source-boundary occurrence encoding is injective as well. -/
theorem longArrowChainFirstDiagonalCutSourceBoundaryPair_injective :
    Function.Injective
      (AR.longArrowChainFirstDiagonalCutSourceBoundaryPair σ) := by
  intro q r h
  apply AR.longArrowChainFirstDiagonalCutCommonTargetPair_injective σ
  exact congrArg Subtype.val h

/-- The exact image of the long-chain quotient diagonal cuts among actual
source-boundary common-target arrow occurrences. -/
abbrev LongArrowChainFirstDiagonalCutOccurrenceImage :=
  Set.range (AR.longArrowChainFirstDiagonalCutSourceBoundaryPair σ)

noncomputable instance longArrowChainFirstDiagonalCutOccurrenceImageFintype :
    Fintype (AR.LongArrowChainFirstDiagonalCutOccurrenceImage σ) :=
  Fintype.ofFinite _

omit [DecidableEq ι] in
/-- Long-chain quotient cut coordinates are equivalent to their exact
labelled occurrence image. -/
def longArrowChainFirstDiagonalCutEquivOccurrenceImage :
    AR.LongArrowChainFirstDiagonalCut σ ≃
      AR.LongArrowChainFirstDiagonalCutOccurrenceImage σ :=
  Equiv.ofInjective
    (AR.longArrowChainFirstDiagonalCutSourceBoundaryPair σ)
    (AR.longArrowChainFirstDiagonalCutSourceBoundaryPair_injective σ)

omit [DecidableEq ι] in
/-- Cardinal form of the exact quotient-cut occurrence encoding. -/
theorem longArrowChainFirstDiagonalCut_card_eq_occurrenceImage_card :
    Fintype.card (AR.LongArrowChainFirstDiagonalCut σ) =
      Fintype.card
        (AR.LongArrowChainFirstDiagonalCutOccurrenceImage σ) :=
  Fintype.card_congr
    (AR.longArrowChainFirstDiagonalCutEquivOccurrenceImage σ)

end OpConjecture.IndecomposableSkeleton.FiniteARTranslationData
