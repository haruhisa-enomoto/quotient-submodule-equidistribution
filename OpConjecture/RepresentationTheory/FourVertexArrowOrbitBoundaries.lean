import OpConjecture.RepresentationTheory.ARNoTransitiveTriangles
import OpConjecture.RepresentationTheory.ARDualLocalRestrictions
import OpConjecture.RepresentationTheory.FourVertexArrowOrbits
import OpConjecture.RepresentationTheory.FourVertexHookChannels
import OpConjecture.Combinatorics.BoundaryTranslationProducts
import OpConjecture.Combinatorics.SquareShiftBoundaryBalance
import OpConjecture.Combinatorics.DiagonalSquareShiftCuts

/-!
# Boundary restrictions for labelled arrow orbits

This file specializes the abstract arrow-orbit chains to finite-dimensional
modules.  In particular, a chain beginning at an arrow whose target is
projective has positive length, because such an arrow cannot simultaneously
start at an injective object.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace OpConjecture.IndecomposableSkeleton.FiniteARTranslationData

universe u v w

variable {K R : Type u} [Field K] [Ring R] [Algebra K R]
  [FiniteDimensional K R] [IsNoetherianRing R]
  {ι : Type v} [Fintype ι] [DecidableEq ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)
  (AR : σ.FiniteARTranslationData)

/-- An admissible strip triple after reversing the translation quiver, but
written in the original skeleton.  Thus its displayed arrows and inverse
translation identity have the source orientation. -/
@[ext]
structure ReverseStripAdmissibleTriple where
  a : ι
  u : ι
  b : ι
  a_ne_u : a ≠ u
  a_ne_b : a ≠ b
  u_ne_b : u ≠ b
  u_noninjective : ¬ Injective (σ.obj u)
  b_noninjective : ¬ Injective (σ.obj b)
  u_to_a : HasIrreducibleMorphism (σ.obj u) (σ.obj a)
  b_to_u : HasIrreducibleMorphism (σ.obj b) (σ.obj u)
  u_not_to_b : ¬ HasIrreducibleMorphism (σ.obj u) (σ.obj b)
  b_not_to_a : ¬ HasIrreducibleMorphism (σ.obj b) (σ.obj a)
  inverseTau_b :
    ((AR.arTranslationEquiv σ).symm ⟨b, b_noninjective⟩).1 = a

omit [Fintype ι] in
noncomputable instance reverseStripAdmissibleTripleFinite :
    Finite (AR.ReverseStripAdmissibleTriple σ) :=
  Finite.of_injective
    (fun T ↦ (T.a, T.u, T.b)) (by
      intro T₁ T₂ h
      ext
      · exact congrArg (fun q ↦ q.1) h
      · exact congrArg (fun q ↦ q.2.1) h
      · exact congrArg (fun q ↦ q.2.2) h)

omit [Fintype ι] in
noncomputable instance reverseStripAdmissibleTripleFintype :
    Fintype (AR.ReverseStripAdmissibleTriple σ) := Fintype.ofFinite _

omit [Fintype ι] [DecidableEq ι] in
include K in
/-- An arrow occurrence ending at a projective does not start at an
injective. -/
theorem arrowToProjective_source_noninjective
    (a : σ.IrreduciblePair) (ha : Projective (σ.obj a.1.2)) :
    ¬ Injective (σ.obj a.1.1) := by
  intro hi
  exact no_irreducible_injective_to_projective
    (K := K) σ hi ha a.2

omit [DecidableEq ι] in
include K AR in
/-- Every projective-target arrow chain has at least one genuine mesh
rotation before reaching its injective-source endpoint. -/
theorem arrowChainLength_pos
    (a : σ.IrreduciblePair) (ha : Projective (σ.obj a.1.2)) :
    0 < (AR.arMeshRotationData σ).arrowChainLength σ a ha := by
  let M := AR.arMeshRotationData σ
  have hterminal := M.arrowChainAt_length_injectiveSource σ a ha
  apply Nat.pos_of_ne_zero
  intro hlen
  change M.arrowChainLength σ a ha = 0 at hlen
  have hstart : M.arrowChainAt σ a (M.arrowChainLength σ a ha) = a := by
    simp [hlen, ARMeshRotationData.arrowChainAt]
  have hi : Injective (σ.obj a.1.1) := by
    simpa only [hstart] using hterminal
  exact arrowToProjective_source_noninjective
    (K := K) σ a ha hi

include AR in
/-- The paper's simultaneous square shift on two actual labelled arrow
chains: equality of chain vertices has the same total multiplicity on the
first-two-row-or-column boundary and on the last-two-row-or-column boundary.
Occurrence positions remain labelled even when their vertex values agree. -/
theorem arrowChain_squareShift_boundary_balance
    (a c : σ.IrreduciblePair)
    (ha : Projective (σ.obj a.1.2))
    (hc : Projective (σ.obj c.1.2)) :
    let M := AR.arMeshRotationData σ
    (∑ p : {p : OpConjecture.SquareShiftBoundaryBalance.Grid
          (M.arrowChainLength σ a ha + 2)
          (M.arrowChainLength σ c hc + 2) //
        OpConjecture.SquareShiftBoundaryBalance.Incoming p},
      if M.arrowChainVertexAt σ a ha p.1.1 =
          M.arrowChainVertexAt σ c hc p.1.2 then 1 else 0) =
    ∑ p : {p : OpConjecture.SquareShiftBoundaryBalance.Grid
          (M.arrowChainLength σ a ha + 2)
          (M.arrowChainLength σ c hc + 2) //
        OpConjecture.SquareShiftBoundaryBalance.Outgoing p},
      if M.arrowChainVertexAt σ a ha p.1.1 =
          M.arrowChainVertexAt σ c hc p.1.2 then 1 else 0 := by
  let M := AR.arMeshRotationData σ
  apply OpConjecture.SquareShiftBoundaryBalance.sum_equalityIndicators_incoming_eq_outgoing
  intro p hp
  have hp' :
      ¬ OpConjecture.SquareShiftBoundaryBalance.Outgoing p := hp
  have hcoords :
      p.1.1 + 2 < M.arrowChainLength σ a ha + 2 ∧
        p.2.1 + 2 < M.arrowChainLength σ c hc + 2 := by
    simpa [OpConjecture.SquareShiftBoundaryBalance.Outgoing,
      not_or, not_le] using hp'
  have hna : p.1.1 < M.arrowChainLength σ a ha := by omega
  have hnc : p.2.1 < M.arrowChainLength σ c hc := by omega
  let p₂ := OpConjecture.SquareShiftBoundaryBalance.addTwo p hp
  have haNP : ¬ Projective
      (σ.obj (M.arrowChainVertexAt σ a ha p₂.1)) := by
    simpa [p₂, OpConjecture.SquareShiftBoundaryBalance.addTwo] using
      M.arrowChainVertexAt_add_two_nonprojective σ a ha hna
  have hcNP : ¬ Projective
      (σ.obj (M.arrowChainVertexAt σ c hc p₂.2)) := by
    simpa [p₂, OpConjecture.SquareShiftBoundaryBalance.addTwo] using
      M.arrowChainVertexAt_add_two_nonprojective σ c hc hnc
  let xa₂ : σ.NonprojectiveLabel :=
    ⟨M.arrowChainVertexAt σ a ha p₂.1, haNP⟩
  let xc₂ : σ.NonprojectiveLabel :=
    ⟨M.arrowChainVertexAt σ c hc p₂.2, hcNP⟩
  have hta : (M.tau xa₂).1 = M.arrowChainVertexAt σ a ha p.1 := by
    simpa [xa₂, p₂,
      OpConjecture.SquareShiftBoundaryBalance.addTwo] using
      M.arTranslation_arrowChainVertexAt_add_two σ a ha hna
  have htc : (M.tau xc₂).1 = M.arrowChainVertexAt σ c hc p.2 := by
    simpa [xc₂, p₂,
      OpConjecture.SquareShiftBoundaryBalance.addTwo] using
      M.arTranslation_arrowChainVertexAt_add_two σ c hc hnc
  constructor
  · intro h
    have hx : xa₂ = xc₂ := by
      apply Subtype.ext
      exact h
    calc
      M.arrowChainVertexAt σ a ha p.1 = (M.tau xa₂).1 := hta.symm
      _ = (M.tau xc₂).1 := congrArg Subtype.val (congrArg M.tau hx)
      _ = M.arrowChainVertexAt σ c hc p.2 := htc
  · intro h
    have ht : M.tau xa₂ = M.tau xc₂ := by
      apply Subtype.ext
      exact hta.trans (h.trans htc.symm)
    exact congrArg Subtype.val (M.tau.injective ht)

/-- Extend the finite vertex list of a projective-target arrow chain to a
total natural-number function.  Only its values in the displayed chain
range are used below. -/
def arrowChainVertexNat
    (a : σ.IrreduciblePair)
    (ha : Projective (σ.obj a.1.2)) (n : ℕ) : ι := by
  let M := AR.arMeshRotationData σ
  by_cases hn : n < M.arrowChainLength σ a ha + 2
  · exact M.arrowChainVertexAt σ a ha ⟨n, hn⟩
  · exact a.1.1

omit [DecidableEq ι] in
@[simp]
theorem arrowChainVertexNat_of_lt
    (a : σ.IrreduciblePair)
    (ha : Projective (σ.obj a.1.2)) (n : ℕ)
    (hn : n < (AR.arMeshRotationData σ).arrowChainLength σ a ha + 2) :
    AR.arrowChainVertexNat σ a ha n =
      (AR.arMeshRotationData σ).arrowChainVertexAt σ a ha ⟨n, hn⟩ := by
  simp [arrowChainVertexNat, hn]

omit [DecidableEq ι] in
/-- The source of a chain occurrence is the natural-number chain vertex at
the same position. -/
theorem arrowChainAt_source_eq_vertexNat
    (a : σ.IrreduciblePair)
    (ha : Projective (σ.obj a.1.2)) {n : ℕ}
    (hn : n ≤ (AR.arMeshRotationData σ).arrowChainLength σ a ha) :
    ((AR.arMeshRotationData σ).arrowChainAt σ a n).1.1 =
      AR.arrowChainVertexNat σ a ha n := by
  have hnlt : n <
      (AR.arMeshRotationData σ).arrowChainLength σ a ha + 2 := by omega
  let M := AR.arMeshRotationData σ
  change n ≤ M.arrowChainLength σ a ha at hn
  let q : Fin (M.arrowChainLength σ a ha + 1) := ⟨n, by omega⟩
  rw [AR.arrowChainVertexNat_of_lt σ a ha n hnlt]
  change (M.arrowChainAt σ a q.1).1.1 =
    M.arrowChainVertexAt σ a ha (M.arrowChainPositionVertex σ a ha q)
  exact M.arrowChainAt_source_eq_vertex σ a ha q

omit [DecidableEq ι] in
/-- The target of a chain occurrence is the natural-number chain vertex
one position later. -/
theorem arrowChainAt_target_eq_vertexNat_succ
    (a : σ.IrreduciblePair)
    (ha : Projective (σ.obj a.1.2)) {n : ℕ}
    (hn : n ≤ (AR.arMeshRotationData σ).arrowChainLength σ a ha) :
    ((AR.arMeshRotationData σ).arrowChainAt σ a n).1.2 =
      AR.arrowChainVertexNat σ a ha (n + 1) := by
  have hnlt : n + 1 <
      (AR.arMeshRotationData σ).arrowChainLength σ a ha + 2 := by omega
  let M := AR.arMeshRotationData σ
  change n ≤ M.arrowChainLength σ a ha at hn
  let q : Fin (M.arrowChainLength σ a ha + 1) := ⟨n, by omega⟩
  rw [AR.arrowChainVertexNat_of_lt σ a ha (n + 1) hnlt]
  change (M.arrowChainAt σ a q.1).1.2 =
    M.arrowChainVertexAt σ a ha
      (M.arrowChainPositionSuccVertex σ a ha q)
  exact (M.arrowChainVertexAt_positionSucc σ a ha q).symm

/-- The labelled equality occurrences on the first actual diagonal cut
of one maximal arrow chain. -/
abbrev ArrowChainFirstDiagonalCut
    (a : σ.IrreduciblePair)
    (ha : Projective (σ.obj a.1.2)) :=
  let M := AR.arMeshRotationData σ
  OpConjecture.DiagonalSquareShiftCuts.FirstCut
    (M.arrowChainLength σ a ha + 1)
    (AR.arrowChainVertexNat σ a ha)

/-- The labelled equality occurrences on the last actual diagonal cut
of one maximal arrow chain. -/
abbrev ArrowChainLastDiagonalCut
    (a : σ.IrreduciblePair)
    (ha : Projective (σ.obj a.1.2)) :=
  let M := AR.arMeshRotationData σ
  OpConjecture.DiagonalSquareShiftCuts.LastCut
    (M.arrowChainLength σ a ha + 1)
    (AR.arrowChainVertexNat σ a ha)

include AR in
/-- Corrected diagonal M₄ count for an actual labelled arrow chain of
paper length at least five.  The equivalence reads only the two genuine
cuts; a square-shift component meeting neither cut contributes to neither
side. -/
def arrowChainFirstDiagonalCutEquivLastDiagonalCut
    (a : σ.IrreduciblePair)
    (ha : Projective (σ.obj a.1.2))
    (hlen : 4 ≤ (AR.arMeshRotationData σ).arrowChainLength σ a ha) :
    AR.ArrowChainFirstDiagonalCut σ a ha ≃
      AR.ArrowChainLastDiagonalCut σ a ha := by
  classical
  let M := AR.arMeshRotationData σ
  let n := M.arrowChainLength σ a ha
  let x := AR.arrowChainVertexNat σ a ha
  change 4 ≤ n at hlen
  apply OpConjecture.DiagonalSquareShiftCuts.firstCutEquivLastCut
    (L := n + 1) (by omega) x
  · intro i j hi hj
    have hi' : i < n := by omega
    have hj' : j < n := by omega
    have hii : i + 2 < n + 2 := by omega
    have hjj : j + 2 < n + 2 := by omega
    have hi₀ : i < n + 2 := by omega
    have hj₀ : j < n + 2 := by omega
    dsimp only [x]
    rw [AR.arrowChainVertexNat_of_lt σ a ha (i + 2) hii,
      AR.arrowChainVertexNat_of_lt σ a ha (j + 2) hjj,
      AR.arrowChainVertexNat_of_lt σ a ha i hi₀,
      AR.arrowChainVertexNat_of_lt σ a ha j hj₀]
    let xi₂ : σ.NonprojectiveLabel :=
      ⟨M.arrowChainVertexAt σ a ha ⟨i + 2, hii⟩,
        M.arrowChainVertexAt_add_two_nonprojective σ a ha hi'⟩
    let xj₂ : σ.NonprojectiveLabel :=
      ⟨M.arrowChainVertexAt σ a ha ⟨j + 2, hjj⟩,
        M.arrowChainVertexAt_add_two_nonprojective σ a ha hj'⟩
    have hti : (M.tau xi₂).1 =
        M.arrowChainVertexAt σ a ha ⟨i, by omega⟩ := by
      simpa [xi₂] using
        M.arTranslation_arrowChainVertexAt_add_two σ a ha hi'
    have htj : (M.tau xj₂).1 =
        M.arrowChainVertexAt σ a ha ⟨j, by omega⟩ := by
      simpa [xj₂] using
        M.arTranslation_arrowChainVertexAt_add_two σ a ha hj'
    constructor
    · intro h
      have hx : xi₂ = xj₂ := Subtype.ext h
      exact hti.symm.trans <|
        (congrArg Subtype.val (congrArg M.tau hx)).trans htj
    · intro h
      have ht : M.tau xi₂ = M.tau xj₂ := by
        apply Subtype.ext
        exact hti.trans (h.trans htj.symm)
      exact congrArg Subtype.val (M.tau.injective ht)
  · intro j hjLower hjUpper heq
    have hj : j - 2 < n := by omega
    have hjj : j < n + 2 := by omega
    let qj : Fin (M.arrowChainLength σ a ha + 2) :=
      ⟨j, by simpa [n] using hjj⟩
    have hjNP : ¬ Projective
        (σ.obj (M.arrowChainVertexAt σ a ha qj)) := by
      let qraw : Fin (M.arrowChainLength σ a ha + 2) :=
        ⟨j - 2 + 2, by omega⟩
      have hq : qj = qraw := by
        apply Fin.ext
        simp only [qj, qraw]
        omega
      simpa only [hq] using
        M.arrowChainVertexAt_add_two_nonprojective σ a ha hj
    apply hjNP
    have hxone : x 1 = a.1.2 := by
      simp [x, ARMeshRotationData.arrowChainVertexAt,
        ARMeshRotationData.arrowChainAt]
    have hxj : x j =
        M.arrowChainVertexAt σ a ha qj := by
      simpa [n, x] using AR.arrowChainVertexNat_of_lt σ a ha j
        (by simpa [n] using hjj)
    rw [← hxj, ← heq, hxone]
    exact ha
  · intro j hjUpper heq
    have hj : j < n := by omega
    have hjj : j < n + 2 := by omega
    have hterminal := M.arrowChainAt_length_injectiveSource σ a ha
    have hbefore := M.arrowChainAt_not_injectiveSource_of_lt σ a ha hj
    apply hbefore
    have hxterminal : x n =
        (M.arrowChainAt σ a n).1.1 := by
      let qn : Fin (M.arrowChainLength σ a ha + 1) :=
        ⟨n, by simp [n]⟩
      have hsource := M.arrowChainAt_source_eq_vertex σ a ha
        qn
      change AR.arrowChainVertexNat σ a ha n = _
      have hnlt : n <
          (AR.arMeshRotationData σ).arrowChainLength σ a ha + 2 := by
        change n < n + 2
        omega
      rw [AR.arrowChainVertexNat_of_lt σ a ha n hnlt]
      simpa [n, qn, ARMeshRotationData.arrowChainPositionVertex] using
        hsource.symm
    have hxj : x j = (M.arrowChainAt σ a j).1.1 := by
      let qj : Fin (M.arrowChainLength σ a ha + 1) :=
        ⟨j, by simpa [n] using Nat.le_of_lt hj⟩
      have hsource := M.arrowChainAt_source_eq_vertex σ a ha
        qj
      change AR.arrowChainVertexNat σ a ha j = _
      rw [AR.arrowChainVertexNat_of_lt σ a ha j (by
        simpa [n] using (show j < n + 2 by omega))]
      simpa [n, qj, ARMeshRotationData.arrowChainPositionVertex] using
        hsource.symm
    have heq' : x n = x j := by simpa using heq
    rw [← hxj, ← heq', hxterminal]
    simpa [n] using hterminal

include AR in
/-- Cardinal form of the corrected diagonal M₄ arrow-occurrence
balance. -/
theorem arrowChainFirstDiagonalCut_card_eq_lastDiagonalCut_card
    (a : σ.IrreduciblePair)
    (ha : Projective (σ.obj a.1.2))
    (hlen : 4 ≤ (AR.arMeshRotationData σ).arrowChainLength σ a ha) :
    Fintype.card (AR.ArrowChainFirstDiagonalCut σ a ha) =
      Fintype.card (AR.ArrowChainLastDiagonalCut σ a ha) :=
  Fintype.card_congr
    (AR.arrowChainFirstDiagonalCutEquivLastDiagonalCut σ a ha hlen)

/-- Projective-target starts of the arrow chains having paper length at
least five.  Each maximal chain has exactly one such starting occurrence. -/
abbrev LongArrowChainStart :=
  {a : {q : σ.IrreduciblePair // Projective (σ.obj q.1.2)} //
    4 ≤ (AR.arMeshRotationData σ).arrowChainLength σ a.1 a.2}

noncomputable instance longArrowChainStartFintype :
    Fintype (AR.LongArrowChainStart σ) :=
  Fintype.ofFinite _

/-- The disjoint union of the quotient-side diagonal cuts over all long
maximal arrow chains. -/
abbrev LongArrowChainFirstDiagonalCut :=
  Σ a : AR.LongArrowChainStart σ,
    AR.ArrowChainFirstDiagonalCut σ a.1.1 a.1.2

/-- The disjoint union of the reversed-side diagonal cuts over all long
maximal arrow chains. -/
abbrev LongArrowChainLastDiagonalCut :=
  Σ a : AR.LongArrowChainStart σ,
    AR.ArrowChainLastDiagonalCut σ a.1.1 a.1.2

noncomputable instance longArrowChainFirstDiagonalCutFintype :
    Fintype (AR.LongArrowChainFirstDiagonalCut σ) :=
  Fintype.ofFinite _

noncomputable instance longArrowChainLastDiagonalCutFintype :
    Fintype (AR.LongArrowChainLastDiagonalCut σ) :=
  Fintype.ofFinite _

include AR in
/-- Aggregate the corrected diagonal-cut bijection over every long
maximal labelled arrow chain. -/
def longArrowChainFirstDiagonalCutEquivLastDiagonalCut :
    AR.LongArrowChainFirstDiagonalCut σ ≃
      AR.LongArrowChainLastDiagonalCut σ :=
  Equiv.sigmaCongr (Equiv.refl _) fun a ↦
    AR.arrowChainFirstDiagonalCutEquivLastDiagonalCut
      σ a.1.1 a.1.2 a.2

omit [DecidableEq ι] in
include AR in
/-- Cardinal form of the aggregate long-chain diagonal balance. -/
theorem longArrowChainFirstDiagonalCut_card_eq_lastDiagonalCut_card :
    Fintype.card (AR.LongArrowChainFirstDiagonalCut σ) =
      Fintype.card (AR.LongArrowChainLastDiagonalCut σ) :=
  Fintype.card_congr
    (AR.longArrowChainFirstDiagonalCutEquivLastDiagonalCut σ)

namespace StripAdmissibleTriple

variable (T : AR.StripAdmissibleTriple σ)

/-- The first displayed arrow of a strip-admissible triple. -/
def firstArrow : σ.IrreduciblePair :=
  ⟨(T.a, T.u), T.a_to_u⟩

/-- The second displayed arrow of a strip-admissible triple. -/
def secondArrow : σ.IrreduciblePair :=
  ⟨(T.u, T.b), T.u_to_b⟩

omit [Fintype ι] [DecidableEq ι] in
/-- The source `a=τb` of an admissible hook is noninjective. -/
theorem a_noninjective : ¬ Injective (σ.obj T.a) := by
  have h := (AR.arTranslation σ ⟨T.b, T.b_nonprojective⟩).2
  rw [T.tau_b] at h
  exact h

/-- The arrow occurrence immediately before the displayed hook arrows in
their mesh-rotation orbit. -/
def hookOrbitAnchor : σ.IrreduciblePair :=
  (((AR.arMeshRotationData σ).arrowOrbitData σ).tau
    ⟨T.firstArrow σ AR, T.u_nonprojective⟩).1

/-- If the hook source is projective, rotate its first arrow once to obtain
the canonical projective-target start of its labelled arrow chain. -/
def projectiveChainStart (_ha : Projective (σ.obj T.a)) :
    σ.IrreduciblePair :=
  T.hookOrbitAnchor σ AR

omit [DecidableEq ι] in
/-- The orbit anchor ends at the first hook label. -/
theorem hookOrbitAnchor_target :
    (T.hookOrbitAnchor σ AR).1.2 = T.a := by
  let M := AR.arMeshRotationData σ
  have hrotate := M.arrowOrbitData_tau_val σ
    ⟨T.firstArrow σ AR, T.u_nonprojective⟩
  exact congrArg Prod.snd hrotate

omit [DecidableEq ι] in
/-- The first successor of the orbit anchor is the first displayed hook
arrow `a → u`, without any boundary assumption on `a`. -/
theorem hookOrbitAnchor_successor :
    ((AR.arMeshRotationData σ).arrowOrbitData σ).successor
        (T.hookOrbitAnchor σ AR) =
      T.firstArrow σ AR := by
  let M := AR.arMeshRotationData σ
  let p : {q : σ.IrreduciblePair // ¬ Projective (σ.obj q.1.2)} :=
    ⟨T.firstArrow σ AR, T.u_nonprojective⟩
  let q := (M.arrowOrbitData σ).tau p
  change (M.arrowOrbitData σ).successor q.1 = p.1
  have hsuccessor : (M.arrowOrbitData σ).successor q.1 =
      (M.arrowOrbitData σ).tau.symm ⟨q.1, q.2⟩ := by
    simp [OpConjecture.BoundaryTranslationChains.Data.successor, q.2]
  rw [hsuccessor]
  exact congrArg Subtype.val ((M.arrowOrbitData σ).tau.symm_apply_apply p)

omit [DecidableEq ι] in
/-- The successor of the first displayed arrow is the second displayed
arrow `u → b`. -/
theorem firstArrow_successor :
    ((AR.arMeshRotationData σ).arrowOrbitData σ).successor
        (T.firstArrow σ AR) =
      T.secondArrow σ AR := by
  let M := AR.arMeshRotationData σ
  let O := M.arrowOrbitData σ
  let aNI : σ.NoninjectiveLabel := ⟨T.a, T.a_noninjective σ AR⟩
  have hsuccessor : O.successor (T.firstArrow σ AR) =
      O.tau.symm ⟨T.firstArrow σ AR, T.a_noninjective σ AR⟩ := by
    simp [OpConjecture.BoundaryTranslationChains.Data.successor,
      firstArrow, T.a_noninjective σ AR]
  have hval := M.arrowOrbitData_tau_symm_val σ
    ⟨T.firstArrow σ AR, T.a_noninjective σ AR⟩
  have htauSubtype : AR.arTranslationEquiv σ
      ⟨T.b, T.b_nonprojective⟩ = aNI := by
    apply Subtype.ext
    exact T.tau_b
  have hinverse : (AR.arTranslationEquiv σ).symm aNI =
      ⟨T.b, T.b_nonprojective⟩ := by
    exact (AR.arTranslationEquiv σ).symm_apply_eq.mpr htauSubtype.symm
  rw [hsuccessor]
  apply Subtype.ext
  rw [hval]
  apply Prod.ext
  · rfl
  · exact congrArg Subtype.val hinverse

omit [DecidableEq ι] in
/-- Rotating the second displayed hook arrow toward the projective end
returns the first displayed hook arrow. -/
theorem secondArrow_predecessor :
    ((AR.arMeshRotationData σ).arrowOrbitData σ).tau
        ⟨T.secondArrow σ AR, T.b_nonprojective⟩ =
      ⟨T.firstArrow σ AR, T.a_noninjective σ AR⟩ := by
  let O := (AR.arMeshRotationData σ).arrowOrbitData σ
  have hsuccessor : O.tau.symm
      ⟨T.firstArrow σ AR, T.a_noninjective σ AR⟩ =
      ⟨T.secondArrow σ AR, T.b_nonprojective⟩ := by
    apply Subtype.ext
    have haNI : ¬ Injective
        (σ.obj (T.firstArrow σ AR).1.1) := by
      simpa [firstArrow] using T.a_noninjective σ AR
    have hs : O.successor (T.firstArrow σ AR) =
        (O.tau.symm
          ⟨T.firstArrow σ AR, T.a_noninjective σ AR⟩).1 := by
      simp [OpConjecture.BoundaryTranslationChains.Data.successor,
        haNI]
    exact hs.symm.trans (T.firstArrow_successor σ AR)
  have hback := O.tau.apply_symm_apply
    ⟨T.firstArrow σ AR, T.a_noninjective σ AR⟩
  simpa only [hsuccessor] using hback

omit [Fintype ι] [DecidableEq ι] in
/-- The first displayed labelled arrow determines its admissible strip
triple.  Its endpoints recover `a,u`, while injectivity of AR translation
recovers `b` from `τb=a`. -/
theorem firstArrow_injective :
    Function.Injective (fun T : AR.StripAdmissibleTriple σ ↦
      T.firstArrow σ AR) := by
  intro T₁ T₂ h
  have ha : T₁.a = T₂.a :=
    congrArg (fun q : σ.IrreduciblePair ↦ q.1.1) h
  have hu : T₁.u = T₂.u :=
    congrArg (fun q : σ.IrreduciblePair ↦ q.1.2) h
  have hbSubtype :
      (⟨T₁.b, T₁.b_nonprojective⟩ : σ.NonprojectiveLabel) =
        ⟨T₂.b, T₂.b_nonprojective⟩ := by
    apply AR.arTranslation_injective σ
    apply Subtype.ext
    exact T₁.tau_b.trans (ha.trans T₂.tau_b.symm)
  exact StripAdmissibleTriple.ext ha hu
    (congrArg Subtype.val hbSubtype)

omit [Fintype ι] [DecidableEq ι] in
/-- The second displayed labelled arrow also determines its admissible
strip triple: its endpoints recover `u,b`, and `a=τb`. -/
theorem secondArrow_injective :
    Function.Injective (fun T : AR.StripAdmissibleTriple σ ↦
      T.secondArrow σ AR) := by
  intro T₁ T₂ h
  have hu : T₁.u = T₂.u :=
    congrArg (fun q : σ.IrreduciblePair ↦ q.1.1) h
  have hb : T₁.b = T₂.b :=
    congrArg (fun q : σ.IrreduciblePair ↦ q.1.2) h
  have ha : T₁.a = T₂.a := by
    calc
      T₁.a = (AR.arTranslation σ
          ⟨T₁.b, T₁.b_nonprojective⟩).1 := T₁.tau_b.symm
      _ = (AR.arTranslation σ
          ⟨T₂.b, T₂.b_nonprojective⟩).1 := by
        congr 2
        exact Subtype.ext hb
      _ = T₂.a := T₂.tau_b
  exact StripAdmissibleTriple.ext ha hu hb

omit [DecidableEq ι] in
/-- The occurrence immediately preceding a hook determines the hook. -/
theorem hookOrbitAnchor_injective :
    Function.Injective (fun T : AR.StripAdmissibleTriple σ ↦
      T.hookOrbitAnchor σ AR) := by
  intro T₁ T₂ h
  apply firstArrow_injective σ AR
  have hs := congrArg
    ((AR.arMeshRotationData σ).arrowOrbitData σ).successor h
  simpa only [T₁.hookOrbitAnchor_successor σ AR,
    T₂.hookOrbitAnchor_successor σ AR] using hs

omit [DecidableEq ι] in
/-- The hook anchor lies before the last two layers of its arrow-orbit
component, since its next two occurrences are the displayed hook arrows. -/
theorem hookOrbitAnchor_not_twoTarget :
    ¬ ((AR.arMeshRotationData σ).arrowOrbitData σ).TwoTarget
      (T.hookOrbitAnchor σ AR) := by
  let M := AR.arMeshRotationData σ
  let O := M.arrowOrbitData σ
  have hanchorNI : ¬ Injective
      (σ.obj (T.hookOrbitAnchor σ AR).1.1) :=
    (O.tau ⟨T.firstArrow σ AR, T.u_nonprojective⟩).2
  apply O.not_twoTarget_of hanchorNI
  have hback : O.tau.symm
      ⟨T.hookOrbitAnchor σ AR, hanchorNI⟩ =
      ⟨T.firstArrow σ AR, T.u_nonprojective⟩ := by
    exact O.tau.symm_apply_apply
      ⟨T.firstArrow σ AR, T.u_nonprojective⟩
  rw [hback]
  exact T.a_noninjective σ AR

omit [DecidableEq ι] in
/-- The global two-step arrow translation sends a hook anchor to its second
displayed arrow. -/
theorem twoStep_successor_hookOrbitAnchor :
    let O := (AR.arMeshRotationData σ).arrowOrbitData σ
    O.twoStep.successor (T.hookOrbitAnchor σ AR) =
      T.secondArrow σ AR := by
  let M := AR.arMeshRotationData σ
  let O := M.arrowOrbitData σ
  change O.twoStep.successor (T.hookOrbitAnchor σ AR) =
    T.secondArrow σ AR
  rw [O.twoStep_successor_eq (T.hookOrbitAnchor σ AR)
    (T.hookOrbitAnchor_not_twoTarget σ AR),
    T.hookOrbitAnchor_successor σ AR,
    T.firstArrow_successor σ AR]

omit [DecidableEq ι] in
/-- The canonical chain start really ends at the projective hook source. -/
theorem projectiveChainStart_target
    (ha : Projective (σ.obj T.a)) :
    (T.projectiveChainStart σ AR ha).1.2 = T.a := by
  exact T.hookOrbitAnchor_target σ AR

omit [DecidableEq ι] in
/-- The source of the canonical projective-target start is noninjective. -/
theorem projectiveChainStart_source_noninjective
    (ha : Projective (σ.obj T.a)) :
    ¬ Injective (σ.obj (T.projectiveChainStart σ AR ha).1.1) :=
  (((AR.arMeshRotationData σ).arrowOrbitData σ).tau
    ⟨T.firstArrow σ AR, T.u_nonprojective⟩).2

omit [DecidableEq ι] in
/-- The first successor of the canonical chain start is the hook arrow
`a → u`. -/
theorem arrowChainAt_projectiveChainStart_one
    (ha : Projective (σ.obj T.a)) :
    (AR.arMeshRotationData σ).arrowChainAt σ
        (T.projectiveChainStart σ AR ha) 1 =
      T.firstArrow σ AR := by
  exact T.hookOrbitAnchor_successor σ AR

omit [DecidableEq ι] in
include K AR in
/-- A projectively based admissible hook occupies at least the first two
successor positions of its canonical arrow chain. -/
theorem two_le_projectiveChainStart_length
    (ha : Projective (σ.obj T.a)) :
    2 ≤ (AR.arMeshRotationData σ).arrowChainLength σ
      (T.projectiveChainStart σ AR ha)
      (T.projectiveChainStart_target σ AR ha ▸ ha) := by
  let M := AR.arMeshRotationData σ
  let q := T.projectiveChainStart σ AR ha
  let hqP : Projective (σ.obj q.1.2) :=
    T.projectiveChainStart_target σ AR ha ▸ ha
  change 2 ≤ M.arrowChainLength σ q hqP
  have hpos := arrowChainLength_pos (K := K) σ AR q hqP
  change 0 < M.arrowChainLength σ q hqP at hpos
  by_cases htwo : 2 ≤ M.arrowChainLength σ q hqP
  · exact htwo
  · have hlt : M.arrowChainLength σ q hqP < 2 :=
      Nat.lt_of_not_ge htwo
    have hlen : M.arrowChainLength σ q hqP = 1 := by omega
    have hterminal := M.arrowChainAt_length_injectiveSource σ q hqP
    have hone := T.arrowChainAt_projectiveChainStart_one σ AR ha
    change Injective
      (σ.obj (M.arrowChainAt σ q (M.arrowChainLength σ q hqP)).1.1) at hterminal
    rw [hlen, hone] at hterminal
    exact (T.a_noninjective σ AR hterminal).elim

omit [DecidableEq ι] in
include K AR in
/-- The second successor occurrence of a projectively based hook ends at
its displayed third label `b`. -/
theorem arrowChainAt_projectiveChainStart_two_target
    (ha : Projective (σ.obj T.a)) :
    let M := AR.arMeshRotationData σ
    let q := T.projectiveChainStart σ AR ha
    (M.arrowChainAt σ q 2).1.2 = T.b := by
  let M := AR.arMeshRotationData σ
  let q := T.projectiveChainStart σ AR ha
  let hqP : Projective (σ.obj q.1.2) :=
    T.projectiveChainStart_target σ AR ha ▸ ha
  have htwo := T.two_le_projectiveChainStart_length (K := K) σ AR ha
  change 2 ≤ M.arrowChainLength σ q hqP at htwo
  have hone := T.arrowChainAt_projectiveChainStart_one σ AR ha
  have htranslate :=
    M.arTranslation_arrowChainAt_succ_target_eq_source
      σ q hqP (n := 1) (by omega)
  let xNP : σ.NonprojectiveLabel :=
    ⟨(M.arrowChainAt σ q 2).1.2,
      M.arrowChainAt_succ_target_nonprojective
        σ q hqP (n := 1) (by omega)⟩
  have hxTau : (AR.arTranslation σ xNP).1 = T.a := by
    change (M.tau xNP).1 = T.a
    rw [htranslate, hone]
    rfl
  have hx : xNP = ⟨T.b, T.b_nonprojective⟩ := by
    apply AR.arTranslation_injective σ
    apply Subtype.ext
    exact hxTau.trans T.tau_b.symm
  exact congrArg Subtype.val hx

omit [DecidableEq ι] in
include K AR in
/-- A projectively based admissible hook occupies vertex positions
`1,2,3` of its canonical arrow chain as `(a,u,b)`. -/
theorem projectiveChainStart_first_hook_vertices
    (ha : Projective (σ.obj T.a)) :
    let M := AR.arMeshRotationData σ
    let q := T.projectiveChainStart σ AR ha
    let hqP : Projective (σ.obj q.1.2) :=
      T.projectiveChainStart_target σ AR ha ▸ ha
    M.arrowChainVertexAt σ q hqP ⟨1, by
        have h := T.two_le_projectiveChainStart_length (K := K) σ AR ha
        change 2 ≤ M.arrowChainLength σ q hqP at h
        omega⟩ = T.a ∧
      M.arrowChainVertexAt σ q hqP ⟨2, by
        have h := T.two_le_projectiveChainStart_length (K := K) σ AR ha
        change 2 ≤ M.arrowChainLength σ q hqP at h
        omega⟩ = T.u ∧
      M.arrowChainVertexAt σ q hqP ⟨3, by
        have h := T.two_le_projectiveChainStart_length (K := K) σ AR ha
        change 2 ≤ M.arrowChainLength σ q hqP at h
        omega⟩ = T.b := by
  let M := AR.arMeshRotationData σ
  let q := T.projectiveChainStart σ AR ha
  let hqP : Projective (σ.obj q.1.2) :=
    T.projectiveChainStart_target σ AR ha ▸ ha
  have hone := T.arrowChainAt_projectiveChainStart_one σ AR ha
  have htwoTarget :=
    T.arrowChainAt_projectiveChainStart_two_target (K := K) σ AR ha
  change
    (M.arrowChainAt σ q 0).1.2 = T.a ∧
      (M.arrowChainAt σ q 1).1.2 = T.u ∧
      (M.arrowChainAt σ q 2).1.2 = T.b
  refine ⟨?_, ?_, htwoTarget⟩
  · simpa [M, q, ARMeshRotationData.arrowChainAt] using
      T.projectiveChainStart_target σ AR ha
  · simpa [firstArrow] using congrArg
      (fun r : σ.IrreduciblePair ↦ r.1.2) hone

omit [DecidableEq ι] in
include K AR in
/-- The canonical projective-target arrow occurrence determines the
projectively based admissible triple from which it was constructed. -/
theorem projectiveChainStart_injective
    {T₁ T₂ : AR.StripAdmissibleTriple σ}
    (h₁ : Projective (σ.obj T₁.a))
    (h₂ : Projective (σ.obj T₂.a))
    (hstart : T₁.projectiveChainStart σ AR h₁ =
      T₂.projectiveChainStart σ AR h₂) :
    T₁ = T₂ := by
  let M := AR.arMeshRotationData σ
  let q₁ := T₁.projectiveChainStart σ AR h₁
  let q₂ := T₂.projectiveChainStart σ AR h₂
  change q₁ = q₂ at hstart
  have ha : T₁.a = T₂.a := by
    calc
      T₁.a = q₁.1.2 := (T₁.projectiveChainStart_target σ AR h₁).symm
      _ = q₂.1.2 := congrArg (fun q : σ.IrreduciblePair ↦ q.1.2) hstart
      _ = T₂.a := T₂.projectiveChainStart_target σ AR h₂
  have hfirst : T₁.firstArrow σ AR = T₂.firstArrow σ AR := by
    calc
      T₁.firstArrow σ AR = M.arrowChainAt σ q₁ 1 :=
        (T₁.arrowChainAt_projectiveChainStart_one σ AR h₁).symm
      _ = M.arrowChainAt σ q₂ 1 := by rw [hstart]
      _ = T₂.firstArrow σ AR :=
        T₂.arrowChainAt_projectiveChainStart_one σ AR h₂
  have hu : T₁.u = T₂.u := by
    exact congrArg (fun q : σ.IrreduciblePair ↦ q.1.2) hfirst
  have hb : T₁.b = T₂.b := by
    calc
      T₁.b = (M.arrowChainAt σ q₁ 2).1.2 :=
        (T₁.arrowChainAt_projectiveChainStart_two_target
          (K := K) σ AR h₁).symm
      _ = (M.arrowChainAt σ q₂ 2).1.2 := by rw [hstart]
      _ = T₂.b :=
        T₂.arrowChainAt_projectiveChainStart_two_target
          (K := K) σ AR h₂
  exact StripAdmissibleTriple.ext ha hu hb

section ReverseEndpoint

variable {S : Type u} [Ring S] [Algebra K S]
  [FiniteDimensional K S] [IsNoetherianRing S]
  {κ : Type w} [Fintype κ]
  (τ : IndecomposableSkeleton.{u, w, u} S κ)
  (D : AlignedBiduality σ τ)
  (ARτ : τ.FiniteARTranslationData)

include K AR D in
/-- Reading a projectively based admissible hook from the opposite end of
its maximal arrow chain produces a reverse-admissible strip triple.  This
is the precise projective-end/injective-end correspondence used by the
wall term in the signed strip count. -/
def projectiveChainEndReverseTriple
    (ha : Projective (σ.obj T.a)) :
    {U : AR.ReverseStripAdmissibleTriple σ //
      Injective (σ.obj U.a)} := by
  classical
  let M := AR.arMeshRotationData σ
  let q := T.projectiveChainStart σ AR ha
  let hqP : Projective (σ.obj q.1.2) :=
    T.projectiveChainStart_target σ AR ha ▸ ha
  let N := M.arrowChainLength σ q hqP
  have hN : 2 ≤ N := by
    simpa [M, q, hqP, N] using
      T.two_le_projectiveChainStart_length (K := K) σ AR ha
  let αA := M.arrowChainAt σ q N
  let αU := M.arrowChainAt σ q (N - 1)
  let αB := M.arrowChainAt σ q (N - 2)
  let aEnd := αA.1.1
  let uEnd := αU.1.1
  let bEnd := αB.1.1
  have hNm1 : N - 1 < N := by omega
  have hNm2 : N - 2 < N := by omega
  have hUA_source : αA.1.1 = αU.1.2 := by
    have h := M.arrowChainAt_succ_source_eq_target
      σ q hqP (n := N - 1) hNm1
    have hind : N - 1 + 1 = N := by omega
    simpa only [hind, αA, αU] using h
  have hBU_source : αU.1.1 = αB.1.2 := by
    have h := M.arrowChainAt_succ_source_eq_target
      σ q hqP (n := N - 2) hNm2
    have hind : N - 2 + 1 = N - 1 := by omega
    simpa only [hind, αU, αB] using h
  have haI : Injective (σ.obj aEnd) := by
    simpa [aEnd, αA, N] using
      M.arrowChainAt_length_injectiveSource σ q hqP
  have huNI : ¬ Injective (σ.obj uEnd) := by
    simpa [uEnd, αU] using
      M.arrowChainAt_not_injectiveSource_of_lt
        σ q hqP hNm1
  have hbNI : ¬ Injective (σ.obj bEnd) := by
    simpa [bEnd, αB] using
      M.arrowChainAt_not_injectiveSource_of_lt
        σ q hqP hNm2
  have hUA : HasIrreducibleMorphism (σ.obj uEnd) (σ.obj aEnd) := by
    change HasIrreducibleMorphism (σ.obj αU.1.1) (σ.obj αA.1.1)
    rw [hUA_source]
    exact αU.2
  have hBU : HasIrreducibleMorphism (σ.obj bEnd) (σ.obj uEnd) := by
    change HasIrreducibleMorphism (σ.obj αB.1.1) (σ.obj αU.1.1)
    rw [hBU_source]
    exact αB.2
  have haNP : ¬ Projective (σ.obj aEnd) := by
    have h := M.arrowChainAt_succ_target_nonprojective
      σ q hqP (n := N - 2) hNm2
    change ¬ Projective (σ.obj αA.1.1)
    rw [hUA_source]
    have hind : N - 2 + 1 = N - 1 := by omega
    simpa only [hind, αU] using h
  let aNP : σ.NonprojectiveLabel := ⟨aEnd, haNP⟩
  let bNI : σ.NoninjectiveLabel := ⟨bEnd, hbNI⟩
  have htauA : (AR.arTranslation σ aNP).1 = bEnd := by
    have haTargetNP : ¬ Projective (σ.obj αU.1.2) := by
      rw [← hUA_source]
      exact haNP
    let aTargetNP : σ.NonprojectiveLabel := ⟨αU.1.2, haTargetNP⟩
    have h := M.arTranslation_arrowChainAt_succ_target_eq_source
      σ q hqP (n := N - 2) hNm2
    have hind : N - 2 + 1 = N - 1 := by omega
    have haLabels : aNP = aTargetNP := by
      apply Subtype.ext
      exact hUA_source
    rw [haLabels]
    change (M.tau aTargetNP).1 = αB.1.1
    simpa only [aTargetNP, hind, αU, αB] using h
  have hInvB : ((AR.arTranslationEquiv σ).symm bNI).1 = aEnd := by
    have htauSubtype : AR.arTranslationEquiv σ aNP = bNI := by
      apply Subtype.ext
      exact htauA
    have hback := (AR.arTranslationEquiv σ).symm_apply_eq.mpr
      htauSubtype.symm
    exact congrArg Subtype.val hback
  have hUnotB :
      ¬ HasIrreducibleMorphism (σ.obj uEnd) (σ.obj bEnd) := by
    intro hUB
    rcases AR.exists_arTranslation_eq_self_of_two_cycle
        (K := K) σ uEnd bEnd hUB hBU with hUfixed | hBfixed
    · obtain ⟨huNP, htauU⟩ := hUfixed
      have hAU :
          HasIrreducibleMorphism (σ.obj aEnd) (σ.obj uEnd) := by
        apply (AR.arTranslation_incidence σ
          ⟨uEnd, huNP⟩ aEnd).2
        simpa only [htauU] using hUA
      exact haNP (D.projective_of_injective_two_cycle
        (k := K) σ τ ARτ aEnd uEnd haI hAU hUA)
    · obtain ⟨hbNP, htauB⟩ := hBfixed
      let bNP : σ.NonprojectiveLabel := ⟨bEnd, hbNP⟩
      have habNP : aNP = bNP := by
        apply AR.arTranslation_injective σ
        apply Subtype.ext
        exact htauA.trans htauB.symm
      have hab : aEnd = bEnd := congrArg Subtype.val habNP
      exact hbNI (hab ▸ haI)
  have hBnotA :
      ¬ HasIrreducibleMorphism (σ.obj bEnd) (σ.obj aEnd) :=
    AR.no_irreducible_transitiveTriangle (K := K) σ hBU hUA
  exact
    ⟨{ a := aEnd
       u := uEnd
       b := bEnd
       a_ne_u := by
         intro h
         exact σ.hasNoIrreducibleEndomorphism_obj aEnd (by
           simpa [h] using hUA)
       a_ne_b := by
         intro h
         exact hbNI (h ▸ haI)
       u_ne_b := by
         intro h
         exact σ.hasNoIrreducibleEndomorphism_obj uEnd (by
           simpa [h] using hBU)
       u_noninjective := huNI
       b_noninjective := hbNI
       u_to_a := hUA
       b_to_u := hBU
       u_not_to_b := hUnotB
       b_not_to_a := hBnotA
       inverseTau_b := hInvB },
     haI⟩

omit [DecidableEq ι] in
include K AR D in
@[simp]
theorem projectiveChainEndReverseTriple_a
    (ha : Projective (σ.obj T.a)) :
    let M := AR.arMeshRotationData σ
    let q := T.projectiveChainStart σ AR ha
    let hqP : Projective (σ.obj q.1.2) :=
      T.projectiveChainStart_target σ AR ha ▸ ha
    (T.projectiveChainEndReverseTriple
      (K := K) σ AR τ D ARτ ha).1.a =
      (M.arrowChainAt σ q (M.arrowChainLength σ q hqP)).1.1 := by
  rfl

omit [DecidableEq ι] in
include K AR D in
@[simp]
theorem projectiveChainEndReverseTriple_u
    (ha : Projective (σ.obj T.a)) :
    let M := AR.arMeshRotationData σ
    let q := T.projectiveChainStart σ AR ha
    let hqP : Projective (σ.obj q.1.2) :=
      T.projectiveChainStart_target σ AR ha ▸ ha
    let N := M.arrowChainLength σ q hqP
    (T.projectiveChainEndReverseTriple
      (K := K) σ AR τ D ARτ ha).1.u =
      (M.arrowChainAt σ q (N - 1)).1.1 := by
  rfl

omit [DecidableEq ι] in
include K AR D in
/-- The injective-end reverse triple retains enough labelled-arrow data to
recover the original projectively based hook. -/
theorem projectiveChainEndReverseTriple_injective :
    Function.Injective
      (fun X : {T : AR.StripAdmissibleTriple σ //
          Projective (σ.obj T.a)} ↦
        X.1.projectiveChainEndReverseTriple
          (K := K) σ AR τ D ARτ X.2) := by
  classical
  intro X₁ X₂ hend
  apply Subtype.ext
  let T₁ := X₁.1
  let T₂ := X₂.1
  let h₁ : Projective (σ.obj T₁.a) := X₁.2
  let h₂ : Projective (σ.obj T₂.a) := X₂.2
  let M := AR.arMeshRotationData σ
  let B := M.arrowOrbitData σ
  let q₁ := T₁.projectiveChainStart σ AR h₁
  let q₂ := T₂.projectiveChainStart σ AR h₂
  let hq₁ : Projective (σ.obj q₁.1.2) :=
    T₁.projectiveChainStart_target σ AR h₁ ▸ h₁
  let hq₂ : Projective (σ.obj q₂.1.2) :=
    T₂.projectiveChainStart_target σ AR h₂ ▸ h₂
  let N₁ := M.arrowChainLength σ q₁ hq₁
  let N₂ := M.arrowChainLength σ q₂ hq₂
  have hN₁ : 2 ≤ N₁ := by
    simpa [M, q₁, hq₁, N₁, T₁, h₁] using
      T₁.two_le_projectiveChainStart_length (K := K) σ AR h₁
  have hN₂ : 2 ≤ N₂ := by
    simpa [M, q₂, hq₂, N₂, T₂, h₂] using
      T₂.two_le_projectiveChainStart_length (K := K) σ AR h₂
  let αA₁ := M.arrowChainAt σ q₁ N₁
  let αA₂ := M.arrowChainAt σ q₂ N₂
  let αU₁ := M.arrowChainAt σ q₁ (N₁ - 1)
  let αU₂ := M.arrowChainAt σ q₂ (N₂ - 1)
  have haEnd := congrArg
    (fun U : {U : AR.ReverseStripAdmissibleTriple σ //
      Injective (σ.obj U.a)} ↦ U.1.a) hend
  have huEnd := congrArg
    (fun U : {U : AR.ReverseStripAdmissibleTriple σ //
      Injective (σ.obj U.a)} ↦ U.1.u) hend
  change αA₁.1.1 = αA₂.1.1 at haEnd
  change αU₁.1.1 = αU₂.1.1 at huEnd
  have hprev₁ : αA₁.1.1 = αU₁.1.2 := by
    have h := M.arrowChainAt_succ_source_eq_target σ q₁ hq₁
      (n := N₁ - 1) (by omega)
    have hind : N₁ - 1 + 1 = N₁ := by omega
    simpa only [hind, αA₁, αU₁] using h
  have hprev₂ : αA₂.1.1 = αU₂.1.2 := by
    have h := M.arrowChainAt_succ_source_eq_target σ q₂ hq₂
      (n := N₂ - 1) (by omega)
    have hind : N₂ - 1 + 1 = N₂ := by omega
    simpa only [hind, αA₂, αU₂] using h
  have hαU : αU₁ = αU₂ := by
    apply Subtype.ext
    apply Prod.ext
    · exact huEnd
    · exact hprev₁.symm.trans (haEnd.trans hprev₂)
  have hsucc₁ : B.successor αU₁ = αA₁ := by
    change B.successor (B.successor^[N₁ - 1] q₁) =
      B.successor^[N₁] q₁
    have hind : N₁ - 1 + 1 = N₁ := by omega
    rw [← hind]
    exact (Function.iterate_succ_apply'
      B.successor (N₁ - 1) q₁).symm
  have hsucc₂ : B.successor αU₂ = αA₂ := by
    change B.successor (B.successor^[N₂ - 1] q₂) =
      B.successor^[N₂] q₂
    have hind : N₂ - 1 + 1 = N₂ := by omega
    rw [← hind]
    exact (Function.iterate_succ_apply'
      B.successor (N₂ - 1) q₂).symm
  have hαA : αA₁ = αA₂ := by
    rw [← hsucc₁, ← hsucc₂, hαU]
  have hendpoint :
      B.boundaryEndpointEquiv ⟨q₁, hq₁⟩ =
        B.boundaryEndpointEquiv ⟨q₂, hq₂⟩ := by
    apply Subtype.ext
    change αA₁ = αA₂
    exact hαA
  have hqSubtype : (⟨q₁, hq₁⟩ : {q : σ.IrreduciblePair //
      Projective (σ.obj q.1.2)}) = ⟨q₂, hq₂⟩ :=
    B.boundaryEndpointEquiv.injective hendpoint
  have hq : q₁ = q₂ := by
    exact congrArg
      (fun z : {q : σ.IrreduciblePair //
        Projective (σ.obj q.1.2)} ↦ z.1) hqSubtype
  exact T₁.projectiveChainStart_injective
    (K := K) σ AR h₁ h₂ hq

end ReverseEndpoint

end StripAdmissibleTriple

end OpConjecture.IndecomposableSkeleton.FiniteARTranslationData
