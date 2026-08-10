import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.NoncommRing
import OpConjecture.RepresentationDirected.ARWordCombinatorics
import OpConjecture.RepresentationDirected.ARWordPrincipalPositivity

/-!
# The numerical endpoint of mesh strictness

This file isolates the elementary part of Iyama's knitting argument.
If the truncated knitting terms are in fact governed by the untruncated mesh
recurrence (the definition-equivalent numerical consequence of strictness),
then their finite sum is a nonnegative right inverse of the mesh matrix.

The hard implication "positive right additive implies strict" is deliberately
not postulated or renamed here.
-/

noncomputable section

open scoped BigOperators Matrix

namespace OpConjecture.RepresentationDirected.MeshKnitting

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Entrywise nonnegativity for an integral matrix. -/
def EntrywiseNonnegative (A : Matrix ι ι ℤ) : Prop :=
  ∀ a x, 0 ≤ A a x

/-- Entrywise positive part.  This is the truncation in Iyama's knitting
recursion. -/
def positivePart (A : Matrix ι ι ℤ) : Matrix ι ι ℤ :=
  fun a x ↦ max (A a x) 0

/-- The truncated knitting iterates

`Theta 0 = I`, `Theta 1 = theta`, and
`Theta (n+2) = (theta * Theta (n+1) - tau * Theta n)_+`.
-/
def truncatedKnitting (theta tau : Matrix ι ι ℤ) :
    ℕ → Matrix ι ι ℤ
  | 0 => 1
  | 1 => theta
  | n + 2 => positivePart
      (theta * truncatedKnitting theta tau (n + 1) -
        tau * truncatedKnitting theta tau n)

/-- The single deep numerical hypothesis: every raw next knitting term is
already nonnegative, so the positive-part truncation never changes it. -/
def TruncationNeverActivates (theta tau : Matrix ι ι ℤ) : Prop :=
  ∀ n, EntrywiseNonnegative
    (theta * truncatedKnitting theta tau (n + 1) -
      tau * truncatedKnitting theta tau n)

omit [Fintype ι] [DecidableEq ι] in
theorem positivePart_eq_self_of_nonnegative
    {A : Matrix ι ι ℤ} (hA : EntrywiseNonnegative A) :
    positivePart A = A := by
  ext a x
  exact max_eq_left (hA a x)

theorem truncatedKnitting_nonnegative
    (theta tau : Matrix ι ι ℤ)
    (htheta : EntrywiseNonnegative theta) :
    ∀ n, EntrywiseNonnegative (truncatedKnitting theta tau n) := by
  intro n
  rcases n with (_ | _ | n)
  · intro a x
    by_cases hax : a = x
    · subst x
      simp [truncatedKnitting]
    · simp [truncatedKnitting, hax]
  · simpa [truncatedKnitting] using htheta
  · intro a x
    simp [truncatedKnitting, positivePart]

omit [DecidableEq ι] in
theorem mul_nonnegative
    {A B : Matrix ι ι ℤ}
    (hA : EntrywiseNonnegative A) (hB : EntrywiseNonnegative B) :
    EntrywiseNonnegative (A * B) := by
  intro a x
  rw [Matrix.mul_apply]
  exact Finset.sum_nonneg fun y _ ↦ mul_nonneg (hA a y) (hB y x)

omit [Fintype ι] [DecidableEq ι] in
/-- A nonzero entry of `(A - B)_+` must already be a nonzero entry of `A`
when `B` is nonnegative. -/
theorem positivePart_sub_ne_zero_imp_left_ne_zero
    {A B : Matrix ι ι ℤ} (hB : EntrywiseNonnegative B)
    {a x : ι} (h : positivePart (A - B) a x ≠ 0) :
    A a x ≠ 0 := by
  intro hA
  apply h
  change max (A a x - B a x) 0 = 0
  rw [hA, zero_sub]
  exact max_eq_right (neg_nonpos.mpr (hB a x))

theorem truncatedKnitting_step_of_noTruncation
    (theta tau : Matrix ι ι ℤ)
    (hNoTruncation : TruncationNeverActivates theta tau) (n : ℕ) :
    truncatedKnitting theta tau (n + 2) =
      theta * truncatedKnitting theta tau (n + 1) -
        tau * truncatedKnitting theta tau n := by
  rw [truncatedKnitting]
  exact positivePart_eq_self_of_nonnegative (hNoTruncation n)

/-- A terminating, untruncated knitting sequence for the mesh operators
`theta` and `tau`.  In the word application, `theta` is the incoming-arrow
matrix and `tau` is the partial translation matrix. -/
structure IsStrictKnittingSequence
    (theta tau : Matrix ι ι ℤ) (knit : ℕ → Matrix ι ι ℤ) : Prop where
  zero : knit 0 = 1
  one : knit 1 = theta
  step : ∀ n, knit (n + 2) = theta * knit (n + 1) - tau * knit n
  nonnegative : ∀ n a x, 0 ≤ knit n a x
  terminates : ∃ N, knit N = 0 ∧ knit (N + 1) = 0

/-- Partial telescoping of the untruncated knitting recurrence. -/
theorem mesh_mul_partial_knitting_sum
    (theta tau : Matrix ι ι ℤ) (knit : ℕ → Matrix ι ι ℤ)
    (hzero : knit 0 = 1) (hone : knit 1 = theta)
    (hstep : ∀ n, knit (n + 2) = theta * knit (n + 1) - tau * knit n)
    (n : ℕ) :
    (1 - theta + tau) * (∑ i ∈ Finset.range (n + 1), knit i) =
      1 - knit (n + 1) + tau * knit n := by
  induction n with
  | zero =>
      simp [hzero, hone]
  | succ n ih =>
      rw [Finset.sum_range_succ]
      rw [mul_add, ih, hstep n]
      noncomm_ring

/-- The finite sum of a strict knitting sequence is a right inverse of the
mesh matrix. -/
theorem strictKnittingSequence_has_rightInverse
    (theta tau : Matrix ι ι ℤ) (knit : ℕ → Matrix ι ι ℤ)
    (h : IsStrictKnittingSequence theta tau knit) :
    ∃ S : Matrix ι ι ℤ,
      (1 - theta + tau) * S = 1 ∧ ∀ a x, 0 ≤ S a x := by
  obtain ⟨N, hN, hN1⟩ := h.terminates
  refine ⟨∑ i ∈ Finset.range (N + 1), knit i, ?_, ?_⟩
  · rw [mesh_mul_partial_knitting_sum theta tau knit h.zero h.one h.step N,
      hN, hN1]
    simp
  · intro a x
    simp only [Matrix.sum_apply]
    exact Finset.sum_nonneg fun i _ ↦ h.nonnegative i a x

/-- If truncation never activates and the truncated iterates terminate, their
finite sum is a nonnegative right inverse of the mesh matrix.  This is the
finite knitting-algebra milestone; Iyama's theorem is needed only to produce
`hNoTruncation` from a positive right-additive function. -/
theorem truncatedKnitting_sum_is_nonnegative_rightInverse
    (theta tau : Matrix ι ι ℤ)
    (htheta : EntrywiseNonnegative theta)
    (hNoTruncation : TruncationNeverActivates theta tau)
    (hTerminates : ∃ N,
      truncatedKnitting theta tau N = 0 ∧
      truncatedKnitting theta tau (N + 1) = 0) :
    ∃ S : Matrix ι ι ℤ,
      (1 - theta + tau) * S = 1 ∧ EntrywiseNonnegative S := by
  apply strictKnittingSequence_has_rightInverse theta tau
    (truncatedKnitting theta tau)
  exact
    { zero := rfl
      one := rfl
      step := truncatedKnitting_step_of_noTruncation theta tau hNoTruncation
      nonnegative := truncatedKnitting_nonnegative theta tau htheta
      terminates := hTerminates }

/-- A left inverse equals a nonnegative right inverse.  This converts the
row-wise inverse recurrence used in the formalization into entrywise
nonnegativity once strict knitting has supplied the right inverse. -/
theorem leftInverse_nonnegative_of_strictKnitting
    (theta tau M : Matrix ι ι ℤ) (knit : ℕ → Matrix ι ι ℤ)
    (hMK : M * (1 - theta + tau) = 1)
    (h : IsStrictKnittingSequence theta tau knit) :
    ∀ a x, 0 ≤ M a x := by
  obtain ⟨S, hKS, hS⟩ :=
    strictKnittingSequence_has_rightInverse theta tau knit h
  have hMS : M = S := by
    calc
      M = M * 1 := by simp
      _ = M * ((1 - theta + tau) * S) := by rw [hKS]
      _ = (M * (1 - theta + tau)) * S := by rw [Matrix.mul_assoc]
      _ = S := by rw [hMK]; simp
  simpa [hMS] using hS

namespace Word

open OpConjecture.RepresentationDirected

variable {L : Type*}

/-- Incoming-arrow operator of a finite AR word.  Its `x`-th column is the
sum of the middle predecessors of `x`. -/
def incomingMatrix (G : SimpleGraph L) (Q : List L) :
    Matrix (Fin Q.length) (Fin Q.length) ℤ := by
  classical
  exact fun y x ↦ if ARWord.IsMiddle G Q y x then 1 else 0

/-- Partial-translation operator of a finite AR word. -/
def translationMatrix (Q : List L) :
    Matrix (Fin Q.length) (Fin Q.length) ℤ := by
  classical
  exact fun p x ↦ if ARWord.IsPrevious Q p x then 1 else 0

/-- The word mesh operator `I - theta + tau`. -/
def meshMatrix (G : SimpleGraph L) (Q : List L) :
    Matrix (Fin Q.length) (Fin Q.length) ℤ :=
  1 - incomingMatrix G Q + translationMatrix Q

theorem incomingMatrix_nonnegative (G : SimpleGraph L) (Q : List L) :
    EntrywiseNonnegative (incomingMatrix G Q) := by
  classical
  intro y x
  simp only [incomingMatrix]
  split <;> simp

theorem translationMatrix_nonnegative (Q : List L) :
    EntrywiseNonnegative (translationMatrix Q) := by
  classical
  intro p x
  simp only [translationMatrix]
  split <;> simp

/-- `A` is supported at least `gap` positions above the diagonal. -/
def SupportedByPositionGap {m : ℕ} (gap : ℕ)
    (A : Matrix (Fin m) (Fin m) ℤ) : Prop :=
  ∀ a x, A a x ≠ 0 → a.val + gap ≤ x.val

theorem mul_supportedByPositionGap
    {m r s : ℕ} {A B : Matrix (Fin m) (Fin m) ℤ}
    (hA0 : EntrywiseNonnegative A) (hB0 : EntrywiseNonnegative B)
    (hA : SupportedByPositionGap r A)
    (hB : SupportedByPositionGap s B) :
    SupportedByPositionGap (r + s) (A * B) := by
  intro a x hne
  have hnonnegative : 0 ≤ (A * B) a x :=
    mul_nonnegative hA0 hB0 a x
  have hpositive : 0 < (A * B) a x :=
    lt_of_le_of_ne hnonnegative hne.symm
  rw [Matrix.mul_apply] at hpositive
  have hterms : ∀ y ∈ (Finset.univ : Finset (Fin m)),
      0 ≤ A a y * B y x :=
    fun y _ ↦ mul_nonneg (hA0 a y) (hB0 y x)
  obtain ⟨y, _, hypositive⟩ :=
    (Finset.sum_pos_iff_of_nonneg hterms).1 hpositive
  have hAy : A a y ≠ 0 := by
    intro hzero
    simp [hzero] at hypositive
  have hBy : B y x ≠ 0 := by
    intro hzero
    simp [hzero] at hypositive
  have hay := hA a y hAy
  have hyx := hB y x hBy
  omega

theorem positivePart_sub_supportedByPositionGap
    {m gap : ℕ} {A B : Matrix (Fin m) (Fin m) ℤ}
    (hB0 : EntrywiseNonnegative B)
    (hA : SupportedByPositionGap gap A) :
    SupportedByPositionGap gap (positivePart (A - B)) := by
  intro a x hne
  exact hA a x (positivePart_sub_ne_zero_imp_left_ne_zero hB0 hne)

theorem incomingMatrix_supported (G : SimpleGraph L) (Q : List L) :
    SupportedByPositionGap 1 (incomingMatrix G Q) := by
  classical
  intro y x hne
  by_cases hmiddle : ARWord.IsMiddle G Q y x
  · exact hmiddle.2.1
  · simp [incomingMatrix, hmiddle] at hne

/-- Every nonzero entry of the `n`-th truncated word-knitting matrix starts
at least `n` positions before its endpoint. -/
theorem truncatedKnitting_supported (G : SimpleGraph L) (Q : List L) :
    ∀ n, SupportedByPositionGap n
      (truncatedKnitting (incomingMatrix G Q) (translationMatrix Q) n) := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
      intro a x hne
      by_cases hax : a = x
      · subst x
        simp
      · simp [truncatedKnitting, hax] at hne
  | one =>
      simpa only [truncatedKnitting] using incomingMatrix_supported G Q
  | more n hn hn1 =>
      rw [truncatedKnitting]
      apply positivePart_sub_supportedByPositionGap
      · exact mul_nonnegative (translationMatrix_nonnegative Q)
          (truncatedKnitting_nonnegative
            (incomingMatrix G Q) (translationMatrix Q)
            (incomingMatrix_nonnegative G Q) n)
      · simpa only [Nat.one_add] using
          mul_supportedByPositionGap
            (incomingMatrix_nonnegative G Q)
            (truncatedKnitting_nonnegative
              (incomingMatrix G Q) (translationMatrix Q)
              (incomingMatrix_nonnegative G Q) (n + 1))
            (incomingMatrix_supported G Q) hn1

/-- Strict increase of word positions makes the truncated knitting recursion
terminate automatically, independently of strictness/no-truncation. -/
theorem truncatedKnitting_terminates (G : SimpleGraph L) (Q : List L) :
    ∃ N,
      truncatedKnitting (incomingMatrix G Q) (translationMatrix Q) N = 0 ∧
      truncatedKnitting (incomingMatrix G Q) (translationMatrix Q)
        (N + 1) = 0 := by
  refine ⟨Q.length, ?_, ?_⟩
  · ext a x
    by_contra hne
    have hgap : a.val + Q.length ≤ x.val :=
      truncatedKnitting_supported G Q Q.length a x hne
    omega
  · ext a x
    by_contra hne
    have hgap : a.val + (Q.length + 1) ≤ x.val :=
      truncatedKnitting_supported G Q (Q.length + 1) a x hne
    omega

theorem mul_incomingMatrix_apply
    (G : SimpleGraph L) (Q : List L)
    (M : Matrix (Fin Q.length) (Fin Q.length) ℤ)
    (a x : Fin Q.length) :
    (M * incomingMatrix G Q) a x =
      PrincipalPositivity.scalarMiddleSum G Q (M a) x := by
  classical
  simp [Matrix.mul_apply, incomingMatrix,
    PrincipalPositivity.scalarMiddleSum, Finset.sum_filter]

theorem mul_translationMatrix_apply_of_previous
    (Q : List L) (M : Matrix (Fin Q.length) (Fin Q.length) ℤ)
    (a p x : Fin Q.length) (hp : ARWord.IsPrevious Q p x) :
    (M * translationMatrix Q) a x = M a p := by
  classical
  rw [Matrix.mul_apply, Fintype.sum_eq_single p]
  · simp [translationMatrix, hp]
  · intro y hyp
    have hy : ¬ ARWord.IsPrevious Q y x := by
      intro hy
      exact hyp (ARWord.isPrevious_unique hy hp)
    simp [translationMatrix, hy]

theorem mul_translationMatrix_apply_of_noPrevious
    (Q : List L) (M : Matrix (Fin Q.length) (Fin Q.length) ℤ)
    (a x : Fin Q.length) (hfirst : ¬ ∃ p, ARWord.IsPrevious Q p x) :
    (M * translationMatrix Q) a x = 0 := by
  classical
  rw [Matrix.mul_apply]
  apply Fintype.sum_eq_zero
  intro p
  have hp : ¬ ARWord.IsPrevious Q p x := fun hp ↦ hfirst ⟨p, hp⟩
  simp [translationMatrix, hp]

theorem mul_meshMatrix_apply_of_previous
    (G : SimpleGraph L) (Q : List L)
    (M : Matrix (Fin Q.length) (Fin Q.length) ℤ)
    (a p x : Fin Q.length) (hp : ARWord.IsPrevious Q p x) :
    (M * meshMatrix G Q) a x =
      M a x - PrincipalPositivity.scalarMiddleSum G Q (M a) x + M a p := by
  rw [meshMatrix, mul_add, mul_sub, mul_one]
  change M a x - (M * incomingMatrix G Q) a x +
    (M * translationMatrix Q) a x = _
  rw [mul_incomingMatrix_apply,
    mul_translationMatrix_apply_of_previous Q M a p x hp]

theorem mul_meshMatrix_apply_of_noPrevious
    (G : SimpleGraph L) (Q : List L)
    (M : Matrix (Fin Q.length) (Fin Q.length) ℤ)
    (a x : Fin Q.length) (hfirst : ¬ ∃ p, ARWord.IsPrevious Q p x) :
    (M * meshMatrix G Q) a x =
      M a x - PrincipalPositivity.scalarMiddleSum G Q (M a) x := by
  rw [meshMatrix, mul_add, mul_sub, mul_one]
  change M a x - (M * incomingMatrix G Q) a x +
    (M * translationMatrix Q) a x = _
  rw [mul_incomingMatrix_apply,
    mul_translationMatrix_apply_of_noPrevious Q M a x hfirst, add_zero]

/-- The literal row recurrence in the production formalization is exactly the
left-inverse equation for the word mesh matrix. -/
theorem satisfiesWordMeshInverseRecurrence_iff_mul_meshMatrix
    (G : SimpleGraph L) (Q : List L)
    (M : Matrix (Fin Q.length) (Fin Q.length) ℤ) :
    PrincipalPositivity.SatisfiesWordMeshInverseRecurrence G Q M ↔
      M * meshMatrix G Q = 1 := by
  constructor
  · intro hrec
    ext a x
    by_cases hprevious : ∃ p, ARWord.IsPrevious Q p x
    · obtain ⟨p, hp⟩ := hprevious
      rw [mul_meshMatrix_apply_of_previous G Q M a p x hp,
        Matrix.one_apply]
      have h := (hrec a x).1 p hp
      omega
    · rw [mul_meshMatrix_apply_of_noPrevious G Q M a x hprevious,
        Matrix.one_apply]
      have h := (hrec a x).2 hprevious
      omega
  · intro hmatrix a x
    refine ⟨?_, ?_⟩
    · intro p hp
      have h := congr_fun (congr_fun hmatrix a) x
      rw [mul_meshMatrix_apply_of_previous G Q M a p x hp,
        Matrix.one_apply] at h
      omega
    · intro hfirst
      have h := congr_fun (congr_fun hmatrix a) x
      rw [mul_meshMatrix_apply_of_noPrevious G Q M a x hfirst,
        Matrix.one_apply] at h
      omega

/-- Word-specialized finite knitting endpoint.  The only non-elementary input
is `hNoTruncation`; for the paper it is supplied by Iyama's theorem that a
positive right-additive function makes the finite translation quiver strict.
-/
theorem knitting_sum_is_nonnegative_wordMeshInverse
    (G : SimpleGraph L) (Q : List L)
    (hNoTruncation : TruncationNeverActivates
      (incomingMatrix G Q) (translationMatrix Q))
    (hTerminates : ∃ N,
      truncatedKnitting (incomingMatrix G Q) (translationMatrix Q) N = 0 ∧
      truncatedKnitting (incomingMatrix G Q) (translationMatrix Q)
        (N + 1) = 0) :
    ∃ S : Matrix (Fin Q.length) (Fin Q.length) ℤ,
      meshMatrix G Q * S = 1 ∧ EntrywiseNonnegative S := by
  simpa only [meshMatrix] using
    truncatedKnitting_sum_is_nonnegative_rightInverse
      (incomingMatrix G Q) (translationMatrix Q)
      (incomingMatrix_nonnegative G Q) hNoTruncation hTerminates

/-- Any row-wise left inverse of the word mesh matrix is therefore the same
nonnegative matrix. -/
theorem leftInverse_wordMesh_nonnegative
    (G : SimpleGraph L) (Q : List L)
    (M : Matrix (Fin Q.length) (Fin Q.length) ℤ)
    (hM : M * meshMatrix G Q = 1)
    (hNoTruncation : TruncationNeverActivates
      (incomingMatrix G Q) (translationMatrix Q))
    (hTerminates : ∃ N,
      truncatedKnitting (incomingMatrix G Q) (translationMatrix Q) N = 0 ∧
      truncatedKnitting (incomingMatrix G Q) (translationMatrix Q)
        (N + 1) = 0) :
    EntrywiseNonnegative M := by
  obtain ⟨S, hSInverse, hSNonnegative⟩ :=
    knitting_sum_is_nonnegative_wordMeshInverse
      G Q hNoTruncation hTerminates
  have hMS : M = S := by
    calc
      M = M * 1 := by simp
      _ = M * (meshMatrix G Q * S) := by rw [hSInverse]
      _ = (M * meshMatrix G Q) * S := by rw [Matrix.mul_assoc]
      _ = S := by rw [hM]; simp
  simpa only [hMS] using hSNonnegative

/-- Fully word-specialized endpoint: after automatic termination and the
row-recurrence/matrix identification, no-truncation is the only remaining
hypothesis needed for nonnegativity. -/
theorem satisfiesWordMeshInverseRecurrence_nonnegative_of_noTruncation
    (G : SimpleGraph L) (Q : List L)
    (M : Matrix (Fin Q.length) (Fin Q.length) ℤ)
    (hNoTruncation : TruncationNeverActivates
      (incomingMatrix G Q) (translationMatrix Q))
    (hRecurrence :
      PrincipalPositivity.SatisfiesWordMeshInverseRecurrence G Q M) :
    EntrywiseNonnegative M := by
  apply leftInverse_wordMesh_nonnegative G Q M
  · exact
      (satisfiesWordMeshInverseRecurrence_iff_mul_meshMatrix G Q M).mp
        hRecurrence
  · exact hNoTruncation
  · exact truncatedKnitting_terminates G Q

end Word

end OpConjecture.RepresentationDirected.MeshKnitting
