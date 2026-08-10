import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Tactic.NoncommRing

/-!
# Two-vertex Peirce connectedness

This file proves the ring-theoretic core of the theorem that a block-connected
split-basic algebra has connected Gabriel support.  For two complementary
nonzero idempotents, if both off-diagonal Peirce corners vanish in `J / J²`,
then nilpotence of `J` forces the corners themselves to vanish and hence makes
one idempotent central.  When the full off-diagonal corners lie in `J`, block
connectedness therefore produces a nonzero off-diagonal cotangent class in at
least one orientation.

Identifying those cotangent classes with Ext-Gabriel arrows is deliberately
kept as a separate split-basic Gabriel-realization input.
-/

noncomputable section

namespace QuotientSubmoduleEquidistribution.TwoVertexPeirceConnectedness

universe u

variable {R : Type u} [Ring R]

/-- If a two-sided ideal `J` contains an off-diagonal Peirce corner and that
corner vanishes modulo `J²`, multiplication by the corner idempotents raises
the `J`-adic filtration by one. -/
theorem peirce_corner_mem_pow_succ
    (J : Ideal R) [J.IsTwoSided]
    (e f : R)
    (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f)
    (hsum : e + f = 1)
    (hResidue : ∀ r : R, e * r * f ∈ J)
    (hCotangent : ∀ r ∈ J, e * r * f ∈ J ^ 2) :
    ∀ n : ℕ, ∀ r ∈ J ^ n, e * r * f ∈ J ^ (n + 1) := by
  intro n
  induction n with
  | zero =>
      intro r _hr
      rw [zero_add, Submodule.pow_one]
      exact hResidue r
  | succ n ih =>
      intro r hr
      change r ∈ J ^ n * J at hr
      refine Submodule.mul_induction_on' (M := J ^ n) (N := J)
        (C := fun r hr ↦ e * r * f ∈ J ^ (n + 1 + 1)) ?generator ?add hr
      · intro x hx y hy
        have hxe : e * x * e ∈ J ^ n := by
          exact Ideal.mul_mem_right e _ (Ideal.mul_mem_left _ e hx)
        have hyf : e * y * f ∈ J ^ 2 := hCotangent y hy
        have hxf : e * x * f ∈ J ^ (n + 1) := ih x hx
        have hyff : f * y * f ∈ J :=
          Ideal.mul_mem_right f _ (Ideal.mul_mem_left _ f hy)
        have hleft : (e * x * e) * (e * y * f) ∈ J ^ (n + 1 + 1) := by
          rw [show n + 1 + 1 = n + 2 by omega,
            Ideal.IsTwoSided.pow_add n 2]
          exact Ideal.mul_mem_mul hxe hyf
        have hright : (e * x * f) * (f * y * f) ∈ J ^ (n + 1 + 1) := by
          rw [show n + 1 + 1 = (n + 1) + 1 by omega,
            Ideal.IsTwoSided.pow_add (n + 1) 1, Submodule.pow_one]
          exact Ideal.mul_mem_mul hxf hyff
        have hleftInsert :
            (e * x * e) * (e * y * f) =
              (e * x * e) * (y * f) := by
          calc
            (e * x * e) * (e * y * f) =
                (e * x * (e * e)) * (y * f) := by
              noncomm_ring
            _ = (e * x * e) * (y * f) := by rw [he.eq]
        have hrightInsert :
            (e * x * f) * (f * y * f) =
              (e * x * f) * (y * f) := by
          calc
            (e * x * f) * (f * y * f) =
                (e * x * (f * f)) * (y * f) := by
              noncomm_ring
            _ = (e * x * f) * (y * f) := by rw [hf.eq]
        have hdecomp :
            e * (x * y) * f =
              (e * x * e) * (e * y * f) +
                (e * x * f) * (f * y * f) := by
          calc
            e * (x * y) * f = e * x * (e + f) * y * f := by
              rw [hsum]
              simp [mul_assoc]
            _ = (e * x * e) * (y * f) +
                (e * x * f) * (y * f) := by
              noncomm_ring
            _ = (e * x * e) * (e * y * f) +
                (e * x * f) * (f * y * f) := by
              rw [hleftInsert, hrightInsert]
        rw [hdecomp]
        exact Ideal.add_mem _ hleft hright
      · intro x hx y hy hx' hy'
        rw [mul_add, add_mul]
        exact Ideal.add_mem _ hx' hy'

/-- Nilpotence kills an off-diagonal Peirce corner once the preceding
filtration-raising hypotheses hold. -/
theorem peirce_corner_eq_zero_of_isNilpotent
    (J : Ideal R) [J.IsTwoSided]
    (e f : R)
    (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f)
    (hsum : e + f = 1)
    (hResidue : ∀ r : R, e * r * f ∈ J)
    (hCotangent : ∀ r ∈ J, e * r * f ∈ J ^ 2)
    (hNilpotent : IsNilpotent J) :
    ∀ r : R, e * r * f = 0 := by
  intro r
  obtain ⟨N, hN⟩ := hNilpotent
  let x := e * r * f
  have hxpow : ∀ n : ℕ, x ∈ J ^ n := by
    intro n
    induction n with
    | zero =>
        rw [Submodule.pow_zero, Ideal.one_eq_top]
        exact Submodule.mem_top
    | succ n ih =>
        have hraise :=
          peirce_corner_mem_pow_succ J e f he hf hsum hResidue hCotangent
            n x ih
        have hcorner : e * x * f = x := by
          dsimp only [x]
          calc
            e * (e * r * f) * f = (e * e) * r * (f * f) := by
              noncomm_ring
            _ = e * r * f := by rw [he.eq, hf.eq]
        simpa [Nat.succ_eq_add_one, hcorner] using hraise
  have hxbot : x ∈ (⊥ : Ideal R) := by
    simpa only [hN, Ideal.zero_eq_bot] using hxpow N
  exact hxbot

/-- In a nilpotent extension, vanishing of both off-diagonal cotangent
corners makes either vertex idempotent central. -/
theorem isMulCentral_of_peirce_cotangent_vanishes
    (J : Ideal R) [J.IsTwoSided]
    (e f : R)
    (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f)
    (hsum : e + f = 1)
    (hResidueEF : ∀ r : R, e * r * f ∈ J)
    (hResidueFE : ∀ r : R, f * r * e ∈ J)
    (hCotangentEF : ∀ r ∈ J, e * r * f ∈ J ^ 2)
    (hCotangentFE : ∀ r ∈ J, f * r * e ∈ J ^ 2)
    (hNilpotent : IsNilpotent J) :
    IsMulCentral e := by
  have hEF : ∀ r : R, e * r * f = 0 :=
    peirce_corner_eq_zero_of_isNilpotent J e f he hf hsum
      hResidueEF hCotangentEF hNilpotent
  have hFE : ∀ r : R, f * r * e = 0 :=
    peirce_corner_eq_zero_of_isNilpotent J f e hf he
      (by simpa [add_comm] using hsum) hResidueFE hCotangentFE hNilpotent
  refine ⟨?_, fun _ _ ↦ (mul_assoc _ _ _).symm,
    fun _ _ ↦ mul_assoc _ _ _⟩
  intro r
  rw [commute_iff_eq]
  calc
    e * r = e * r * (e + f) := by rw [hsum, mul_one]
    _ = e * r * e := by rw [mul_add, hEF, add_zero]
    _ = (e + f) * r * e := by
      simp only [add_mul, hFE, add_zero]
    _ = r * e := by rw [hsum, one_mul]

/-- A nontrivial block-connected Peirce pair has a nonzero off-diagonal
class in `J / J²` in at least one orientation. -/
theorem exists_cross_cotangent_of_blockConnected
    (J : Ideal R) [J.IsTwoSided]
    (e f : R)
    (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f)
    (hsum : e + f = 1)
    (he0 : e ≠ 0)
    (hf0 : f ≠ 0)
    (hConnected : ∀ z : R, IsIdempotentElem z → IsMulCentral z →
      z = 0 ∨ z = 1)
    (hResidueEF : ∀ r : R, e * r * f ∈ J)
    (hResidueFE : ∀ r : R, f * r * e ∈ J)
    (hNilpotent : IsNilpotent J) :
    (∃ r ∈ J, e * r * f ∉ J ^ 2) ∨
      ∃ r ∈ J, f * r * e ∉ J ^ 2 := by
  classical
  by_contra hNoCross
  push Not at hNoCross
  have hCentral : IsMulCentral e :=
    isMulCentral_of_peirce_cotangent_vanishes J e f he hf hsum
      hResidueEF hResidueFE hNoCross.1 hNoCross.2 hNilpotent
  rcases hConnected e he hCentral with heZero | heOne
  · exact he0 heZero
  · apply hf0
    have hcancel : 1 + f = 1 + 0 := by
      simpa only [heOne, add_zero] using hsum
    exact add_left_cancel hcancel

/-- Artinian specialization at the actual Jacobson radical, assuming both
full off-diagonal corners lie in that radical. -/
theorem exists_cross_jacobson_cotangent_of_blockConnected
    [IsArtinianRing R]
    (e f : R)
    (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f)
    (hsum : e + f = 1)
    (he0 : e ≠ 0)
    (hf0 : f ≠ 0)
    (hConnected : ∀ z : R, IsIdempotentElem z → IsMulCentral z →
      z = 0 ∨ z = 1)
    (hResidueEF : ∀ r : R, e * r * f ∈ Ring.jacobson R)
    (hResidueFE : ∀ r : R, f * r * e ∈ Ring.jacobson R) :
    (∃ r ∈ Ring.jacobson R,
      e * r * f ∉ (Ring.jacobson R) ^ 2) ∨
      ∃ r ∈ Ring.jacobson R,
        f * r * e ∉ (Ring.jacobson R) ^ 2 := by
  apply exists_cross_cotangent_of_blockConnected
    (Ring.jacobson R) e f he hf hsum he0 hf0 hConnected
      hResidueEF hResidueFE
  rw [← Ideal.jacobson_bot]
  exact IsArtinianRing.isNilpotent_jacobson_bot

end QuotientSubmoduleEquidistribution.TwoVertexPeirceConnectedness
