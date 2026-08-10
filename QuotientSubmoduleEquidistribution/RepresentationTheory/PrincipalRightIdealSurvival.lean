import QuotientSubmoduleEquidistribution.RepresentationTheory.CyclicRightIdeal

/-!
# Survival from isomorphic cyclic right ideals

This file isolates the abstract finite-dimensional argument used to prove
that a distinguished radical-square element survives a quotient.  It does
not construct a quiver algebra or classify modules.

The key point is that an inclusion `aA ⊆ xA` between isomorphic cyclic
right ideals is an equality by finite-dimensionality.  If `a ∈ J²` but
`x ∉ J²`, such an inclusion is impossible.  A relation
`a = x * t + a * s` with `s ∈ J` produces the inclusion because `1 - s`
is a unit in an Artinian ring.
-/

noncomputable section

open CategoryTheory MulOpposite

namespace QuotientSubmoduleEquidistribution.Tsukamoto

universe u v

variable {K : Type u} {A : Type v}
  [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]

/-- In a finite-dimensional algebra, an inclusion between isomorphic
principal right ideals is equality. -/
theorem principalRightIdeal_eq_of_le_of_iso
    (K : Type u) [Field K] [Algebra K A] [FiniteDimensional K A]
    {a x : A}
    (hle : principalRightIdeal a ≤ principalRightIdeal x)
    (e : cyclicRightIdealFG a ≅ cyclicRightIdealFG x) :
    principalRightIdeal a = principalRightIdeal x := by
  let E :
      (principalRightIdeal a).restrictScalars K ≃ₗ[Aᵐᵒᵖ]
        (principalRightIdeal x).restrictScalars K :=
    (principalRightIdeal a).restrictScalarsEquiv K ≪≫ₗ
      FGModuleCat.isoToLinearEquiv e ≪≫ₗ
        ((principalRightIdeal x).restrictScalarsEquiv K).symm
  let eK :
      (principalRightIdeal a).restrictScalars K ≃ₗ[K]
        (principalRightIdeal x).restrictScalars K :=
    E.restrictScalars K
  apply Submodule.restrictScalars_injective K
  apply Submodule.eq_of_le_of_finrank_eq
  · exact hle
  · exact eK.finrank_eq

/-- If `I` is two-sided and contains `a`, then every element of `aA`
belongs to `I`. -/
theorem unop_mem_twoSidedIdeal_of_mem_principalRightIdeal
    (I : Ideal A) [I.IsTwoSided]
    {a : A} (haI : a ∈ I)
    {y : Aᵐᵒᵖ} (hy : y ∈ principalRightIdeal a) :
    unop y ∈ I := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
      rw [Set.mem_singleton_iff.mp hy]
      simpa using haI
  | zero => simp
  | add y z _ _ hy hz =>
      simpa using I.add_mem hy hz
  | smul r y _ hy =>
      change unop (r * y) ∈ I
      rw [unop_mul]
      exact I.mul_mem_right (unop r) hy

/-- A right multiple identity `a = x * r` induces `aA ⊆ xA`. -/
theorem principalRightIdeal_le_of_eq_mul
    {a x r : A} (h : a = x * r) :
    principalRightIdeal a ≤ principalRightIdeal x := by
  unfold principalRightIdeal
  apply Ideal.span_le.mpr
  rintro y hy
  rw [Set.mem_singleton_iff] at hy
  subst y
  rw [h, op_mul]
  exact Ideal.mul_mem_left _ _
    (Ideal.subset_span (Set.mem_singleton (op x)))

/-- In an Artinian ring, `1 - s` is a unit for every `s` in the Jacobson
radical.  The proof uses nilpotence of the radical and is valid without a
commutativity hypothesis. -/
theorem isUnit_one_sub_of_mem_jacobson
    [IsArtinianRing A]
    (s : A) (hs : s ∈ Ring.jacobson A) :
    IsUnit (1 - s) := by
  obtain ⟨n, hn⟩ :=
    (IsArtinianRing.isNilpotent_jacobson_bot (R := A))
  have hn' : (Ring.jacobson A) ^ n = 0 := by
    simpa only [Ideal.jacobson_bot] using hn
  have hsPowMem : s ^ n ∈ (Ring.jacobson A) ^ n :=
    Ideal.pow_mem_pow hs n
  have hsPow : s ^ n = 0 := by
    rw [hn'] at hsPowMem
    exact Ideal.mem_bot.mp hsPowMem
  exact (show IsNilpotent s from ⟨n, hsPow⟩).isUnit_one_sub

/-- The paper's radical rearrangement
`a = x * t + a * s`, with `s ∈ J(A)`, implies `aA ⊆ xA`. -/
theorem principalRightIdeal_le_of_jacobson_rearrangement
    [IsArtinianRing A]
    {a x t s : A}
    (hs : s ∈ Ring.jacobson A)
    (h : a = x * t + a * s) :
    principalRightIdeal a ≤ principalRightIdeal x := by
  have hUnit : IsUnit (1 - s) :=
    isUnit_one_sub_of_mem_jacobson (A := A) s hs
  obtain ⟨w, hw⟩ := hUnit
  have haw : a * (w : A) = x * t := by
    rw [hw]
    calc
      a * (1 - s) = a - a * s := by rw [mul_sub, mul_one]
      _ = (x * t + a * s) - a * s :=
        congrArg (fun z => z - a * s) h
      _ = x * t := add_sub_cancel_right _ _
  have har : a = x * (t * (↑(w⁻¹) : A)) := by
    calc
      a = (a * (w : A)) * (↑(w⁻¹) : A) := by simp
      _ = (x * t) * (↑(w⁻¹) : A) := by rw [haw]
      _ = x * (t * (↑(w⁻¹) : A)) := by rw [mul_assoc]
  exact principalRightIdeal_le_of_eq_mul har

/-- Abstract quotient-survival contradiction.  Isomorphic cyclic right
ideals cannot satisfy the paper's radical rearrangement when their
generators lie on opposite sides of `J(A)²`. -/
theorem false_of_cyclicRightIdeal_iso_of_jacobsonSquare_separation
    (K : Type u) [Field K] [Algebra K A] [FiniteDimensional K A]
    {a x t s : A}
    (hIso : cyclicRightIdealFG a ≅ cyclicRightIdealFG x)
    (hs : s ∈ Ring.jacobson A)
    (hEq : a = x * t + a * s)
    (haJ2 : a ∈ (Ring.jacobson A) ^ 2)
    (hxJ2 : x ∉ (Ring.jacobson A) ^ 2) :
    False := by
  letI : IsArtinianRing A := IsArtinianRing.of_finite K A
  have hle : principalRightIdeal a ≤ principalRightIdeal x :=
    principalRightIdeal_le_of_jacobson_rearrangement hs hEq
  have hideals : principalRightIdeal a = principalRightIdeal x :=
    principalRightIdeal_eq_of_le_of_iso K hle hIso
  have hxMemX : op x ∈ principalRightIdeal x :=
    Ideal.subset_span (Set.mem_singleton (op x))
  have hxMemA : op x ∈ principalRightIdeal a := by
    rw [hideals]
    exact hxMemX
  apply hxJ2
  exact unop_mem_twoSidedIdeal_of_mem_principalRightIdeal
    ((Ring.jacobson A) ^ 2) haJ2 hxMemA

end QuotientSubmoduleEquidistribution.Tsukamoto
