import OpConjecture.RepresentationTheory.MoritaBasicizationInterface

/-!
# Square-zero Jacobson radical in idempotent corners

For an idempotent `e` in a ring `A`, the Jacobson radical of `eAe` embeds in
the Jacobson radical of `A`.  The proof is the elementary block-triangular
inverse argument.  Consequently a square-zero Jacobson radical remains
square-zero after passing to any idempotent corner, in particular to the
basic corner used in Morita reduction.
-/

set_option autoImplicit false

noncomputable section

namespace OpConjecture.MoritaBasicizationInterface

universe u

variable {A : Type u} [Ring A]
variable {e : A} (he : IsIdempotentElem e)

/-- The underlying element of a radical element of `eAe` lies in the
Jacobson radical of `A`. -/
theorem corner_jacobson_val_mem
    (x : he.Corner) (hx : x ∈ Ring.jacobson he.Corner) :
    x.1 ∈ Ring.jacobson A := by
  rw [← Ideal.jacobson_bot, Ideal.mem_jacobson_iff]
  intro a
  let y : he.Corner := ⟨e * a * e, ⟨a, rfl⟩⟩
  have hx' : x ∈ Ideal.jacobson (⊥ : Ideal he.Corner) := by
    simpa only [Ideal.jacobson_bot] using hx
  obtain ⟨d, hd⟩ := (Ideal.mem_jacobson_iff.mp hx') y
  have hdEq : d * y * x + d - 1 = 0 := by
    simpa only [Submodule.mem_bot] using hd
  have hdVal := congrArg Subtype.val hdEq
  change d.1 * (e * a * e) * x.1 + d.1 - e = 0 at hdVal
  have hxCorner := (Subsemigroup.mem_corner_iff he).mp x.property
  have hdCorner := (Subsemigroup.mem_corner_iff he).mp d.property
  have hprod : d.1 * (e * a * e) * x.1 = d.1 * a * x.1 := by
    calc
      d.1 * (e * a * e) * x.1 =
          ((d.1 * e) * a) * (e * x.1) := by noncomm_ring
      _ = d.1 * a * x.1 := by rw [hdCorner.2, hxCorner.1]
  rw [hprod] at hdVal
  have hdax : d.1 + d.1 * a * x.1 = e := by
    rw [add_comm]
    exact sub_eq_zero.mp hdVal
  let z : A :=
    d.1 + (1 - e) - (1 - e) * a * x.1 * d.1
  refine ⟨z, ?_⟩
  rw [Submodule.mem_bot]
  have hbe : (1 - e) * a * x.1 * e = (1 - e) * a * x.1 := by
    simp only [mul_assoc, hxCorner.2]
  have hz : z * (1 + a * x.1) = 1 := by
    calc
      z * (1 + a * x.1) =
          (d.1 + d.1 * a * x.1) + (1 - e) +
            (1 - e) * a * x.1 -
              ((1 - e) * a * x.1) *
                (d.1 + d.1 * a * x.1) := by
        simp only [z]
        noncomm_ring
      _ = e + (1 - e) + (1 - e) * a * x.1 -
            ((1 - e) * a * x.1) * e := by rw [hdax]
      _ = 1 := by rw [hbe]; noncomm_ring
  calc
    z * a * x.1 + z - 1 = z * (1 + a * x.1) - 1 := by
      noncomm_ring
    _ = 0 := by rw [hz, sub_self]

/-- A square-zero Jacobson radical stays square-zero in every idempotent
corner. -/
theorem corner_jacobson_sq_eq_bot
    (hJ : (Ring.jacobson A) ^ 2 = ⊥) :
    (Ring.jacobson he.Corner) ^ 2 = ⊥ := by
  rw [show (2 : ℕ) = 1 + 1 by omega, Submodule.pow_succ,
    Submodule.pow_one]
  apply le_antisymm
  · rw [Ideal.mul_le]
    intro x hx y hy
    rw [Submodule.mem_bot]
    apply Subtype.ext
    change x.1 * y.1 = 0
    have hxA : x.1 ∈ Ring.jacobson A :=
      corner_jacobson_val_mem he x hx
    have hyA : y.1 ∈ Ring.jacobson A :=
      corner_jacobson_val_mem he y hy
    have hxy : x.1 * y.1 ∈ (Ring.jacobson A) ^ 2 := by
      rw [show (2 : ℕ) = 1 + 1 by omega, Submodule.pow_succ,
        Submodule.pow_one]
      exact Ideal.mul_mem_mul hxA hyA
    rw [hJ] at hxy
    simpa using hxy
  · exact bot_le

end OpConjecture.MoritaBasicizationInterface
