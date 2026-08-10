import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Artinian.Module

/-!
# A concrete algebra model for the live-path lollipop

The algebra is a triangular five-coordinate model with vertex-one corner
the dual numbers, vertex-two corner `K`, and a two-dimensional arrow corner
which is regular on the right over the dual numbers.  Its displayed
generators satisfy `x² = 0` and `a*x = u ≠ 0`.

This file does not yet assert a universal bound-path-algebra presentation or
identify the Jacobson radical and primitive idempotents.
-/

noncomputable section

open scoped RightActions

namespace OpConjecture.LollipopConcrete.B1

universe u

variable (K : Type u) [Field K]

/-- The vertex-one loop corner `K[ε]/(ε²)`. -/
abbrev LoopAlgebra := TrivSqZeroExt K K

/-- The diagonal subalgebra: dual numbers at vertex one and `K` at vertex two. -/
abbrev BaseAlgebra := LoopAlgebra K × K

/-- The arrow corner, with basis `a, a*x`, identified with the regular right
module over the loop corner. -/
abbrev ArrowCorner := LoopAlgebra K

/-- Left multiplication on the arrow corner only sees vertex two. -/
def leftArrowCharacter : BaseAlgebra K →+* K :=
  RingHom.snd (LoopAlgebra K) K

instance : Module (BaseAlgebra K) (ArrowCorner K) :=
  Module.compHom (ArrowCorner K) (leftArrowCharacter K)

/-- Right multiplication on the arrow corner sees the dual-number corner at
vertex one. -/
def rightArrowCharacter : (BaseAlgebra K)ᵐᵒᵖ →+* LoopAlgebra K :=
  (RingHom.fst (LoopAlgebra K) K).fromOpposite fun _ _ => Commute.all _ _

instance : Module (BaseAlgebra K)ᵐᵒᵖ (ArrowCorner K) :=
  Module.compHom (ArrowCorner K) (rightArrowCharacter K)

@[simp] theorem left_smul_fst (r : BaseAlgebra K) (m : ArrowCorner K) :
    TrivSqZeroExt.fst (r • m) = r.2 * TrivSqZeroExt.fst m := rfl

@[simp] theorem left_smul_snd (r : BaseAlgebra K) (m : ArrowCorner K) :
    TrivSqZeroExt.snd (r • m) = r.2 * TrivSqZeroExt.snd m := rfl

@[simp] theorem right_smul_fst (r : (BaseAlgebra K)ᵐᵒᵖ) (m : ArrowCorner K) :
    TrivSqZeroExt.fst (r • m) =
      TrivSqZeroExt.fst r.unop.1 * TrivSqZeroExt.fst m := rfl

@[simp] theorem right_smul_snd (r : (BaseAlgebra K)ᵐᵒᵖ) (m : ArrowCorner K) :
    TrivSqZeroExt.snd (r • m) =
      TrivSqZeroExt.fst r.unop.1 * TrivSqZeroExt.snd m +
        TrivSqZeroExt.snd r.unop.1 * TrivSqZeroExt.fst m := rfl

instance : SMulCommClass (BaseAlgebra K) (BaseAlgebra K)ᵐᵒᵖ (ArrowCorner K) where
  smul_comm r s m := by
    ext <;> simp only [left_smul_fst, left_smul_snd, right_smul_fst,
      right_smul_snd] <;> ring

instance : IsScalarTower K (BaseAlgebra K) (ArrowCorner K) where
  smul_assoc c r m := by
    ext <;> simp only [left_smul_fst, left_smul_snd, Prod.smul_snd,
      TrivSqZeroExt.fst_smul, TrivSqZeroExt.snd_smul, smul_eq_mul] <;> ring

instance : IsScalarTower K (BaseAlgebra K)ᵐᵒᵖ (ArrowCorner K) where
  smul_assoc c r m := by
    ext <;> simp only [right_smul_fst, right_smul_snd,
      MulOpposite.unop_smul, Prod.smul_fst, TrivSqZeroExt.fst_smul,
      TrivSqZeroExt.snd_smul, smul_eq_mul] <;> ring

/-- The five-dimensional triangular coordinate algebra. -/
abbrev B1Model := TrivSqZeroExt (BaseAlgebra K) (ArrowCorner K)

/-- Vertex idempotent at the loop vertex. -/
def e1 : B1Model K := TrivSqZeroExt.inl (1, 0)

/-- Vertex idempotent at the terminal vertex. -/
def e2 : B1Model K := TrivSqZeroExt.inl (0, 1)

/-- The square-zero loop. -/
def x : B1Model K :=
  TrivSqZeroExt.inl (TrivSqZeroExt.inr 1, 0)

/-- The arrow from vertex one to vertex two. -/
def a : B1Model K := TrivSqZeroExt.inr 1

/-- The live length-two coordinate, algebraically `a * x`. -/
def u : B1Model K :=
  TrivSqZeroExt.inr (TrivSqZeroExt.inr 1)

@[simp] theorem e1_add_e2 : e1 K + e2 K = 1 := by
  ext <;> simp [e1, e2]

@[simp] theorem e1_sq : e1 K * e1 K = e1 K := by
  ext <;> simp [e1]

@[simp] theorem e2_sq : e2 K * e2 K = e2 K := by
  ext <;> simp [e2]

@[simp] theorem e1_mul_e2 : e1 K * e2 K = 0 := by
  ext <;> simp [e1, e2]

@[simp] theorem e2_mul_e1 : e2 K * e1 K = 0 := by
  ext <;> simp [e1, e2]

@[simp] theorem e1_mul_x : e1 K * x K = x K := by
  ext <;> simp [e1, x]

@[simp] theorem x_mul_e1 : x K * e1 K = x K := by
  ext <;> simp [e1, x]

@[simp] theorem e2_mul_x : e2 K * x K = 0 := by
  ext <;> simp [e2, x]

@[simp] theorem x_mul_e2 : x K * e2 K = 0 := by
  ext <;> simp [e2, x]

@[simp] theorem x_sq : x K * x K = 0 := by
  ext <;> simp [x]

@[simp] theorem e2_mul_a : e2 K * a K = a K := by
  ext <;> simp [e2, a]

@[simp] theorem a_mul_e1 : a K * e1 K = a K := by
  ext <;> simp [e1, a]

@[simp] theorem a_mul_x : a K * x K = u K := by
  ext <;> simp [a, x, u]

theorem u_ne_zero : u K ≠ 0 := by
  intro h
  have hcoord := congrArg (fun z : B1Model K => z.2.2) h
  change (1 : K) = 0 at hcoord
  exact one_ne_zero hcoord

theorem a_mul_x_ne_zero : a K * x K ≠ 0 := by
  rw [a_mul_x]
  exact u_ne_zero K

@[simp] theorem u_mul_x : u K * x K = 0 := by
  ext <;> simp [u, x]

@[simp] theorem e2_mul_u : e2 K * u K = u K := by
  ext <;> simp [e2, u]

@[simp] theorem u_mul_e1 : u K * e1 K = u K := by
  ext <;> simp [e1, u]

@[simp] theorem e1_mul_a : e1 K * a K = 0 := by
  ext <;> simp [e1, a]

@[simp] theorem a_mul_e2 : a K * e2 K = 0 := by
  ext <;> simp [e2, a]

@[simp] theorem e1_mul_u : e1 K * u K = 0 := by
  ext <;> simp [e1, u]

@[simp] theorem u_mul_e2 : u K * e2 K = 0 := by
  ext <;> simp [e2, u]

noncomputable instance finiteDimensional :
    FiniteDimensional K (B1Model K) := by
  change Module.Finite K (((K × K) × K) × (K × K))
  infer_instance

noncomputable instance isNoetherianRing :
    IsNoetherianRing (B1Model K) :=
  IsNoetherianRing.of_finite K (B1Model K)

noncomputable instance isArtinianRing :
    IsArtinianRing (B1Model K) :=
  IsArtinianRing.of_finite K (B1Model K)

theorem finrank_eq_five : Module.finrank K (B1Model K) = 5 := by
  change Module.finrank K (((K × K) × K) × (K × K)) = 5
  simp

end OpConjecture.LollipopConcrete.B1
