import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Artinian.Module

/-!
# A concrete square-zero model for the dead-path lollipop

This file isolates a concrete algebra model for the presentation layer
missing from the project foundation's free-quiver representation API.  Over a field `K`,
take the trivial square-zero extension of `K × K` by the bimodule with basis
`x, a` and supports

* `e₁ x = x = x e₁`,
* `e₂ a = a = a e₁`.

Thus all products of two off-diagonal generators vanish.  The coordinate
corners match the loop `1 → 1` and stem `1 → 2` of the intended lollipop.
This file proves the coordinate identities, but does not yet assert a
universal bound-path-algebra presentation, identify the Jacobson radical, or
prove primitivity of the vertex idempotents.
-/

open scoped RightActions

namespace OpConjecture.LollipopConcrete

variable (K : Type*) [Field K]

/-- The vertex subalgebra, with coordinate idempotents `(1, 0)` and `(0, 1)`. -/
abbrev VertexAlgebra := K × K

/-- The radical bimodule.  The two coordinates are the loop `x` and arrow `a`. -/
structure B0Radical where
  x : K
  a : K

omit [Field K] in
@[ext] theorem B0Radical.ext {u v : B0Radical K} (hx : u.x = v.x) (ha : u.a = v.a) : u = v := by
  cases u
  cases v
  simp_all

/-- Coordinates transport the additive group structure to the radical. -/
def B0Radical.equivProd : B0Radical K ≃ K × K where
  toFun m := (m.x, m.a)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup (B0Radical K) := (B0Radical.equivProd K).addCommGroup

@[simp] theorem B0Radical.zero_x : (0 : B0Radical K).x = 0 := rfl

@[simp] theorem B0Radical.zero_a : (0 : B0Radical K).a = 0 := rfl

/-- The coordinate equivalence after transporting the additive group. -/
def B0Radical.addEquivProd : B0Radical K ≃+ K × K where
  __ := B0Radical.equivProd K
  map_add' _ _ := rfl

/-- The ordinary `K`-vector-space structure on the two radical coordinates. -/
instance : Module K (B0Radical K) := (B0Radical.addEquivProd K).module K

@[simp] theorem B0Radical.add_x (m n : B0Radical K) :
    (m + n).x = m.x + n.x := rfl

@[simp] theorem B0Radical.add_a (m n : B0Radical K) :
    (m + n).a = m.a + n.a := rfl

@[simp] theorem B0Radical.smul_x (c : K) (m : B0Radical K) :
    (c • m).x = c * m.x := rfl

@[simp] theorem B0Radical.smul_a (c : K) (m : B0Radical K) :
    (c • m).a = c * m.a := rfl

/-- Left multiplication by the vertex algebra: `e₁` supports `x`, `e₂` supports `a`. -/
instance : Module (VertexAlgebra K) (B0Radical K) :=
  (B0Radical.addEquivProd K).module (VertexAlgebra K)

/-- Both radical generators end at vertex `1` on the right. -/
def rightVertexCharacter : (VertexAlgebra K)ᵐᵒᵖ →+* K :=
  (RingHom.fst K K).fromOpposite fun _ _ => Commute.all _ _

/-- The right action of the vertex algebra on each radical coordinate factors through vertex `1`. -/
instance : Module (VertexAlgebra K)ᵐᵒᵖ K := Module.compHom K (rightVertexCharacter K)

/-- Right multiplication by the vertex algebra on the radical. -/
instance : Module (VertexAlgebra K)ᵐᵒᵖ (B0Radical K) :=
  (B0Radical.addEquivProd K).module (VertexAlgebra K)ᵐᵒᵖ

@[simp] theorem B0Radical.left_smul_x (r : VertexAlgebra K) (m : B0Radical K) :
    (r • m).x = r.1 * m.x := rfl

@[simp] theorem B0Radical.left_smul_a (r : VertexAlgebra K) (m : B0Radical K) :
    (r • m).a = r.2 * m.a := rfl

@[simp] theorem B0Radical.right_smul_x (r : (VertexAlgebra K)ᵐᵒᵖ) (m : B0Radical K) :
    (r • m).x = r.unop.1 * m.x := rfl

@[simp] theorem B0Radical.right_smul_a (r : (VertexAlgebra K)ᵐᵒᵖ) (m : B0Radical K) :
    (r • m).a = r.unop.1 * m.a := rfl

instance : IsScalarTower K (VertexAlgebra K) (B0Radical K) where
  smul_assoc c r m := by
    apply B0Radical.ext
    · simp
      ring
    · simp
      ring

instance : IsScalarTower K (VertexAlgebra K)ᵐᵒᵖ (B0Radical K) where
  smul_assoc c r m := by
    apply B0Radical.ext
    · simp
      ring
    · simp
      ring

instance : SMulCommClass (VertexAlgebra K) (VertexAlgebra K)ᵐᵒᵖ (B0Radical K) where
  smul_comm r s m := by
    apply B0Radical.ext
    · simp only [B0Radical.left_smul_x, B0Radical.right_smul_x]
      ac_rfl
    · simp only [B0Radical.left_smul_a, B0Radical.right_smul_a]
      ac_rfl

/-- The square-zero extension intended to model the dead-path lollipop. -/
abbrev B0Model := TrivSqZeroExt (VertexAlgebra K) (B0Radical K)

/-- The radical coordinate type is the ordinary two-dimensional vector
space. -/
def B0Radical.linearEquivProd : B0Radical K ≃ₗ[K] K × K where
  __ := B0Radical.addEquivProd K
  map_smul' _ _ := rfl

noncomputable instance B0Radical.finiteDimensional :
    FiniteDimensional K (B0Radical K) :=
  (B0Radical.linearEquivProd K).symm.finiteDimensional

/-- The concrete square-zero lollipop algebra is finite-dimensional. -/
noncomputable instance B0Model.finiteDimensional :
    FiniteDimensional K (B0Model K) := by
  change Module.Finite K ((K × K) × B0Radical K)
  infer_instance

noncomputable instance B0Model.isNoetherianRing :
    IsNoetherianRing (B0Model K) :=
  IsNoetherianRing.of_finite K (B0Model K)

noncomputable instance B0Model.isArtinianRing :
    IsArtinianRing (B0Model K) :=
  IsArtinianRing.of_finite K (B0Model K)

/-- The four coordinate generators give the expected dimension. -/
theorem B0Model_finrank : Module.finrank K (B0Model K) = 4 := by
  change Module.finrank K ((K × K) × B0Radical K) = 4
  have hrank : Module.finrank K (B0Radical K) = 2 := by
    calc
      Module.finrank K (B0Radical K) = Module.finrank K (K × K) :=
        (B0Radical.linearEquivProd K).finrank_eq
      _ = 2 := by simp
  simp [hrank]

def e1 : B0Model K := TrivSqZeroExt.inl (1, 0)
def e2 : B0Model K := TrivSqZeroExt.inl (0, 1)
def x : B0Model K := TrivSqZeroExt.inr ⟨1, 0⟩
def a : B0Model K := TrivSqZeroExt.inr ⟨0, 1⟩

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

@[simp] theorem e2_mul_a : e2 K * a K = a K := by
  ext <;> simp [e2, a]

@[simp] theorem a_mul_e1 : a K * e1 K = a K := by
  ext <;> simp [e1, a]

@[simp] theorem e2_mul_x : e2 K * x K = 0 := by
  ext <;> simp [e2, x]

@[simp] theorem x_mul_e2 : x K * e2 K = 0 := by
  ext <;> simp [e2, x]

@[simp] theorem e1_mul_a : e1 K * a K = 0 := by
  ext <;> simp [e1, a]

@[simp] theorem a_mul_e2 : a K * e2 K = 0 := by
  ext <;> simp [e2, a]

/-- Products of any two off-diagonal coordinate generators vanish. -/
@[simp] theorem radical_mul_radical (u v : B0Radical K) :
    (TrivSqZeroExt.inr u : B0Model K) * TrivSqZeroExt.inr v = 0 := by
  exact TrivSqZeroExt.inr_mul_inr (VertexAlgebra K) u v

@[simp] theorem x_sq : x K * x K = 0 := radical_mul_radical K _ _

/-- With paths read in the left-module/later-factor-first convention, the
paper path `x` followed by `a` is represented by the product `a * x`. -/
@[simp] theorem a_mul_x : a K * x K = 0 := radical_mul_radical K _ _

/-- The opposite order also vanishes because this model is square-zero. -/
@[simp] theorem x_mul_a : x K * a K = 0 := radical_mul_radical K _ _

end OpConjecture.LollipopConcrete
