import Mathlib.Algebra.Module.MinimalAxioms
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import OpConjecture.RepresentationTheory.SplitBasicCoordinateSystem

/-!
# Split basic algebras as trivial square-zero extensions

For a split basic algebra with square-zero Jacobson radical, this file
packages the radical as a bimodule over the coordinate semisimple algebra and
upgrades the linear decomposition to an algebra equivalence with Mathlib's
`TrivSqZeroExt`.
-/

set_option autoImplicit false

noncomputable section

namespace OpConjecture.SplitBasicCoordinateSystem.QuotientCoordinateData

universe u v

variable {K B : Type u} {I : Type v}
  [Field K] [Ring B] [Algebra K B] [IsArtinianRing B]
  [Fintype I] [DecidableEq I]

/-- A copy of the Jacobson radical whose type remembers the chosen coordinate
data, allowing its left and right coordinate-algebra actions to be registered
as instances without ambiguity. -/
structure RadicalBimodule
    (D : QuotientCoordinateData (K := K) (B := B) (I := I)) where
  val : Ring.jacobson B

namespace RadicalBimodule

variable
    (D : QuotientCoordinateData (K := K) (B := B) (I := I))

/-- Forget the tagged bimodule wrapper. -/
def equiv : RadicalBimodule D ≃ Ring.jacobson B where
  toFun := RadicalBimodule.val
  invFun := RadicalBimodule.mk
  left_inv _ := rfl
  right_inv _ := rfl

omit [IsArtinianRing B] [Fintype I] [DecidableEq I] in
theorem ext' {x y : RadicalBimodule D} (h : x.val = y.val) : x = y := by
  cases x
  cases y
  cases h
  rfl

instance : AddCommGroup (RadicalBimodule D) :=
  (equiv D).addCommGroup

instance : Module K (RadicalBimodule D) :=
  (equiv D).module K

instance : Module B (RadicalBimodule D) :=
  (equiv D).module B

instance : SMul Bᵐᵒᵖ (RadicalBimodule D) where
  smul b x :=
    ⟨⟨(x.val : B) * MulOpposite.unop b,
      (Ring.jacobson B).mul_mem_right _ x.val.property⟩⟩

instance : Module Bᵐᵒᵖ (RadicalBimodule D) :=
  Module.ofMinimalAxioms
    (by
      intro b x y
      apply ext' D
      apply Subtype.ext
      change ((x.val : B) + y.val) * MulOpposite.unop b =
        (x.val : B) * MulOpposite.unop b + y.val * MulOpposite.unop b
      exact add_mul _ _ _)
    (by
      intro a b x
      apply ext' D
      apply Subtype.ext
      change (x.val : B) * (MulOpposite.unop a + MulOpposite.unop b) =
        x.val * MulOpposite.unop a + x.val * MulOpposite.unop b
      exact mul_add _ _ _)
    (by
      intro a b x
      apply ext' D
      apply Subtype.ext
      change (x.val : B) * MulOpposite.unop (a * b) =
        (x.val * MulOpposite.unop b) * MulOpposite.unop a
      simp [mul_assoc])
    (by
      intro x
      apply ext' D
      apply Subtype.ext
      change (x.val : B) * 1 = x.val
      exact mul_one _)

instance : Module (I → K) (RadicalBimodule D) :=
  Module.compHom _ D.coordinateSection.toRingHom

instance : Module (I → K)ᵐᵒᵖ (RadicalBimodule D) :=
  Module.compHom _ (RingHom.op D.coordinateSection.toRingHom)

instance : SMulCommClass (I → K) (I → K)ᵐᵒᵖ
    (RadicalBimodule D) where
  smul_comm s t x := by
    apply ext' D
    apply Subtype.ext
    change D.coordinateSection s *
        ((x.val : B) * D.coordinateSection (MulOpposite.unop t)) =
      (D.coordinateSection s * (x.val : B)) *
        D.coordinateSection (MulOpposite.unop t)
    exact (mul_assoc _ _ _).symm

instance : IsScalarTower K (I → K) (RadicalBimodule D) :=
  ⟨by
    intro k s x
    apply ext' D
    apply Subtype.ext
    change D.coordinateSection (k • s) * (x.val : B) =
      k • (D.coordinateSection s * (x.val : B))
    rw [map_smul, Algebra.smul_mul_assoc]⟩

instance : IsScalarTower K (I → K)ᵐᵒᵖ (RadicalBimodule D) :=
  ⟨by
    intro k s x
    apply ext' D
    apply Subtype.ext
    change (x.val : B) *
        D.coordinateSection (MulOpposite.unop (k • s)) =
      k • ((x.val : B) * D.coordinateSection (MulOpposite.unop s))
    rw [MulOpposite.unop_smul, map_smul, Algebra.mul_smul_comm]⟩

/-- Inclusion of the tagged radical into the algebra. -/
def inclusion : RadicalBimodule D →ₗ[K] B where
  toFun x := x.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The algebra map from the trivial square-zero extension to `B`. -/
def squareZeroLift
    (hJ : (Ring.jacobson B) ^ 2 = ⊥) :
    TrivSqZeroExt (I → K) (RadicalBimodule D) →ₐ[K] B :=
  TrivSqZeroExt.lift D.coordinateSection (inclusion D)
    (by
      intro x y
      exact radical_mul_eq_zero_of_sq_eq_bot hJ x.val y.val)
    (by intro r x; rfl)
    (by intro r x; rfl)

/-- The square-zero-extension map is bijective by the previously constructed
semisimple--radical decomposition. -/
theorem squareZeroLift_bijective
    (hJ : (Ring.jacobson B) ^ 2 = ⊥) :
    Function.Bijective (squareZeroLift D hJ) := by
  change Function.Bijective
    (fun z : (I → K) × RadicalBimodule D ↦
      D.coordinateSection z.1 + (z.2.val : B))
  let e : ((I → K) × RadicalBimodule D) ≃
      ((I → K) × Ring.jacobson B) :=
    Equiv.prodCongr (Equiv.refl _) (equiv D)
  exact D.splitRadicalLinearEquiv.bijective.comp e.bijective

/-- A split basic algebra with square-zero radical is the trivial extension
of its coordinate semisimple algebra by its radical bimodule. -/
def squareZeroAlgEquiv
    (hJ : (Ring.jacobson B) ^ 2 = ⊥) :
    TrivSqZeroExt (I → K) (RadicalBimodule D) ≃ₐ[K] B :=
  AlgEquiv.ofBijective (squareZeroLift D hJ)
    (squareZeroLift_bijective D hJ)

/-- The induced equivalence between left modules over `B` and over its
square-zero normal form. -/
def squareZeroLeftModuleEquivalence
    (hJ : (Ring.jacobson B) ^ 2 = ⊥) :
    ModuleCat B ≌
      ModuleCat (TrivSqZeroExt (I → K) (RadicalBimodule D)) :=
  ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    (squareZeroAlgEquiv D hJ).toRingEquiv

/-- The corresponding equivalence for right modules, expressed as left
modules over the opposite rings. -/
def squareZeroRightModuleEquivalence
    (hJ : (Ring.jacobson B) ^ 2 = ⊥) :
    ModuleCat Bᵐᵒᵖ ≌
      ModuleCat (TrivSqZeroExt (I → K) (RadicalBimodule D))ᵐᵒᵖ :=
  ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    (AlgEquiv.op (squareZeroAlgEquiv D hJ)).toRingEquiv

end RadicalBimodule

end OpConjecture.SplitBasicCoordinateSystem.QuotientCoordinateData
