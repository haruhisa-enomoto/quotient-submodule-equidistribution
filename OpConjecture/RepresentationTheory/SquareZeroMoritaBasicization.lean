import OpConjecture.RepresentationTheory.CornerRadicalSquareZero
import OpConjecture.RepresentationTheory.FullIdempotentMorita
import OpConjecture.RepresentationTheory.SplitBasicSquareZeroExtension

/-!
# Morita basicization preserving square-zero radical

The full-idempotent basic corner used by the project inherits a square-zero
Jacobson radical.  This file bundles the ordinary Morita basic model with
that inherited equation and proves existence over an algebraically closed
field.
-/

set_option autoImplicit false

noncomputable section

namespace OpConjecture.MoritaBasicizationInterface

universe u

variable {K A : Type u}
variable [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]

/-- A conventional Morita basic model whose target still has square-zero
Jacobson radical. -/
structure SquareZeroMoritaBasicModel where
  basicModel : MoritaBasicModel (K := K) (A := A)
  radical_sq : (Ring.jacobson basicModel.Carrier) ^ 2 = ⊥

namespace SquareZeroMoritaBasicModel

/-- A chosen basicizing full idempotent produces a square-zero Morita basic
model whenever the source radical is square-zero. -/
def ofBasicizingFullIdempotent
    (P : BasicizingFullIdempotent (K := K) (A := A))
    (hJ : (Ring.jacobson A) ^ 2 = ⊥) :
    SquareZeroMoritaBasicModel (K := K) (A := A) where
  basicModel := MoritaBasicModel.ofBasicizingFullIdempotent
    (OpConjecture.FullIdempotentMorita.fullIdempotentMoritaBridge
      (K := K) (A := A)) P
  radical_sq := by
    exact corner_jacobson_sq_eq_bot P.idem hJ

variable [IsAlgClosed K]

omit [FiniteDimensional K A] in
/-- The square-zero Morita basic target has split quotient coordinates. -/
theorem exists_quotientCoordinateData
    (P : SquareZeroMoritaBasicModel (K := K) (A := A)) :
    ∃ n : ℕ,
      Nonempty
        (OpConjecture.SplitBasicCoordinateSystem.QuotientCoordinateData
          (K := K) (B := P.basicModel.Carrier) (I := Fin n)) :=
  P.basicModel.exists_target_quotientCoordinateData

end SquareZeroMoritaBasicModel

/-- A square-zero Morita basic model together with chosen split coordinates
on its semisimple quotient. -/
structure CoordinatizedSquareZeroMoritaModel where
  squareZeroModel : SquareZeroMoritaBasicModel (K := K) (A := A)
  vertexCount : ℕ
  coordinateData :
    OpConjecture.SplitBasicCoordinateSystem.QuotientCoordinateData
      (K := K) (B := squareZeroModel.basicModel.Carrier)
      (I := Fin vertexCount)

namespace CoordinatizedSquareZeroMoritaModel

variable (P : CoordinatizedSquareZeroMoritaModel (K := K) (A := A))

local instance : IsArtinianRing P.squareZeroModel.basicModel.Carrier :=
  IsArtinianRing.of_finite K P.squareZeroModel.basicModel.Carrier

/-- The radical bimodule in the chosen split coordinates. -/
abbrev RadicalBimodule :=
  OpConjecture.SplitBasicCoordinateSystem.QuotientCoordinateData.RadicalBimodule
    P.coordinateData

/-- The tagged radical is finite-dimensional over the ground field. -/
instance radicalBimoduleFinite : Module.Finite K P.RadicalBimodule := by
  apply Module.Finite.of_injective
    (OpConjecture.SplitBasicCoordinateSystem.QuotientCoordinateData.RadicalBimodule.inclusion
      P.coordinateData)
  intro x y hxy
  apply OpConjecture.SplitBasicCoordinateSystem.QuotientCoordinateData.RadicalBimodule.ext'
    P.coordinateData
  apply Subtype.ext
  exact hxy

/-- Hence it is finite over the coordinate algebra on the left. -/
instance radicalBimoduleCoordinateFinite :
    Module.Finite (Fin P.vertexCount → K) P.RadicalBimodule :=
  Module.Finite.of_restrictScalars_finite K _ _

/-- The same finite-generation statement for the coordinate right action. -/
instance radicalBimoduleOppositeCoordinateFinite :
    Module.Finite (Fin P.vertexCount → K)ᵐᵒᵖ P.RadicalBimodule :=
  Module.Finite.of_restrictScalars_finite K _ _

/-- The selected basic algebra is explicitly a trivial square-zero extension
of the coordinate semisimple algebra by its radical bimodule. -/
def squareZeroAlgEquiv :
    TrivSqZeroExt (Fin P.vertexCount → K) P.RadicalBimodule ≃ₐ[K]
      P.squareZeroModel.basicModel.Carrier :=
  OpConjecture.SplitBasicCoordinateSystem.QuotientCoordinateData.RadicalBimodule.squareZeroAlgEquiv
    P.coordinateData P.squareZeroModel.radical_sq

/-- The induced equivalence on left-module categories. -/
def squareZeroLeftModuleEquivalence :
    ModuleCat P.squareZeroModel.basicModel.Carrier ≌
      ModuleCat
        (TrivSqZeroExt (Fin P.vertexCount → K) P.RadicalBimodule) :=
  OpConjecture.SplitBasicCoordinateSystem.QuotientCoordinateData.RadicalBimodule.squareZeroLeftModuleEquivalence
    P.coordinateData P.squareZeroModel.radical_sq

/-- The induced equivalence on right-module categories. -/
def squareZeroRightModuleEquivalence :
    ModuleCat P.squareZeroModel.basicModel.Carrierᵐᵒᵖ ≌
      ModuleCat
        (TrivSqZeroExt (Fin P.vertexCount → K) P.RadicalBimodule)ᵐᵒᵖ :=
  OpConjecture.SplitBasicCoordinateSystem.QuotientCoordinateData.RadicalBimodule.squareZeroRightModuleEquivalence
    P.coordinateData P.squareZeroModel.radical_sq

/-- The left-module normal-form equivalence restricted to finitely generated
modules. -/
def squareZeroLeftFgEquivalence :
    FGModuleCat P.squareZeroModel.basicModel.Carrier ≌
      FGModuleCat
        (TrivSqZeroExt (Fin P.vertexCount → K) P.RadicalBimodule) := by
  letI : IsArtinianRing
      (TrivSqZeroExt (Fin P.vertexCount → K) P.RadicalBimodule) :=
    P.squareZeroAlgEquiv.symm.toRingEquiv.isArtinianRing
  exact OpConjecture.MoritaRestriction.fgEquivalence
    P.squareZeroLeftModuleEquivalence

/-- The right-module normal-form equivalence restricted to finitely generated
modules. -/
def squareZeroRightFgEquivalence :
    FGModuleCat P.squareZeroModel.basicModel.Carrierᵐᵒᵖ ≌
      FGModuleCat
        (TrivSqZeroExt (Fin P.vertexCount → K) P.RadicalBimodule)ᵐᵒᵖ := by
  letI : IsArtinianRing P.squareZeroModel.basicModel.Carrierᵐᵒᵖ :=
    OpConjecture.isArtinianRing_op_of_finiteDimensional K
      P.squareZeroModel.basicModel.Carrier
  letI : IsArtinianRing
      (TrivSqZeroExt (Fin P.vertexCount → K) P.RadicalBimodule)ᵐᵒᵖ :=
    (AlgEquiv.op P.squareZeroAlgEquiv).symm.toRingEquiv.isArtinianRing
  exact OpConjecture.MoritaRestriction.fgEquivalence
    P.squareZeroRightModuleEquivalence

/-- The original algebra's finitely generated left modules transported all
the way to the split square-zero normal form. -/
def sourceLeftFgEquivalence :
    FGModuleCat A ≌
      FGModuleCat
        (TrivSqZeroExt (Fin P.vertexCount → K) P.RadicalBimodule) :=
  P.squareZeroModel.basicModel.morita.finiteDimensionalFgEquivalence.trans
    P.squareZeroLeftFgEquivalence

/-- The original algebra's finitely generated right modules transported all
the way to the split square-zero normal form. -/
def sourceRightFgEquivalence :
    FGModuleCat Aᵐᵒᵖ ≌
      FGModuleCat
        (TrivSqZeroExt (Fin P.vertexCount → K) P.RadicalBimodule)ᵐᵒᵖ :=
  P.squareZeroModel.basicModel.rightFgEquivalence.trans
    P.squareZeroRightFgEquivalence

end CoordinatizedSquareZeroMoritaModel

variable [IsAlgClosed K]

/-- Every finite-dimensional square-zero algebra over an algebraically
closed field has a Morita-equivalent basic target with square-zero radical. -/
theorem exists_squareZeroMoritaBasicModel
    (hJ : (Ring.jacobson A) ^ 2 = ⊥) :
    Nonempty (SquareZeroMoritaBasicModel (K := K) (A := A)) := by
  obtain ⟨P⟩ := exists_basicizingFullIdempotent K A
  exact ⟨SquareZeroMoritaBasicModel.ofBasicizingFullIdempotent P hJ⟩

/-- The same existence theorem with split quotient coordinates chosen once
and for all. -/
theorem exists_coordinatizedSquareZeroMoritaModel
    (hJ : (Ring.jacobson A) ^ 2 = ⊥) :
    Nonempty
      (CoordinatizedSquareZeroMoritaModel (K := K) (A := A)) := by
  obtain ⟨P⟩ := exists_squareZeroMoritaBasicModel (K := K) (A := A) hJ
  obtain ⟨n, ⟨D⟩⟩ := P.exists_quotientCoordinateData
  exact ⟨{
    squareZeroModel := P
    vertexCount := n
    coordinateData := D }⟩

end OpConjecture.MoritaBasicizationInterface
