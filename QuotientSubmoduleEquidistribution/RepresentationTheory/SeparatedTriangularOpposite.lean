import QuotientSubmoduleEquidistribution.RepresentationTheory.MoritaRestriction
import QuotientSubmoduleEquidistribution.RepresentationTheory.SeparatedTriangularAlgebra
import QuotientSubmoduleEquidistribution.RepresentationTheory.TrivSqZeroExtOpposite

/-!
# Opposite of a separated triangular algebra

Swapping the two diagonal coordinates identifies the opposite of the
separated triangular algebra for a bimodule `J` with the separated triangular
algebra for the bimodule with exchanged actions.  This file packages the ring
equivalence and its restrictions to module categories.
-/

set_option autoImplicit false

noncomputable section

open scoped RightActions

namespace QuotientSubmoduleEquidistribution.SeparatedTriangularAlgebra

open QuotientSubmoduleEquidistribution.TrivSqZeroExtOpposite

universe u v

variable {S : Type u} {J : Type v}
variable [CommRing S] [AddCommGroup J]
variable [Module S J] [Module Sᵐᵒᵖ J]
variable [SMulCommClass S Sᵐᵒᵖ J]

/-- The opposite separated triangular algebra is the separated triangular
algebra for the bimodule with exchanged actions. -/
def oppositeRingEquiv :
    (Algebra S J)ᵐᵒᵖ ≃+* Algebra S (ReversedBimodule S J) where
  toFun x :=
    (((MulOpposite.unop x).1.2, (MulOpposite.unop x).1.1),
      ⟨ReversedBimodule.mk (MulOpposite.unop x).2.val⟩)
  invFun x :=
    MulOpposite.op ((x.1.2, x.1.1), ⟨x.2.val.val⟩)
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl
  map_mul' := by
    rintro ⟨⟨⟨a, b⟩, ⟨j⟩⟩⟩ ⟨⟨⟨c, d⟩, ⟨k⟩⟩⟩
    apply TrivSqZeroExt.ext
    · exact Prod.ext (mul_comm d b) (mul_comm c a)
    · apply SeparatedIdeal.ext
      apply ReversedBimodule.ext'
      exact add_comm (c • j) (k <• b)
  map_add' := by
    rintro ⟨⟨⟨a, b⟩, ⟨j⟩⟩⟩ ⟨⟨⟨c, d⟩, ⟨k⟩⟩⟩
    rfl

/-- The opposite-ring identification on all module categories. -/
def oppositeModuleEquivalence :
    ModuleCat.{max u v} (Algebra S J)ᵐᵒᵖ ≌
      ModuleCat.{max u v} (Algebra S (ReversedBimodule S J)) :=
  ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    (oppositeRingEquiv (S := S) (J := J)).symm

/-- The opposite-ring identification restricted to finitely generated
modules over Artinian separated triangular algebras. -/
def oppositeFgEquivalence
    [IsArtinianRing (Algebra S J)ᵐᵒᵖ]
    [IsArtinianRing (Algebra S (ReversedBimodule S J))] :
    FGModuleCat.{max u v} (Algebra S J)ᵐᵒᵖ ≌
      FGModuleCat.{max u v} (Algebra S (ReversedBimodule S J)) :=
  QuotientSubmoduleEquidistribution.MoritaRestriction.fgEquivalence
    (oppositeModuleEquivalence (S := S) (J := J))

end QuotientSubmoduleEquidistribution.SeparatedTriangularAlgebra
