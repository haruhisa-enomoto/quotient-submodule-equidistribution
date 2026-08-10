import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.Finiteness.Prod
import QuotientSubmoduleEquidistribution.RepresentationTheory.FiniteType
import QuotientSubmoduleEquidistribution.RepresentationTheory.SeparatedTriangularAlgebra
import QuotientSubmoduleEquidistribution.RepresentationTheory.SeparatedTriangularAlgebraEquivalence
import QuotientSubmoduleEquidistribution.RepresentationTheory.TrivSqZeroExtSeparatedCorrespondence
import QuotientSubmoduleEquidistribution.RepresentationTheory.TrivSqZeroExtSeparatedSimple

/-!
# Finiteness of separated realizations

When the square-zero bimodule is finite over its semisimple base, finite
generation of an original module descends to its top and radical layers and
then ascends to the corresponding triangular-algebra realization.  This is
the finiteness bridge needed to place the separated realization in an
`FGModuleCat` skeleton.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.TrivSqZeroExtSeparatedFinite

open SeparatedTriangularAlgebra
open TrivSqZeroExtSeparatedCorrespondence
open TrivSqZeroExtSeparatedData

universe u v w

variable {S : Type u} {J : Type v}
variable [CommRing S] [AddCommGroup J]
variable [Module S J] [Module Sᵐᵒᵖ J]
variable [SMulCommClass S Sᵐᵒᵖ J]

/-- A finitely generated module over the trivial extension remains finitely
generated after restriction to the base inclusion. -/
theorem restrictInl_moduleFinite
    [Module.Finite S J]
    (X : FGModuleCat.{w} (TrivSqZeroExt S J)) :
    letI : Module S X :=
      Module.compHom X (TrivSqZeroExt.inlHom S J)
    Module.Finite S X := by
  let R := TrivSqZeroExt S J
  let i := TrivSqZeroExt.inlHom S J
  letI : Module S X := Module.compHom X i
  letI : IsScalarTower S R X :=
    ⟨fun s r x ↦ by
      change (s • r) • x =
        (TrivSqZeroExt.inl s : R) • (r • x)
      rw [← TrivSqZeroExt.inl_mul_eq_smul, mul_smul]⟩
  haveI : Module.Finite S R := by
    change Module.Finite S (S × J)
    infer_instance
  exact Module.Finite.trans R X

/-- The separated top of a finitely generated original module is finite over
the base. -/
theorem moduleSeparatedData_top_moduleFinite
    [IsSemisimpleRing S] [Module.Finite S J]
    (X : FGModuleCat.{w} (TrivSqZeroExt S J)) :
    Module.Finite S
      (moduleSeparatedData (S := S) (J := J) X.obj).top := by
  let R := TrivSqZeroExt S J
  let i := TrivSqZeroExt.inlHom S J
  letI : Module S X := Module.compHom X i
  letI : IsScalarTower S R X :=
    ⟨fun s r x ↦ by
      change (s • r) • x =
        (TrivSqZeroExt.inl s : R) • (r • x)
      rw [← TrivSqZeroExt.inl_mul_eq_smul, mul_smul]⟩
  haveI : Module.Finite S R := by
    change Module.Finite S (S × J)
    infer_instance
  haveI : Module.Finite S X := Module.Finite.trans R X
  change Module.Finite S (X ⧸ Module.jacobson R X)
  infer_instance

/-- The separated radical of a finitely generated original module is finite
over the semisimple base. -/
theorem moduleSeparatedData_radical_moduleFinite
    [IsSemisimpleRing S] [Module.Finite S J]
    (X : FGModuleCat.{w} (TrivSqZeroExt S J)) :
    Module.Finite S
      (moduleSeparatedData (S := S) (J := J) X.obj).radical := by
  let R := TrivSqZeroExt S J
  let i := TrivSqZeroExt.inlHom S J
  letI : Module S X := Module.compHom X i
  letI : IsScalarTower S R X :=
    ⟨fun s r x ↦ by
      change (s • r) • x =
        (TrivSqZeroExt.inl s : R) • (r • x)
      rw [← TrivSqZeroExt.inl_mul_eq_smul, mul_smul]⟩
  haveI : Module.Finite S R := by
    change Module.Finite S (S × J)
    infer_instance
  haveI : Module.Finite S X := Module.Finite.trans R X
  let RX := Module.jacobson R X
  change Module.Finite S RX
  haveI : IsNoetherian S X := inferInstance
  haveI : IsNoetherian S RX :=
    isNoetherian_of_injective (RX.subtype.restrictScalars S)
      RX.subtype_injective
  infer_instance

/-- The separated top of a nonzero finitely generated original module is
nonzero. -/
theorem moduleSeparatedData_top_nontrivial
    [IsSemisimpleRing S]
    (X : FGModuleCat.{w} (TrivSqZeroExt S J)) [Nontrivial X] :
    Nontrivial
      (moduleSeparatedData (S := S) (J := J) X.obj).top := by
  rw [← not_subsingleton_iff_nontrivial]
  intro hsub
  exact (Module.jacobson_lt_top (TrivSqZeroExt S J) X).ne
    (Submodule.Quotient.subsingleton_iff.mp hsub)

/-- Finite top and radical layers give a finitely generated module over the
triangular separated algebra. -/
theorem realized_moduleFinite
    (D : SeparatedData.{u, v, w} (S := S) (J := J))
    [Module.Finite S D.top] [Module.Finite S D.radical] :
    Module.Finite (Algebra S J) (Realized D) := by
  let A := Algebra S J
  letI : Module A (Realized D) := realizedModule D
  haveI : Module.Finite S (Realized D) := by
    change Module.Finite S (D.top × D.radical)
    infer_instance
  letI : IsScalarTower S A (Realized D) :=
    ⟨fun s a x ↦ by
      let q : A := TrivSqZeroExt.inl ((s, s) : S × S)
      have hsa : s • a = q * a := by
        apply TrivSqZeroExt.ext
        · rfl
        · apply SeparatedIdeal.ext
          rw [TrivSqZeroExt.snd_smul, TrivSqZeroExt.snd_mul]
          dsimp only [q]
          simp
          change s • a.snd.val = s • a.snd.val
          rfl
      calc
        (s • a) • x = (q * a) • x := by rw [hsa]
        _ = q • (a • x) := by rw [mul_smul]
        _ = s • (a • x) := by
          rcases a • x with ⟨t, d⟩
          apply Prod.ext
          · rfl
          · change s • d + D.action 0 t = s • d
            rw [map_zero, AddMonoidHom.zero_apply, add_zero]⟩
  exact Module.Finite.of_restrictScalars_finite S A (Realized D)

/-- In particular, the separated datum of any finitely generated original
module realizes to a finitely generated triangular-algebra module. -/
theorem moduleSeparatedData_realized_moduleFinite
    [IsSemisimpleRing S] [Module.Finite S J]
    (X : FGModuleCat.{w} (TrivSqZeroExt S J)) :
    let D := moduleSeparatedData (S := S) (J := J) X.obj
    letI : Module (Algebra S J) (Realized D) := realizedModule D
    Module.Finite (Algebra S J) (Realized D) := by
  let D := moduleSeparatedData (S := S) (J := J) X.obj
  letI : Module.Finite S D.top :=
    moduleSeparatedData_top_moduleFinite X
  letI : Module.Finite S D.radical :=
    moduleSeparatedData_radical_moduleFinite X
  exact realized_moduleFinite D

/-- The free radical-side copy attached to a finite original module is finite
over the triangular separated algebra. -/
theorem freeData_realized_moduleFinite
    [IsSemisimpleRing S] [Module.Finite S J]
    (X : FGModuleCat.{w} (TrivSqZeroExt S J)) :
    let D := TrivSqZeroExtSeparatedSimple.freeData
      (S := S) (J := J) X.obj
    letI : Module (Algebra S J) (Realized D) := realizedModule D
    Module.Finite (Algebra S J) (Realized D) := by
  let D := TrivSqZeroExtSeparatedSimple.freeData
    (S := S) (J := J) X.obj
  letI : Module.Finite S D.top := by
    change Module.Finite S PUnit
    infer_instance
  letI : Module.Finite S D.radical :=
    moduleSeparatedData_top_moduleFinite X
  exact realized_moduleFinite D

/-! ## Finiteness in the reverse direction -/

/-- The diagonal inclusion of the semisimple base into the triangular
separated algebra. -/
def diagonalHom : S →+* Algebra S J :=
  (TrivSqZeroExt.inlHom (S × S) (SeparatedIdeal S J)).comp
    (RingHom.prod (RingHom.id S) (RingHom.id S))

omit [Module Sᵐᵒᵖ J] [SMulCommClass S Sᵐᵒᵖ J] in
/-- The tagged separated ideal is finite whenever the original square-zero
bimodule is finite. -/
theorem separatedIdeal_moduleFinite [Module.Finite S J] :
    Module.Finite S (SeparatedIdeal S J) := by
  let e : SeparatedIdeal S J ≃ₗ[S] J :=
    { SeparatedIdeal.equiv (S := S) (J := J) with
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact Module.Finite.equiv e.symm

/-- The triangular separated algebra is finite over its diagonal base. -/
theorem triangularAlgebra_moduleFinite [Module.Finite S J] :
    Module.Finite S (Algebra S J) := by
  letI : Module.Finite S (SeparatedIdeal S J) :=
    separatedIdeal_moduleFinite
  change Module.Finite S ((S × S) × SeparatedIdeal S J)
  infer_instance

/-- Restricting a finite triangular-algebra module along the diagonal base
inclusion preserves finite generation. -/
theorem restrictDiagonal_moduleFinite [Module.Finite S J]
    (X : FGModuleCat.{w} (Algebra S J)) :
    letI : Module S X :=
      Module.compHom X (diagonalHom (S := S) (J := J))
    Module.Finite S X := by
  let A := Algebra S J
  let q : S →+* A := diagonalHom (S := S) (J := J)
  haveI : Module.Finite S A := triangularAlgebra_moduleFinite
  letI : Module S X := Module.compHom X q
  letI : IsScalarTower S A X :=
    ⟨fun s a x ↦ by
      have hsa : s • a = q s * a := by
        apply TrivSqZeroExt.ext
        · rfl
        · apply SeparatedIdeal.ext
          rw [TrivSqZeroExt.snd_smul, TrivSqZeroExt.snd_mul]
          dsimp only [q, diagonalHom]
          simp
          change s • a.snd.val = s • a.snd.val
          rfl
      change (s • a) • x = q s • (a • x)
      rw [hsa, mul_smul]⟩
  exact Module.Finite.trans A X

private theorem diagonalHom_eq_radicalScalar_add_topScalar (s : S) :
    diagonalHom (S := S) (J := J) s =
      (radicalScalar s : Algebra S J) + topScalar s := by
  calc
    diagonalHom (S := S) (J := J) s =
        (((s, s), ⟨0⟩) : Algebra S J) := rfl
    _ = (radicalScalar s : Algebra S J) + topScalar s +
        TrivSqZeroExt.inr ⟨0⟩ :=
      scalar_decomposition (S := S) (J := J) s s 0
    _ = (radicalScalar s : Algebra S J) + topScalar s := by
      rw [show (⟨0⟩ : SeparatedIdeal S J) = 0 by
        apply SeparatedIdeal.ext
        rfl]
      rw [TrivSqZeroExt.inr_zero]
      exact add_zero _

/-- The top-idempotent layer of a finite triangular-algebra module is finite
over the semisimple base. -/
theorem ofModule_top_moduleFinite
    [IsSemisimpleRing S] [Module.Finite S J]
    (X : FGModuleCat.{w} (Algebra S J)) :
    Module.Finite S (ofModule (S := S) (J := J) X.obj).top := by
  let A := Algebra S J
  let q : S →+* A := diagonalHom (S := S) (J := J)
  letI : Module S X := Module.compHom X q
  haveI : Module.Finite S X := restrictDiagonal_moduleFinite X
  haveI : IsNoetherian S X := inferInstance
  let l : (ofModule (S := S) (J := J) X.obj).top →ₗ[S] X :=
    { toFun := Subtype.val
      map_add' := fun _ _ ↦ rfl
      map_smul' := by
        intro s t
        change (topScalar s : A) • t.val = q s • t.val
        rw [diagonalHom_eq_radicalScalar_add_topScalar]
        rw [add_smul, radicalScalar_smul_top_eq_zero X.obj, zero_add] }
  haveI : IsNoetherian S (ofModule (S := S) (J := J) X.obj).top :=
    isNoetherian_of_injective l Subtype.val_injective
  infer_instance

/-- The radical-idempotent layer of a finite triangular-algebra module is
finite over the semisimple base. -/
theorem ofModule_radical_moduleFinite
    [IsSemisimpleRing S] [Module.Finite S J]
    (X : FGModuleCat.{w} (Algebra S J)) :
    Module.Finite S (ofModule (S := S) (J := J) X.obj).radical := by
  let A := Algebra S J
  let q : S →+* A := diagonalHom (S := S) (J := J)
  letI : Module S X := Module.compHom X q
  haveI : Module.Finite S X := restrictDiagonal_moduleFinite X
  haveI : IsNoetherian S X := inferInstance
  let l : (ofModule (S := S) (J := J) X.obj).radical →ₗ[S] X :=
    { toFun := Subtype.val
      map_add' := fun _ _ ↦ rfl
      map_smul' := by
        intro s d
        change (radicalScalar s : A) • d.val = q s • d.val
        rw [diagonalHom_eq_radicalScalar_add_topScalar]
        rw [add_smul, topScalar_smul_radical_eq_zero X.obj, add_zero] }
  haveI : IsNoetherian S (ofModule (S := S) (J := J) X.obj).radical :=
    isNoetherian_of_injective l Subtype.val_injective
  infer_instance

/-- Finite separated layers reconstruct to a finitely generated module over
the original trivial square-zero extension. -/
theorem reconstructed_moduleFinite
    (D : SeparatedData.{u, v, w} (S := S) (J := J))
    [Module.Finite S D.top] [Module.Finite S D.radical] :
    Module.Finite (TrivSqZeroExt S J) (Reconstructed D) := by
  let R := TrivSqZeroExt S J
  letI : Module R (Reconstructed D) := reconstructedModule D
  haveI : Module.Finite S (Reconstructed D) := by
    change Module.Finite S (D.top × D.radical)
    infer_instance
  letI : IsScalarTower S R (Reconstructed D) :=
    ⟨fun s r x ↦ by
      let q : R := TrivSqZeroExt.inl s
      have hsr : s • r = q * r := by
        rw [TrivSqZeroExt.inl_mul_eq_smul]
      calc
        (s • r) • x = (q * r) • x := by rw [hsr]
        _ = q • (r • x) := by rw [mul_smul]
        _ = s • (r • x) := by
          rcases r • x with ⟨t, d⟩
          apply Prod.ext
          · rfl
          · change s • d + D.action 0 t = s • d
            rw [map_zero, AddMonoidHom.zero_apply, add_zero]⟩
  exact Module.Finite.of_restrictScalars_finite S R (Reconstructed D)

/-- Extracting the two diagonal layers of a finite triangular module and
reconstructing them gives a finite original square-zero module. -/
theorem ofModule_reconstructed_moduleFinite
    [IsSemisimpleRing S] [Module.Finite S J]
    (X : FGModuleCat.{w} (Algebra S J)) :
    let D := ofModule (S := S) (J := J) X.obj
    letI : Module (TrivSqZeroExt S J) (Reconstructed D) :=
      reconstructedModule D
    Module.Finite (TrivSqZeroExt S J) (Reconstructed D) := by
  let D := ofModule (S := S) (J := J) X.obj
  letI : Module.Finite S D.top := ofModule_top_moduleFinite X
  letI : Module.Finite S D.radical := ofModule_radical_moduleFinite X
  exact reconstructed_moduleFinite D

end QuotientSubmoduleEquidistribution.TrivSqZeroExtSeparatedFinite
