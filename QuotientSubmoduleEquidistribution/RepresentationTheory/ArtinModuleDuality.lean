import QuotientSubmoduleEquidistribution.RepresentationTheory.RingelImageQuotient
import QuotientSubmoduleEquidistribution.RepresentationTheory.ContragredientDuality
import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Artin duality on torsionless and cotorsionless module categories

Finite-dimensional `K`-duality sends an embedding into a projective right
module to an epimorphism from an injective left module.  We prove the converse
using biduality, identify the two object properties exactly, and restrict the
maintained contragredient anti-equivalence to an anti-equivalence
`L(Rᵐᵒᵖ)ᵒᵖ ≃ K(R)`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace QuotientSubmoduleEquidistribution.RingelEta

universe u

open QuotientSubmoduleEquidistribution.RingelStable
open QuotientSubmoduleEquidistribution.RingelStable.FaithfulCoreAdapter

variable (K R : Type u)
  [Field K] [Ring R] [Algebra K R] [FiniteDimensional K R]
  [IsNoetherianRing R] [IsNoetherianRing Rᵐᵒᵖ]

omit [IsNoetherianRing R] [IsNoetherianRing Rᵐᵒᵖ] in
/-- Torsionlessness is invariant under isomorphism. -/
theorem torsionless_of_iso
    {X Y : FGModuleCat.{u} R} (e : X ≅ Y)
    (hX : Torsionless X) : Torsionless Y :=
  FaithfulCoreAdapter.torsionless_of_iso e hX

omit [IsNoetherianRing R] [IsNoetherianRing Rᵐᵒᵖ] in
/-- Cotorsionlessness is invariant under isomorphism. -/
theorem cotorsionless_of_iso
    {X Y : FGModuleCat.{u} R} (e : X ≅ Y)
    (hX : Cotorsionless X) : Cotorsionless Y :=
  FaithfulCoreAdapter.cotorsionless_of_iso e hX

/-- `K`-duality sends a torsionless `Rᵐᵒᵖ`-module to a cotorsionless
`R`-module. -/
theorem cotorsionless_reverseDual_of_torsionless
    (M : FGModuleCat.{u} Rᵐᵒᵖ) (hM : Torsionless M) :
    Cotorsionless
      ((QuotientSubmoduleEquidistribution.Contragredient.reverseDualityEquivalence K R).functor.obj
        (Opposite.op M)) := by
  let E := QuotientSubmoduleEquidistribution.Contragredient.reverseDualityEquivalence K R
  obtain ⟨P, f, hP, hf⟩ := hM
  letI : Mono f := hf
  letI : Epi f.op := inferInstance
  have hPop : Injective (Opposite.op P) :=
    Injective.projective_iff_injective_op.mp hP
  have hDP : Injective (E.functor.obj (Opposite.op P)) :=
    (E.map_injective_iff (Opposite.op P)).2 hPop
  exact ⟨E.functor.obj (Opposite.op P), E.functor.map f.op,
    hDP, inferInstance⟩

/-- Conversely, cotorsionlessness of the dual implies torsionlessness of the
original module.  The proof applies the inverse anti-equivalence and then
uses the bidual unit isomorphism. -/
theorem torsionless_of_cotorsionless_reverseDual
    (M : FGModuleCat.{u} Rᵐᵒᵖ)
    (hM : Cotorsionless
      ((QuotientSubmoduleEquidistribution.Contragredient.reverseDualityEquivalence K R).functor.obj
        (Opposite.op M))) :
    Torsionless M := by
  let E := QuotientSubmoduleEquidistribution.Contragredient.reverseDualityEquivalence K R
  let B := E.rightOp.symm
  let Y := E.functor.obj (Opposite.op M)
  obtain ⟨I, p, hI, hp⟩ := hM
  letI : Epi p := hp
  letI : Mono p.op := inferInstance
  have hIop : Projective (Opposite.op I) :=
    Injective.injective_iff_projective_op.mp hI
  have hBI : Projective (B.functor.obj (Opposite.op I)) :=
    (B.map_projective_iff (Opposite.op I)).2 hIop
  have hdual : Torsionless (B.functor.obj (Opposite.op Y)) :=
    ⟨B.functor.obj (Opposite.op I), B.functor.map p.op,
      hBI, inferInstance⟩
  exact torsionless_of_iso (R := Rᵐᵒᵖ)
    (E.unitIso.app (Opposite.op M)).unop hdual

/-- Exact object-property identity underlying Artin duality. -/
theorem cotorsionless_inverseImage_reverseDual_eq_torsionless_op :
    (cotorsionlessModuleProperty (R := R)).inverseImage
        (QuotientSubmoduleEquidistribution.Contragredient.reverseDualityEquivalence K R).functor =
      (torsionlessModuleProperty (R := Rᵐᵒᵖ)).op := by
  ext X
  induction X with
  | op M =>
      exact ⟨torsionless_of_cotorsionless_reverseDual K R M,
        cotorsionless_reverseDual_of_torsionless K R M⟩

/-- Artin `K`-duality restricted to torsionless modules on the opposite side
and cotorsionless modules on the original side. -/
def artinTorsionlessCotorsionlessAntiEquivalence :
    (TorsionlessModuleCategory (R := Rᵐᵒᵖ))ᵒᵖ ≌
      CotorsionlessModuleCategory (R := R) :=
  (ObjectProperty.opEquivalence
      (torsionlessModuleProperty (R := Rᵐᵒᵖ))).symm |>.trans
    ((QuotientSubmoduleEquidistribution.Contragredient.reverseDualityEquivalence K R).congrFullSubcategory
      (cotorsionless_inverseImage_reverseDual_eq_torsionless_op K R))

end QuotientSubmoduleEquidistribution.RingelEta
