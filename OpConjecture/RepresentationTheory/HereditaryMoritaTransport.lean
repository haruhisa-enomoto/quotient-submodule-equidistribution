import OpConjecture.RepresentationTheory.ConnectedSmallCoreHereditary
import OpConjecture.RepresentationTheory.MoritaConsequences

/-!
# Morita transport of finite left heredity

Finite left heredity is categorical in the finitely generated module
category: an equivalence preserves monomorphisms and projective objects.
This file proves that statement directly for the project predicate used by
the small-core arguments.
-/

noncomputable section

open CategoryTheory

namespace OpConjecture.HereditaryMoritaTransport

universe u

open OpConjecture.IndecomposableSkeleton
open OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore

/-- An equivalence of finitely generated module categories transports the
property that every submodule of a finitely generated projective module is
projective. -/
theorem finitelyGeneratedLeftHereditary_of_fgEquivalence
    {A B : Type u}
    [Ring A] [IsNoetherianRing A]
    [Ring B] [IsNoetherianRing B]
    (E : FGModuleCat.{u} A ≌ FGModuleCat.{u} B)
    (hA : FinitelyGeneratedLeftHereditary A) :
    FinitelyGeneratedLeftHereditary B := by
  intro P hP S
  let X : FGModuleCat.{u} B := FGModuleCat.of B S
  let f : X ⟶ P := FGModuleCat.ofHom S.subtype
  haveI : Mono f :=
    ConcreteCategory.mono_of_injective f S.subtype_injective

  let g : E.inverse.obj X ⟶ E.inverse.obj P := E.inverse.map f
  haveI : Mono g := E.inverse.map_mono f
  have hg : Function.Injective g.hom.hom :=
    (fg_mono_iff_injective g).mp inferInstance

  let T : Submodule A (E.inverse.obj P) :=
    LinearMap.range g.hom.hom
  have hT : Module.Projective A T :=
    hA (E.inverse.obj P)
      ((E.symm.map_projective_iff P).mpr hP) T

  let e : E.inverse.obj X ≃ₗ[A] T :=
    LinearEquiv.ofInjective g.hom.hom hg
  have hEXmodule : Module.Projective A (E.inverse.obj X) := by
    letI : Module.Projective A T := hT
    exact Module.Projective.of_equiv' e.symm
  have hEX : Projective (E.inverse.obj X) :=
    OpConjecture.RingelStable.fgProjective_of_moduleProjective
      (E.inverse.obj X) hEXmodule

  exact
    OpConjecture.RingelStable.moduleProjective_of_fgProjective X
      ((E.symm.map_projective_iff X).mp hEX)

/-- Finite left heredity is invariant under an equivalence of finitely
generated module categories. -/
theorem finitelyGeneratedLeftHereditary_iff_of_fgEquivalence
    {A B : Type u}
    [Ring A] [IsNoetherianRing A]
    [Ring B] [IsNoetherianRing B]
    (E : FGModuleCat.{u} A ≌ FGModuleCat.{u} B) :
    FinitelyGeneratedLeftHereditary A ↔
      FinitelyGeneratedLeftHereditary B :=
  ⟨finitelyGeneratedLeftHereditary_of_fgEquivalence E,
    finitelyGeneratedLeftHereditary_of_fgEquivalence E.symm⟩

end OpConjecture.HereditaryMoritaTransport
