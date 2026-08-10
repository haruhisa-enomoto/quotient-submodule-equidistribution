import QuotientSubmoduleEquidistribution.RepresentationTheory.Trace

/-!
# Stable isomorphisms of indecomposable nonprojectives

This is the Krull--Schmidt step used implicitly in Ringel's passage from
his stable duality to a bijection on indecomposable torsionless modules.
-/

noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.RingelStable

universe u

variable {R : Type u} [Ring R]

/-- A categorical morphism factors through a finitely generated
categorical projective. -/
structure FactorsThroughProjective
    {X Y : FGModuleCat.{u} R} (f : X ⟶ Y) where
  middle : FGModuleCat.{u} R
  projective : Projective middle
  left : X ⟶ middle
  right : middle ⟶ Y
  fac : left ≫ right = f

/-- The concrete two-sided inverse data represented by an isomorphism in
the stable category modulo projectives. -/
structure StableIso (X Y : FGModuleCat.{u} R) where
  hom : X ⟶ Y
  inv : Y ⟶ X
  hom_inv_diff :
    FactorsThroughProjective (hom ≫ inv - CategoryStruct.id X)
  inv_hom_diff :
    FactorsThroughProjective (inv ≫ hom - CategoryStruct.id Y)

/-- If an endomorphism of a finite module factors through a categorical
projective and is invertible as a linear map, then the module is itself
categorically projective. -/
theorem projective_of_isUnit_of_factorsThroughProjective
    {X : FGModuleCat.{u} R} {f : X ⟶ X}
    (hf : FactorsThroughProjective f)
    (hu : IsUnit f.hom.hom) :
    Projective X := by
  rcases hf with ⟨P, hP, a, b, hab⟩
  letI : Projective P := hP
  have hbij : Function.Bijective f.hom.hom :=
    (Module.End.isUnit_iff f.hom.hom).1 hu
  let U := forget₂ (FGModuleCat R) (ModuleCat R)
  letI : IsIso (U.map f) := by
    change IsIso f.hom
    exact (ConcreteCategory.isIso_iff_bijective f.hom).2 hbij
  letI : IsIso f := isIso_of_reflects_iso f U
  let r : Retract X P :=
    {
    i := a
    r := b ≫ inv f
    retract := by rw [← Category.assoc, hab]; simp }
  exact r.projective

/-- A factor-through-projective endomorphism of a nonprojective object is
not a unit. -/
theorem not_isUnit_of_factorsThroughProjective
    {X : FGModuleCat.{u} R} {f : X ⟶ X}
    (hX : ¬ Projective X)
    (hf : FactorsThroughProjective f) :
    ¬ IsUnit f.hom.hom := by
  intro hu
  exact hX
    (projective_of_isUnit_of_factorsThroughProjective hf hu)

private theorem composite_bijective_of_stableIso
    {X Y : FGModuleCat.{u} R}
    (hXindec : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R X)
    (hXfinite : IsFiniteLength R X)
    (hXnonproj : ¬ Projective X)
    (f : X ⟶ Y) (g : Y ⟶ X)
    (hfac : FactorsThroughProjective
      (f ≫ g - CategoryStruct.id X)) :
    Function.Bijective (f ≫ g).hom.hom := by
  letI : IsNoetherian R X :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hXfinite).1
  letI : IsArtinian R X :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hXfinite).2
  let d : Module.End R X :=
    (f ≫ g - CategoryStruct.id X).hom.hom
  have hdnonunit : ¬ IsUnit d :=
    not_isUnit_of_factorsThroughProjective hXnonproj hfac
  have hdnil : IsNilpotent d :=
    (hXindec.isNilpotent_iff_not_isUnit d).2 hdnonunit
  have hunit : IsUnit (f ≫ g).hom.hom := by
    have hEq : (1 + d : Module.End R X) = (f ≫ g).hom.hom := by
      ext x
      change x + (g.hom.hom (f.hom.hom x) - x) =
        g.hom.hom (f.hom.hom x)
      abel
    rw [← hEq]
    exact hdnil.isUnit_one_add
  exact (Module.End.isUnit_iff (f ≫ g).hom.hom).1 hunit

/-- Stable-isomorphic indecomposable nonprojective finite modules are
already isomorphic.  This is the load-bearing Krull--Schmidt reflection
step behind Ringel's Corollary 1. -/
theorem nonempty_iso_of_stableIso
    {X Y : FGModuleCat.{u} R}
    (hXindec : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R X)
    (hYindec : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R Y)
    (hXfinite : IsFiniteLength R X)
    (hYfinite : IsFiniteLength R Y)
    (hXnonproj : ¬ Projective X)
    (hYnonproj : ¬ Projective Y)
    (e : StableIso X Y) :
    Nonempty (X ≅ Y) := by
  have hfg : Function.Bijective (e.hom ≫ e.inv).hom.hom :=
    composite_bijective_of_stableIso
      hXindec hXfinite hXnonproj e.hom e.inv e.hom_inv_diff
  have hgf : Function.Bijective (e.inv ≫ e.hom).hom.hom :=
    composite_bijective_of_stableIso
      hYindec hYfinite hYnonproj e.inv e.hom e.inv_hom_diff
  have hinj : Function.Injective e.hom.hom.hom := by
    intro x y hxy
    apply hfg.1
    change e.inv.hom.hom (e.hom.hom.hom x) =
      e.inv.hom.hom (e.hom.hom.hom y)
    rw [hxy]
  have hsurj : Function.Surjective e.hom.hom.hom := by
    intro y
    obtain ⟨z, hz⟩ := hgf.2 y
    refine ⟨e.inv.hom.hom z, ?_⟩
    exact hz
  let U := forget₂ (FGModuleCat R) (ModuleCat R)
  letI : IsIso (U.map e.hom) := by
    change IsIso e.hom.hom
    exact
      (ConcreteCategory.isIso_iff_bijective e.hom.hom).2
        ⟨hinj, hsurj⟩
  letI : IsIso e.hom := isIso_of_reflects_iso e.hom U
  exact ⟨asIso e.hom⟩

/-! ## The injective-stable dual -/

/-- A categorical morphism factors through a finitely generated
categorical injective. -/
structure FactorsThroughInjective
    {X Y : FGModuleCat.{u} R} (f : X ⟶ Y) where
  middle : FGModuleCat.{u} R
  injective : Injective middle
  left : X ⟶ middle
  right : middle ⟶ Y
  fac : left ≫ right = f

/-- Concrete inverse data modulo morphisms factoring through injectives. -/
structure InjectiveStableIso (X Y : FGModuleCat.{u} R) where
  hom : X ⟶ Y
  inv : Y ⟶ X
  hom_inv_diff :
    FactorsThroughInjective (hom ≫ inv - CategoryStruct.id X)
  inv_hom_diff :
    FactorsThroughInjective (inv ≫ hom - CategoryStruct.id Y)

/-- The injective analogue of
`projective_of_isUnit_of_factorsThroughProjective`. -/
theorem injective_of_isUnit_of_factorsThroughInjective
    {X : FGModuleCat.{u} R} {f : X ⟶ X}
    (hf : FactorsThroughInjective f)
    (hu : IsUnit f.hom.hom) :
    Injective X := by
  rcases hf with ⟨I, hI, a, b, hab⟩
  letI : Injective I := hI
  have hbij : Function.Bijective f.hom.hom :=
    (Module.End.isUnit_iff f.hom.hom).1 hu
  let U := forget₂ (FGModuleCat R) (ModuleCat R)
  letI : IsIso (U.map f) := by
    change IsIso f.hom
    exact (ConcreteCategory.isIso_iff_bijective f.hom).2 hbij
  letI : IsIso f := isIso_of_reflects_iso f U
  let r : Retract X I :=
    {
    i := a
    r := b ≫ inv f
    retract := by rw [← Category.assoc, hab]; simp }
  exact r.injective

/-- A factor-through-injective endomorphism of a noninjective object is
not a unit. -/
theorem not_isUnit_of_factorsThroughInjective
    {X : FGModuleCat.{u} R} {f : X ⟶ X}
    (hX : ¬ Injective X)
    (hf : FactorsThroughInjective f) :
    ¬ IsUnit f.hom.hom := by
  intro hu
  exact hX (injective_of_isUnit_of_factorsThroughInjective hf hu)

private theorem composite_bijective_of_injectiveStableIso
    {X Y : FGModuleCat.{u} R}
    (hXindec : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R X)
    (hXfinite : IsFiniteLength R X)
    (hXnoninj : ¬ Injective X)
    (f : X ⟶ Y) (g : Y ⟶ X)
    (hfac : FactorsThroughInjective
      (f ≫ g - CategoryStruct.id X)) :
    Function.Bijective (f ≫ g).hom.hom := by
  letI : IsNoetherian R X :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hXfinite).1
  letI : IsArtinian R X :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hXfinite).2
  let d : Module.End R X :=
    (f ≫ g - CategoryStruct.id X).hom.hom
  have hdnonunit : ¬ IsUnit d :=
    not_isUnit_of_factorsThroughInjective hXnoninj hfac
  have hdnil : IsNilpotent d :=
    (hXindec.isNilpotent_iff_not_isUnit d).2 hdnonunit
  have hunit : IsUnit (f ≫ g).hom.hom := by
    have hEq : (1 + d : Module.End R X) = (f ≫ g).hom.hom := by
      ext x
      change x + (g.hom.hom (f.hom.hom x) - x) =
        g.hom.hom (f.hom.hom x)
      abel
    rw [← hEq]
    exact hdnil.isUnit_one_add
  exact (Module.End.isUnit_iff (f ≫ g).hom.hom).1 hunit

/-- Injective-stable-isomorphic indecomposable noninjective finite modules
are already isomorphic. -/
theorem nonempty_iso_of_injectiveStableIso
    {X Y : FGModuleCat.{u} R}
    (hXindec : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R X)
    (hYindec : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R Y)
    (hXfinite : IsFiniteLength R X)
    (hYfinite : IsFiniteLength R Y)
    (hXnoninj : ¬ Injective X)
    (hYnoninj : ¬ Injective Y)
    (e : InjectiveStableIso X Y) :
    Nonempty (X ≅ Y) := by
  have hfg : Function.Bijective (e.hom ≫ e.inv).hom.hom :=
    composite_bijective_of_injectiveStableIso
      hXindec hXfinite hXnoninj e.hom e.inv e.hom_inv_diff
  have hgf : Function.Bijective (e.inv ≫ e.hom).hom.hom :=
    composite_bijective_of_injectiveStableIso
      hYindec hYfinite hYnoninj e.inv e.hom e.inv_hom_diff
  have hinj : Function.Injective e.hom.hom.hom := by
    intro x y hxy
    apply hfg.1
    change e.inv.hom.hom (e.hom.hom.hom x) =
      e.inv.hom.hom (e.hom.hom.hom y)
    rw [hxy]
  have hsurj : Function.Surjective e.hom.hom.hom := by
    intro y
    obtain ⟨z, hz⟩ := hgf.2 y
    refine ⟨e.inv.hom.hom z, ?_⟩
    exact hz
  let U := forget₂ (FGModuleCat R) (ModuleCat R)
  letI : IsIso (U.map e.hom) := by
    change IsIso e.hom.hom
    exact
      (ConcreteCategory.isIso_iff_bijective e.hom.hom).2
        ⟨hinj, hsurj⟩
  letI : IsIso e.hom := isIso_of_reflects_iso e.hom U
  exact ⟨asIso e.hom⟩

end QuotientSubmoduleEquidistribution.RingelStable
