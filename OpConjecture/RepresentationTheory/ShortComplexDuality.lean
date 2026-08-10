import OpConjecture.RepresentationTheory.ProjectiveInjectiveBoundary
import Mathlib.Algebra.Homology.ShortComplex.Preadditive
import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Three-term projective complexes and Hom duality

This file gives a source-faithful categorical model for the category used in
Ringel's proof.  A projective three-term complex is a short complex in the
full category of finitely generated projectives.  Its ordinary exactness is
measured after forgetting to `FGModuleCat`.  Any anti-equivalence of the
projective categories reverses such complexes, and its action extends to an
anti-equivalence of the corresponding short-complex categories.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace OpConjecture.RingelEta

universe u v u' v'

section ShortComplexEquivalence

variable {C : Type u} {D : Type u'}
  [Category.{v} C] [Category.{v'} D]
  [HasZeroMorphisms C] [HasZeroMorphisms D]

/-- An equivalence acts degreewise on short complexes. -/
def mapShortComplexEquivalence (E : C ≌ D) :
    ShortComplex C ≌ ShortComplex D where
  functor := E.functor.mapShortComplex
  inverse := E.inverse.mapShortComplex
  unitIso := NatIso.ofComponents
    (fun S ↦ S.mapNatIso E.unitIso)
    (fun {X Y} f ↦ by
      ext
      · exact E.unitIso.hom.naturality f.τ₁
      · exact E.unitIso.hom.naturality f.τ₂
      · exact E.unitIso.hom.naturality f.τ₃)
  counitIso := NatIso.ofComponents
    (fun S ↦ S.mapNatIso E.counitIso)
    (fun {X Y} f ↦ by
      ext
      · exact E.counitIso.hom.naturality f.τ₁
      · exact E.counitIso.hom.naturality f.τ₂
      · exact E.counitIso.hom.naturality f.τ₃)
  functor_unitIso_comp X := by
    ext
    · exact E.functor_unitIso_comp X.X₁
    · exact E.functor_unitIso_comp X.X₂
    · exact E.functor_unitIso_comp X.X₃

/-- An anti-equivalence reverses a three-term complex and then acts
degreewise.  This is the formal version of applying `Hom(-,Λ)` to
`P₁ → P₀ → P₋₁`. -/
def mapShortComplexAntiEquivalence (E : Cᵒᵖ ≌ D) :
    (ShortComplex C)ᵒᵖ ≌ ShortComplex D :=
  (ShortComplex.opEquiv C).trans
    (mapShortComplexEquivalence E)

@[simp]
theorem mapShortComplexAntiEquivalence_obj_X₁
    (E : Cᵒᵖ ≌ D) (S : ShortComplex C) :
    ((mapShortComplexAntiEquivalence E).functor.obj
      (Opposite.op S)).X₁ = E.functor.obj (Opposite.op S.X₃) :=
  rfl

@[simp]
theorem mapShortComplexAntiEquivalence_obj_X₂
    (E : Cᵒᵖ ≌ D) (S : ShortComplex C) :
    ((mapShortComplexAntiEquivalence E).functor.obj
      (Opposite.op S)).X₂ = E.functor.obj (Opposite.op S.X₂) :=
  rfl

@[simp]
theorem mapShortComplexAntiEquivalence_obj_X₃
    (E : Cᵒᵖ ≌ D) (S : ShortComplex C) :
    ((mapShortComplexAntiEquivalence E).functor.obj
      (Opposite.op S)).X₃ = E.functor.obj (Opposite.op S.X₁) :=
  rfl

@[simp]
theorem mapShortComplexAntiEquivalence_obj_f
    (E : Cᵒᵖ ≌ D) (S : ShortComplex C) :
    ((mapShortComplexAntiEquivalence E).functor.obj
      (Opposite.op S)).f = E.functor.map S.g.op :=
  rfl

@[simp]
theorem mapShortComplexAntiEquivalence_obj_g
    (E : Cᵒᵖ ≌ D) (S : ShortComplex C) :
    ((mapShortComplexAntiEquivalence E).functor.obj
      (Opposite.op S)).g = E.functor.map S.f.op :=
  rfl

end ShortComplexEquivalence

section ProjectiveComplex

variable {R : Type u} [Ring R] [IsNoetherianRing R]

open OpConjecture.RingelStable

/-- Three-term complexes of finitely generated projective modules. -/
abbrev ProjectiveComplex (R : Type u) [Ring R] [IsNoetherianRing R] :=
  ShortComplex (FGProjectives (R := R))

/-- Forget a projective three-term complex to finitely generated modules. -/
def forgetProjectiveComplex :
    ProjectiveComplex R ⥤ ShortComplex (FGModuleCat.{u} R) :=
  (ObjectProperty.ι (fgProjectiveProperty (R := R))).mapShortComplex

/-- Exactness of a projective complex in the ambient module category. -/
def ProjectiveComplex.Exact (S : ProjectiveComplex R) : Prop :=
  (forgetProjectiveComplex (R := R)).obj S |>.Exact

theorem ProjectiveComplex.Exact.isoInvariant
    {S T : ProjectiveComplex R} (e : S ≅ T)
    (hS : S.Exact) : T.Exact := by
  exact ShortComplex.exact_of_iso
    ((forgetProjectiveComplex (R := R)).mapIso e) hS

variable {S : Type u'} [Ring S] [IsNoetherianRing S]

/-- The Hom-dual of a three-term projective complex along a specified
anti-equivalence of finite projectives. -/
def ProjectiveComplex.homDual
    (H : (FGProjectives (R := R))ᵒᵖ ≌ FGProjectives (R := S))
    (P : ProjectiveComplex R) : ProjectiveComplex S :=
  (mapShortComplexAntiEquivalence H).functor.obj (Opposite.op P)

/-- Ringel's strong exactness condition: the projective complex is exact,
and its reversed Hom-dual complex is exact. -/
def ProjectiveComplex.StronglyExact
    (H : (FGProjectives (R := R))ᵒᵖ ≌ FGProjectives (R := S))
    (P : ProjectiveComplex R) : Prop :=
  P.Exact ∧ (P.homDual H).Exact

/-- The object property defining Ringel's category `E` for a chosen
projective Hom anti-equivalence. -/
def stronglyExactProperty
    (H : (FGProjectives (R := R))ᵒᵖ ≌ FGProjectives (R := S)) :
    ObjectProperty (ProjectiveComplex R) :=
  fun P ↦ P.StronglyExact H

/-- Ringel's category `E` of strongly exact three-term projective
complexes. -/
abbrev StronglyExactComplexCategory
    (H : (FGProjectives (R := R))ᵒᵖ ≌ FGProjectives (R := S)) :=
  (stronglyExactProperty H).FullSubcategory

section RingelHom

variable [IsNoetherianRing Rᵐᵒᵖ]

/-- Ringel's concrete projective Hom anti-equivalence. -/
abbrev regularHomProjectiveAntiEquivalence :
    (FGProjectives (R := R))ᵒᵖ ≌ FGProjectives (R := Rᵐᵒᵖ) :=
  fgProjectiveHomDuality (R := R)

/-- The source-faithful category `E(Λ)` appearing in Ringel's proof. -/
abbrev RingelE :=
  StronglyExactComplexCategory
    (regularHomProjectiveAntiEquivalence (R := R))

end RingelHom

end ProjectiveComplex

end OpConjecture.RingelEta
