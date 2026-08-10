import QuotientSubmoduleEquidistribution.RepresentationTheory.AuslanderTranspose
import QuotientSubmoduleEquidistribution.RepresentationTheory.NoParallelExtOne
import QuotientSubmoduleEquidistribution.RepresentationTheory.StableHomExtAlmostSplit
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
import Mathlib.CategoryTheory.Abelian.ShortExact

/-!
# Realizing degree-one Ext classes by finite short exact sequences

Every `Ext¹` class between finitely generated modules over a left Noetherian
ring is represented by a short exact sequence whose middle term is again
finitely generated.  Combining this realization theorem with the abstract
stable Hom--Ext socle pairing produces an actual right almost-split morphism.

The construction is general and presentation-theoretic.  It uses a finite
free presentation and an explicit pushout; no concrete algebra or module
classification occurs.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace QuotientSubmoduleEquidistribution.FGExtRealization

universe u uQ vQ uOmega

open QuotientSubmoduleEquidistribution.NoParallelExtOne

variable {R : Type u} [Ring R]

/-- The fully faithful inclusion of finitely generated modules into all
modules. -/
abbrev inclusion : FGModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)

instance inclusion_additive : (inclusion (R := R)).Additive where
  map_add := rfl

/-- A projective finitely generated module remains projective after forgetting
finite generation. -/
instance inclusion_preservesProjectiveObjects :
    (inclusion (R := R)).PreservesProjectiveObjects where
  projective_obj {X} hX := by
    letI : Module.Projective R X :=
      QuotientSubmoduleEquidistribution.RingelStable.moduleProjective_of_fgProjective X hX
    exact X.obj.projective_of_categoryTheory_projective

namespace PushoutExtension

variable {P S T : Type u}
  [AddCommGroup P] [AddCommGroup S] [AddCommGroup T]
  [Module R P] [Module R S] [Module R T]
  [Module.Finite R P] [Module.Finite R S] [Module.Finite R T]

/-- The existing explicit pushout sequence, with its finite objects bundled
in `FGModuleCat`. -/
abbrev fgShortComplex
    (p : P →ₗ[R] S) (f : LinearMap.ker p →ₗ[R] T) :
    ShortComplex (FGModuleCat.{u} R) :=
  ShortComplex.mk
    (FGModuleCat.ofHom (NoParallelExtOne.PushoutExtension.inclusion p f))
    (FGModuleCat.ofHom (NoParallelExtOne.PushoutExtension.projection p f))
    (by
      apply FGModuleCat.hom_ext
      ext t
      change NoParallelExtOne.PushoutExtension.projection p f
          ((NoParallelExtOne.PushoutExtension.relation p f).mkQ (t, 0)) = 0
      simpa using
        NoParallelExtOne.PushoutExtension.projection_mkQ p f (t, 0))

/-- Forgetting finite generation recovers the ambient pushout complex
definitionally. -/
theorem fgShortComplex_map_inclusion
    (p : P →ₗ[R] S) (f : LinearMap.ker p →ₗ[R] T) :
    (fgShortComplex p f).map (inclusion (R := R)) =
      NoParallelExtOne.PushoutExtension.shortComplex p f := by
  rfl

/-- The finite pushout complex is short exact, reflected from `ModuleCat`. -/
theorem fgShortExact
    [IsNoetherianRing R]
    (p : P →ₗ[R] S) (hp : Function.Surjective p)
    (f : LinearMap.ker p →ₗ[R] T) :
    (fgShortComplex p f).ShortExact := by
  apply ShortExact.reflects_shortExact_of_faithful (inclusion (R := R))
  simpa [fgShortComplex_map_inclusion] using
    NoParallelExtOne.PushoutExtension.shortExact p hp f

end PushoutExtension

variable [IsNoetherianRing R] [HasExt.{u} (FGModuleCat.{u} R)]

/-- Every degree-one Ext class between finitely generated modules is
represented by a short exact sequence with finitely generated middle term. -/
theorem exists_shortExact_with_extClass_eq
    (X T : FGModuleCat.{u} R) (xi : Ext X T 1) :
    ∃ (E : FGModuleCat.{u} R) (i : T ⟶ E) (q : E ⟶ X)
      (zero : i ≫ q = 0)
      (hS : (ShortComplex.mk i q zero).ShortExact),
      hS.extClass = xi := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R X
  let xiAmbient :
      Ext ((inclusion (R := R)).obj X) ((inclusion (R := R)).obj T) 1 :=
    xi.mapExactFunctor (inclusion (R := R))
  obtain ⟨f, hf⟩ :=
    NoParallelExtOne.PushoutExtension.exists_pushout_with_extClass_eq
      p hp xiAmbient
  let S : ShortComplex (FGModuleCat.{u} R) :=
    PushoutExtension.fgShortComplex p f
  let hS : S.ShortExact := PushoutExtension.fgShortExact p hp f
  refine ⟨S.X₂, S.f, S.g, S.zero, hS, ?_⟩
  apply
    ((inclusion (R := R)).mapExt_bijective_of_preservesProjectiveObjects
      X T 1).injective
  change hS.extClass.mapExactFunctor (inclusion (R := R)) =
    xi.mapExactFunctor (inclusion (R := R))
  rw [Ext.mapExactFunctor_extClass]
  convert hf using 1 <;> rfl

/-- A stable Hom--Ext socle pairing on finitely generated modules produces a
right almost-split morphism realizing its distinguished class. -/
theorem _root_.QuotientSubmoduleEquidistribution.StableHomExtSoclePairing.exists_rightAlmostSplit
    {QCat : Type uQ} [Category.{vQ} QCat]
    {Q : FGModuleCat.{u} R ⥤ QCat} [Q.Full]
    {X T : FGModuleCat.{u} R}
    {Omega : Type uOmega} [Zero Omega]
    (P : StableHomExtSoclePairing Q X T Omega) :
    ∃ (E : FGModuleCat.{u} R) (i : T ⟶ E) (q : E ⟶ X)
      (zero : i ≫ q = 0)
      (hS : (ShortComplex.mk i q zero).ShortExact),
      hS.extClass = P.socleClass ∧ IsRightAlmostSplit q := by
  obtain ⟨E, i, q, zero, hS, hclass⟩ :=
    exists_shortExact_with_extClass_eq X T P.socleClass
  exact ⟨E, i, q, zero, hS, hclass,
    P.isRightAlmostSplit_of_realizes_socleClass i q zero hS hclass⟩

end QuotientSubmoduleEquidistribution.FGExtRealization
