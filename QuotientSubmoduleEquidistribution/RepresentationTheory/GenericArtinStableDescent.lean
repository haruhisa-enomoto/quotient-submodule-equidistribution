import QuotientSubmoduleEquidistribution.RepresentationTheory.StableCoreCategories

/-!
# Stable descent of an arbitrary finite-module anti-equivalence

Any equivalence from the opposite category of finite right modules to finite
left modules is automatically additive.  It exchanges projectives with
injectives, torsionless modules with cotorsionless modules, and the two
factor-through ideals.  Consequently it descends, without extra data, to an
anti-equivalence between the corresponding stable categories.

This is the generic categorical part of Artin duality.  Constructing the
finite-module anti-equivalence itself over a general commutative Artinian base
remains a separate input.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace QuotientSubmoduleEquidistribution.ArtinDuality

universe u

open QuotientSubmoduleEquidistribution.RingelStable
open QuotientSubmoduleEquidistribution.RingelStable.FaithfulCoreAdapter

variable {R : Type u} [Ring R]
  (E : (FGModuleCat.{u} Rᵐᵒᵖ)ᵒᵖ ≌ FGModuleCat.{u} R)

/-- An equivalence between the finite module categories is automatically
additive because it preserves binary products. -/
instance moduleAntiEquivalence_functor_additive : E.functor.Additive :=
  Functor.additive_of_preserves_binary_products E.functor

/-- An arbitrary finite-module anti-equivalence sends torsionless right
modules to cotorsionless left modules. -/
theorem cotorsionless_map_of_torsionless
    (M : FGModuleCat.{u} Rᵐᵒᵖ) (hM : Torsionless M) :
    Cotorsionless (E.functor.obj (Opposite.op M)) := by
  obtain ⟨P, f, hP, hf⟩ := hM
  letI : Mono f := hf
  letI : Epi f.op := inferInstance
  have hPop : Injective (Opposite.op P) :=
    Injective.projective_iff_injective_op.mp hP
  have hEP : Injective (E.functor.obj (Opposite.op P)) :=
    (E.map_injective_iff (Opposite.op P)).2 hPop
  exact ⟨E.functor.obj (Opposite.op P), E.functor.map f.op,
    hEP, inferInstance⟩

/-- Reflection through the inverse equivalence gives the converse
torsionless criterion. -/
theorem torsionless_of_cotorsionless_map
    (M : FGModuleCat.{u} Rᵐᵒᵖ)
    (hM : Cotorsionless (E.functor.obj (Opposite.op M))) :
    Torsionless M := by
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

/-- Exact object-property identity underlying generic Artin duality. -/
theorem cotorsionless_inverseImage_eq_torsionless_op :
    (cotorsionlessModuleProperty (R := R)).inverseImage E.functor =
      (torsionlessModuleProperty (R := Rᵐᵒᵖ)).op := by
  ext X
  induction X with
  | op M =>
      exact ⟨torsionless_of_cotorsionless_map E M,
        cotorsionless_map_of_torsionless E M⟩

/-- Restriction of the module anti-equivalence to torsionless and
cotorsionless objects before taking stable quotients. -/
def torsionlessCotorsionlessAntiEquivalence :
    (TorsionlessModuleCategory (R := Rᵐᵒᵖ))ᵒᵖ ≌
      CotorsionlessModuleCategory (R := R) :=
  (ObjectProperty.opEquivalence
      (torsionlessModuleProperty (R := Rᵐᵒᵖ))).symm |>.trans
    (E.congrFullSubcategory
      (cotorsionless_inverseImage_eq_torsionless_op E))

/-- Mapping the opposite of a projective factorization gives an injective
factorization. -/
def factorsThroughInjective_map_op
    {X Y : FGModuleCat.{u} Rᵐᵒᵖ} {f : X ⟶ Y}
    (hf : FactorsThroughProjective f) :
    FactorsThroughInjective (E.functor.map f.op) := by
  have hPop : Injective (Opposite.op hf.middle) :=
    Injective.projective_iff_injective_op.mp hf.projective
  exact
    { middle := E.functor.obj (Opposite.op hf.middle)
      injective := (E.map_injective_iff (Opposite.op hf.middle)).2 hPop
      left := E.functor.map hf.right.op
      right := E.functor.map hf.left.op
      fac := by
        rw [← E.functor.map_comp]
        change E.functor.map (hf.left ≫ hf.right).op = E.functor.map f.op
        rw [hf.fac] }

/-- Reflection through the inverse equivalence recovers the original
projective factorization. -/
def factorsThroughProjective_of_map_op
    {X Y : FGModuleCat.{u} Rᵐᵒᵖ} {f : X ⟶ Y}
    (hf : FactorsThroughInjective (E.functor.map f.op)) :
    FactorsThroughProjective f := by
  have hGI : Injective (E.inverse.obj hf.middle) :=
    (E.symm.map_injective_iff hf.middle).2 hf.injective
  have hP : Projective (E.inverse.obj hf.middle).unop := by
    apply Injective.projective_iff_injective_op.mpr
    simpa using hGI
  let leftDual :
      E.functor.obj (Opposite.op Y) ⟶
        E.functor.obj (E.inverse.obj hf.middle) :=
    hf.left ≫ E.counitIso.inv.app hf.middle
  let rightDual :
      E.functor.obj (E.inverse.obj hf.middle) ⟶
        E.functor.obj (Opposite.op X) :=
    E.counitIso.hom.app hf.middle ≫ hf.right
  let leftLift := E.functor.preimage leftDual
  let rightLift := E.functor.preimage rightDual
  have hop : leftLift ≫ rightLift = f.op := by
    apply E.functor.map_injective
    rw [E.functor.map_comp, Functor.map_preimage, Functor.map_preimage]
    simp [leftDual, rightDual, Category.assoc, hf.fac]
  exact
    { middle := (E.inverse.obj hf.middle).unop
      projective := hP
      left := rightLift.unop
      right := leftLift.unop
      fac := by
        apply Quiver.Hom.op_inj
        simpa only [op_comp, Quiver.Hom.op_unop] using hop }

/-- The projective-factor ideal is carried onto the injective-factor ideal. -/
theorem factorsThroughInjective_map_op_iff
    {X Y : FGModuleCat.{u} Rᵐᵒᵖ} (f : X ⟶ Y) :
    Nonempty (FactorsThroughInjective (E.functor.map f.op)) ↔
      Nonempty (FactorsThroughProjective f) := by
  constructor
  · rintro ⟨hf⟩
    exact ⟨factorsThroughProjective_of_map_op E hf⟩
  · rintro ⟨hf⟩
    exact ⟨factorsThroughInjective_map_op E hf⟩

/-- Additivity converts a factorization of `f-g` to the difference of the
two mapped morphisms. -/
def factorsThroughInjective_map_difference
    {X Y : FGModuleCat.{u} Rᵐᵒᵖ} (f g : X ⟶ Y)
    (hfg : FactorsThroughProjective (f - g)) :
    FactorsThroughInjective
      (E.functor.map f.op - E.functor.map g.op) := by
  have h := factorsThroughInjective_map_op E hfg
  convert h using 1
  rw [← E.functor.map_sub]
  rfl

/-- Descent to the ambient projective- and injective-stable quotients. -/
def ambientStableFunctor :
    (ProjectiveStableCategory (R := Rᵐᵒᵖ))ᵒᵖ ⥤
      InjectiveStableCategory (R := R) where
  obj X :=
    (injectiveStableFunctor (R := R)).obj
      (E.functor.obj (Opposite.op X.unop.as))
  map {X Y} f :=
    Quot.liftOn f.unop
      (fun h ↦
        (injectiveStableFunctor (R := R)).map (E.functor.map h.op))
      (by
        intro h h' hh'
        apply (injectiveStable_map_eq_iff _ _).2
        have hrel : projectiveStableRel (R := Rᵐᵒᵖ) h h' :=
          (HomRel.compClosure_iff_self _ h h').1 hh'
        rcases hrel with ⟨hrel⟩
        exact ⟨factorsThroughInjective_map_difference E h h' hrel⟩)
  map_id X := by
    change (injectiveStableFunctor (R := R)).map
      (E.functor.map (𝟙 X.unop.as).op) = 𝟙 _
    rw [op_id, E.functor.map_id,
      (injectiveStableFunctor (R := R)).map_id]
  map_comp {X Y Z} f g := by
    rw [unop_comp]
    refine Quot.inductionOn f.unop ?_
    intro f
    refine Quot.inductionOn g.unop ?_
    intro g
    change (injectiveStableFunctor (R := R)).map
        (E.functor.map (g ≫ f).op) =
      (injectiveStableFunctor (R := R)).map
          (E.functor.map f.op) ≫
        (injectiveStableFunctor (R := R)).map
          (E.functor.map g.op)
    rw [op_comp, E.functor.map_comp,
      (injectiveStableFunctor (R := R)).map_comp]

/-- Equality after descent is exactly the original projective-factor
congruence. -/
theorem ambientStableFunctor_map_quotient_eq_iff
    {X Y : FGModuleCat.{u} Rᵐᵒᵖ} (f g : X ⟶ Y) :
    (ambientStableFunctor E).map
          ((projectiveStableFunctor (R := Rᵐᵒᵖ)).map f).op =
        (ambientStableFunctor E).map
          ((projectiveStableFunctor (R := Rᵐᵒᵖ)).map g).op ↔
      Nonempty (FactorsThroughProjective (f - g)) := by
  change
    (injectiveStableFunctor (R := R)).map (E.functor.map f.op) =
        (injectiveStableFunctor (R := R)).map (E.functor.map g.op) ↔
      Nonempty (FactorsThroughProjective (f - g))
  rw [injectiveStable_map_eq_iff]
  have hmap :
      E.functor.map f.op - E.functor.map g.op =
        E.functor.map (f - g).op := by
    rw [← E.functor.map_sub]
    rfl
  rw [hmap]
  exact factorsThroughInjective_map_op_iff E (f - g)

instance ambientStableFunctor_full :
    (ambientStableFunctor E).Full where
  map_surjective {X Y} f := by
    let h := (injectiveStableFunctor (R := R)).preimage f
    let k := E.functor.preimage h
    refine ⟨((projectiveStableFunctor (R := Rᵐᵒᵖ)).map k.unop).op, ?_⟩
    change (injectiveStableFunctor (R := R)).map
      (E.functor.map k) = f
    rw [Functor.map_preimage, Functor.map_preimage]

instance ambientStableFunctor_faithful :
    (ambientStableFunctor E).Faithful where
  map_injective {X Y} f g hfg := by
    let f₀ :=
      (projectiveStableFunctor (R := Rᵐᵒᵖ)).preimage f.unop
    let g₀ :=
      (projectiveStableFunctor (R := Rᵐᵒᵖ)).preimage g.unop
    have hf :
        ((projectiveStableFunctor (R := Rᵐᵒᵖ)).map f₀).op = f := by
      apply Quiver.Hom.unop_inj
      exact (projectiveStableFunctor (R := Rᵐᵒᵖ)).map_preimage f.unop
    have hg :
        ((projectiveStableFunctor (R := Rᵐᵒᵖ)).map g₀).op = g := by
      apply Quiver.Hom.unop_inj
      exact (projectiveStableFunctor (R := Rᵐᵒᵖ)).map_preimage g.unop
    have hcanon :
        (ambientStableFunctor E).map
            ((projectiveStableFunctor (R := Rᵐᵒᵖ)).map f₀).op =
          (ambientStableFunctor E).map
            ((projectiveStableFunctor (R := Rᵐᵒᵖ)).map g₀).op := by
      rw [hf, hg]
      exact hfg
    have hfactor : Nonempty (FactorsThroughProjective (f₀ - g₀)) :=
      (ambientStableFunctor_map_quotient_eq_iff E f₀ g₀).1 hcanon
    have hquot :
        (projectiveStableFunctor (R := Rᵐᵒᵖ)).map f₀ =
          (projectiveStableFunctor (R := Rᵐᵒᵖ)).map g₀ :=
      (projectiveStable_map_eq_iff f₀ g₀).2 hfactor
    exact hf.symm.trans ((congrArg Quiver.Hom.op hquot).trans hg)

/-- Restriction of the ambient descent to torsionless and cotorsionless
stable objects. -/
def torsionlessCotorsionlessStableFunctor :
    (TorsionlessStableCategory (R := Rᵐᵒᵖ))ᵒᵖ ⥤
      CotorsionlessStableCategory (R := R) where
  obj X :=
    ⟨(ambientStableFunctor E).obj (Opposite.op X.unop.obj),
      cotorsionless_map_of_torsionless E X.unop.obj.as X.unop.property⟩
  map f := ObjectProperty.homMk
    ((ambientStableFunctor E).map f.unop.hom.op)
  map_id X := by
    apply ObjectProperty.hom_ext
    exact (ambientStableFunctor E).map_id (Opposite.op X.unop.obj)
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact (ambientStableFunctor E).map_comp f.unop.hom.op g.unop.hom.op

/-- Restricted map equality is again exactly projective factorization of the
original difference. -/
theorem torsionlessCotorsionlessStableFunctor_map_quotient_eq_iff
    {X Y : TorsionlessModuleCategory (R := Rᵐᵒᵖ)}
    (f g : X ⟶ Y) :
    (torsionlessCotorsionlessStableFunctor E).map
          ((torsionlessStableQuotientFunctor (R := Rᵐᵒᵖ)).map f).op =
        (torsionlessCotorsionlessStableFunctor E).map
          ((torsionlessStableQuotientFunctor (R := Rᵐᵒᵖ)).map g).op ↔
      Nonempty (FactorsThroughProjective (f.hom - g.hom)) := by
  constructor
  · intro h
    exact (ambientStableFunctor_map_quotient_eq_iff E f.hom g.hom).1
      (congrArg (fun q ↦ q.hom) h)
  · intro h
    apply ObjectProperty.hom_ext
    exact (ambientStableFunctor_map_quotient_eq_iff E f.hom g.hom).2 h

instance torsionlessCotorsionlessStableFunctor_full :
    (torsionlessCotorsionlessStableFunctor E).Full where
  map_surjective {X Y} f := by
    obtain ⟨q, hq⟩ := (ambientStableFunctor E).map_surjective f.hom
    refine ⟨(ObjectProperty.homMk q.unop).op, ?_⟩
    apply ObjectProperty.hom_ext
    change (ambientStableFunctor E).map q = f.hom
    exact hq

instance torsionlessCotorsionlessStableFunctor_faithful :
    (torsionlessCotorsionlessStableFunctor E).Faithful where
  map_injective {X Y} f g hfg := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply Quiver.Hom.op_inj
    apply (ambientStableFunctor E).map_injective
    exact congrArg (fun h ↦ h.hom) hfg

instance torsionlessCotorsionlessStableFunctor_essSurj :
    (torsionlessCotorsionlessStableFunctor E).EssSurj where
  mem_essImage Y := by
    let M : FGModuleCat.{u} Rᵐᵒᵖ := (E.inverse.obj Y.obj.as).unop
    have hdual : Cotorsionless (E.functor.obj (Opposite.op M)) := by
      simpa [M] using
        (cotorsionless_of_iso (R := R)
          (E.counitIso.app Y.obj.as).symm Y.property)
    have hM : Torsionless M :=
      torsionless_of_cotorsionless_map E M hdual
    let X : TorsionlessStableCategory (R := Rᵐᵒᵖ) :=
      ⟨(projectiveStableFunctor (R := Rᵐᵒᵖ)).obj M, hM⟩
    refine ⟨Opposite.op X, ⟨?_⟩⟩
    exact ObjectProperty.isoMk _
      ((injectiveStableFunctor (R := R)).mapIso
        (E.counitIso.app Y.obj.as))

instance torsionlessCotorsionlessStableFunctor_isEquivalence :
    (torsionlessCotorsionlessStableFunctor E).IsEquivalence where

/-- The stable Artin-duality anti-equivalence derived solely from the
finite-module anti-equivalence. -/
def torsionlessCotorsionlessStableEquivalence :
    (TorsionlessStableCategory (R := Rᵐᵒᵖ))ᵒᵖ ≌
      CotorsionlessStableCategory (R := R) :=
  (torsionlessCotorsionlessStableFunctor E).asEquivalence

end QuotientSubmoduleEquidistribution.ArtinDuality
