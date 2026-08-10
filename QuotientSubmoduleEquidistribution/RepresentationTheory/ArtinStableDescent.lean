import QuotientSubmoduleEquidistribution.RepresentationTheory.ArtinModuleDuality

/-!
# Descent of Artin duality to stable quotient categories

The contragredient anti-equivalence sends maps through projectives to maps
through injectives.  We use this to construct the induced functor from the
opposite projective-stable category to the injective-stable category, and
then restrict it to torsionless and cotorsionless objects.  All quotient
well-definedness is proved here.  The descended functor is then proved full,
faithful, and essentially surjective.
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

/-- The concrete reverse dual functor is additive. -/
instance reverseDualityFunctor_additive :
    (QuotientSubmoduleEquidistribution.Contragredient.reverseDualityEquivalence K R).functor.Additive where
  map_add {X Y} f g := by
    letI : Module K X.unop :=
      Module.restrictScalars K Rᵐᵒᵖ X.unop
    letI : IsScalarTower K Rᵐᵒᵖ X.unop :=
      IsScalarTower.restrictScalars K Rᵐᵒᵖ X.unop
    letI : FiniteDimensional K X.unop :=
      Module.Finite.trans Rᵐᵒᵖ X.unop
    letI : Module K Y.unop :=
      Module.restrictScalars K Rᵐᵒᵖ Y.unop
    letI : IsScalarTower K Rᵐᵒᵖ Y.unop :=
      IsScalarTower.restrictScalars K Rᵐᵒᵖ Y.unop
    letI : FiniteDimensional K Y.unop :=
      Module.Finite.trans Rᵐᵒᵖ Y.unop
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro x
    change Module.Dual K X.unop at φ
    change φ (f.unop.hom.hom x + g.unop.hom.hom x) =
      φ (f.unop.hom.hom x) + φ (g.unop.hom.hom x)
    exact map_add φ _ _

/-- Applying `K`-duality to the opposite of a map through a projective
produces a map through an injective. -/
def factorsThroughInjective_reverseDual_op
    {X Y : FGModuleCat.{u} Rᵐᵒᵖ} {f : X ⟶ Y}
    (hf : FactorsThroughProjective f) :
    FactorsThroughInjective
      ((QuotientSubmoduleEquidistribution.Contragredient.reverseDualityEquivalence K R).functor.map
        f.op) := by
  let E := QuotientSubmoduleEquidistribution.Contragredient.reverseDualityEquivalence K R
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

/-- Reflection counterpart to
`factorsThroughInjective_reverseDual_op`: a factorization of the dual map
through an injective pulls back, using the unit of the anti-equivalence, to
a factorization of the original map through a projective. -/
def factorsThroughProjective_of_reverseDual_op
    {X Y : FGModuleCat.{u} Rᵐᵒᵖ} {f : X ⟶ Y}
    (hf : FactorsThroughInjective
      ((QuotientSubmoduleEquidistribution.Contragredient.reverseDualityEquivalence K R).functor.map
        f.op)) :
    FactorsThroughProjective f := by
  let E := QuotientSubmoduleEquidistribution.Contragredient.reverseDualityEquivalence K R
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
    simp [leftDual, rightDual, Category.assoc, hf.fac, E]
  exact
    { middle := (E.inverse.obj hf.middle).unop
      projective := hP
      left := rightLift.unop
      right := leftLift.unop
      fac := by
        apply Quiver.Hom.op_inj
        simpa only [op_comp, Quiver.Hom.op_unop] using hop }

omit [IsNoetherianRing R] [IsNoetherianRing Rᵐᵒᵖ] in
/-- Reverse duality carries the projective-factor ideal onto, not merely
into, the injective-factor ideal. -/
theorem factorsThroughInjective_reverseDual_op_iff
    {X Y : FGModuleCat.{u} Rᵐᵒᵖ} (f : X ⟶ Y) :
    Nonempty (FactorsThroughInjective
        ((QuotientSubmoduleEquidistribution.Contragredient.reverseDualityEquivalence K R).functor.map
          f.op)) ↔
      Nonempty (FactorsThroughProjective f) := by
  constructor
  · rintro ⟨hf⟩
    exact ⟨factorsThroughProjective_of_reverseDual_op K R hf⟩
  · rintro ⟨hf⟩
    exact ⟨factorsThroughInjective_reverseDual_op K R hf⟩

/-- The corresponding statement for differences, in the exact form needed
by the stable congruences. -/
def factorsThroughInjective_reverseDual_difference
    {X Y : FGModuleCat.{u} Rᵐᵒᵖ} (f g : X ⟶ Y)
    (hfg : FactorsThroughProjective (f - g)) :
    FactorsThroughInjective
      ((QuotientSubmoduleEquidistribution.Contragredient.reverseDualityEquivalence K R).functor.map f.op -
        (QuotientSubmoduleEquidistribution.Contragredient.reverseDualityEquivalence K R).functor.map g.op) := by
  let E := QuotientSubmoduleEquidistribution.Contragredient.reverseDualityEquivalence K R
  have h := factorsThroughInjective_reverseDual_op K R hfg
  convert h using 1
  rw [← E.functor.map_sub]
  rfl

/-- Artin duality descended to the ambient stable quotient categories. -/
def artinAmbientStableFunctor :
    (ProjectiveStableCategory (R := Rᵐᵒᵖ))ᵒᵖ ⥤
      InjectiveStableCategory (R := R) where
  obj X :=
    (injectiveStableFunctor (R := R)).obj
      ((QuotientSubmoduleEquidistribution.Contragredient.reverseDualityEquivalence K R).functor.obj
        (Opposite.op X.unop.as))
  map {X Y} f :=
    Quot.liftOn f.unop
      (fun h ↦
        (injectiveStableFunctor (R := R)).map
          ((QuotientSubmoduleEquidistribution.Contragredient.reverseDualityEquivalence K R).functor.map
            h.op))
      (by
        intro h h' hh'
        apply (injectiveStable_map_eq_iff _ _).2
        have hrel : projectiveStableRel (R := Rᵐᵒᵖ) h h' :=
          (HomRel.compClosure_iff_self _ h h').1 hh'
        rcases hrel with ⟨hrel⟩
        exact ⟨factorsThroughInjective_reverseDual_difference K R h h' hrel⟩)
  map_id X := by
    change (injectiveStableFunctor (R := R)).map
      ((QuotientSubmoduleEquidistribution.Contragredient.reverseDualityEquivalence K R).functor.map
        (𝟙 X.unop.as).op) = 𝟙 _
    rw [op_id,
      (QuotientSubmoduleEquidistribution.Contragredient.reverseDualityEquivalence K R).functor.map_id,
      (injectiveStableFunctor (R := R)).map_id]
  map_comp {X Y Z} f g := by
    rw [unop_comp]
    refine Quot.inductionOn f.unop ?_
    intro f
    refine Quot.inductionOn g.unop ?_
    intro g
    change (injectiveStableFunctor (R := R)).map
        ((QuotientSubmoduleEquidistribution.Contragredient.reverseDualityEquivalence K R).functor.map
          (g ≫ f).op) =
      (injectiveStableFunctor (R := R)).map
          ((QuotientSubmoduleEquidistribution.Contragredient.reverseDualityEquivalence K R).functor.map
            f.op) ≫
        (injectiveStableFunctor (R := R)).map
          ((QuotientSubmoduleEquidistribution.Contragredient.reverseDualityEquivalence K R).functor.map
            g.op)
    rw [op_comp,
      (QuotientSubmoduleEquidistribution.Contragredient.reverseDualityEquivalence K R).functor.map_comp,
      (injectiveStableFunctor (R := R)).map_comp]

omit [IsNoetherianRing R] [IsNoetherianRing Rᵐᵒᵖ] in
/-- Equality of dualized canonical stable maps is exactly the original
projective-factor congruence.  This is the map-level reflection statement
used for faithfulness of the descended functor. -/
theorem artinAmbientStableFunctor_map_quotient_eq_iff
    {X Y : FGModuleCat.{u} Rᵐᵒᵖ} (f g : X ⟶ Y) :
    (artinAmbientStableFunctor K R).map
          ((projectiveStableFunctor (R := Rᵐᵒᵖ)).map f).op =
        (artinAmbientStableFunctor K R).map
          ((projectiveStableFunctor (R := Rᵐᵒᵖ)).map g).op ↔
      Nonempty (FactorsThroughProjective (f - g)) := by
  let E := QuotientSubmoduleEquidistribution.Contragredient.reverseDualityEquivalence K R
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
  exact factorsThroughInjective_reverseDual_op_iff K R (f - g)

/-- Every injective-stable morphism between dual objects lifts through the
ordinary full anti-equivalence and then through the projective quotient. -/
instance artinAmbientStableFunctor_full :
    (artinAmbientStableFunctor K R).Full where
  map_surjective {X Y} f := by
    let E := QuotientSubmoduleEquidistribution.Contragredient.reverseDualityEquivalence K R
    let h := (injectiveStableFunctor (R := R)).preimage f
    let k := E.functor.preimage h
    refine ⟨((projectiveStableFunctor (R := Rᵐᵒᵖ)).map k.unop).op, ?_⟩
    change (injectiveStableFunctor (R := R)).map
      (E.functor.map k) = f
    rw [Functor.map_preimage, Functor.map_preimage]

/-- The reflected factorization criterion makes the descended ambient
duality faithful. -/
instance artinAmbientStableFunctor_faithful :
    (artinAmbientStableFunctor K R).Faithful where
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
        (artinAmbientStableFunctor K R).map
            ((projectiveStableFunctor (R := Rᵐᵒᵖ)).map f₀).op =
          (artinAmbientStableFunctor K R).map
            ((projectiveStableFunctor (R := Rᵐᵒᵖ)).map g₀).op := by
      rw [hf, hg]
      exact hfg
    have hfactor : Nonempty (FactorsThroughProjective (f₀ - g₀)) :=
      (artinAmbientStableFunctor_map_quotient_eq_iff K R f₀ g₀).1 hcanon
    have hquot :
        (projectiveStableFunctor (R := Rᵐᵒᵖ)).map f₀ =
          (projectiveStableFunctor (R := Rᵐᵒᵖ)).map g₀ :=
      (projectiveStable_map_eq_iff f₀ g₀).2 hfactor
    exact hf.symm.trans ((congrArg Quiver.Hom.op hquot).trans hg)

/-- Restriction of descended Artin duality to torsionless and cotorsionless
stable objects. -/
def artinTorsionlessCotorsionlessStableFunctor :
    (TorsionlessStableCategory (R := Rᵐᵒᵖ))ᵒᵖ ⥤
      CotorsionlessStableCategory (R := R) where
  obj X :=
    ⟨(artinAmbientStableFunctor K R).obj
        (Opposite.op X.unop.obj),
      cotorsionless_reverseDual_of_torsionless K R
        X.unop.obj.as X.unop.property⟩
  map f := ObjectProperty.homMk
    ((artinAmbientStableFunctor K R).map f.unop.hom.op)
  map_id X := by
    apply ObjectProperty.hom_ext
    exact (artinAmbientStableFunctor K R).map_id
      (Opposite.op X.unop.obj)
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact (artinAmbientStableFunctor K R).map_comp
      f.unop.hom.op g.unop.hom.op

/-- On the restricted categories, equality after stable Artin duality is
again exactly factorization of the original difference through a
projective module. -/
theorem artinTorsionlessCotorsionlessStableFunctor_map_quotient_eq_iff
    {X Y : TorsionlessModuleCategory (R := Rᵐᵒᵖ)}
    (f g : X ⟶ Y) :
    (artinTorsionlessCotorsionlessStableFunctor K R).map
          ((torsionlessStableQuotientFunctor (R := Rᵐᵒᵖ)).map f).op =
        (artinTorsionlessCotorsionlessStableFunctor K R).map
          ((torsionlessStableQuotientFunctor (R := Rᵐᵒᵖ)).map g).op ↔
      Nonempty (FactorsThroughProjective (f.hom - g.hom)) := by
  constructor
  · intro h
    apply (artinAmbientStableFunctor_map_quotient_eq_iff K R
      f.hom g.hom).1
    exact congrArg (fun q ↦ q.hom) h
  · intro h
    apply ObjectProperty.hom_ext
    exact (artinAmbientStableFunctor_map_quotient_eq_iff K R
      f.hom g.hom).2 h

/-- Fullness descends to the torsionless/cotorsionless full
subcategories. -/
instance artinTorsionlessCotorsionlessStableFunctor_full :
    (artinTorsionlessCotorsionlessStableFunctor K R).Full where
  map_surjective {X Y} f := by
    obtain ⟨q, hq⟩ :=
      (artinAmbientStableFunctor K R).map_surjective f.hom
    refine ⟨(ObjectProperty.homMk q.unop).op, ?_⟩
    apply ObjectProperty.hom_ext
    change (artinAmbientStableFunctor K R).map q = f.hom
    exact hq

/-- Faithfulness of the ambient descent restricts to the two full
stable subcategories. -/
instance artinTorsionlessCotorsionlessStableFunctor_faithful :
    (artinTorsionlessCotorsionlessStableFunctor K R).Faithful where
  map_injective {X Y} f g hfg := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply Quiver.Hom.op_inj
    apply (artinAmbientStableFunctor K R).map_injective
    exact congrArg (fun h ↦ h.hom) hfg

/-- Every cotorsionless stable object is represented by the dual of a
torsionless module.  The counit of ordinary Artin duality supplies the
stable isomorphism. -/
instance artinTorsionlessCotorsionlessStableFunctor_essSurj :
    (artinTorsionlessCotorsionlessStableFunctor K R).EssSurj where
  mem_essImage Y := by
    let E := QuotientSubmoduleEquidistribution.Contragredient.reverseDualityEquivalence K R
    let M : FGModuleCat.{u} Rᵐᵒᵖ :=
      (E.inverse.obj Y.obj.as).unop
    have hdual :
        Cotorsionless (E.functor.obj (Opposite.op M)) := by
      simpa [M] using
        (cotorsionless_of_iso (R := R)
          (E.counitIso.app Y.obj.as).symm Y.property)
    have hM : Torsionless M :=
      torsionless_of_cotorsionless_reverseDual K R M hdual
    let X : TorsionlessStableCategory (R := Rᵐᵒᵖ) :=
      ⟨(projectiveStableFunctor (R := Rᵐᵒᵖ)).obj M, hM⟩
    refine ⟨Opposite.op X, ⟨?_⟩⟩
    exact ObjectProperty.isoMk _
      ((injectiveStableFunctor (R := R)).mapIso
        (E.counitIso.app Y.obj.as))

/-- The descended stable functor is full, faithful, and essentially
surjective. -/
instance artinTorsionlessCotorsionlessStableFunctor_isEquivalence :
    (artinTorsionlessCotorsionlessStableFunctor K R).IsEquivalence where

/-- Artin duality as an explicit anti-equivalence between the
projective-stable torsionless category and the injective-stable
cotorsionless category. -/
def artinTorsionlessCotorsionlessStableEquivalence :
    (TorsionlessStableCategory (R := Rᵐᵒᵖ))ᵒᵖ ≌
      CotorsionlessStableCategory (R := R) :=
  (artinTorsionlessCotorsionlessStableFunctor K R).asEquivalence

end QuotientSubmoduleEquidistribution.RingelEta
