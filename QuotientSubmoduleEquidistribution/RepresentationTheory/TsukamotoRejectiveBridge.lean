import QuotientSubmoduleEquidistribution.RepresentationTheory.StrongHeredity
import QuotientSubmoduleEquidistribution.RepresentationTheory.GenericAdditiveRejective

/-!
The right-handed implication in Tsukamoto,
Proposition 3.16:

`add(eA)` right rejective in `proj A` implies `AeA` projective as a
right `A`-module.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open MulOpposite

namespace QuotientSubmoduleEquidistribution.Tsukamoto

universe v u

variable {A : Type u} [Ring A]

private abbrev FiniteProjectives (A : Type u) [Ring A] :=
  (AuslanderEquivalence.finiteProjectiveModules Aᵐᵒᵖ).FullSubcategory

private abbrev regularRightModule (A : Type u) [Ring A] :
    ModuleCat.{u} Aᵐᵒᵖ :=
  ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ

private abbrev regularFiniteProjective (A : Type u) [Ring A] :
    FiniteProjectives A :=
  ⟨regularRightModule A,
    Module.Finite.self Aᵐᵒᵖ,
    ModuleCat.projective_of_free
      (Module.Basis.singleton Unit Aᵐᵒᵖ)⟩

private def addPrincipalInFiniteProjectives (e : A) :
    ObjectProperty (FiniteProjectives A) :=
  fun X ↦ addPrincipalRightModule e X.obj

private theorem finiteAddClosure_self
    {C : Type u} [Category.{v} C] [Preadditive C]
    [HasFiniteBiproducts C] (X : C) :
    AuslanderEquivalence.finiteAddClosure X X := by
  refine ⟨{
    n := 1
    retract := Retract.ofIso
      (biproductUniqueIso
        (fun _ : Fin 1 ↦ X)).symm }⟩

private def principalFiniteProjective
    {e : A} (he : IsIdempotentElem e) :
    FiniteProjectives A :=
  ⟨principalRightModule e,
    principalRightModule_mem_finiteProjectiveModules he⟩

private def principalAddObject
    {e : A} (he : IsIdempotentElem e) :
    (addPrincipalInFiniteProjectives e).FullSubcategory :=
  ⟨principalFiniteProjective he,
    finiteAddClosure_self (principalRightModule e)⟩

private abbrev principalIdealOpposite (e : A) : Ideal Aᵐᵒᵖ :=
  (principalTwoSidedIdeal e).asIdealOpposite

private abbrev principalIdealOppositeModule (e : A) :
    ModuleCat.{u} Aᵐᵒᵖ :=
  ModuleCat.of Aᵐᵒᵖ (principalIdealOpposite e)

/-- Any map `eA → A` takes values in `AeA`. -/
private theorem principalMap_mem_twoSidedSpan
    {e : A} (he : IsIdempotentElem e)
    (f : principalRightIdeal e →ₗ[Aᵐᵒᵖ] Aᵐᵒᵖ)
    (x : principalRightIdeal e) :
    f x ∈ principalIdealOpposite e := by
  let motive :
      ∀ y : Aᵐᵒᵖ,
        y ∈ Submodule.span Aᵐᵒᵖ {op e} → Prop :=
    fun y hy ↦
      f ⟨y, hy⟩ ∈ principalIdealOpposite e
  exact Submodule.span_induction
    (p := motive)
    (fun y hy ↦ by
      have hy_eq : y = op e := Set.mem_singleton_iff.mp hy
      subst y
      let ge : principalRightIdeal e :=
        ⟨op e, Ideal.subset_span (Set.mem_singleton (op e))⟩
      change
        f (⟨op e, _⟩ : principalRightIdeal e) ∈
          principalIdealOpposite e
      have harg :
          (⟨op e, _⟩ : principalRightIdeal e) = ge :=
        Subtype.ext (by rfl)
      rw [harg]
      have hfixed : op e • ge = ge := by
        apply Subtype.ext
        change op e * op e = op e
        apply unop_injective
        simpa using he.eq
      have hf_fixed : op e • f ge = f ge := by
        rw [← f.map_smul, hfixed]
      rw [← hf_fixed]
      rw [TwoSidedIdeal.mem_asIdealOpposite]
      have he_mem :
          e ∈ principalTwoSidedIdeal e :=
        TwoSidedIdeal.subset_span (Set.mem_singleton e)
      change unop (f ge) * e ∈ principalTwoSidedIdeal e
      exact
        (principalTwoSidedIdeal e).mul_mem_left
          (unop (f ge)) e he_mem)
    (by
      change f (0 : principalRightIdeal e) ∈
        principalIdealOpposite e
      rw [f.map_zero]
      exact (principalIdealOpposite e).zero_mem)
    (fun x y hx hy hfx hfy ↦ by
      change
        f (⟨x + y, _⟩ : principalRightIdeal e) ∈
          principalIdealOpposite e
      change f (⟨x, hx⟩ : principalRightIdeal e) ∈
        principalIdealOpposite e at hfx
      change f (⟨y, hy⟩ : principalRightIdeal e) ∈
        principalIdealOpposite e at hfy
      have harg :
          (⟨x + y, _⟩ : principalRightIdeal e) =
            (⟨x, hx⟩ : principalRightIdeal e) +
              (⟨y, hy⟩ : principalRightIdeal e) :=
        Subtype.ext (by rfl)
      rw [harg, f.map_add]
      exact (principalIdealOpposite e).add_mem hfx hfy)
    (fun r x hx hfx ↦ by
      change
        f (⟨r • x, _⟩ : principalRightIdeal e) ∈
          principalIdealOpposite e
      change f (⟨x, hx⟩ : principalRightIdeal e) ∈
        principalIdealOpposite e at hfx
      have harg :
          (⟨r • x, _⟩ : principalRightIdeal e) =
            r • (⟨x, hx⟩ : principalRightIdeal e) :=
        Subtype.ext (by rfl)
      rw [harg, f.map_smul]
      exact (principalIdealOpposite e).smul_mem r hfx)
    x.property

private def liftPrincipalMap
    {e : A} (he : IsIdempotentElem e)
    (f : principalRightModule e ⟶ regularRightModule A) :
    principalRightModule e ⟶ principalIdealOppositeModule e :=
  ModuleCat.ofHom <|
    f.hom.codRestrict
      (principalIdealOpposite e)
      (principalMap_mem_twoSidedSpan he f.hom)

private theorem liftPrincipalMap_comp_subtype
    {e : A} (he : IsIdempotentElem e)
    (f : principalRightModule e ⟶ regularRightModule A) :
    liftPrincipalMap he f ≫
        ModuleCat.ofHom
          (Submodule.subtype (principalIdealOpposite e)) =
      f := by
  apply ModuleCat.hom_ext
  rfl

/-- A map from any object of `add(eA)` into `A` takes values in `AeA`,
packaged as an actual factorization through the ideal inclusion. -/
private def liftFiniteAddMap
    {e : A} (he : IsIdempotentElem e)
    {X : ModuleCat.{u} Aᵐᵒᵖ}
    (P : AuslanderEquivalence.FiniteAddPresentation
      (principalRightModule e) X)
    (f : X ⟶ regularRightModule A) :
    X ⟶ principalIdealOppositeModule e :=
  let E : Fin P.n → ModuleCat.{u} Aᵐᵒᵖ :=
    fun _ ↦ principalRightModule e
  P.retract.i ≫
    biproduct.desc (fun j : Fin P.n ↦
      liftPrincipalMap he
        (biproduct.ι E j ≫
          P.retract.r ≫ f))

private theorem liftFiniteAddMap_comp_subtype
    {e : A} (he : IsIdempotentElem e)
    {X : ModuleCat.{u} Aᵐᵒᵖ}
    (P : AuslanderEquivalence.FiniteAddPresentation
      (principalRightModule e) X)
    (f : X ⟶ regularRightModule A) :
    liftFiniteAddMap he P f ≫
        ModuleCat.ofHom
          (Submodule.subtype (principalIdealOpposite e)) =
      f := by
  let E : Fin P.n → ModuleCat.{u} Aᵐᵒᵖ :=
    fun _ ↦ principalRightModule e
  rw [show liftFiniteAddMap he P f =
      P.retract.i ≫
        biproduct.desc (fun j : Fin P.n ↦
          liftPrincipalMap he
            (biproduct.ι E j ≫
              P.retract.r ≫ f)) by rfl,
    Category.assoc]
  have hdesc :
      biproduct.desc (fun j : Fin P.n ↦
          liftPrincipalMap he
            (biproduct.ι E j ≫
              P.retract.r ≫ f)) ≫
          ModuleCat.ofHom
            (Submodule.subtype (principalIdealOpposite e)) =
        P.retract.r ≫ f := by
    apply biproduct.hom_ext'
    intro j
    simp only [biproduct.ι_desc_assoc]
    exact liftPrincipalMap_comp_subtype he _
  rw [hdesc]
  calc
    P.retract.i ≫ P.retract.r ≫ f =
        (P.retract.i ≫ P.retract.r) ≫ f := by
          rw [Category.assoc]
    _ = f := by
      rw [P.retract.retract, Category.id_comp]

/-- The right-module carried by a two-sided ideal is canonically the
opposite of its right-ideal realization in `Aᵐᵒᵖ`. -/
private def asIdealOppositeLinearEquiv
    (H : TwoSidedIdeal A) :
    H.asIdealOpposite ≃ₗ[Aᵐᵒᵖ] H where
  toFun x :=
    ⟨unop x,
      TwoSidedIdeal.mem_asIdealOpposite.mp x.property⟩
  invFun x :=
    ⟨op x,
      TwoSidedIdeal.mem_asIdealOpposite.mpr x.property⟩
  left_inv x := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)
  map_smul' r x := Subtype.ext (by rfl)

/-- Source-faithful right-handed direction of Tsukamoto,
Proposition 3.16.  The ambient category is the literal full category of
finitely generated projective right `A`-modules. -/
theorem principalTwoSidedIdeal_rightProjective_of_rightRejective
    {e : A} (he : IsIdempotentElem e)
    (hrr :
      CategoricalRejective.IsRightRejective
        (addPrincipalInFiniteProjectives e)) :
    IsRightProjectiveIdeal (principalTwoSidedIdeal e) := by
  let D := hrr.some
  let R : FiniteProjectives A := regularFiniteProjective A
  let Y :=
    D.coreflector.obj R
  let c :
      (addPrincipalInFiniteProjectives e).ι.obj Y ⟶ R :=
    D.adjunction.counit.app R
  let cLinear : Y.obj.obj →ₗ[Aᵐᵒᵖ] Aᵐᵒᵖ :=
    c.hom.hom
  haveI hc : Mono c :=
    D.counit_mono R
  let P :=
    Y.property.some
  let l :
      Y.obj.obj ⟶ principalIdealOppositeModule e :=
    liftFiniteAddMap he P c.hom
  have hl_comp :
      l ≫ ModuleCat.ofHom
          (Submodule.subtype (principalIdealOpposite e)) =
        c.hom :=
    liftFiniteAddMap_comp_subtype he P c.hom
  have hl_injective :
      Function.Injective l.hom := by
    intro x y hxy
    let fx : R ⟶ Y.obj :=
      ObjectProperty.homMk <|
        ModuleCat.ofHom
          (LinearMap.toSpanSingleton Aᵐᵒᵖ Y.obj.obj x)
    let fy : R ⟶ Y.obj :=
      ObjectProperty.homMk <|
        ModuleCat.ofHom
          (LinearMap.toSpanSingleton Aᵐᵒᵖ Y.obj.obj y)
    have hxc :=
      ConcreteCategory.congr_hom hl_comp x
    have hyc :=
      ConcreteCategory.congr_hom hl_comp y
    have hcxcy :
        cLinear x = cLinear y := by
      exact hxc.symm.trans <|
        congrArg
          (fun q : principalIdealOpposite e ↦
            (q : Aᵐᵒᵖ)) hxy |>.trans hyc
    have hfxfy : fx = fy := by
      apply (cancel_mono c).1
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      dsimp only [fx, fy]
      simp only [ObjectProperty.FullSubcategory.comp_hom,
        ObjectProperty.homMk_hom, ModuleCat.hom_comp]
      change
        cLinear.comp
            (LinearMap.toSpanSingleton Aᵐᵒᵖ Y.obj.obj x) =
          cLinear.comp
            (LinearMap.toSpanSingleton Aᵐᵒᵖ Y.obj.obj y)
      rw [LinearMap.comp_toSpanSingleton,
        LinearMap.comp_toSpanSingleton, hcxcy]
    have hfxfyModule : fx.hom = fy.hom :=
      congrArg (fun k ↦ k.hom) hfxfy
    have hfxfyLinear :
        (LinearMap.toSpanSingleton Aᵐᵒᵖ Y.obj.obj x) =
          LinearMap.toSpanSingleton Aᵐᵒᵖ Y.obj.obj y := by
      exact congrArg (fun k ↦ k.hom) hfxfyModule
    exact
      (LinearMap.toSpanSingleton_injective
        Aᵐᵒᵖ Y.obj.obj) hfxfyLinear
  have factor_through_counit
      (X :
        (addPrincipalInFiniteProjectives e).FullSubcategory)
      (f :
        (addPrincipalInFiniteProjectives e).ι.obj X ⟶ R) :
      (addPrincipalInFiniteProjectives e).ι.map
          (D.adjunction.homEquiv X R f) ≫ c =
        f := by
    rw [← D.adjunction.homEquiv_counit]
    exact (D.adjunction.homEquiv X R).symm_apply_apply f
  have range_stable_mulRight
      (a : A) {z : Aᵐᵒᵖ}
      (hz : z ∈ LinearMap.range cLinear) :
      z * op a ∈ LinearMap.range cLinear := by
    obtain ⟨y, hy⟩ := hz
    let m : R ⟶ R :=
      ObjectProperty.homMk <|
        ModuleCat.ofHom (LinearMap.mulRight Aᵐᵒᵖ (op a))
    let g :=
      D.adjunction.homEquiv Y R (c ≫ m)
    refine ⟨g.hom.hom.hom y, ?_⟩
    have hfactor :
        (addPrincipalInFiniteProjectives e).ι.map g ≫ c =
          c ≫ m :=
      factor_through_counit Y (c ≫ m)
    have hpoint :=
      ConcreteCategory.congr_hom hfactor y
    change
      cLinear (g.hom.hom.hom y) =
        cLinear y * op a at hpoint
    simpa [hy] using hpoint
  let K : TwoSidedIdeal A :=
    TwoSidedIdeal.mk'
      {a : A | op a ∈ LinearMap.range cLinear}
      (by
        change (0 : Aᵐᵒᵖ) ∈ LinearMap.range cLinear
        exact (LinearMap.range cLinear).zero_mem)
      (by
        intro x y hx hy
        change op (x + y) ∈ LinearMap.range cLinear
        rw [show op (x + y) = op x + op y by rfl]
        exact (LinearMap.range cLinear).add_mem hx hy)
      (by
        intro x hx
        change op (-x) ∈ LinearMap.range cLinear
        rw [show op (-x) = -op x by rfl]
        exact (LinearMap.range cLinear).neg_mem hx)
      (by
        intro x y hy
        change op (x * y) ∈ LinearMap.range cLinear
        change op y * op x ∈ LinearMap.range cLinear
        exact range_stable_mulRight x hy)
      (by
        intro x y hx
        change op (x * y) ∈ LinearMap.range cLinear
        change op y • op x ∈ LinearMap.range cLinear
        exact (LinearMap.range cLinear).smul_mem (op y) hx)
  have he_mem_K : e ∈ K := by
    let E :
        (addPrincipalInFiniteProjectives e).FullSubcategory :=
      principalAddObject he
    let j :
        (addPrincipalInFiniteProjectives e).ι.obj E ⟶ R :=
      ObjectProperty.homMk <|
        ModuleCat.ofHom
          (Submodule.subtype (principalRightIdeal e))
    let g :=
      D.adjunction.homEquiv E R j
    let ge : principalRightIdeal e :=
      ⟨op e,
        Ideal.subset_span (Set.mem_singleton (op e))⟩
    have he_range :
        op e ∈ LinearMap.range cLinear := by
      refine ⟨g.hom.hom.hom ge, ?_⟩
      have hfactor :
          (addPrincipalInFiniteProjectives e).ι.map g ≫ c =
            j :=
        factor_through_counit E j
      have hpoint :=
        ConcreteCategory.congr_hom hfactor ge
      change
        cLinear (g.hom.hom.hom ge) = op e at hpoint
      exact hpoint
    dsimp only [K]
    rw [TwoSidedIdeal.mem_mk']
    exact he_range
  have hspan_le_K :
      principalTwoSidedIdeal e ≤ K := by
    apply TwoSidedIdeal.span_le.mpr
    rw [Set.singleton_subset_iff]
    exact he_mem_K
  have hl_surjective :
      Function.Surjective l.hom := by
    intro q
    change principalIdealOpposite e at q
    have hqH :
        unop q ∈ principalTwoSidedIdeal e :=
      TwoSidedIdeal.mem_asIdealOpposite.mp
        (show
          (q : Aᵐᵒᵖ) ∈
            (principalTwoSidedIdeal e).asIdealOpposite
          from q.property)
    have hqK :
        unop q ∈ K :=
      hspan_le_K hqH
    have hqRange :
        op (unop q) ∈ LinearMap.range cLinear := by
      dsimp only [K] at hqK
      rw [TwoSidedIdeal.mem_mk'] at hqK
      exact hqK
    obtain ⟨y, hy⟩ := hqRange
    refine ⟨y, ?_⟩
    apply Subtype.ext
    have hpoint :=
      ConcreteCategory.congr_hom hl_comp y
    change
      ((l.hom y : principalIdealOpposite e) : Aᵐᵒᵖ) =
        cLinear y at hpoint
    have hy' :
        cLinear y = (q : Aᵐᵒᵖ) := by
      simpa using hy
    exact hpoint.trans hy'
  let el :
      Y.obj.obj ≃ₗ[Aᵐᵒᵖ] principalIdealOpposite e :=
    LinearEquiv.ofBijective l.hom
      ⟨hl_injective, hl_surjective⟩
  have hYprojective :
      Module.Projective Aᵐᵒᵖ Y.obj.obj :=
    (IsProjective.iff_projective Y.obj.obj).mpr
      Y.obj.property.2
  letI :
      Module.Projective Aᵐᵒᵖ Y.obj.obj :=
    hYprojective
  letI :
      Module.Projective Aᵐᵒᵖ (principalIdealOpposite e) :=
    Module.Projective.of_equiv el
  exact
    Module.Projective.of_equiv
      (asIdealOppositeLinearEquiv
        (principalTwoSidedIdeal e))

/-- Public-shape wrapper with the ambient property written literally,
so no scratch-private abbreviation occurs in the theorem signature. -/
theorem principalTwoSidedIdeal_rightProjective_of_literal_rightRejective
    {e : A} (he : IsIdempotentElem e)
    (hrr :
      CategoricalRejective.IsRightRejective
        (fun X :
          (AuslanderEquivalence.finiteProjectiveModules
            Aᵐᵒᵖ).FullSubcategory ↦
          addPrincipalRightModule e X.obj)) :
    IsRightProjectiveIdeal (principalTwoSidedIdeal e) :=
  principalTwoSidedIdeal_rightProjective_of_rightRejective
    he hrr

end QuotientSubmoduleEquidistribution.Tsukamoto
