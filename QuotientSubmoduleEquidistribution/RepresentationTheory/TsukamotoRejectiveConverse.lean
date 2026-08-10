import QuotientSubmoduleEquidistribution.RepresentationTheory.GeneratorApproximationRejective
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import QuotientSubmoduleEquidistribution.RepresentationTheory.PrincipalIdealInAdd
import QuotientSubmoduleEquidistribution.RepresentationTheory.StrongHeredity
import QuotientSubmoduleEquidistribution.RepresentationTheory.TsukamotoRejectiveBridge

/-!
# The projective-ideal-to-rejective converse

This specializes the generic generator-approximation criterion to prove the
converse direction of Tsukamoto's projectivity/rejectivity bridge.  For a
finite-dimensional algebra, right projectivity of `AeA` is the only
ideal-module hypothesis.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open MulOpposite

namespace QuotientSubmoduleEquidistribution.Tsukamoto

universe u

variable {A : Type u} [Ring A]

private abbrev FiniteProjectives (A : Type u) [Ring A] :=
  (AuslanderEquivalence.finiteProjectiveModules
    Aᵐᵒᵖ).FullSubcategory

private abbrev regularRightModule (A : Type u) [Ring A] :
    ModuleCat.{u} Aᵐᵒᵖ :=
  ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ

private abbrev principalIdealOpposite (e : A) : Ideal Aᵐᵒᵖ :=
  (principalTwoSidedIdeal e).asIdealOpposite

private abbrev principalIdealOppositeModule (e : A) :
    ModuleCat.{u} Aᵐᵒᵖ :=
  ModuleCat.of Aᵐᵒᵖ (principalIdealOpposite e)

/-- Any right-module map `eA → A` takes values in `AeA`. -/
private theorem principalMap_mem_twoSidedSpan
    {e : A} (he : IsIdempotentElem e)
    (f : principalRightIdeal e →ₗ[Aᵐᵒᵖ] Aᵐᵒᵖ)
    (x : principalRightIdeal e) :
    f x ∈ principalIdealOpposite e := by
  let motive :
      ∀ y : Aᵐᵒᵖ,
        y ∈ Submodule.span Aᵐᵒᵖ {op e} → Prop :=
    fun y hy =>
      f ⟨y, hy⟩ ∈ principalIdealOpposite e
  exact Submodule.span_induction
    (p := motive)
    (fun y hy => by
      have hy_eq : y = op e :=
        Set.mem_singleton_iff.mp hy
      subst y
      let ge : principalRightIdeal e :=
        ⟨op e,
          Ideal.subset_span
            (Set.mem_singleton (op e))⟩
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
        TwoSidedIdeal.subset_span
          (Set.mem_singleton e)
      change
        unop (f ge) * e ∈ principalTwoSidedIdeal e
      exact
        (principalTwoSidedIdeal e).mul_mem_left
          (unop (f ge)) e he_mem)
    (by
      change
        f (0 : principalRightIdeal e) ∈
          principalIdealOpposite e
      rw [f.map_zero]
      exact (principalIdealOpposite e).zero_mem)
    (fun x y hx hy hfx hfy => by
      change
        f (⟨x + y, _⟩ : principalRightIdeal e) ∈
          principalIdealOpposite e
      change
        f (⟨x, hx⟩ : principalRightIdeal e) ∈
          principalIdealOpposite e at hfx
      change
        f (⟨y, hy⟩ : principalRightIdeal e) ∈
          principalIdealOpposite e at hfy
      have harg :
          (⟨x + y, _⟩ : principalRightIdeal e) =
            (⟨x, hx⟩ : principalRightIdeal e) +
              (⟨y, hy⟩ : principalRightIdeal e) :=
        Subtype.ext (by rfl)
      rw [harg, f.map_add]
      exact
        (principalIdealOpposite e).add_mem hfx hfy)
    (fun r x hx hfx => by
      change
        f (⟨r • x, _⟩ : principalRightIdeal e) ∈
          principalIdealOpposite e
      change
        f (⟨x, hx⟩ : principalRightIdeal e) ∈
          principalIdealOpposite e at hfx
      have harg :
          (⟨r • x, _⟩ : principalRightIdeal e) =
            r • (⟨x, hx⟩ :
              principalRightIdeal e) :=
        Subtype.ext (by rfl)
      rw [harg, f.map_smul]
      exact
        (principalIdealOpposite e).smul_mem r hfx)
    x.property

private def liftPrincipalMap
    {e : A} (he : IsIdempotentElem e)
    (f :
      principalRightModule e ⟶ regularRightModule A) :
    principalRightModule e ⟶
      principalIdealOppositeModule e :=
  ModuleCat.ofHom <|
    f.hom.codRestrict
      (principalIdealOpposite e)
      (principalMap_mem_twoSidedSpan he f.hom)

private theorem liftPrincipalMap_comp_subtype
    {e : A} (he : IsIdempotentElem e)
    (f :
      principalRightModule e ⟶ regularRightModule A) :
    liftPrincipalMap he f ≫
        ModuleCat.ofHom
          (Submodule.subtype
            (principalIdealOpposite e)) =
      f := by
  apply ModuleCat.hom_ext
  rfl

private def liftFiniteAddMap
    {e : A} (he : IsIdempotentElem e)
    {X : ModuleCat.{u} Aᵐᵒᵖ}
    (P :
      AuslanderEquivalence.FiniteAddPresentation
        (principalRightModule e) X)
    (f : X ⟶ regularRightModule A) :
    X ⟶ principalIdealOppositeModule e :=
  let E : Fin P.n → ModuleCat.{u} Aᵐᵒᵖ :=
    fun _ => principalRightModule e
  P.retract.i ≫
    biproduct.desc (fun j : Fin P.n =>
      liftPrincipalMap he
        (biproduct.ι E j ≫ P.retract.r ≫ f))

private theorem liftFiniteAddMap_comp_subtype
    {e : A} (he : IsIdempotentElem e)
    {X : ModuleCat.{u} Aᵐᵒᵖ}
    (P :
      AuslanderEquivalence.FiniteAddPresentation
        (principalRightModule e) X)
    (f : X ⟶ regularRightModule A) :
    liftFiniteAddMap he P f ≫
        ModuleCat.ofHom
          (Submodule.subtype
            (principalIdealOpposite e)) =
      f := by
  let E : Fin P.n → ModuleCat.{u} Aᵐᵒᵖ :=
    fun _ => principalRightModule e
  rw [show liftFiniteAddMap he P f =
      P.retract.i ≫
        biproduct.desc (fun j : Fin P.n =>
          liftPrincipalMap he
            (biproduct.ι E j ≫
              P.retract.r ≫ f)) by rfl,
    Category.assoc]
  have hdesc :
      biproduct.desc (fun j : Fin P.n =>
          liftPrincipalMap he
            (biproduct.ι E j ≫
              P.retract.r ≫ f)) ≫
          ModuleCat.ofHom
            (Submodule.subtype
              (principalIdealOpposite e)) =
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

/-- A monic `add(eA)`-approximation of the regular right module
already implies right rejectivity inside the literal category of
finitely generated projective right modules. -/
theorem addPrincipalRightModule_rightRejective_of_regularApproximation
    {e : A} (he : IsIdempotentElem e)
    (R :
      CategoricalRejective.MonicRightApproximation
        (addPrincipalRightModule e)
        (regularRightModule A)) :
    CategoricalRejective.IsRightRejective
      (fun X : FiniteProjectives A =>
        addPrincipalRightModule e X.obj) := by
  apply
    CategoricalRejective.isRightRejective_of_monicRightApproximations
  intro X
  have hXregular :
      AuslanderEquivalence.finiteAddClosure
        (regularRightModule A) X.obj :=
    (AuslanderEquivalence.finiteAddClosure_regular_iff
      Aᵐᵒᵖ X.obj).mpr X.property
  let P :=
    CategoricalRejective.finiteAddClosureSubcategory
      (principalRightModule e)
  obtain ⟨RX⟩ :=
    CategoricalRejective.monicRightApproximation_of_finiteAddPresentation
      P R hXregular.some
  have heAregular :
      AuslanderEquivalence.finiteAddClosure
        (regularRightModule A)
        (principalRightModule e) :=
    (AuslanderEquivalence.finiteAddClosure_regular_iff
      Aᵐᵒᵖ (principalRightModule e)).mpr
        (principalRightModule_mem_finiteProjectiveModules he)
  have hRXregular :
      AuslanderEquivalence.finiteAddClosure
        (regularRightModule A) RX.obj.obj :=
    CategoricalRejective.finiteAddClosure_trans
      heAregular RX.obj.property
  have hRXprojective :
      AuslanderEquivalence.finiteProjectiveModules
        Aᵐᵒᵖ RX.obj.obj :=
    (AuslanderEquivalence.finiteAddClosure_regular_iff
      Aᵐᵒᵖ RX.obj.obj).mp hRXregular
  let RXprojective : FiniteProjectives A :=
    ⟨RX.obj.obj, hRXprojective⟩
  let Pfinite :
      ObjectProperty (FiniteProjectives A) :=
    fun Y => addPrincipalRightModule e Y.obj
  let RXadd :
      Pfinite.FullSubcategory :=
    ⟨RXprojective, RX.obj.property⟩
  let c : RXprojective ⟶ X :=
    ObjectProperty.homMk RX.map
  have hc : Mono c := by
    constructor
    intro Z f g hfg
    apply ObjectProperty.hom_ext
    have hfg0 :
        f.hom ≫ RX.map = g.hom ≫ RX.map := by
      have hfg1 :=
        congrArg (fun t => t.hom) hfg
      dsimp only [c] at hfg1
      simpa only [
        ObjectProperty.FullSubcategory.comp_hom,
        ObjectProperty.homMk_hom] using hfg1
    haveI : Mono RX.map := RX.mono
    exact (cancel_mono RX.map).1 hfg0
  refine ⟨{
    obj := RXadd
    map := c
    mono := hc
    factors := ?_ }⟩
  intro Y f
  let Yambient :
      (addPrincipalRightModule e).FullSubcategory :=
    ⟨Y.obj.obj, Y.property⟩
  obtain ⟨g, hg⟩ :=
    RX.factors Yambient f.hom
  let g0 : Y.obj.obj ⟶ RX.obj.obj := g.hom
  have hg0 : g0 ≫ RX.map = f.hom := by
    dsimp only [g0]
    exact hg
  let gProjective : Y.obj ⟶ RXprojective :=
    ObjectProperty.homMk g0
  let gAdd : Y ⟶ RXadd :=
    ObjectProperty.homMk gProjective
  refine ⟨gAdd, ?_⟩
  apply ObjectProperty.hom_ext
  dsimp only [gAdd, gProjective, c]
  simpa only [
    ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.homMk_hom,
    ObjectProperty.ι_obj,
    ObjectProperty.ι_map] using hg0


/-- Once the right ideal module `AeA` belongs to `add(eA)`, its literal
inclusion into `A` is a monic right approximation, hence `add(eA)` is
right rejective in finitely generated projectives. -/
theorem addPrincipalRightModule_rightRejective_of_ideal_mem_add
    {e : A} (he : IsIdempotentElem e)
    (hadd :
      addPrincipalRightModule e
        (principalIdealOppositeModule e)) :
    CategoricalRejective.IsRightRejective
      (fun X : FiniteProjectives A =>
        addPrincipalRightModule e X.obj) := by
  let H : ModuleCat.{u} Aᵐᵒᵖ :=
    principalIdealOppositeModule e
  let j : H ⟶ regularRightModule A :=
    ModuleCat.ofHom
      (Submodule.subtype (principalIdealOpposite e))
  let HAdd :
      (addPrincipalRightModule e).FullSubcategory :=
    ⟨H, hadd⟩
  have hj : Mono j := by
    apply (ModuleCat.mono_iff_injective j).mpr
    exact Subtype.val_injective
  let R :
      CategoricalRejective.MonicRightApproximation
        (addPrincipalRightModule e)
        (regularRightModule A) :=
    { obj := HAdd
      map := j
      mono := hj
      factors := by
        intro X f
        let P := X.property.some
        let g0 : X.obj ⟶ H :=
          liftFiniteAddMap he P f
        let g : X ⟶ HAdd :=
          ObjectProperty.homMk g0
        refine ⟨g, ?_⟩
        dsimp only [g, g0, j, H]
        exact liftFiniteAddMap_comp_subtype he P f }
  exact
    addPrincipalRightModule_rightRejective_of_regularApproximation
      he R


/-- Full finite-projective converse in the arbitrary-ring setting.
Finite generation is stated explicitly because projectivity alone does
not imply membership in the finite additive closure outside the Artin
or finite-dimensional setting. -/
theorem principalTwoSidedIdeal_rightRejective_of_finite_projective
    {e : A} (he : IsIdempotentElem e)
    (hfinite :
      Module.Finite Aᵐᵒᵖ (principalTwoSidedIdeal e))
    (hprojective :
      IsRightProjectiveIdeal (principalTwoSidedIdeal e)) :
    CategoricalRejective.IsRightRejective
      (fun X : FiniteProjectives A =>
        addPrincipalRightModule e X.obj) := by
  obtain ⟨P⟩ :=
    principalTwoSidedIdeal_mem_add_of_finite_projective
      e hfinite hprojective
  let equiv :=
    asIdealOppositeLinearEquiv
      (principalTwoSidedIdeal e)
  let iso :
      principalIdealOppositeModule e ≅
        ModuleCat.of Aᵐᵒᵖ
          (principalTwoSidedIdeal e) :=
    equiv.toModuleIso
  have hadd :
      addPrincipalRightModule e
        (principalIdealOppositeModule e) :=
    ⟨{
      n := P.n
      retract :=
        (Retract.ofIso iso).trans P.retract }⟩
  exact
    addPrincipalRightModule_rightRejective_of_ideal_mem_add
      he hadd


/-- Finite-dimensional-algebra form of Tsukamoto's converse.  Here the
right ideal `AeA` is automatically finitely generated, so projectivity
is the only ideal-module hypothesis. -/
theorem principalTwoSidedIdeal_rightRejective_of_finiteDimensional
    {k : Type u} [Field k] [Algebra k A]
    [FiniteDimensional k A]
    {e : A} (he : IsIdempotentElem e)
    (hprojective :
      IsRightProjectiveIdeal (principalTwoSidedIdeal e)) :
    CategoricalRejective.IsRightRejective
      (fun X : FiniteProjectives A =>
        addPrincipalRightModule e X.obj) := by
  let H := principalTwoSidedIdeal e
  letI : Module k H :=
    Module.restrictScalars k Aᵐᵒᵖ H
  letI : IsScalarTower k Aᵐᵒᵖ H :=
    IsScalarTower.restrictScalars k Aᵐᵒᵖ H
  have hfiniteK : Module.Finite k H := by
    exact
      Module.Finite.of_injective
        ((TwoSidedIdeal.subtypeMop H).restrictScalars k)
        (TwoSidedIdeal.subtypeMop_injective H)
  have hfinite :
      Module.Finite Aᵐᵒᵖ H :=
    Module.Finite.of_restrictScalars_finite
      k Aᵐᵒᵖ H
  exact
    principalTwoSidedIdeal_rightRejective_of_finite_projective
      he hfinite hprojective

/-- Tsukamoto's right-handed projectivity/rejectivity equivalence for a
finite-dimensional algebra. -/
theorem addPrincipalRightModule_rightRejective_iff_rightProjectiveIdeal
    {k : Type u} [Field k] [Algebra k A]
    [FiniteDimensional k A]
    {e : A} (he : IsIdempotentElem e) :
    CategoricalRejective.IsRightRejective
        (fun X :
          (AuslanderEquivalence.finiteProjectiveModules
            Aᵐᵒᵖ).FullSubcategory ↦
          addPrincipalRightModule e X.obj) ↔
      IsRightProjectiveIdeal
        (principalTwoSidedIdeal e) := by
  constructor
  · exact
      principalTwoSidedIdeal_rightProjective_of_literal_rightRejective
        he
  · exact
      principalTwoSidedIdeal_rightRejective_of_finiteDimensional
        (k := k) he

namespace IdempotentIdealChain

variable {n : ℕ} (H : IdempotentIdealChain A n)

/-- Ambient right rejectivity of all nonfinal principal-module terms
presented by an idempotent ideal chain. -/
def PrincipalRightTermsAreRejective
    (P : H.IdempotentPresentation) : Prop :=
  ∀ i : Fin n,
    CategoricalRejective.IsRightRejective
      (fun X :
        (AuslanderEquivalence.finiteProjectiveModules
          Aᵐᵒᵖ).FullSubcategory ↦
        addPrincipalRightModule
          (P.generator i.castSucc) X.obj)

/-- The termwise projectivity/rejectivity part of Tsukamoto's
strong-heredity-chain theorem. -/
theorem principalRightTermsAreRejective_iff_rightProjective
    {k : Type u} [Field k] [Algebra k A]
    [FiniteDimensional k A]
    (P : H.IdempotentPresentation) :
    H.PrincipalRightTermsAreRejective P ↔
      ∀ i : Fin n,
        IsRightProjectiveIdeal (H.ideal i.castSucc) := by
  constructor
  · intro h i
    have hi :=
      (addPrincipalRightModule_rightRejective_iff_rightProjectiveIdeal
        (k := k) (P.isIdempotent i.castSucc)).mp
        (h i)
    rw [P.span_eq i.castSucc] at hi
    exact hi
  · intro h i
    apply
      (addPrincipalRightModule_rightRejective_iff_rightProjectiveIdeal
        (k := k) (P.isIdempotent i.castSucc)).mpr
    rw [P.span_eq i.castSucc]
    exact h i

end IdempotentIdealChain

end QuotientSubmoduleEquidistribution.Tsukamoto
