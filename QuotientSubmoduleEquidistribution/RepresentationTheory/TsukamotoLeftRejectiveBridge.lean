import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import QuotientSubmoduleEquidistribution.RepresentationTheory.TsukamotoRejectiveBridge

/-!
# The left-handed Tsukamoto projectivity bridge

Formalization of the implication

`add(eA)` left rejective in `proj A` implies `AeA` projective as a left
`A`-module.

The proof follows Tsukamoto's duality argument, but constructs only the
piece of `Hom_A(-, A)` needed at the regular module.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open MulOpposite

namespace QuotientSubmoduleEquidistribution.Tsukamoto.LeftBridge

universe u vC uC

variable {A : Type u} [Ring A]

private abbrev FiniteProjectives (A : Type u) [Ring A] :=
  (AuslanderEquivalence.finiteProjectiveModules
    Aᵐᵒᵖ).FullSubcategory

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
    {C : Type uC} [Category.{vC} C] [Preadditive C]
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

private def regularDualScalarRingEquiv :
    A ≃+*
      (End (Opposite.op (regularRightModule A)))ᵐᵒᵖ where
  toFun a :=
    op
      (ModuleCat.ofHom
        (LinearMap.mulRight Aᵐᵒᵖ (op a))).op
  invFun f :=
    unop (f.unop.unop.hom (1 : Aᵐᵒᵖ))
  left_inv a := by
    simp
  right_inv f := by
    apply MulOpposite.unop_injective
    apply Quiver.Hom.unop_inj
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change
      x * f.unop.unop.hom 1 =
        f.unop.unop.hom x
    simpa using
      (f.unop.unop.hom.map_smul x (1 : Aᵐᵒᵖ)).symm
  map_add' a b := by
    apply MulOpposite.unop_injective
    apply Quiver.Hom.unop_inj
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change x * (op a + op b) =
      x * op a + x * op b
    exact mul_add x (op a) (op b)
  map_mul' a b := by
    apply MulOpposite.unop_injective
    apply Quiver.Hom.unop_inj
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simp

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

private theorem finiteAddClosure_op
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    [HasFiniteBiproducts C]
    {G X : C}
    (h : AuslanderEquivalence.finiteAddClosure G X) :
    AuslanderEquivalence.finiteAddClosure
      (Opposite.op G) (Opposite.op X) := by
  obtain ⟨P⟩ := h
  let E : Fin P.n → C := fun _ ↦ G
  let Eop : Fin P.n → Cᵒᵖ :=
    fun j ↦ Opposite.op (E j)
  let biproductOpIso :
      Opposite.op (biproduct E) ≅ biproduct Eop :=
    (biproduct.isoCoproduct E).op.symm ≪≫
      opCoproductIsoProduct E ≪≫
      (biproduct.isoProduct Eop).symm
  exact ⟨{
    n := P.n
    retract :=
      P.retract.op.trans
        (Retract.ofIso biproductOpIso) }⟩

private abbrev restrictRegularDualModule
    (M : ModuleCat.{u} Aᵐᵒᵖ) :
    Module A
      (Opposite.op (regularRightModule A) ⟶
        Opposite.op M) :=
  Module.compHom
    (Opposite.op (regularRightModule A) ⟶
      Opposite.op M)
    regularDualScalarRingEquiv.toRingHom

attribute [local instance] restrictRegularDualModule

private theorem regularDualProjective
    (M : ModuleCat.{u} Aᵐᵒᵖ)
    (hM :
      AuslanderEquivalence.finiteAddClosure
        (regularRightModule A) M) :
    Module.Projective A
      (Opposite.op (regularRightModule A) ⟶
        Opposite.op M) := by
  let G := Opposite.op (regularRightModule A)
  let X : (AuslanderEquivalence.finiteAddClosure G).FullSubcategory :=
    ⟨Opposite.op M, finiteAddClosure_op hM⟩
  have hprojective :
      Module.Projective
        ((End G)ᵐᵒᵖ)
        (G ⟶ Opposite.op M) :=
    (IsProjective.iff_projective
      (G ⟶ Opposite.op M)).mpr
      (AuslanderEquivalence.homFromGenerator_obj_projective
        G X)
  letI :
      Module.Projective
        ((End G)ᵐᵒᵖ)
        (G ⟶ Opposite.op M) :=
    hprojective
  let e := regularDualScalarRingEquiv (A := A)
  letI :
      RingHomInvPair
        e.symm.toRingHom e.toRingHom :=
    RingHomInvPair.of_ringEquiv e.symm
  letI :
      RingHomInvPair
        e.toRingHom e.symm.toRingHom :=
    RingHomInvPair.of_ringEquiv e
  let transfer :
      (G ⟶ Opposite.op M) ≃ₛₗ[e.symm.toRingHom]
        (G ⟶ Opposite.op M) := by
    refine {
      toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := ?_ }
    intro r x
    change r • x =
      regularDualScalarRingEquiv
          (A := A)
          ((regularDualScalarRingEquiv
            (A := A)).symm r) • x
    rw [(regularDualScalarRingEquiv
      (A := A)).apply_symm_apply]
  exact Module.Projective.of_equiv
    (σ' := e.toRingHom) transfer

private abbrev principalIdealOpposite (e : A) : Ideal Aᵐᵒᵖ :=
  (principalTwoSidedIdeal e).asIdealOpposite

private abbrev principalIdealOppositeModule (e : A) :
    ModuleCat.{u} Aᵐᵒᵖ :=
  ModuleCat.of Aᵐᵒᵖ (principalIdealOpposite e)

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
    (fun x y hx hy hfx hfy ↦ by
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
    (fun r x hx hfx ↦ by
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
    fun _ ↦ principalRightModule e
  P.retract.i ≫
    biproduct.desc (fun j : Fin P.n ↦
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

private theorem finiteAddMap_mem_twoSidedSpan
    {e : A} (he : IsIdempotentElem e)
    {X : ModuleCat.{u} Aᵐᵒᵖ}
    (P :
      AuslanderEquivalence.FiniteAddPresentation
        (principalRightModule e) X)
    (f : X ⟶ regularRightModule A)
    (x : X) :
    unop (f.hom x) ∈ principalTwoSidedIdeal e := by
  let l := liftFiniteAddMap he P f
  have hl :=
    liftFiniteAddMap_comp_subtype he P f
  have hpoint :=
    ConcreteCategory.congr_hom hl x
  have hmem :
      (l.hom x : Aᵐᵒᵖ) ∈
        principalIdealOpposite e :=
    l.hom x |>.property
  rw [TwoSidedIdeal.mem_asIdealOpposite] at hmem
  change
    ((l.hom x : principalIdealOpposite e) : Aᵐᵒᵖ) =
      f.hom x at hpoint
  simpa [← hpoint] using hmem

private def dualEvaluation
    {Y : FiniteProjectives A}
    (c : regularFiniteProjective A ⟶ Y) :
    (Opposite.op (regularRightModule A) ⟶
        Opposite.op Y.obj) →ₗ[A] A where
  toFun f :=
    unop ((c.hom ≫ f.unop).hom (1 : Aᵐᵒᵖ))
  map_add' f g := by
    simp
  map_smul' a f := by
    rfl

/-- Left-handed direction of Tsukamoto's projectivity/rejectivity
bridge.  In fact no Artinian or finite-dimensional hypothesis is needed
for this implication. -/
theorem principalTwoSidedIdeal_leftProjective_of_leftRejective
    {e : A} (he : IsIdempotentElem e)
    (hlr :
      CategoricalRejective.IsLeftRejective
        (addPrincipalInFiniteProjectives e)) :
    IsLeftProjectiveIdeal (principalTwoSidedIdeal e) := by
  let D := hlr.some
  let R : FiniteProjectives A :=
    regularFiniteProjective A
  let Y :=
    D.reflector.obj R
  let c :
      R ⟶ Y.obj :=
    D.adjunction.unit.app R
  let P :=
    Y.property.some
  let evalH :
      (Opposite.op (regularRightModule A) ⟶
          Opposite.op Y.obj.obj) →ₗ[A]
        principalTwoSidedIdeal e :=
    (dualEvaluation c).codRestrict
      (principalTwoSidedIdeal e).asIdeal
      (fun f ↦ by
        simpa [dualEvaluation] using
          finiteAddMap_mem_twoSidedSpan
            he P f.unop
            (c.hom.hom (1 : Aᵐᵒᵖ)))
  haveI hc : Epi c :=
    D.unit_epi R
  have hevalH_injective :
      Function.Injective evalH := by
    intro f g hfg
    apply Quiver.Hom.unop_inj
    let ff : Y.obj ⟶ R :=
      ObjectProperty.homMk f.unop
    let gg : Y.obj ⟶ R :=
      ObjectProperty.homMk g.unop
    have hvalue :
        (c.hom ≫ f.unop).hom (1 : Aᵐᵒᵖ) =
          (c.hom ≫ g.unop).hom (1 : Aᵐᵒᵖ) := by
      apply MulOpposite.unop_injective
      exact congrArg Subtype.val hfg
    have hcomp : c ≫ ff = c ≫ gg := by
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      let qf :=
        (c.hom ≫ f.unop).hom
      let qg :=
        (c.hom ≫ g.unop).hom
      calc
        qf x = x * qf 1 := by
          simpa [qf] using
            qf.map_smul x (1 : Aᵐᵒᵖ)
        _ = x * qg 1 := by rw [hvalue]
        _ = qg x := by
          simpa [qg] using
            (qg.map_smul x (1 : Aᵐᵒᵖ)).symm
    have hffgg : ff = gg :=
      (cancel_epi c).1 hcomp
    exact congrArg (fun k ↦ k.hom) hffgg
  have factor_through_unit
      (X :
        (addPrincipalInFiniteProjectives e).FullSubcategory)
      (f :
        R ⟶ (addPrincipalInFiniteProjectives e).ι.obj X) :
      c ≫
          (addPrincipalInFiniteProjectives e).ι.map
            ((D.adjunction.homEquiv R X).symm f) =
        f := by
    calc
      c ≫
          (addPrincipalInFiniteProjectives e).ι.map
            ((D.adjunction.homEquiv R X).symm f) =
          D.adjunction.homEquiv R X
            ((D.adjunction.homEquiv R X).symm f) :=
        (D.adjunction.homEquiv_unit R X _).symm
      _ = f :=
        (D.adjunction.homEquiv R X).apply_symm_apply f
  have range_stable_mulRight
      (b : A) {z : A}
      (hz : z ∈ LinearMap.range (dualEvaluation c)) :
      z * b ∈ LinearMap.range (dualEvaluation c) := by
    obtain ⟨f, hf⟩ := hz
    let m : R ⟶ R :=
      ObjectProperty.homMk <|
        ModuleCat.ofHom
          (LinearMap.mulRight Aᵐᵒᵖ (op b))
    let g :=
      (D.adjunction.homEquiv R Y).symm (m ≫ c)
    let f' :
        Opposite.op (regularRightModule A) ⟶
          Opposite.op Y.obj.obj :=
      (((addPrincipalInFiniteProjectives e).ι.map g).hom ≫
        f.unop).op
    refine ⟨f', ?_⟩
    have hfactor :
        c ≫
            (addPrincipalInFiniteProjectives e).ι.map g =
          m ≫ c :=
      factor_through_unit Y (m ≫ c)
    have hfactorModule :
        c.hom ≫
            ((addPrincipalInFiniteProjectives e).ι.map g).hom =
          m.hom ≫ c.hom :=
      congrArg (fun k ↦ k.hom) hfactor
    have hfop :
        (c.hom ≫ f.unop).hom (1 : Aᵐᵒᵖ) =
          op z := by
      apply unop_injective
      simpa [dualEvaluation] using hf
    change
      unop
          (((c.hom ≫
              ((addPrincipalInFiniteProjectives e).ι.map g).hom) ≫
            f.unop).hom (1 : Aᵐᵒᵖ)) =
        z * b
    rw [hfactorModule]
    let q :=
      (c.hom ≫ f.unop).hom
    change
      unop
          (f.unop.hom
            (c.hom.hom
              (m.hom.hom (1 : Aᵐᵒᵖ)))) =
        z * b
    have hm :
        m.hom.hom (1 : Aᵐᵒᵖ) = op b := by
      simp [m]
    rw [hm]
    change
      unop (q (op b)) = z * b
    calc
      unop (q (op b)) =
          unop (op b * q 1) := by
        congr 1
        simpa [q] using
          q.map_smul (op b) (1 : Aᵐᵒᵖ)
      _ = z * b := by
        rw [hfop]
        rfl
  let K : TwoSidedIdeal A :=
    TwoSidedIdeal.mk'
      {a : A |
        a ∈ LinearMap.range (dualEvaluation c)}
      (LinearMap.range (dualEvaluation c)).zero_mem
      (fun hx hy ↦
        (LinearMap.range (dualEvaluation c)).add_mem hx hy)
      (fun hx ↦
        (LinearMap.range (dualEvaluation c)).neg_mem hx)
      (fun hy ↦
        (LinearMap.range (dualEvaluation c)).smul_mem
          _ hy)
      (fun hx ↦
        range_stable_mulRight _ hx)
  have he_mem_K : e ∈ K := by
    let E :
        (addPrincipalInFiniteProjectives e).FullSubcategory :=
      principalAddObject he
    let p :
        R ⟶ (addPrincipalInFiniteProjectives e).ι.obj E :=
      ObjectProperty.homMk <|
        ModuleCat.ofHom (principalRightProjection e)
    let g :=
      (D.adjunction.homEquiv R E).symm p
    let j : E.obj ⟶ R :=
      ObjectProperty.homMk <|
        ModuleCat.ofHom
          (Submodule.subtype (principalRightIdeal e))
    let f :
        Opposite.op (regularRightModule A) ⟶
          Opposite.op Y.obj.obj :=
      (((addPrincipalInFiniteProjectives e).ι.map g).hom ≫
        j.hom).op
    have hfactor :
        c ≫
            (addPrincipalInFiniteProjectives e).ι.map g =
          p :=
      factor_through_unit E p
    have hfactorModule :
        c.hom ≫
            ((addPrincipalInFiniteProjectives e).ι.map g).hom =
          p.hom :=
      congrArg (fun k ↦ k.hom) hfactor
    have heRange :
        e ∈ LinearMap.range (dualEvaluation c) := by
      refine ⟨f, ?_⟩
      change
        unop
            (((c.hom ≫
                ((addPrincipalInFiniteProjectives e).ι.map g).hom) ≫
              j.hom).hom (1 : Aᵐᵒᵖ)) =
          e
      rw [hfactorModule]
      change
        unop
            (((principalRightProjection e)
              (1 : Aᵐᵒᵖ) :
                principalRightIdeal e).1) =
          e
      simp [principalRightProjection]
    dsimp only [K]
    rw [TwoSidedIdeal.mem_mk']
    exact heRange
  have hspan_le_K :
      principalTwoSidedIdeal e ≤ K := by
    apply TwoSidedIdeal.span_le.mpr
    rw [Set.singleton_subset_iff]
    exact he_mem_K
  have hevalH_surjective :
      Function.Surjective evalH := by
    intro q
    have hqK : (q : A) ∈ K :=
      hspan_le_K q.property
    have hqRange :
        (q : A) ∈
          LinearMap.range (dualEvaluation c) := by
      dsimp only [K] at hqK
      rw [TwoSidedIdeal.mem_mk'] at hqK
      exact hqK
    obtain ⟨f, hf⟩ := hqRange
    refine ⟨f, ?_⟩
    apply Subtype.ext
    exact hf
  let el :
      (Opposite.op (regularRightModule A) ⟶
          Opposite.op Y.obj.obj) ≃ₗ[A]
        principalTwoSidedIdeal e :=
    LinearEquiv.ofBijective evalH
      ⟨hevalH_injective, hevalH_surjective⟩
  have hYregular :
      AuslanderEquivalence.finiteAddClosure
        (regularRightModule A) Y.obj.obj :=
    (AuslanderEquivalence.finiteAddClosure_regular_iff
      Aᵐᵒᵖ Y.obj.obj).mpr Y.obj.property
  letI :
      Module.Projective A
        (Opposite.op (regularRightModule A) ⟶
          Opposite.op Y.obj.obj) :=
    regularDualProjective Y.obj.obj hYregular
  exact Module.Projective.of_equiv el

/-- Public-shape wrapper with the ambient finite-projective category and
the additive closure written literally. -/
theorem principalTwoSidedIdeal_leftProjective_of_literal_leftRejective
    {e : A} (he : IsIdempotentElem e)
    (hlr :
      CategoricalRejective.IsLeftRejective
        (fun X :
          (AuslanderEquivalence.finiteProjectiveModules
            Aᵐᵒᵖ).FullSubcategory ↦
          addPrincipalRightModule e X.obj)) :
    IsLeftProjectiveIdeal (principalTwoSidedIdeal e) :=
  principalTwoSidedIdeal_leftProjective_of_leftRejective
    he hlr

end QuotientSubmoduleEquidistribution.Tsukamoto.LeftBridge

