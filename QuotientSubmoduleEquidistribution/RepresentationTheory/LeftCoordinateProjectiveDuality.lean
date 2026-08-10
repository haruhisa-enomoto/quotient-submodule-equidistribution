import QuotientSubmoduleEquidistribution.RepresentationTheory.CoordinateStandardKernelFiltration
import QuotientSubmoduleEquidistribution.RepresentationTheory.TsukamotoLeftRejectiveConverse

/-!
# The projective dual of a legal subobject-deletion chain

This file isolates the reusable projective-level input for the
left-module CPS construction.  The existing finite-projective Hom duality in
`TsukamotoLeftRejectiveConverse` is private, so the first section reconstructs
its public interface.  The second section sends every left-rejective term of a
legal subobject-deletion chain to a right-rejective subcategory of finite
projective left modules over the skeleton Auslander algebra.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits MulOpposite

namespace QuotientSubmoduleEquidistribution.CPSLeftStandardLayers

universe vC vD uC uD u

/-- Finitely generated projective right `A`-modules. -/
abbrev RightFiniteProjectives (A : Type u) [Ring A] :=
  (AuslanderEquivalence.finiteProjectiveModules Aᵐᵒᵖ).FullSubcategory

/-- Finitely generated projective left `A`-modules. -/
abbrev LeftFiniteProjectives (A : Type u) [Ring A] :=
  (AuslanderEquivalence.finiteProjectiveModules A).FullSubcategory

/-- The right regular module as a finite-projective object. -/
def rightRegularFiniteProjective (A : Type u) [Ring A] :
    RightFiniteProjectives A :=
  ⟨ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ,
    Module.Finite.self Aᵐᵒᵖ,
    ModuleCat.projective_of_free (Module.Basis.singleton Unit Aᵐᵒᵖ)⟩

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts
  FintypeCat.fintype

/-- A finite biproduct in an opposite category is the opposite of the
corresponding finite biproduct. -/
def opBiproductIso
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    [HasFiniteBiproducts C]
    {J : Type*} [Fintype J] (F : J → C) :
    Opposite.op (biproduct F) ≅
      biproduct (fun j ↦ Opposite.op (F j)) :=
  (biproduct.isoCoproduct F).op.symm ≪≫
    opCoproductIsoProduct F ≪≫
    (biproduct.isoProduct (fun j ↦ Opposite.op (F j))).symm

private theorem finiteAddClosure_op
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    [HasFiniteBiproducts C]
    {G X : C}
    (h : AuslanderEquivalence.finiteAddClosure G X) :
    AuslanderEquivalence.finiteAddClosure
      (Opposite.op G) (Opposite.op X) := by
  obtain ⟨P⟩ := h
  let E : Fin P.n → C := fun _ ↦ G
  let Eop : Fin P.n → Cᵒᵖ := fun j ↦ Opposite.op (E j)
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

private theorem finiteAddClosure_unop
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    [HasFiniteBiproducts C]
    {G X : C}
    (h : AuslanderEquivalence.finiteAddClosure
      (Opposite.op G) (Opposite.op X)) :
    AuslanderEquivalence.finiteAddClosure G X := by
  obtain ⟨P⟩ := h
  let E : Fin P.n → C := fun _ ↦ G
  let Eop : Fin P.n → Cᵒᵖ := fun j ↦ Opposite.op (E j)
  let biproductOpIso :
      Opposite.op (biproduct E) ≅ biproduct Eop :=
    (biproduct.isoCoproduct E).op.symm ≪≫
      opCoproductIsoProduct E ≪≫
      (biproduct.isoProduct Eop).symm
  exact ⟨{
    n := P.n
    retract :=
      (P.retract.op.map (unopUnop C)).trans
        (Retract.ofIso biproductOpIso.unop) }⟩

private theorem finiteAddClosure_op_iff
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    [HasFiniteBiproducts C]
    {G X : C} :
    AuslanderEquivalence.finiteAddClosure
        (Opposite.op G) (Opposite.op X) ↔
      AuslanderEquivalence.finiteAddClosure G X :=
  ⟨finiteAddClosure_unop, finiteAddClosure_op⟩

private theorem finiteAddClosure_map_functor
    {C : Type uC} {D : Type uD}
    [Category.{vC} C] [Preadditive C]
    [Category.{vD} D] [Preadditive D]
    [HasFiniteBiproducts C] [HasFiniteBiproducts D]
    (E : C ≌ D) {G X : C}
    (h : AuslanderEquivalence.finiteAddClosure G X) :
    AuslanderEquivalence.finiteAddClosure
      (E.functor.obj G) (E.functor.obj X) := by
  obtain ⟨P⟩ := h
  letI : PreservesBiproduct (fun _ : Fin P.n ↦ G) E.functor :=
    preservesBiproduct_of_preservesProduct E.functor
  exact ⟨{
    n := P.n
    retract :=
      (P.retract.map E.functor).trans
        (Retract.ofIso
          (E.functor.mapBiproduct (fun _ : Fin P.n ↦ G))) }⟩

private theorem finiteAddClosure_map_equivalence_iff
    {C : Type uC} {D : Type uD}
    [Category.{vC} C] [Preadditive C]
    [Category.{vD} D] [Preadditive D]
    [HasFiniteBiproducts C] [HasFiniteBiproducts D]
    (E : C ≌ D) {G X : C} :
    AuslanderEquivalence.finiteAddClosure
        (E.functor.obj G) (E.functor.obj X) ↔
      AuslanderEquivalence.finiteAddClosure G X := by
  constructor
  · intro h
    have h' := finiteAddClosure_map_functor E.symm h
    have h'' :
        AuslanderEquivalence.finiteAddClosure
          G (E.inverse.obj (E.functor.obj X)) :=
      (AuslanderEquivalence.finiteAddClosure_iff_of_iso
        (E.unitIso.app G)).mpr h'
    obtain ⟨P⟩ := h''
    exact ⟨{
      n := P.n
      retract :=
        (Retract.ofIso (E.unitIso.app X)).trans P.retract }⟩
  · exact finiteAddClosure_map_functor E

private instance finiteAddClosure_isClosedUnderIsomorphisms
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    [HasFiniteBiproducts C] (G : C) :
    (AuslanderEquivalence.finiteAddClosure G).IsClosedUnderIsomorphisms where
  of_iso {X Y} i hX := by
    obtain ⟨P⟩ := hX
    exact ⟨{
      n := P.n
      retract := (Retract.ofIso i.symm).trans P.retract }⟩

private instance finiteProjective_isClosedUnderIsomorphisms
    (S : Type u) [Ring S] :
    (AuslanderEquivalence.finiteProjectiveModules S).IsClosedUnderIsomorphisms where
  of_iso {X Y} i hX := by
    have hAddX :
        AuslanderEquivalence.finiteAddClosure
          (ModuleCat.of S S) X :=
      (AuslanderEquivalence.finiteAddClosure_regular_iff S X).mpr hX
    obtain ⟨P⟩ := hAddX
    apply (AuslanderEquivalence.finiteAddClosure_regular_iff S Y).mp
    exact ⟨{
      n := P.n
      retract := (Retract.ofIso i.symm).trans P.retract }⟩

private theorem finiteProjective_restrictScalars_inverseImage
    {R S : Type u} [Ring R] [Ring S]
    (e : R ≃+* S) :
    (AuslanderEquivalence.finiteProjectiveModules R).inverseImage
        (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).functor =
      AuslanderEquivalence.finiteProjectiveModules S := by
  funext M
  apply propext
  let E := ModuleCat.restrictScalarsEquivalenceOfRingEquiv e
  let i : E.functor.obj (ModuleCat.of S S) ≅ ModuleCat.of R R :=
    ModuleCat.restrictScalarsIsoOfEquiv e
  calc
    AuslanderEquivalence.finiteProjectiveModules R (E.functor.obj M) ↔
        AuslanderEquivalence.finiteAddClosure
          (ModuleCat.of R R) (E.functor.obj M) :=
      (AuslanderEquivalence.finiteAddClosure_regular_iff
        R (E.functor.obj M)).symm
    _ ↔ AuslanderEquivalence.finiteAddClosure
          (E.functor.obj (ModuleCat.of S S)) (E.functor.obj M) :=
      (AuslanderEquivalence.finiteAddClosure_iff_of_iso i).symm
    _ ↔ AuslanderEquivalence.finiteAddClosure
          (ModuleCat.of S S) M :=
      finiteAddClosure_map_equivalence_iff E
    _ ↔ AuslanderEquivalence.finiteProjectiveModules S M :=
      AuslanderEquivalence.finiteAddClosure_regular_iff S M

/-- Restriction of scalars along a ring equivalence preserves the full
subcategory of finite projectives. -/
def finiteProjectiveRestrictScalarsEquivalence
    {R S : Type u} [Ring R] [Ring S]
    (e : R ≃+* S) :
    LeftFiniteProjectives S ≌ LeftFiniteProjectives R :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).congrFullSubcategory
    (finiteProjective_restrictScalars_inverseImage e)

private abbrev regularRightModule (A : Type u) [Ring A] :
    ModuleCat.{u} Aᵐᵒᵖ :=
  ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ

/-- Scalar identification for the Hom-dual of the right regular module. -/
def regularDualScalarRingEquiv {A : Type u} [Ring A] :
    A ≃+* (End (Opposite.op (regularRightModule A)))ᵐᵒᵖ where
  toFun a :=
    op (ModuleCat.ofHom (LinearMap.mulRight Aᵐᵒᵖ (op a))).op
  invFun f := unop (f.unop.unop.hom (1 : Aᵐᵒᵖ))
  left_inv a := by simp
  right_inv f := by
    apply MulOpposite.unop_injective
    apply Quiver.Hom.unop_inj
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change x * f.unop.unop.hom 1 = f.unop.unop.hom x
    simpa using (f.unop.unop.hom.map_smul x (1 : Aᵐᵒᵖ)).symm
  map_add' a b := by
    apply MulOpposite.unop_injective
    apply Quiver.Hom.unop_inj
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change x * (op a + op b) = x * op a + x * op b
    exact mul_add x (op a) (op b)
  map_mul' a b := by
    apply MulOpposite.unop_injective
    apply Quiver.Hom.unop_inj
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simp

/-- The left `A`-module structure on the endomorphism space which occurs as
the Hom dual of the right regular module. -/
abbrev regularHomDualModule (A : Type u) [Ring A] :
    Module A
      (Opposite.op (regularRightModule A) ⟶
        Opposite.op (regularRightModule A)) :=
  Module.compHom
    (Opposite.op (regularRightModule A) ⟶
      Opposite.op (regularRightModule A))
    (regularDualScalarRingEquiv (A := A)).toRingHom

attribute [local instance] regularHomDualModule

/-- Evaluation at `1` identifies the Hom dual of the right regular module
with the left regular module. -/
def regularHomDualLinearEquiv (A : Type u) [Ring A] :
    (Opposite.op (regularRightModule A) ⟶
        Opposite.op (regularRightModule A)) ≃ₗ[A] A where
  toFun f := unop (f.unop.hom (1 : Aᵐᵒᵖ))
  invFun a :=
    (ModuleCat.ofHom (LinearMap.mulRight Aᵐᵒᵖ (op a))).op
  left_inv f := by
    apply Quiver.Hom.unop_inj
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change x * f.unop.hom 1 = f.unop.hom x
    simpa using (f.unop.hom.map_smul x (1 : Aᵐᵒᵖ)).symm
  right_inv a := by simp
  map_add' f g := by
    simp
  map_smul' a f := by
    rfl

private theorem oppositeFiniteProjective_eq_finiteAddClosure
    {A : Type u} [Ring A] :
    (AuslanderEquivalence.finiteProjectiveModules Aᵐᵒᵖ).op =
      AuslanderEquivalence.finiteAddClosure
        (Opposite.op (regularRightModule A)) := by
  funext X
  apply propext
  induction X with
  | op X =>
      exact
        (AuslanderEquivalence.finiteAddClosure_regular_iff
          Aᵐᵒᵖ X).symm.trans finiteAddClosure_op_iff.symm

/-- The ring-general Hom duality between finite projective right and left
`A`-modules.  This is the public interface missing from the current tracked
API. -/
def regularHomDualityEquivalence
    (A : Type u) [Ring A] :
    (RightFiniteProjectives A)ᵒᵖ ≌ LeftFiniteProjectives A :=
  (ObjectProperty.opEquivalence
      (AuslanderEquivalence.finiteProjectiveModules Aᵐᵒᵖ)).symm |>.trans <|
    (ObjectProperty.fullSubcategoryCongr
      (oppositeFiniteProjective_eq_finiteAddClosure (A := A))) |>.trans <|
    (AuslanderEquivalence.auslanderEquivalence
      (Opposite.op (regularRightModule A))) |>.trans <|
    finiteProjectiveRestrictScalarsEquivalence
      (regularDualScalarRingEquiv (A := A))

/-- An anti-equivalence between full subcategories of module categories
preserves the concrete module-level indecomposability predicate.  This is the
full-subcategory analogue of `ContragredientDuality.indecomposable_map_anti`;
it needs no exactness or finiteness hypothesis. -/
theorem indecomposable_map_anti_fullSubcategory
    {R S : Type u} [Ring R] [Ring S]
    (P : ObjectProperty (ModuleCat.{u} R))
    (Q : ObjectProperty (ModuleCat.{u} S))
    (E : P.FullSubcategoryᵒᵖ ≌ Q.FullSubcategory)
    {M : P.FullSubcategory}
    (hM : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R M.obj) :
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule S
      (E.functor.obj (Opposite.op M)).obj := by
  rw [QuotientSubmoduleEquidistribution.Foundation.isIndecomposableModule_iff_nontrivial_and_forall_isIdempotentElem]
  constructor
  · by_contra h
    letI : Subsingleton (E.functor.obj (Opposite.op M)).obj :=
      not_nontrivial_iff_subsingleton.mp h
    have htarget :
        (𝟙 (E.functor.obj (Opposite.op M)) :
          E.functor.obj (Opposite.op M) ⟶
            E.functor.obj (Opposite.op M)) = 0 := by
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      ext x
      exact Subsingleton.elim _ _
    have hsourceOp :
        (𝟙 (Opposite.op M) : Opposite.op M ⟶ Opposite.op M) = 0 := by
      apply E.functor.map_injective
      simpa using htarget
    have hsource : (𝟙 M : M ⟶ M) = 0 := by
      apply Quiver.Hom.op_inj
      simpa using hsourceOp
    letI : Nontrivial M.obj := hM.nontrivial
    have hend : (1 : Module.End R M.obj) = 0 := by
      have hlinear := congrArg (fun f : M ⟶ M ↦ f.hom.hom) hsource
      simpa [Module.End.one_eq_id] using hlinear
    exact one_ne_zero hend
  · intro f hf
    let fcat :
        E.functor.obj (Opposite.op M) ⟶
          E.functor.obj (Opposite.op M) :=
      ObjectProperty.homMk (ModuleCat.ofHom f)
    have fcat_apply (x : (E.functor.obj (Opposite.op M)).obj) :
        fcat.hom.hom x = f x :=
      rfl
    let gop : Opposite.op M ⟶ Opposite.op M :=
      E.functor.preimage fcat
    let g : Module.End R M.obj :=
      gop.unop.hom.hom
    have hcat : gop ≫ gop = gop := by
      apply E.functor.map_injective
      rw [E.functor.map_comp]
      change
        E.functor.map (E.functor.preimage fcat) ≫
            E.functor.map (E.functor.preimage fcat) =
          E.functor.map (E.functor.preimage fcat)
      rw [E.functor.map_preimage fcat]
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      change f.comp f = f
      change f * f = f at hf
      simpa [Module.End.mul_eq_comp] using hf
    have hg : IsIdempotentElem g := by
      change g * g = g
      have hlinear :=
        congrArg
          (fun q : Opposite.op M ⟶ Opposite.op M ↦
            q.unop.hom.hom) hcat
      simpa [g, Module.End.mul_eq_comp] using hlinear
    rcases hM.eq_zero_or_eq_one_of_isIdempotentElem hg with hg | hg
    · left
      have hgcat : gop = 0 := by
        apply Quiver.Hom.unop_inj
        apply ObjectProperty.hom_ext
        apply ModuleCat.hom_ext
        exact hg
      have hfcat : fcat = 0 := by
        calc
          fcat = E.functor.map gop :=
            (E.functor.map_preimage fcat).symm
          _ = E.functor.map 0 := congrArg E.functor.map hgcat
          _ = 0 := E.functor.map_zero (Opposite.op M) (Opposite.op M)
      ext x
      have hx := congrArg
        (fun q : E.functor.obj (Opposite.op M) ⟶
            E.functor.obj (Opposite.op M) ↦ q.hom.hom x) hfcat
      rw [fcat_apply] at hx
      simpa using hx
    · right
      have hgcat : gop = 𝟙 (Opposite.op M) := by
        apply Quiver.Hom.unop_inj
        apply ObjectProperty.hom_ext
        apply ModuleCat.hom_ext
        simpa [g, Module.End.one_eq_id] using hg
      have hfcat :
          fcat = 𝟙 (E.functor.obj (Opposite.op M)) := by
        calc
          fcat = E.functor.map gop :=
            (E.functor.map_preimage fcat).symm
          _ = E.functor.map (𝟙 (Opposite.op M)) :=
            congrArg E.functor.map hgcat
          _ = 𝟙 (E.functor.obj (Opposite.op M)) :=
            E.functor.map_id (Opposite.op M)
      ext x
      have hx := congrArg
        (fun q : E.functor.obj (Opposite.op M) ⟶
            E.functor.obj (Opposite.op M) ↦ q.hom.hom x) hfcat
      rw [fcat_apply] at hx
      simpa [Module.End.one_eq_id] using hx

namespace Coordinate

open QuotientSubmoduleEquidistribution.IndecomposableSkeleton
open QuotientSubmoduleEquidistribution.IndecomposableSkeleton.LegalSubobjectDeletionChain
open QuotientSubmoduleEquidistribution.AuslanderEquivalence.CoordinateIdempotent

universe uR uκ wR

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {κ : Type uκ}
  (σ : IndecomposableSkeleton.{uR, uκ, wR} R κ)
  [Fintype κ]

local notation "Γ" => skeletonAuslanderAlgebra σ

local instance rightTarget_hasFiniteBiproducts :
    HasFiniteBiproducts (skeletonProjectiveTarget σ) :=
  CategoricalAdditiveSubcategory.hasFiniteBiproductsOfEquivalence
    (skeletonAuslanderEquivalence σ)

local instance leftTarget_hasFiniteBiproducts :
    HasFiniteBiproducts (LeftFiniteProjectives Γ) := by
  exact CategoricalAdditiveSubcategory.hasFiniteBiproductsOfEquivalence
    (regularHomDualityEquivalence Γ)

/-- The left coordinate projective dual to the usual right coordinate
projective.  Its ambient module is literally a left `Γ`-module. -/
abbrev leftCoordinateProjective (i : κ) :
    LeftFiniteProjectives Γ :=
  (regularHomDualityEquivalence Γ).functor.obj
    (Opposite.op (coordinateProjective σ i))

/-- Left coordinate objects are finite projective by construction. -/
theorem leftCoordinateProjective_isFiniteProjective (i : κ) :
    AuslanderEquivalence.finiteProjectiveModules Γ
      (leftCoordinateProjective σ i).obj :=
  (leftCoordinateProjective σ i).property

/-- Hom duality preserves the indecomposability of every coordinate
projective. -/
theorem leftCoordinateProjective_indecomposable (i : κ) :
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule Γ
      (leftCoordinateProjective σ i).obj := by
  exact indecomposable_map_anti_fullSubcategory
    (AuslanderEquivalence.finiteProjectiveModules Γᵐᵒᵖ)
    (AuslanderEquivalence.finiteProjectiveModules Γ)
    (regularHomDualityEquivalence Γ)
    (coordinateProjective_indecomposable σ i)

/-- The Hom dual of the right regular module is the left regular module. -/
def leftDualRegularIso :
    ((regularHomDualityEquivalence Γ).functor.obj
      (Opposite.op (rightRegularFiniteProjective Γ))).obj ≅
      ModuleCat.of Γ Γ := by
  dsimp [regularHomDualityEquivalence,
    finiteProjectiveRestrictScalarsEquivalence]
  change
    ModuleCat.of Γ
        (Opposite.op (regularRightModule Γ) ⟶
          Opposite.op (regularRightModule Γ)) ≅
      ModuleCat.of Γ Γ
  exact (regularHomDualLinearEquiv Γ).toModuleIso

/-- The biproduct of all right coordinate projectives is the right regular
`Γ`-module. -/
def rightCoordinateProjectiveBiproductIsoRegular :
    (⨁ fun i : κ ↦ (coordinateProjective σ i).obj) ≅
      ModuleCat.of Γᵐᵒᵖ Γᵐᵒᵖ := by
  let P := AuslanderEquivalence.finiteProjectiveModules Γᵐᵒᵖ
  exact
    biproduct.mapIso (fun i ↦
      (P.ι.mapIso (auslanderImageIsoCoordinateProjective σ i)).symm) ≪≫
      auslanderImageBiproductIsoRegular σ

/-- Full-subcategory form of the right-coordinate regular decomposition. -/
def rightCoordinateProjectiveBiproductIsoRegularTarget :
    (⨁ fun i : κ ↦ coordinateProjective σ i) ≅
      rightRegularFiniteProjective Γ := by
  let P := AuslanderEquivalence.finiteProjectiveModules Γᵐᵒᵖ
  let F : κ → skeletonProjectiveTarget σ :=
    fun i ↦ coordinateProjective σ i
  letI : PreservesBiproduct F P.ι :=
    preservesBiproduct_of_preservesProduct P.ι
  exact P.isoMk <|
    P.ι.mapBiproduct F ≪≫
      rightCoordinateProjectiveBiproductIsoRegular σ

/-- Hom duality transports the right-coordinate regular decomposition to a
literal decomposition of the left regular module by the left coordinate
projectives. -/
def leftCoordinateProjectiveBiproductIsoRegular :
    (⨁ fun i : κ ↦ (leftCoordinateProjective σ i).obj) ≅
      ModuleCat.of Γ Γ := by
  let E := regularHomDualityEquivalence Γ
  let PR := AuslanderEquivalence.finiteProjectiveModules Γᵐᵒᵖ
  let PL := AuslanderEquivalence.finiteProjectiveModules Γ
  let F : κ → skeletonProjectiveTarget σ :=
    fun i ↦ coordinateProjective σ i
  let Fop : κ → (skeletonProjectiveTarget σ)ᵒᵖ :=
    fun i ↦ Opposite.op (F i)
  let FL : κ → LeftFiniteProjectives Γ :=
    fun i ↦ leftCoordinateProjective σ i
  letI : PreservesBiproduct Fop E.functor :=
    preservesBiproduct_of_preservesProduct E.functor
  letI : PreservesBiproduct FL PL.ι :=
    preservesBiproduct_of_preservesProduct PL.ι
  exact
    (PL.ι.mapBiproduct FL).symm ≪≫
      PL.ι.mapIso (E.functor.mapBiproduct Fop).symm ≪≫
      PL.ι.mapIso (E.functor.mapIso (opBiproductIso F).symm) ≪≫
      PL.ι.mapIso (E.functor.mapIso
        (rightCoordinateProjectiveBiproductIsoRegularTarget σ).op.symm) ≪≫
      leftDualRegularIso σ

/-- Distinct labels remain nonisomorphic after finite-projective Hom
duality. -/
theorem leftCoordinateProjective_eq_of_iso {i j : κ}
    (e : leftCoordinateProjective σ i ≅
      leftCoordinateProjective σ j) :
    i = j := by
  let E := regularHomDualityEquivalence Γ
  let eop :
      Opposite.op (coordinateProjective σ i) ≅
        Opposite.op (coordinateProjective σ j) :=
    E.unitIso.app (Opposite.op (coordinateProjective σ i)) ≪≫
      E.inverse.mapIso e ≪≫
      (E.unitIso.app (Opposite.op (coordinateProjective σ j))).symm
  exact
    (coordinateProjective_eq_of_iso σ eop.unop).symm

/-- The simple top of a left coordinate projective. -/
abbrev leftCoordinateSimple (i : κ) : ModuleCat.{wR} Γ :=
  ModuleCat.of Γ
    ((leftCoordinateProjective σ i).obj ⧸
      Module.jacobson Γ (leftCoordinateProjective σ i).obj)

/-- The canonical projective cover of a left coordinate simple. -/
def leftCoordinateProjectiveCover
    (hfinite : ∀ i : κ,
      IsFiniteLength Γ (leftCoordinateProjective σ i).obj)
    (i : κ) :
    QuotientSubmoduleEquidistribution.Tsukamoto.StandardSemantics.ProjectiveCover
      (leftCoordinateSimple σ i) := by
  open QuotientSubmoduleEquidistribution.ProjectiveSimpleTop in
  let hP := leftCoordinateProjective_isFiniteProjective σ i
  letI : Module.Finite Γ (leftCoordinateProjective σ i).obj := hP.1
  letI : Projective (leftCoordinateProjective σ i).obj := hP.2
  letI : Module.Projective Γ (leftCoordinateProjective σ i).obj :=
    (IsProjective.iff_projective
      (leftCoordinateProjective σ i).obj).mpr hP.2
  exact
    jacobsonProjectiveCoverOfIndecomposable
      (hfinite i) (leftCoordinateProjective_indecomposable σ i)

/-- Each left coordinate radical quotient is simple. -/
theorem leftCoordinateSimple_isSimple
    (hfinite : ∀ i : κ,
      IsFiniteLength Γ (leftCoordinateProjective σ i).obj)
    (i : κ) :
    Simple (leftCoordinateSimple σ i) := by
  open QuotientSubmoduleEquidistribution.ProjectiveSimpleTop in
  let hP := leftCoordinateProjective_isFiniteProjective σ i
  letI : Module.Finite Γ (leftCoordinateProjective σ i).obj := hP.1
  letI : Projective (leftCoordinateProjective σ i).obj := hP.2
  letI : Module.Projective Γ (leftCoordinateProjective σ i).obj :=
    (IsProjective.iff_projective
      (leftCoordinateProjective σ i).obj).mpr hP.2
  rw [simple_iff_isSimpleModule]
  exact
    simple_top_of_indec_projective
      (hfinite i) (leftCoordinateProjective_indecomposable σ i)

/-- Distinct left coordinate simples have distinct labels. -/
theorem leftCoordinateSimple_eq_of_iso
    (hfinite : ∀ i : κ,
      IsFiniteLength Γ (leftCoordinateProjective σ i).obj)
    {i j : κ}
    (e : leftCoordinateSimple σ i ≅ leftCoordinateSimple σ j) :
    i = j := by
  open QuotientSubmoduleEquidistribution.Tsukamoto.StandardSemantics in
  let pIso :
      (leftCoordinateProjectiveCover σ hfinite i).object ≅
        (leftCoordinateProjectiveCover σ hfinite j).object :=
    ProjectiveCover.objectIsoOfTargetIso
      (leftCoordinateProjectiveCover σ hfinite i)
      (leftCoordinateProjectiveCover σ hfinite j) e
  exact leftCoordinateProjective_eq_of_iso σ
    ((AuslanderEquivalence.finiteProjectiveModules Γ).isoMk pIso)

/-- A nonzero map from a left coordinate projective to a simple module
identifies the latter with the corresponding coordinate top. -/
def simpleIsoLeftCoordinateSimpleOfNonzero
    (hfinite : ∀ i : κ,
      IsFiniteLength Γ (leftCoordinateProjective σ i).obj)
    (i : κ)
    (S : ModuleCat.{wR} Γ) (hS : Simple S)
    (f : (leftCoordinateProjective σ i).obj ⟶ S)
    (hf : f ≠ 0) :
    S ≅ leftCoordinateSimple σ i := by
  open QuotientSubmoduleEquidistribution.ProjectiveSimpleTop in
  letI : Simple S := hS
  letI : IsSimpleModule Γ S := isSimpleModule_of_simple S
  let hindec := leftCoordinateProjective_indecomposable σ i
  let hP := leftCoordinateProjective_isFiniteProjective σ i
  letI : Nontrivial (leftCoordinateProjective σ i).obj :=
    hindec.nontrivial
  letI : Module.Finite Γ (leftCoordinateProjective σ i).obj := hP.1
  letI : Projective (leftCoordinateProjective σ i).obj := hP.2
  letI : Module.Projective Γ (leftCoordinateProjective σ i).obj :=
    (IsProjective.iff_projective
      (leftCoordinateProjective σ i).obj).mpr hP.2
  letI : IsLocalRing
      (Module.End Γ (leftCoordinateProjective σ i).obj) :=
    QuotientSubmoduleEquidistribution.Foundation.isLocalRing_end_of_isIndecomposable (hfinite i) hindec
  letI : Epi f := epi_of_nonzero_to_simple hf
  exact
    (topLinearEquivOfSurjectiveToSimple f.hom
      ((ModuleCat.epi_iff_surjective f).mp inferInstance)).toModuleIso.symm

/-- There are no maps from a left coordinate projective to a differently
labelled coordinate simple. -/
theorem hom_leftCoordinateSimple_eq_zero_of_ne
    (hfinite : ∀ i : κ,
      IsFiniteLength Γ (leftCoordinateProjective σ i).obj)
    {i j : κ} (hij : i ≠ j)
    (f : (leftCoordinateProjective σ i).obj ⟶
      leftCoordinateSimple σ j) :
    f = 0 := by
  by_contra hf
  let e : leftCoordinateSimple σ j ≅ leftCoordinateSimple σ i :=
    simpleIsoLeftCoordinateSimpleOfNonzero σ hfinite i
      (leftCoordinateSimple σ j)
      (leftCoordinateSimple_isSimple σ hfinite j) f hf
  exact hij <| (leftCoordinateSimple_eq_of_iso σ hfinite e).symm

/-- The statement that the left coordinate tops exhaust the simple left
`Γ`-modules. -/
def LeftCoordinateSimpleCompleteness
    : Prop :=
  ∀ (S : ModuleCat.{wR} Γ), Simple S →
    ∃ i : κ, Nonempty (S ≅ leftCoordinateSimple σ i)

/-- The left-coordinate regular decomposition proves that the coordinate
tops exhaust all simple left `Γ`-modules. -/
theorem leftCoordinateSimple_complete
    (hfinite : ∀ i : κ,
      IsFiniteLength Γ (leftCoordinateProjective σ i).obj) :
    LeftCoordinateSimpleCompleteness σ := by
  intro S hS
  letI : Simple S := hS
  letI : IsSimpleModule Γ S := isSimpleModule_of_simple S
  letI : Nontrivial S := IsSimpleModule.nontrivial Γ S
  obtain ⟨s, hs⟩ := exists_ne (0 : S)
  let q : ModuleCat.of Γ Γ ⟶ S :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton Γ S s)
  haveI : Epi q := by
    rw [ModuleCat.epi_iff_surjective]
    exact IsSimpleModule.toSpanSingleton_surjective Γ hs
  let F : κ → ModuleCat.{wR} Γ :=
    fun i ↦ (leftCoordinateProjective σ i).obj
  let t : (⨁ F) ⟶ S :=
    (leftCoordinateProjectiveBiproductIsoRegular σ).hom ≫ q
  haveI : Epi t := by
    dsimp [t]
    infer_instance
  have ht : t ≠ 0 := by
    intro ht
    exact Simple.not_isZero S (IsZero.of_epi_eq_zero t ht)
  have hcomponent :
      ∃ i : κ, biproduct.ι F i ≫ t ≠ 0 := by
    by_contra h
    push Not at h
    apply ht
    apply biproduct.hom_ext'
    intro i
    exact h i
  obtain ⟨i, hi⟩ := hcomponent
  exact ⟨i, ⟨
    simpleIsoLeftCoordinateSimpleOfNonzero
      σ hfinite i S hS (biproduct.ι F i ≫ t) hi⟩⟩

/-- Complete left coordinate simple/projective-cover data. -/
structure LeftCoordinateSimpleCoverClassification
    where
  simple_isSimple : ∀ i, Simple (leftCoordinateSimple σ i)
  simple_complete : LeftCoordinateSimpleCompleteness σ
  simple_nodup :
    ∀ {i j}, Nonempty
      (leftCoordinateSimple σ i ≅ leftCoordinateSimple σ j) → i = j
  cover : ∀ i,
    QuotientSubmoduleEquidistribution.Tsukamoto.StandardSemantics.ProjectiveCover
      (leftCoordinateSimple σ i)
  hom_projective_simple_eq_zero_of_ne :
    ∀ {i j}, i ≠ j →
      ∀ f : (leftCoordinateProjective σ i).obj ⟶
        leftCoordinateSimple σ j, f = 0

/-- Once left-simple completeness is supplied, every remaining field follows
from finite-projective Hom duality and the generic simple-top theorem. -/
def leftCoordinateSimpleCoverClassification_of_complete
    (hfinite : ∀ i : κ,
      IsFiniteLength Γ (leftCoordinateProjective σ i).obj)
    (hcomplete : LeftCoordinateSimpleCompleteness σ) :
    LeftCoordinateSimpleCoverClassification σ where
  simple_isSimple := leftCoordinateSimple_isSimple σ hfinite
  simple_complete := hcomplete
  simple_nodup := by
    rintro i j ⟨e⟩
    exact leftCoordinateSimple_eq_of_iso σ hfinite e
  cover := leftCoordinateProjectiveCover σ hfinite
  hom_projective_simple_eq_zero_of_ne :=
    hom_leftCoordinateSimple_eq_zero_of_ne σ hfinite

/-- Finite length of the left coordinate projectives now supplies the full
simple/projective-cover classification unconditionally. -/
def leftCoordinateSimpleCoverClassification
    (hfinite : ∀ i : κ,
      IsFiniteLength Γ (leftCoordinateProjective σ i).obj) :
    LeftCoordinateSimpleCoverClassification σ :=
  leftCoordinateSimpleCoverClassification_of_complete σ hfinite
    (leftCoordinateSimple_complete σ hfinite)

/-- The right-rejective object property obtained by taking the opposite of a
left-rejective target term and applying finite-projective Hom duality. -/
def dualTargetRightRejectiveProperty
    (hfinite : ∀ X : FGModuleCat.{wR} R, IsFiniteLength R X)
    (d : LegalSubobjectDeletionChain.Chain σ)
    (i : Fin (Fintype.card κ + 1)) :
    ObjectProperty (LeftFiniteProjectives Γ) :=
  CategoricalRejective.imageProperty
    (regularHomDualityEquivalence Γ)
    (targetLeftRejectiveTerm σ
      (skeletonAuslanderEquivalence σ) hfinite d i).1.carrier.op

/-- Every dual target term is right rejective.  This is the exact
handedness-conversion needed by the standard-kernel construction. -/
theorem dualTargetRightRejectiveProperty_isRightRejective
    (hfinite : ∀ X : FGModuleCat.{wR} R, IsFiniteLength R X)
    (d : LegalSubobjectDeletionChain.Chain σ)
    (i : Fin (Fintype.card κ + 1)) :
    CategoricalRejective.IsRightRejective
      (dualTargetRightRejectiveProperty σ hfinite d i) := by
  let P := targetLeftRejectiveTerm σ
    (skeletonAuslanderEquivalence σ) hfinite d i
  exact
    CategoricalRejective.Equivalence.isRightRejective_image
      (regularHomDualityEquivalence Γ) P.1.carrier.op
      (CategoricalRejective.isRightRejective_op_of_isLeftRejective P.2)

/-- A surviving label gives an object of the corresponding dual
right-rejective term. -/
theorem leftCoordinateProjective_mem_dualTarget
    (hfinite : ∀ X : FGModuleCat.{wR} R, IsFiniteLength R X)
    (d : LegalSubobjectDeletionChain.Chain σ)
    (i : Fin (Fintype.card κ + 1))
    (j : κ) (hj : j ∈ d.support i) :
    dualTargetRightRejectiveProperty σ hfinite d i
      (leftCoordinateProjective σ j) := by
  let E := regularHomDualityEquivalence Γ
  let P := targetLeftRejectiveTerm σ
    (skeletonAuslanderEquivalence σ) hfinite d i
  have hjP : P.1.carrier (coordinateProjective σ j) := by
    rw [targetLeftRejectiveTerm_subcategory]
    exact coordinateProjective_mem_transportedGenerated
      σ (d.support i) j hj
  change
    P.1.carrier
      (Opposite.unop
        (E.inverse.obj
          (E.functor.obj (Opposite.op (coordinateProjective σ j)))))
  exact P.1.iso_mem (E.unitIso.app
    (Opposite.op (coordinateProjective σ j))).unop.symm hjP

/-- An actual finite biproduct presentation by selected left coordinate
projectives. -/
structure LeftCoordinateAddPresentation
    (T : Set κ) (X : ModuleCat.{wR} Γ) where
  index : FintypeCat.{0}
  label : index → κ
  mem : ∀ t, label t ∈ T
  iso : X ≅
    ⨁ fun t : index ↦ (leftCoordinateProjective σ (label t)).obj

/-- Membership in a dual target term yields a literal finite biproduct
presentation by the surviving left coordinate projectives. -/
def leftCoordinateAddPresentation_of_mem_dualTarget
    (hfinite : ∀ X : FGModuleCat.{wR} R, IsFiniteLength R X)
    (d : LegalSubobjectDeletionChain.Chain σ)
    (i : Fin (Fintype.card κ + 1))
    (X : LeftFiniteProjectives Γ)
    (hX : dualTargetRightRejectiveProperty σ hfinite d i X) :
    LeftCoordinateAddPresentation σ (d.support i) X.obj := by
  let E := regularHomDualityEquivalence Γ
  let PR := AuslanderEquivalence.finiteProjectiveModules Γᵐᵒᵖ
  let PL := AuslanderEquivalence.finiteProjectiveModules Γ
  let Y : skeletonProjectiveTarget σ :=
    Opposite.unop (E.inverse.obj X)
  have hYtarget :
      (targetLeftRejectiveTerm σ
        (skeletonAuslanderEquivalence σ) hfinite d i).1.carrier Y := by
    exact hX
  have hYgenerated :
      (σ.transportedGeneratedSubcategory
        (skeletonAuslanderEquivalence σ) (d.support i)).carrier Y := by
    rw [← targetLeftRejectiveTerm_subcategory σ hfinite
      (skeletonAuslanderEquivalence σ) d i]
    exact hYtarget
  let P := coordinateAddPresentation_of_mem_transportedGenerated
    σ (d.support i) Y hYgenerated
  let F : P.index → skeletonProjectiveTarget σ :=
    fun t ↦ coordinateProjective σ (P.label t)
  let Fop : P.index → (skeletonProjectiveTarget σ)ᵒᵖ :=
    fun t ↦ Opposite.op (F t)
  let FL : P.index → LeftFiniteProjectives Γ :=
    fun t ↦ leftCoordinateProjective σ (P.label t)
  letI : PreservesBiproduct F PR.ι :=
    preservesBiproduct_of_preservesProduct PR.ι
  letI : PreservesBiproduct Fop E.functor :=
    preservesBiproduct_of_preservesProduct E.functor
  letI : PreservesBiproduct FL PL.ι :=
    preservesBiproduct_of_preservesProduct PL.ι
  let eY : Y ≅ ⨁ F :=
    PR.isoMk (P.iso ≪≫ (PR.ι.mapBiproduct F).symm)
  refine {
    index := P.index
    label := P.label
    mem := P.mem
    iso := ?_ }
  exact
    PL.ι.mapIso (E.counitIso.app X).symm ≪≫
      PL.ι.mapIso (E.functor.mapIso eY.op.symm) ≪≫
      PL.ι.mapIso (E.functor.mapIso (opBiproductIso F)) ≪≫
      PL.ι.mapIso (E.functor.mapBiproduct Fop) ≪≫
      PL.ι.mapBiproduct FL

end Coordinate

end QuotientSubmoduleEquidistribution.CPSLeftStandardLayers
