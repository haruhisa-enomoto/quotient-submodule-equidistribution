import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.CategoryTheory.Idempotents.Basic
import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Finiteness.Cardinality
import QuotientSubmoduleEquidistribution.RepresentationTheory.FiniteType

/-!
# The additive-generator form of the Auslander equivalence

This file proves the purely additive categorical statement:
`Hom(G,-)` is fully faithful on the retract closure of finite powers of `G`.
For a module category its target is naturally the category of left modules
over `(End G)ᵐᵒᵖ`, i.e. right modules over `End G`.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open Opposite

namespace QuotientSubmoduleEquidistribution.AuslanderEquivalence

universe v u w

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C]

/-- A witness that `X` belongs to `add G`: it is a retract of a finite
biproduct of copies of `G`. -/
structure FiniteAddPresentation (G X : C) where
  n : ℕ
  retract : Retract X (⨁ fun _ : Fin n => G)

/-- The object property defining `add G`. -/
def finiteAddClosure (G : C) : ObjectProperty C :=
  fun X ↦ Nonempty (FiniteAddPresentation G X)

/-- An object is a finite additive generator when every object is a retract
of a finite biproduct of copies of it. -/
def IsFiniteAddGenerator (G : C) : Prop :=
  ∀ X : C, finiteAddClosure G X

/-- The additive closure of a finite additive generator is all objects. -/
theorem finiteAddClosure_eq_top
    (G : C) (hG : IsFiniteAddGenerator G) :
    finiteAddClosure G = ⊤ := by
  funext X
  apply propext
  exact ⟨fun _ ↦ trivial, fun _ ↦ hG X⟩

/-- Replacing the chosen generator by an isomorphic object does not change
its finite additive closure. -/
def FiniteAddPresentation.replaceGenerator
    {G H X : C} (e : G ≅ H)
    (P : FiniteAddPresentation G X) :
    FiniteAddPresentation H X where
  n := P.n
  retract :=
    P.retract.trans
      (Retract.ofIso
        (biproduct.mapIso fun _ : Fin P.n ↦ e))

/-- Membership in a finite additive closure is invariant under replacing
the generator by an isomorphic object. -/
theorem finiteAddClosure_iff_of_iso
    {G H X : C} (e : G ≅ H) :
    finiteAddClosure G X ↔ finiteAddClosure H X :=
  ⟨fun ⟨P⟩ ↦
      ⟨P.replaceGenerator e⟩,
    fun ⟨P⟩ ↦
      ⟨P.replaceGenerator e.symm⟩⟩

/-- The representable module functor on `add G`.  Since Mathlib module
categories are left-module categories, this is a functor to left modules
over `(End G)ᵐᵒᵖ`, equivalently right modules over `End G`. -/
def homFromGenerator (G : C) :
    (finiteAddClosure G).FullSubcategory ⥤
      ModuleCat.{v} (End G)ᵐᵒᵖ :=
  (finiteAddClosure G).ι ⋙ preadditiveCoyonedaObj G

omit [HasFiniteBiproducts C] in
private theorem linear_map_comp
    {G X Y : C}
    (α :
      ModuleCat.of (End G)ᵐᵒᵖ (G ⟶ X) ⟶
        ModuleCat.of (End G)ᵐᵒᵖ (G ⟶ Y))
    (e : End G) (k : G ⟶ X) :
    α.hom (e ≫ k) = e ≫ α.hom k := by
  change
    α.hom (MulOpposite.op e • k) =
      MulOpposite.op e • α.hom k
  exact α.hom.map_smul (MulOpposite.op e) k

/-- The representable module functor is full on `add G`. -/
instance homFromGenerator_full (G : C) :
    (homFromGenerator G).Full where
  map_surjective {X Y} α := by
    change
      ModuleCat.of (End G)ᵐᵒᵖ (G ⟶ X.obj) ⟶
        ModuleCat.of (End G)ᵐᵒᵖ (G ⟶ Y.obj) at α
    let P := X.property.some
    let q : (⨁ fun _ : Fin P.n => G) ⟶ Y.obj :=
      biproduct.desc fun j ↦
        α.hom (biproduct.ι (fun _ : Fin P.n => G) j ≫ P.retract.r)
    let f : X.obj ⟶ Y.obj := P.retract.i ≫ q
    refine ⟨ObjectProperty.homMk f, ?_⟩
    apply ModuleCat.hom_ext
    ext h
    let h' : G ⟶ X.obj := h
    change
      h' ≫ f = α.hom h'
    dsimp only [f, q]
    rw [← Category.assoc, biproduct.desc_eq,
      Preadditive.comp_sum]
    simp_rw [← Category.assoc]
    simp_rw [← linear_map_comp α]
    rw [← map_sum]
    congr 1
    have ht :=
      congrArg
        (fun t ↦ h' ≫ P.retract.i ≫ t ≫
          P.retract.r)
        (biproduct.total
          (f := fun _ : Fin P.n => G))
    calc
      _ =
          h' ≫ P.retract.i ≫
            𝟙 (⨁ fun _ : Fin P.n => G) ≫
              P.retract.r := by
        simpa only [Preadditive.comp_sum,
          Preadditive.sum_comp, Category.assoc]
          using ht
      _ = h' := by simp

/-- The representable module functor is faithful on `add G`. -/
instance homFromGenerator_faithful (G : C) :
    (homFromGenerator G).Faithful where
  map_injective {X Y} f g hfg := by
    change
      (preadditiveCoyonedaObj G).map f.hom =
        (preadditiveCoyonedaObj G).map g.hom at hfg
    let P := X.property.some
    apply ObjectProperty.hom_ext
    apply (cancel_epi P.retract.r).1
    apply biproduct.hom_ext'
    intro j
    have h :=
      congrArg
        (fun k ↦
          k.hom
            (biproduct.ι (fun _ : Fin P.n => G) j ≫
              P.retract.r))
        hfg
    dsimp [preadditiveCoyonedaObj] at h
    convert h using 1 <;>
      exact (Category.assoc _ _ _).symm

/-- The bundled fully faithful form. -/
def homFromGeneratorFullyFaithful (G : C) :
    (homFromGenerator G).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful
    (homFromGenerator G)

/-- The regular left `(End G)ᵐᵒᵖ`-module is the representable module
`Hom(G,G)`. -/
def regularLinearEquiv (G : C) :
    (End G)ᵐᵒᵖ ≃ₗ[(End G)ᵐᵒᵖ] (G ⟶ G) where
  toFun := MulOpposite.unop
  invFun := MulOpposite.op
  left_inv := MulOpposite.op_unop
  right_inv := MulOpposite.unop_op
  map_add' := fun _ _ ↦ rfl
  map_smul' := fun _ _ ↦ rfl

omit [HasFiniteBiproducts C] in
/-- `Hom(G,G)` is a projective module over `(End G)ᵐᵒᵖ`. -/
theorem homSelf_projective (G : C) :
    Projective ((preadditiveCoyonedaObj G).obj G) := by
  let S := (End G)ᵐᵒᵖ
  have hregular :
      Projective (ModuleCat.of S S) :=
    ModuleCat.projective_of_free
      (Module.Basis.singleton Unit S)
  exact Projective.of_iso
    (regularLinearEquiv G).toModuleIso hregular

/-- Every representable module coming from `add G` is projective. -/
theorem homFromGenerator_obj_projective
    (G : C)
    (X : (finiteAddClosure G).FullSubcategory) :
    Projective ((homFromGenerator G).obj X) := by
  let P := X.property.some
  let F := preadditiveCoyonedaObj G
  have targetProjective :
      Projective
        (⨁ fun _ : Fin P.n => F.obj G) := by
    classical
    refine ⟨fun {E Y} f e _ ↦ ?_⟩
    choose lift hlift using
      fun j ↦
        (homSelf_projective G).factors
          (biproduct.ι
            (fun _ : Fin P.n => F.obj G) j ≫ f) e
    refine ⟨biproduct.desc lift, ?_⟩
    apply biproduct.hom_ext'
    intro j
    simpa only [biproduct.ι_desc_assoc]
      using hlift j
  have sourceProjective :
      Projective
        (F.obj (⨁ fun _ : Fin P.n => G)) :=
    Projective.of_iso
      (F.mapBiproduct
        (fun _ : Fin P.n => G)).symm
      targetProjective
  letI :
      Projective
        (F.obj (⨁ fun _ : Fin P.n => G)) :=
    sourceProjective
  exact (P.retract.map F).projective

/-- The image of an object in `add G` lies in the additive retract closure
of the regular representable module. -/
def homFromGenerator_obj_finiteAddPresentation
    (G : C)
    (X : (finiteAddClosure G).FullSubcategory) :
    FiniteAddPresentation
      ((preadditiveCoyonedaObj G).obj G)
      ((homFromGenerator G).obj X) := by
  let P := X.property.some
  let F := preadditiveCoyonedaObj G
  exact
    { n := P.n
      retract :=
        (P.retract.map F).trans
          (Retract.ofIso
            (F.mapBiproduct
              (fun _ : Fin P.n => G))) }

/-- `Hom(G,-)` with both source and target restricted to additive
retract closures. -/
def homFromGeneratorToAdd (G : C) :
    (finiteAddClosure G).FullSubcategory ⥤
      (finiteAddClosure
        ((preadditiveCoyonedaObj G).obj G)).FullSubcategory :=
  (finiteAddClosure
    ((preadditiveCoyonedaObj G).obj G)).lift
      (homFromGenerator G)
      (fun X ↦
        ⟨homFromGenerator_obj_finiteAddPresentation G X⟩)

/-- The restricted-to-`add` functor remains fully faithful. -/
def homFromGeneratorToAddFullyFaithful (G : C) :
    (homFromGeneratorToAdd G).FullyFaithful :=
  by
    unfold homFromGeneratorToAdd
    exact Functor.FullyFaithful.ofFullyFaithful _

/-- If the source category is idempotent complete, every object in the
additive retract closure of the regular representable module comes from
`add G`. -/
theorem homFromGeneratorToAdd_essSurj
    [IsIdempotentComplete C] (G : C) :
    (homFromGeneratorToAdd G).EssSurj := by
  refine ⟨fun Y ↦ ?_⟩
  let Q := Y.property.some
  let F := preadditiveCoyonedaObj G
  let A : C := ⨁ fun _ : Fin Q.n => G
  let φ :
      F.obj A ≅
        ⨁ fun _ : Fin Q.n => F.obj G :=
    F.mapBiproduct (fun _ : Fin Q.n => G)
  let r :
      Retract Y.obj (F.obj A) :=
    Q.retract.trans (Retract.ofIso φ.symm)
  let A' :
      (finiteAddClosure G).FullSubcategory :=
    ⟨A, ⟨{
      n := Q.n
      retract := Retract.refl A }⟩⟩
  let p : F.obj A ⟶ F.obj A :=
    r.r ≫ r.i
  have hp : p ≫ p = p := by
    dsimp only [p]
    simp [Category.assoc]
  let FF := homFromGeneratorFullyFaithful G
  let p' :
      (homFromGenerator G).obj A' ⟶
        (homFromGenerator G).obj A' :=
    p
  let a : A' ⟶ A' := FF.preimage p'
  have hmapa :
      (homFromGenerator G).map a = p' :=
    FF.map_preimage p'
  have ha : a ≫ a = a := by
    apply (homFromGenerator G).map_injective
    rw [Functor.map_comp, hmapa]
    change p ≫ p = p
    exact hp
  have ha0 : a.hom ≫ a.hom = a.hom :=
    congrArg (fun k ↦ k.hom) ha
  rcases
      IsIdempotentComplete.idempotents_split
        A a.hom ha0 with
    ⟨Z, i, e, hie, hei⟩
  let X :
      (finiteAddClosure G).FullSubcategory :=
    ⟨Z, ⟨{
      n := Q.n
      retract :=
        { i := i
          r := e
          retract := hie } }⟩⟩
  have hmapa0 : F.map a.hom = p := by
    change F.map a.hom = p at hmapa
    exact hmapa
  let isoAmbient : F.obj Z ≅ Y.obj :=
    { hom := F.map i ≫ r.r
      inv := r.i ≫ F.map e
      hom_inv_id := by
        calc
          (F.map i ≫ r.r) ≫
                (r.i ≫ F.map e) =
              F.map i ≫ (r.r ≫ r.i) ≫
                F.map e := by simp only [Category.assoc]
          _ = F.map i ≫ F.map a.hom ≫
                F.map e := by
              dsimp only [p] at hmapa0
              rw [hmapa0]
          _ = 𝟙 _ := by
              rw [← F.map_comp, ← F.map_comp,
                ← hei]
              simp [Category.assoc, hie]
      inv_hom_id := by
        calc
          (r.i ≫ F.map e) ≫
                (F.map i ≫ r.r) =
              r.i ≫ F.map (e ≫ i) ≫
                r.r := by
              simp only [Category.assoc,
                F.map_comp]
          _ = r.i ≫ F.map a.hom ≫
                r.r := by rw [hei]
          _ = r.i ≫ (r.r ≫ r.i) ≫
                r.r := by
              dsimp only [p] at hmapa0
              rw [hmapa0]
          _ = 𝟙 _ := by
              simp [Category.assoc] }
  exact
    ⟨X, ⟨ObjectProperty.isoMk _ isoAmbient⟩⟩

/-- The purely additive Auslander equivalence: the idempotent-complete
additive closure of `G` is equivalent to the additive closure of its regular
representable module. -/
def additiveAuslanderEquivalence
    [IsIdempotentComplete C] (G : C) :
    (finiteAddClosure G).FullSubcategory ≌
      (finiteAddClosure
        ((preadditiveCoyonedaObj G).obj G)).FullSubcategory := by
  letI :
      (homFromGeneratorToAdd G).IsEquivalence :=
    Functor.IsEquivalence.mk
      (homFromGeneratorToAddFullyFaithful G).faithful
      (homFromGeneratorToAddFullyFaithful G).full
      (homFromGeneratorToAdd_essSurj G)
  exact (homFromGeneratorToAdd G).asEquivalence

/-- The usual object property of finitely generated projective modules. -/
def finiteProjectiveModules
    (S : Type v) [Ring S] :
    ObjectProperty (ModuleCat.{v} S) :=
  fun M ↦ Module.Finite S M ∧ Projective M

/-- Over a ring, the additive retract closure of the regular module is
exactly the class of finitely generated projective modules. -/
theorem finiteAddClosure_regular_iff
    (S : Type v) [Ring S] (M : ModuleCat.{v} S) :
    finiteAddClosure (ModuleCat.of S S) M ↔
      finiteProjectiveModules S M := by
  constructor
  · rintro ⟨P⟩
    have hBfinite :
        Module.Finite S
          (⨁ fun _ : Fin P.n ↦ ModuleCat.of S S :
            ModuleCat.{v} S) := by
      have hPi :
          Module.Finite S (∀ _ : Fin P.n, S) :=
        inferInstance
      exact
        (Module.Finite.equiv_iff
          (ModuleCat.biproductIsoPi
            (fun _ : Fin P.n ↦
              ModuleCat.of S S)).toLinearEquiv).mpr hPi
    have hMfinite : Module.Finite S M := by
      letI :
          Module.Finite S
            (⨁ fun _ : Fin P.n ↦ ModuleCat.of S S :
              ModuleCat.{v} S) :=
        hBfinite
      exact
        Module.Finite.of_surjective
          P.retract.r.hom
          (fun x ↦
            ⟨P.retract.i.hom x, by
              change
                (P.retract.i ≫ P.retract.r).hom x =
                  x
              rw [P.retract.retract]
              rfl⟩)
    have hRegularProjective :
        Projective (ModuleCat.of S S) :=
      ModuleCat.projective_of_free
        (Module.Basis.singleton Unit S)
    have hBprojective :
        Projective
          (⨁ fun _ : Fin P.n ↦ ModuleCat.of S S :
            ModuleCat.{v} S) := by
      classical
      refine ⟨fun {E Y} f e _ ↦ ?_⟩
      choose lift hlift using
        fun j ↦
          hRegularProjective.factors
            (biproduct.ι
              (fun _ : Fin P.n ↦
                ModuleCat.of S S) j ≫ f) e
      refine ⟨biproduct.desc lift, ?_⟩
      apply biproduct.hom_ext'
      intro j
      simpa only [biproduct.ι_desc_assoc]
        using hlift j
    letI :
        Projective
          (⨁ fun _ : Fin P.n ↦ ModuleCat.of S S :
            ModuleCat.{v} S) :=
      hBprojective
    exact ⟨hMfinite, P.retract.projective⟩
  · rintro ⟨hMfinite, hMprojective⟩
    letI : Module.Finite S M := hMfinite
    letI : Projective M := hMprojective
    obtain ⟨n, p, hp⟩ :=
      Module.Finite.exists_fin' S M
    let e :
        ModuleCat.of S (Fin n → S) ⟶ M :=
      ModuleCat.ofHom p
    haveI : Epi e := by
      exact
        (ModuleCat.epi_iff_surjective e).mpr hp
    obtain ⟨i, hi⟩ :=
      Projective.factors (𝟙 M) e
    let rFree :
        Retract M (ModuleCat.of S (Fin n → S)) :=
      { i := i
        r := e
        retract := hi }
    let φ :
        (⨁ fun _ : Fin n ↦ ModuleCat.of S S :
          ModuleCat.{v} S) ≅
          ModuleCat.of S (Fin n → S) :=
      ModuleCat.biproductIsoPi
        (fun _ : Fin n ↦ ModuleCat.of S S)
    exact
      ⟨{
        n := n
        retract :=
          rFree.trans (Retract.ofIso φ.symm) }⟩

/-- The additive closure of the regular module, as an equality of object
properties, is the conventional finitely generated projective locus. -/
theorem finiteAddClosure_regular_eq_finiteProjective
    (S : Type v) [Ring S] :
    finiteAddClosure (ModuleCat.of S S) =
      finiteProjectiveModules S := by
  funext M
  exact propext (finiteAddClosure_regular_iff S M)

omit [HasFiniteBiproducts C] in
/-- The additive closure of `Hom(G,G)` consists exactly of the finitely
generated projective modules over `(End G)ᵐᵒᵖ`. -/
theorem finiteAddClosure_homSelf_eq_finiteProjective
    (G : C) :
    finiteAddClosure
        ((preadditiveCoyonedaObj G).obj G) =
      finiteProjectiveModules (End G)ᵐᵒᵖ := by
  funext M
  apply propext
  exact
    (finiteAddClosure_iff_of_iso
      ((regularLinearEquiv G).toModuleIso.symm :
        (preadditiveCoyonedaObj G).obj G ≅
          ModuleCat.of (End G)ᵐᵒᵖ
            (End G)ᵐᵒᵖ)).trans
      (finiteAddClosure_regular_iff
        (End G)ᵐᵒᵖ M)

/-- `Hom(G,-)` with source restricted to `add G` and codomain restricted
to the conventional finitely generated projective modules. -/
def homFromGeneratorToProjectives (G : C) :
    (finiteAddClosure G).FullSubcategory ⥤
      (finiteProjectiveModules
        (End G)ᵐᵒᵖ).FullSubcategory :=
  homFromGeneratorToAdd G ⋙
    (ObjectProperty.fullSubcategoryCongr
      (finiteAddClosure_homSelf_eq_finiteProjective G)).functor

/-- The projective-target restriction of `Hom(G,-)` is fully faithful. -/
def homFromGeneratorToProjectivesFullyFaithful
    (G : C) :
    (homFromGeneratorToProjectives G).FullyFaithful :=
  (homFromGeneratorToAddFullyFaithful G).comp
    (ObjectProperty.fullSubcategoryCongr
      (finiteAddClosure_homSelf_eq_finiteProjective G)).fullyFaithfulFunctor

/-- The precise additive Auslander equivalence with the conventional
finitely generated projective target. -/
def auslanderEquivalence
    [IsIdempotentComplete C] (G : C) :
    (finiteAddClosure G).FullSubcategory ≌
      (finiteProjectiveModules
        (End G)ᵐᵒᵖ).FullSubcategory :=
  (additiveAuslanderEquivalence G).trans
    (ObjectProperty.fullSubcategoryCongr
      (finiteAddClosure_homSelf_eq_finiteProjective G))

/-- The functor underlying `auslanderEquivalence` is the restricted
representable functor just defined. -/
theorem auslanderEquivalence_functor
    [IsIdempotentComplete C] (G : C) :
    (auslanderEquivalence G).functor =
      homFromGeneratorToProjectives G :=
  rfl

/-- If `G` generates the whole category, the additive Auslander equivalence
has the ambient category itself as source. -/
def finiteAddGeneratorAuslanderEquivalence
    [IsIdempotentComplete C]
    (G : C) (hG : IsFiniteAddGenerator G) :
    C ≌
      (finiteProjectiveModules
        (End G)ᵐᵒᵖ).FullSubcategory :=
  (ObjectProperty.topEquivalence C).symm |>.trans
    (ObjectProperty.fullSubcategoryCongr
      (finiteAddClosure_eq_top G hG).symm) |>.trans
    (auslanderEquivalence G)

namespace FiniteTypeGenerator

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- In finite representation type, the direct sum of one copy of each
chosen indecomposable is the standard additive generator. -/
noncomputable abbrev additiveGenerator [Finite ι] :
    FGModuleCat.{w} R :=
  ⨁ σ.obj

/-- Completeness and decomposition of a finite indecomposable skeleton
make its standard direct sum a finite additive generator. -/
theorem additiveGenerator_isFiniteAddGenerator
    [Finite ι] :
    IsFiniteAddGenerator (additiveGenerator σ) := by
  classical
  intro X
  obtain ⟨n, a, ⟨e⟩⟩ := σ.decomposes X
  let summandRetract (t : Fin n) :
      Retract (σ.obj (a t)) (additiveGenerator σ) :=
    { i := biproduct.ι σ.obj (a t)
      r := biproduct.π σ.obj (a t)
      retract := by simp }
  let sumRetract :
      Retract
        (⨁ fun t : Fin n ↦ σ.obj (a t))
        (⨁ fun _ : Fin n ↦ additiveGenerator σ) :=
    { i := biproduct.map fun t ↦
        (summandRetract t).i
      r := biproduct.map fun t ↦
        (summandRetract t).r
      retract := by
        apply biproduct.hom_ext'
        intro t
        simp [summandRetract] }
  exact
    ⟨{
      n := n
      retract :=
        (Retract.ofIso e).trans sumRetract }⟩

/-- The Auslander equivalence attached to a finite complete
indecomposable skeleton. -/
noncomputable def auslanderEquivalence
    [Finite ι] :
    FGModuleCat.{w} R ≌
      (finiteProjectiveModules
        (End (additiveGenerator σ))ᵐᵒᵖ).FullSubcategory :=
  finiteAddGeneratorAuslanderEquivalence
    (additiveGenerator σ)
    (additiveGenerator_isFiniteAddGenerator σ)

end FiniteTypeGenerator

section FGModuleCat

variable {R : Type v} [Ring R] [IsNoetherianRing R]

local instance :
    HasFiniteBiproducts (FGModuleCat.{v} R) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- The specialization to finitely generated modules over a left-Noetherian
ring.  In particular this applies to modules over an Artin algebra. -/
def fgModuleAddAuslanderEquivalence
    (G : FGModuleCat.{v} R) :
    (finiteAddClosure G).FullSubcategory ≌
      (finiteProjectiveModules
        (End G)ᵐᵒᵖ).FullSubcategory :=
  auslanderEquivalence G

/-- When `G` is a finite additive generator, `Hom_R(G,-)` identifies the
whole finitely generated module category with finitely generated projective
right `End(G)`-modules. -/
def fgModuleGeneratorAuslanderEquivalence
    (G : FGModuleCat.{v} R)
    (hG : IsFiniteAddGenerator G) :
    FGModuleCat.{v} R ≌
      (finiteProjectiveModules
        (End G)ᵐᵒᵖ).FullSubcategory :=
  finiteAddGeneratorAuslanderEquivalence G hG

end FGModuleCat

end QuotientSubmoduleEquidistribution.AuslanderEquivalence
