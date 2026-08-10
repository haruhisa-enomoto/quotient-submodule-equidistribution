import OpConjecture.RepresentationTheory.RingelStableCounting
import OpConjecture.RepresentationTheory.LeftCoordinateProjectiveDuality
import OpConjecture.RepresentationTheory.ContragredientDuality

/-!
# The projective--injective boundary pairing

This constructs the projective part of Ringel's Corollary 1 from the
maintained Hom duality on finite projectives and finite-dimensional
contragredient duality.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Set

namespace OpConjecture.RingelStable

universe u v

variable {R : Type u} [Ring R] [IsNoetherianRing R]

/-- Categorical projectives among finitely generated modules. -/
def fgProjectiveProperty :
    ObjectProperty (FGModuleCat.{u} R) :=
  fun X ↦ Projective X

/-- Categorical injectives among finitely generated modules. -/
def fgInjectiveProperty :
    ObjectProperty (FGModuleCat.{u} R) :=
  fun X ↦ Injective X

instance fgInjectiveProperty_isoClosed :
    (fgInjectiveProperty (R := R)).IsClosedUnderIsomorphisms where
  of_iso e h := CategoryTheory.Injective.of_iso e h

abbrev FGProjectives :=
  (fgProjectiveProperty (R := R)).FullSubcategory

abbrev FGInjectives :=
  (fgInjectiveProperty (R := R)).FullSubcategory

omit [IsNoetherianRing R] in
/-- A categorical projective in `FGModuleCat` is projective as an
unbundled module.  The proof splits one finite free presentation. -/
theorem moduleProjective_of_fgProjective
    (X : FGModuleCat.{u} R) (h : Projective X) :
    Module.Projective R X := by
  classical
  letI : Projective X := h
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R X
  let F : FGModuleCat.{u} R := FGModuleCat.of R (Fin n → R)
  let q : F ⟶ X := FGModuleCat.ofHom p
  haveI : Epi q :=
    (OpConjecture.IndecomposableSkeleton.fg_epi_iff_surjective q).2 hp
  obtain ⟨s, hs⟩ := Projective.factors (CategoryStruct.id X) q
  letI : Module.Projective R F :=
    Module.Projective.of_basis (Pi.basisFun R (Fin n))
  apply Module.Projective.of_split s.hom.hom q.hom.hom
  exact congrArg (fun f : X ⟶ X ↦ f.hom.hom) hs

omit [IsNoetherianRing R] in
/-- Conversely, module projectivity gives categorical projectivity in the
finitely generated subcategory. -/
theorem fgProjective_of_moduleProjective
    (X : FGModuleCat.{u} R) (h : Module.Projective R X) :
    Projective X := by
  letI : Module.Projective R X := h
  constructor
  intro E Y f e _
  obtain ⟨g, hg⟩ :=
    Module.projective_lifting_property
      e.hom.hom f.hom.hom
      ((OpConjecture.IndecomposableSkeleton.fg_epi_iff_surjective e).1
        inferInstance)
  refine ⟨FGModuleCat.ofHom g, ?_⟩
  apply FGModuleCat.hom_ext
  exact hg

abbrev LeftFiniteProjectives :=
  OpConjecture.CPSLeftStandardLayers.LeftFiniteProjectives R

/-- Rebundle an `FGModuleCat` projective as a finite projective in the
ambient `ModuleCat`. -/
def fgProjectivesToFiniteProjectives :
    FGProjectives (R := R) ⥤ LeftFiniteProjectives (R := R) := by
  exact
    { obj := fun X ↦
        ⟨X.obj.obj, X.obj.property, by
          letI : Module.Projective R X.obj :=
            moduleProjective_of_fgProjective X.obj X.property
          exact ModuleCat.projective_of_categoryTheory_projective X.obj.obj⟩
      map := fun f ↦ ObjectProperty.homMk f.hom.hom
      map_id := fun _ ↦ rfl
      map_comp := fun _ _ ↦ rfl }

/-- Rebundle a finite projective ambient module as a categorical
projective in `FGModuleCat`. -/
def finiteProjectivesToFGProjectives :
    LeftFiniteProjectives (R := R) ⥤ FGProjectives (R := R) := by
  exact
    { obj := fun X ↦
        ⟨⟨X.obj, X.property.1⟩,
          fgProjective_of_moduleProjective
            ⟨X.obj, X.property.1⟩
            ((IsProjective.iff_projective X.obj).2 X.property.2)⟩
      map := fun f ↦
        ObjectProperty.homMk (ObjectProperty.homMk f.hom)
      map_id := fun _ ↦ rfl
      map_comp := fun _ _ ↦ rfl }

/-- The two re-bundlings are inverse equivalences. -/
def fgProjectivesEquivFiniteProjectives :
    FGProjectives (R := R) ≌ LeftFiniteProjectives (R := R) where
  functor := fgProjectivesToFiniteProjectives (R := R)
  inverse := finiteProjectivesToFGProjectives (R := R)
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- The maintained Hom duality, rebundled as an anti-equivalence between
finitely generated projectives on the two module sides. -/
def fgProjectiveHomDuality [IsNoetherianRing Rᵐᵒᵖ] :
    (FGProjectives (R := R))ᵒᵖ ≌ FGProjectives (R := Rᵐᵒᵖ) :=
  (fgProjectivesEquivFiniteProjectives (R := R)).op |>.trans
    ((OpConjecture.CPSLeftStandardLayers.regularHomDualityEquivalence R).rightOp.symm) |>.trans
      (fgProjectivesEquivFiniteProjectives (R := Rᵐᵒᵖ)).symm

section Contragredient

variable [IsNoetherianRing Rᵐᵒᵖ]
  (K : Type u) [Field K] [Algebra K R] [FiniteDimensional K R]

omit [IsNoetherianRing R] [IsNoetherianRing Rᵐᵒᵖ] in
private theorem reverseDual_injective_inverseImage :
    (fgInjectiveProperty (R := R)).inverseImage
        (OpConjecture.Contragredient.reverseDualityEquivalence K R).functor =
      (fgProjectiveProperty (R := Rᵐᵒᵖ)).op := by
  funext X
  apply propext
  induction X with
  | op X =>
      exact
        ((OpConjecture.Contragredient.reverseDualityEquivalence K R).map_injective_iff
          (Opposite.op X)).trans
          (CategoryTheory.Injective.projective_iff_injective_op.symm)

/-- Contragredient duality restricted from projective right modules to
injective left modules. -/
def reverseDualProjectiveInjectiveEquivalence :
    (FGProjectives (R := Rᵐᵒᵖ))ᵒᵖ ≌ FGInjectives (R := R) :=
  (ObjectProperty.opEquivalence
      (fgProjectiveProperty (R := Rᵐᵒᵖ))).symm |>.trans
    ((OpConjecture.Contragredient.reverseDualityEquivalence K R).congrFullSubcategory
      (reverseDual_injective_inverseImage (R := R) K))

/-- The finite-projective Hom dual followed by `K`-duality gives the
Nakayama equivalence from indecomposable projectives to
indecomposable injectives. -/
def projectiveInjectiveEquivalence :
    FGProjectives (R := R) ≌ FGInjectives (R := R) :=
  (fgProjectiveHomDuality (R := R)).rightOp.trans
    (reverseDualProjectiveInjectiveEquivalence (R := R) K)

omit [IsNoetherianRing R] [IsNoetherianRing Rᵐᵒᵖ] in
/-- An equivalence between full subcategories of `FGModuleCat` preserves
the concrete module-level indecomposability predicate. -/
theorem indecomposable_map_fgFullSubcategory
    (P Q : ObjectProperty (FGModuleCat.{u} R))
    (E : P.FullSubcategory ≌ Q.FullSubcategory)
    {M : P.FullSubcategory}
    (hM : OpConjecture.Foundation.IsIndecomposableModule R M.obj) :
    OpConjecture.Foundation.IsIndecomposableModule R (E.functor.obj M).obj := by
  rw [OpConjecture.Foundation.isIndecomposableModule_iff_nontrivial_and_forall_isIdempotentElem]
  constructor
  · by_contra h
    letI : Subsingleton (E.functor.obj M).obj :=
      not_nontrivial_iff_subsingleton.mp h
    have htarget :
        (CategoryStruct.id (E.functor.obj M) :
          E.functor.obj M ⟶ E.functor.obj M) = 0 := by
      apply ObjectProperty.hom_ext
      apply FGModuleCat.hom_ext
      ext x
      exact Subsingleton.elim _ _
    have hsource :
        (CategoryStruct.id M : M ⟶ M) = 0 := by
      apply E.functor.map_injective
      simpa using htarget
    letI : Nontrivial M.obj := hM.nontrivial
    have hend : (1 : Module.End R M.obj) = 0 := by
      have hlinear :=
        congrArg (fun f : M ⟶ M ↦ f.hom.hom.hom) hsource
      simpa [Module.End.one_eq_id] using hlinear
    exact one_ne_zero hend
  · intro f hf
    let fcat :
        E.functor.obj M ⟶ E.functor.obj M :=
      ObjectProperty.homMk (FGModuleCat.ofHom f)
    have fcat_apply (x : (E.functor.obj M).obj) :
        fcat.hom.hom.hom x = f x :=
      rfl
    let gcat : M ⟶ M := E.functor.preimage fcat
    let g : Module.End R M.obj := gcat.hom.hom.hom
    have hcat : gcat ≫ gcat = gcat := by
      apply E.functor.map_injective
      rw [E.functor.map_comp]
      change
        E.functor.map (E.functor.preimage fcat) ≫
            E.functor.map (E.functor.preimage fcat) =
          E.functor.map (E.functor.preimage fcat)
      rw [E.functor.map_preimage fcat]
      apply ObjectProperty.hom_ext
      apply FGModuleCat.hom_ext
      change f.comp f = f
      change f * f = f at hf
      simpa [Module.End.mul_eq_comp] using hf
    have hg : IsIdempotentElem g := by
      change g * g = g
      have hlinear :=
        congrArg (fun q : M ⟶ M ↦ q.hom.hom.hom) hcat
      simpa [g, Module.End.mul_eq_comp] using hlinear
    rcases hM.eq_zero_or_eq_one_of_isIdempotentElem hg with hg | hg
    · left
      have hgcat : gcat = 0 := by
        apply ObjectProperty.hom_ext
        apply FGModuleCat.hom_ext
        exact hg
      have hfcat : fcat = 0 := by
        calc
          fcat = E.functor.map gcat :=
            (E.functor.map_preimage fcat).symm
          _ = E.functor.map 0 := congrArg E.functor.map hgcat
          _ = 0 := E.functor.map_zero M M
      ext x
      have hx := congrArg
        (fun q : E.functor.obj M ⟶ E.functor.obj M ↦
          q.hom.hom.hom x) hfcat
      rw [fcat_apply] at hx
      simpa using hx
    · right
      have hgcat : gcat = CategoryStruct.id M := by
        apply ObjectProperty.hom_ext
        apply FGModuleCat.hom_ext
        simpa [g, Module.End.one_eq_id] using hg
      have hfcat :
          fcat = CategoryStruct.id (E.functor.obj M) := by
        calc
          fcat = E.functor.map gcat :=
            (E.functor.map_preimage fcat).symm
          _ = E.functor.map (CategoryStruct.id M) :=
            congrArg E.functor.map hgcat
          _ = CategoryStruct.id (E.functor.obj M) :=
            E.functor.map_id M
      ext x
      have hx := congrArg
        (fun q : E.functor.obj M ⟶ E.functor.obj M ↦
          q.hom.hom.hom x) hfcat
      rw [fcat_apply] at hx
      simpa [Module.End.one_eq_id] using hx

section SkeletonBoundary

variable {iota : Type v}
  (sigma : OpConjecture.IndecomposableSkeleton.{u, v, u} R iota)

abbrev BoundaryEquivalence :=
  projectiveInjectiveEquivalence (R := R) K

/-- Bundle a projective skeleton label in the projective full
subcategory. -/
def projectiveLabelObject
    (i : {i // i ∈ projectiveSet sigma}) :
    FGProjectives (R := R) :=
  ⟨sigma.obj i.1, i.2⟩

/-- Bundle an injective skeleton label in the injective full
subcategory. -/
def injectiveLabelObject
    (i : {i // i ∈ injectiveSet sigma}) :
    FGInjectives (R := R) :=
  ⟨sigma.obj i.1, i.2⟩

private theorem projectiveBoundaryImage_indec
    (i : {i // i ∈ projectiveSet sigma}) :
    OpConjecture.Foundation.IsIndecomposableModule R
      ((BoundaryEquivalence (R := R) K).functor.obj
        (projectiveLabelObject sigma i)).obj :=
  indecomposable_map_fgFullSubcategory
    (fgProjectiveProperty (R := R))
    (fgInjectiveProperty (R := R))
    (BoundaryEquivalence (R := R) K)
    (sigma.indecomposable i.1)

private theorem injectiveBoundaryPreimage_indec
    (i : {i // i ∈ injectiveSet sigma}) :
    OpConjecture.Foundation.IsIndecomposableModule R
      ((BoundaryEquivalence (R := R) K).inverse.obj
        (injectiveLabelObject sigma i)).obj :=
  indecomposable_map_fgFullSubcategory
    (fgInjectiveProperty (R := R))
    (fgProjectiveProperty (R := R))
    (BoundaryEquivalence (R := R) K).symm
    (sigma.indecomposable i.1)

/-- The chosen skeleton label of the Nakayama image of a projective
label. -/
def projectiveToInjectiveLabel
    (i : {i // i ∈ projectiveSet sigma}) : iota :=
  Classical.choose
    (sigma.complete
      ((BoundaryEquivalence (R := R) K).functor.obj
        (projectiveLabelObject sigma i)).obj
      (projectiveBoundaryImage_indec (R := R) K sigma i))

/-- The chosen representative is isomorphic to the Nakayama image. -/
def projectiveToInjectiveObjIso
    (i : {i // i ∈ projectiveSet sigma}) :
    ((BoundaryEquivalence (R := R) K).functor.obj
      (projectiveLabelObject sigma i)).obj ≅
        sigma.obj (projectiveToInjectiveLabel (R := R) K sigma i) :=
  Classical.choice
    (Classical.choose_spec
      (sigma.complete
        ((BoundaryEquivalence (R := R) K).functor.obj
          (projectiveLabelObject sigma i)).obj
        (projectiveBoundaryImage_indec (R := R) K sigma i)))

/-- The projective-to-injective map on chosen labels. -/
def projectiveToInjective
    (i : {i // i ∈ projectiveSet sigma}) :
    {i // i ∈ injectiveSet sigma} :=
  ⟨projectiveToInjectiveLabel (R := R) K sigma i, by
    exact
      (CategoryTheory.Injective.iso_iff
        (projectiveToInjectiveObjIso (R := R) K sigma i)).1
        ((BoundaryEquivalence (R := R) K).functor.obj
          (projectiveLabelObject sigma i)).property⟩

/-- The chosen skeleton label of the inverse Nakayama image of an
injective label. -/
def injectiveToProjectiveLabel
    (i : {i // i ∈ injectiveSet sigma}) : iota :=
  Classical.choose
    (sigma.complete
      ((BoundaryEquivalence (R := R) K).inverse.obj
        (injectiveLabelObject sigma i)).obj
      (injectiveBoundaryPreimage_indec (R := R) K sigma i))

/-- The chosen representative is isomorphic to the inverse Nakayama
image. -/
def injectiveToProjectiveObjIso
    (i : {i // i ∈ injectiveSet sigma}) :
    ((BoundaryEquivalence (R := R) K).inverse.obj
      (injectiveLabelObject sigma i)).obj ≅
        sigma.obj (injectiveToProjectiveLabel (R := R) K sigma i) :=
  Classical.choice
    (Classical.choose_spec
      (sigma.complete
        ((BoundaryEquivalence (R := R) K).inverse.obj
          (injectiveLabelObject sigma i)).obj
        (injectiveBoundaryPreimage_indec (R := R) K sigma i)))

/-- The injective-to-projective map on chosen labels. -/
def injectiveToProjective
    (i : {i // i ∈ injectiveSet sigma}) :
    {i // i ∈ projectiveSet sigma} :=
  ⟨injectiveToProjectiveLabel (R := R) K sigma i, by
    exact
      (CategoryTheory.Projective.iso_iff
        (injectiveToProjectiveObjIso (R := R) K sigma i)).1
        ((BoundaryEquivalence (R := R) K).inverse.obj
          (injectiveLabelObject sigma i)).property⟩

/-- The two selected boundary maps compose to the identity on projective
labels. -/
theorem injectiveToProjective_projectiveToInjective
    (i : {i // i ∈ projectiveSet sigma}) :
    injectiveToProjective (R := R) K sigma
      (projectiveToInjective (R := R) K sigma i) = i := by
  apply Subtype.ext
  apply sigma.eq_of_iso
  let E := BoundaryEquivalence (R := R) K
  let P := fgProjectiveProperty (R := R)
  let Q := fgInjectiveProperty (R := R)
  exact ⟨
    (injectiveToProjectiveObjIso (R := R) K sigma
      (projectiveToInjective (R := R) K sigma i)).symm ≪≫
    P.ι.mapIso
      (E.inverse.mapIso
        (Q.ι.preimageIso
          (X := injectiveLabelObject sigma
            (projectiveToInjective (R := R) K sigma i))
          (Y := E.functor.obj (projectiveLabelObject sigma i))
          (projectiveToInjectiveObjIso (R := R) K sigma i).symm)) ≪≫
    P.ι.mapIso (E.unitIso.app (projectiveLabelObject sigma i)).symm⟩

/-- The two selected boundary maps compose to the identity on injective
labels. -/
theorem projectiveToInjective_injectiveToProjective
    (i : {i // i ∈ injectiveSet sigma}) :
    projectiveToInjective (R := R) K sigma
      (injectiveToProjective (R := R) K sigma i) = i := by
  apply Subtype.ext
  apply sigma.eq_of_iso
  let E := BoundaryEquivalence (R := R) K
  let P := fgProjectiveProperty (R := R)
  let Q := fgInjectiveProperty (R := R)
  exact ⟨
    (projectiveToInjectiveObjIso (R := R) K sigma
      (injectiveToProjective (R := R) K sigma i)).symm ≪≫
    Q.ι.mapIso
      (E.functor.mapIso
        (P.ι.preimageIso
          (X := projectiveLabelObject sigma
            (injectiveToProjective (R := R) K sigma i))
          (Y := E.inverse.obj (injectiveLabelObject sigma i))
          (injectiveToProjectiveObjIso (R := R) K sigma i).symm)) ≪≫
    Q.ι.mapIso (E.counitIso.app (injectiveLabelObject sigma i))⟩

/-- The actual projective--injective equivalence on chosen skeleton
labels. -/
def projectiveInjectiveLabelEquiv :
    {i // i ∈ projectiveSet sigma} ≃
      {i // i ∈ injectiveSet sigma} where
  toFun := projectiveToInjective (R := R) K sigma
  invFun := injectiveToProjective (R := R) K sigma
  left_inv := injectiveToProjective_projectiveToInjective
    (R := R) K sigma
  right_inv := projectiveToInjective_injectiveToProjective
    (R := R) K sigma

include K in
/-- Therefore the projective and injective boundaries have equal finite
cardinality. -/
theorem projectiveSet_ncard_eq_injectiveSet_ncard :
    (projectiveSet sigma).ncard = (injectiveSet sigma).ncard :=
  Set.ncard_congr' (projectiveInjectiveLabelEquiv (R := R) K sigma)

end SkeletonBoundary

end Contragredient

section AbstractBoundary

variable [IsNoetherianRing Rᵐᵒᵖ]

omit [IsNoetherianRing R] [IsNoetherianRing Rᵐᵒᵖ] in
private theorem antiEquivalence_injective_inverseImage
    (E : (FGModuleCat.{u} Rᵐᵒᵖ)ᵒᵖ ≌ FGModuleCat.{u} R) :
    (fgInjectiveProperty (R := R)).inverseImage E.functor =
      (fgProjectiveProperty (R := Rᵐᵒᵖ)).op := by
  funext X
  apply propext
  induction X with
  | op X =>
      exact
        (E.map_injective_iff (Opposite.op X)).trans
          (CategoryTheory.Injective.projective_iff_injective_op.symm)

/-- An arbitrary finite-module anti-equivalence restricts from projectives
on the opposite side to injectives on the original side. -/
def reverseProjectiveInjectiveEquivalenceOfAntiEquivalence
    (E : (FGModuleCat.{u} Rᵐᵒᵖ)ᵒᵖ ≌ FGModuleCat.{u} R) :
    (FGProjectives (R := Rᵐᵒᵖ))ᵒᵖ ≌ FGInjectives (R := R) :=
  (ObjectProperty.opEquivalence
      (fgProjectiveProperty (R := Rᵐᵒᵖ))).symm |>.trans
    (E.congrFullSubcategory
      (antiEquivalence_injective_inverseImage (R := R) E))

/-- Projective Hom duality followed by an arbitrary finite-module
anti-equivalence gives a same-ring projective--injective equivalence. -/
def projectiveInjectiveEquivalenceOfAntiEquivalence
    (E : (FGModuleCat.{u} Rᵐᵒᵖ)ᵒᵖ ≌ FGModuleCat.{u} R) :
    FGProjectives (R := R) ≌ FGInjectives (R := R) :=
  (fgProjectiveHomDuality (R := R)).rightOp.trans
    (reverseProjectiveInjectiveEquivalenceOfAntiEquivalence (R := R) E)

section AbstractSkeletonBoundary

variable {iota : Type v}
  (sigma : OpConjecture.IndecomposableSkeleton.{u, v, u} R iota)
  (E : (FGModuleCat.{u} Rᵐᵒᵖ)ᵒᵖ ≌ FGModuleCat.{u} R)

private theorem projectiveBoundaryImage_indec_ofAntiEquivalence
    (i : {i // i ∈ projectiveSet sigma}) :
    OpConjecture.Foundation.IsIndecomposableModule R
      ((projectiveInjectiveEquivalenceOfAntiEquivalence (R := R) E).functor.obj
        (projectiveLabelObject sigma i)).obj :=
  indecomposable_map_fgFullSubcategory
    (fgProjectiveProperty (R := R))
    (fgInjectiveProperty (R := R))
    (projectiveInjectiveEquivalenceOfAntiEquivalence (R := R) E)
    (sigma.indecomposable i.1)

private theorem injectiveBoundaryPreimage_indec_ofAntiEquivalence
    (i : {i // i ∈ injectiveSet sigma}) :
    OpConjecture.Foundation.IsIndecomposableModule R
      ((projectiveInjectiveEquivalenceOfAntiEquivalence (R := R) E).inverse.obj
        (injectiveLabelObject sigma i)).obj :=
  indecomposable_map_fgFullSubcategory
    (fgInjectiveProperty (R := R))
    (fgProjectiveProperty (R := R))
    (projectiveInjectiveEquivalenceOfAntiEquivalence (R := R) E).symm
    (sigma.indecomposable i.1)

/-- The chosen skeleton label of the boundary image of a projective label. -/
def projectiveToInjectiveLabelOfAntiEquivalence
    (i : {i // i ∈ projectiveSet sigma}) : iota :=
  Classical.choose
    (sigma.complete
      ((projectiveInjectiveEquivalenceOfAntiEquivalence (R := R) E).functor.obj
        (projectiveLabelObject sigma i)).obj
      (projectiveBoundaryImage_indec_ofAntiEquivalence (R := R) sigma E i))

/-- The chosen representative is isomorphic to the boundary image. -/
def projectiveToInjectiveObjIsoOfAntiEquivalence
    (i : {i // i ∈ projectiveSet sigma}) :
    ((projectiveInjectiveEquivalenceOfAntiEquivalence (R := R) E).functor.obj
      (projectiveLabelObject sigma i)).obj ≅
        sigma.obj (projectiveToInjectiveLabelOfAntiEquivalence (R := R) sigma E i) :=
  Classical.choice
    (Classical.choose_spec
      (sigma.complete
        ((projectiveInjectiveEquivalenceOfAntiEquivalence (R := R) E).functor.obj
          (projectiveLabelObject sigma i)).obj
        (projectiveBoundaryImage_indec_ofAntiEquivalence (R := R) sigma E i)))

/-- The projective-to-injective map on chosen labels. -/
def projectiveToInjectiveOfAntiEquivalence
    (i : {i // i ∈ projectiveSet sigma}) :
    {i // i ∈ injectiveSet sigma} :=
  ⟨projectiveToInjectiveLabelOfAntiEquivalence (R := R) sigma E i, by
    exact
      (CategoryTheory.Injective.iso_iff
        (projectiveToInjectiveObjIsoOfAntiEquivalence (R := R) sigma E i)).1
        ((projectiveInjectiveEquivalenceOfAntiEquivalence (R := R) E).functor.obj
          (projectiveLabelObject sigma i)).property⟩

/-- The chosen skeleton label of the inverse boundary image of an injective
label. -/
def injectiveToProjectiveLabelOfAntiEquivalence
    (i : {i // i ∈ injectiveSet sigma}) : iota :=
  Classical.choose
    (sigma.complete
      ((projectiveInjectiveEquivalenceOfAntiEquivalence (R := R) E).inverse.obj
        (injectiveLabelObject sigma i)).obj
      (injectiveBoundaryPreimage_indec_ofAntiEquivalence (R := R) sigma E i))

/-- The chosen representative is isomorphic to the inverse boundary image. -/
def injectiveToProjectiveObjIsoOfAntiEquivalence
    (i : {i // i ∈ injectiveSet sigma}) :
    ((projectiveInjectiveEquivalenceOfAntiEquivalence (R := R) E).inverse.obj
      (injectiveLabelObject sigma i)).obj ≅
        sigma.obj (injectiveToProjectiveLabelOfAntiEquivalence (R := R) sigma E i) :=
  Classical.choice
    (Classical.choose_spec
      (sigma.complete
        ((projectiveInjectiveEquivalenceOfAntiEquivalence (R := R) E).inverse.obj
          (injectiveLabelObject sigma i)).obj
        (injectiveBoundaryPreimage_indec_ofAntiEquivalence (R := R) sigma E i)))

/-- The injective-to-projective map on chosen labels. -/
def injectiveToProjectiveOfAntiEquivalence
    (i : {i // i ∈ injectiveSet sigma}) :
    {i // i ∈ projectiveSet sigma} :=
  ⟨injectiveToProjectiveLabelOfAntiEquivalence (R := R) sigma E i, by
    exact
      (CategoryTheory.Projective.iso_iff
        (injectiveToProjectiveObjIsoOfAntiEquivalence (R := R) sigma E i)).1
        ((projectiveInjectiveEquivalenceOfAntiEquivalence (R := R) E).inverse.obj
          (injectiveLabelObject sigma i)).property⟩

/-- The selected boundary maps compose to the identity on projective labels. -/
theorem injectiveToProjective_projectiveToInjective_ofAntiEquivalence
    (i : {i // i ∈ projectiveSet sigma}) :
    injectiveToProjectiveOfAntiEquivalence (R := R) sigma E
      (projectiveToInjectiveOfAntiEquivalence (R := R) sigma E i) = i := by
  apply Subtype.ext
  apply sigma.eq_of_iso
  let B := projectiveInjectiveEquivalenceOfAntiEquivalence (R := R) E
  let P := fgProjectiveProperty (R := R)
  let Q := fgInjectiveProperty (R := R)
  exact ⟨
    (injectiveToProjectiveObjIsoOfAntiEquivalence (R := R) sigma E
      (projectiveToInjectiveOfAntiEquivalence (R := R) sigma E i)).symm ≪≫
    P.ι.mapIso
      (B.inverse.mapIso
        (Q.ι.preimageIso
          (X := injectiveLabelObject sigma
            (projectiveToInjectiveOfAntiEquivalence (R := R) sigma E i))
          (Y := B.functor.obj (projectiveLabelObject sigma i))
          (projectiveToInjectiveObjIsoOfAntiEquivalence
            (R := R) sigma E i).symm)) ≪≫
    P.ι.mapIso (B.unitIso.app (projectiveLabelObject sigma i)).symm⟩

/-- The selected boundary maps compose to the identity on injective labels. -/
theorem projectiveToInjective_injectiveToProjective_ofAntiEquivalence
    (i : {i // i ∈ injectiveSet sigma}) :
    projectiveToInjectiveOfAntiEquivalence (R := R) sigma E
      (injectiveToProjectiveOfAntiEquivalence (R := R) sigma E i) = i := by
  apply Subtype.ext
  apply sigma.eq_of_iso
  let B := projectiveInjectiveEquivalenceOfAntiEquivalence (R := R) E
  let P := fgProjectiveProperty (R := R)
  let Q := fgInjectiveProperty (R := R)
  exact ⟨
    (projectiveToInjectiveObjIsoOfAntiEquivalence (R := R) sigma E
      (injectiveToProjectiveOfAntiEquivalence (R := R) sigma E i)).symm ≪≫
    Q.ι.mapIso
      (B.functor.mapIso
        (P.ι.preimageIso
          (X := projectiveLabelObject sigma
            (injectiveToProjectiveOfAntiEquivalence (R := R) sigma E i))
          (Y := B.inverse.obj (injectiveLabelObject sigma i))
          (injectiveToProjectiveObjIsoOfAntiEquivalence
            (R := R) sigma E i).symm)) ≪≫
    Q.ι.mapIso (B.counitIso.app (injectiveLabelObject sigma i))⟩

/-- An arbitrary finite-module anti-equivalence gives an equivalence between
the chosen indecomposable projective and injective labels. -/
def projectiveInjectiveLabelEquivOfAntiEquivalence :
    {i // i ∈ projectiveSet sigma} ≃
      {i // i ∈ injectiveSet sigma} where
  toFun := projectiveToInjectiveOfAntiEquivalence (R := R) sigma E
  invFun := injectiveToProjectiveOfAntiEquivalence (R := R) sigma E
  left_inv :=
    injectiveToProjective_projectiveToInjective_ofAntiEquivalence
      (R := R) sigma E
  right_inv :=
    projectiveToInjective_injectiveToProjective_ofAntiEquivalence
      (R := R) sigma E

end AbstractSkeletonBoundary

end AbstractBoundary

end OpConjecture.RingelStable
