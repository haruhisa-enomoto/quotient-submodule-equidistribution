import OpConjecture.RepresentationTheory.CoordinateIdempotent
import OpConjecture.RepresentationTheory.SkeletonAlignment

/-!
# Coordinate indecomposable projectives of the Auslander algebra

The singleton coordinate projectives form a complete duplicate-free family
of indecomposable finitely generated projective modules over the chosen
skeleton Auslander algebra.  This is the projective-object prerequisite for
constructing the simple labels and projective covers in the CPS
standard-module package.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace OpConjecture.AuslanderEquivalence.CoordinateIdempotent

open OpConjecture.IndecomposableSkeleton

universe uR uι wR

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {κ : Type uι}
  (σ : IndecomposableSkeleton.{uR, uι, wR} R κ)
  [Finite κ]

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- The partial generator supported at one label is that skeleton object. -/
def partialGeneratorSingletonIso (i : κ) :
    partialGenerator σ.obj (fun j ↦ j = i) ≅ σ.obj i := by
  letI : Unique (Subtype fun j : κ ↦ j = i) := {
    default := ⟨i, rfl⟩
    uniq j := Subtype.ext j.property }
  exact biproductUniqueIso _

/-- The coordinate projective attached to a single skeleton label. -/
abbrev coordinateProjective (i : κ) :
    skeletonProjectiveTarget σ :=
  principalProjectiveObject σ (fun j ↦ j = i)

/-- Under the Auslander equivalence, a skeleton representative is its
singleton coordinate projective. -/
def auslanderImageIsoCoordinateProjective (i : κ) :
    (skeletonAuslanderEquivalence σ).functor.obj (σ.obj i) ≅
      coordinateProjective σ i :=
  (skeletonAuslanderEquivalence σ).functor.mapIso
      (partialGeneratorSingletonIso σ i).symm ≪≫
    auslanderImagePartialGeneratorIsoPrincipal σ (fun j ↦ j = i)

/-- Distinct skeleton labels give nonisomorphic coordinate projectives. -/
theorem coordinateProjective_eq_of_iso {i j : κ}
    (e : coordinateProjective σ i ≅ coordinateProjective σ j) :
    i = j := by
  let E := skeletonAuslanderEquivalence σ
  let e' : E.functor.obj (σ.obj i) ≅ E.functor.obj (σ.obj j) :=
    auslanderImageIsoCoordinateProjective σ i ≪≫ e ≪≫
      (auslanderImageIsoCoordinateProjective σ j).symm
  apply σ.eq_of_iso
  exact ⟨
    E.unitIso.app (σ.obj i) ≪≫
      E.inverse.mapIso e' ≪≫
      (E.unitIso.app (σ.obj j)).symm⟩

/-- Singleton coordinate objects are finite projective modules by
construction. -/
theorem coordinateProjective_isFiniteProjective (i : κ) :
    AuslanderEquivalence.finiteProjectiveModules
      (skeletonAuslanderAlgebra σ)ᵐᵒᵖ
      (coordinateProjective σ i).obj :=
  (coordinateProjective σ i).property

/-- The finite-projective Auslander equivalence preserves the concrete
module-level indecomposability predicate.  This is the full-subcategory
variant of `IndecomposableSkeleton.Equivalence.indecomposable_map`. -/
theorem indecomposable_auslanderImage {M : FGModuleCat.{wR} R}
    (hM : OpConjecture.Foundation.IsIndecomposableModule R M) :
    OpConjecture.Foundation.IsIndecomposableModule
      (skeletonAuslanderAlgebra σ)ᵐᵒᵖ
      ((skeletonAuslanderEquivalence σ).functor.obj M).obj := by
  let E := skeletonAuslanderEquivalence σ
  rw [OpConjecture.Foundation.isIndecomposableModule_iff_nontrivial_and_forall_isIdempotentElem]
  constructor
  · by_contra h
    letI : Subsingleton ((E.functor.obj M).obj) :=
      not_nontrivial_iff_subsingleton.mp h
    have htarget :
        (𝟙 (E.functor.obj M) :
          E.functor.obj M ⟶ E.functor.obj M) = 0 := by
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      ext x
      exact Subsingleton.elim _ _
    have hsource : (𝟙 M : M ⟶ M) = 0 := by
      apply E.functor.map_injective
      simpa using htarget
    letI : Nontrivial M := hM.nontrivial
    have hend : (1 : Module.End R M) = 0 := by
      have hlinear :=
        congrArg (fun f : M ⟶ M ↦ f.hom.hom) hsource
      simpa [Module.End.one_eq_id] using hlinear
    exact one_ne_zero hend
  · intro f hf
    let fbase :
        (E.functor.obj M).obj ⟶ (E.functor.obj M).obj :=
      ModuleCat.ofHom f
    let fcat : E.functor.obj M ⟶ E.functor.obj M :=
      ObjectProperty.homMk fbase
    let gcat : M ⟶ M :=
      E.functor.preimage fcat
    let g : Module.End R M :=
      gcat.hom.hom
    have hcat : gcat ≫ gcat = gcat := by
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
        congrArg (fun q : M ⟶ M ↦ q.hom.hom) hcat
      simpa [g, Module.End.mul_eq_comp] using hlinear
    rcases
        hM.eq_zero_or_eq_one_of_isIdempotentElem hg with
      hg | hg
    · left
      have hgcat : gcat = 0 := by
        apply FGModuleCat.hom_ext
        exact hg
      have hfcat : fcat = 0 := by
        calc
          fcat = E.functor.map gcat :=
            (E.functor.map_preimage fcat).symm
          _ = E.functor.map 0 := congrArg E.functor.map hgcat
          _ = 0 := E.functor.map_zero M M
      have hlinear :=
        congrArg
          (fun q : E.functor.obj M ⟶ E.functor.obj M ↦
            q.hom.hom)
          hfcat
      exact hlinear
    · right
      have hgcat : gcat = 𝟙 M := by
        apply FGModuleCat.hom_ext
        simpa [g, Module.End.one_eq_id] using hg
      have hfcat : fcat = 𝟙 (E.functor.obj M) := by
        calc
          fcat = E.functor.map gcat :=
            (E.functor.map_preimage fcat).symm
          _ = E.functor.map (𝟙 M) :=
            congrArg E.functor.map hgcat
          _ = 𝟙 (E.functor.obj M) := E.functor.map_id M
      have hlinear :=
        congrArg
          (fun q : E.functor.obj M ⟶ E.functor.obj M ↦
            q.hom.hom)
          hfcat
      ext x
      have hx := congrArg (fun q ↦ q x) hlinear
      change f x = x at hx
      exact hx

/-- The finite-projective Auslander equivalence also reflects the
concrete module-level indecomposability predicate. -/
theorem indecomposable_of_auslanderImage {M : FGModuleCat.{wR} R}
    (hM :
      OpConjecture.Foundation.IsIndecomposableModule
        (skeletonAuslanderAlgebra σ)ᵐᵒᵖ
        ((skeletonAuslanderEquivalence σ).functor.obj M).obj) :
    OpConjecture.Foundation.IsIndecomposableModule R M := by
  let E := skeletonAuslanderEquivalence σ
  rw [OpConjecture.Foundation.isIndecomposableModule_iff_nontrivial_and_forall_isIdempotentElem]
  constructor
  · by_contra h
    letI : Subsingleton M :=
      not_nontrivial_iff_subsingleton.mp h
    have hsource : (𝟙 M : M ⟶ M) = 0 := by
      apply FGModuleCat.hom_ext
      ext x
      exact Subsingleton.elim _ _
    have htarget :
        (𝟙 (E.functor.obj M) :
          E.functor.obj M ⟶ E.functor.obj M) = 0 := by
      simpa using congrArg E.functor.map hsource
    letI : Nontrivial ((E.functor.obj M).obj) :=
      hM.nontrivial
    have hend :
        (1 :
          Module.End (skeletonAuslanderAlgebra σ)ᵐᵒᵖ
            ((E.functor.obj M).obj)) = 0 := by
      have hlinear :=
        congrArg
          (fun q : E.functor.obj M ⟶ E.functor.obj M ↦
            q.hom.hom)
          htarget
      simpa [Module.End.one_eq_id] using hlinear
    exact one_ne_zero hend
  · intro g hg
    let gcat : M ⟶ M :=
      FGModuleCat.ofHom g
    let fcat : E.functor.obj M ⟶ E.functor.obj M :=
      E.functor.map gcat
    let f :
        Module.End (skeletonAuslanderAlgebra σ)ᵐᵒᵖ
          ((E.functor.obj M).obj) :=
      fcat.hom.hom
    have hgcat : gcat ≫ gcat = gcat := by
      apply FGModuleCat.hom_ext
      change g.comp g = g
      change g * g = g at hg
      simpa [Module.End.mul_eq_comp] using hg
    have hf : IsIdempotentElem f := by
      change f * f = f
      have htarget :=
        congrArg E.functor.map hgcat
      rw [E.functor.map_comp] at htarget
      have hlinear :=
        congrArg
          (fun q : E.functor.obj M ⟶ E.functor.obj M ↦
            q.hom.hom)
          htarget
      simpa [f, fcat, Module.End.mul_eq_comp] using hlinear
    rcases
        hM.eq_zero_or_eq_one_of_isIdempotentElem hf with
      hf | hf
    · left
      have hfcat : fcat = 0 := by
        apply ObjectProperty.hom_ext
        apply ModuleCat.hom_ext
        exact hf
      have hgcatZero : gcat = 0 := by
        apply E.functor.map_injective
        simpa [fcat] using hfcat
      have hlinear :=
        congrArg (fun q : M ⟶ M ↦ q.hom.hom) hgcatZero
      change g = 0 at hlinear
      exact hlinear
    · right
      have hfcat : fcat = 𝟙 (E.functor.obj M) := by
        apply ObjectProperty.hom_ext
        apply ModuleCat.hom_ext
        simpa [f, Module.End.one_eq_id] using hf
      have hgcatOne : gcat = 𝟙 M := by
        apply E.functor.map_injective
        simpa [fcat] using hfcat
      have hlinear :=
        congrArg (fun q : M ⟶ M ↦ q.hom.hom) hgcatOne
      ext x
      have hx := congrArg (fun q ↦ q x) hlinear
      change g x = x at hx
      exact hx

/-- Thus the concrete indecomposability predicate is equivalent on the
two sides of the finite-projective Auslander equivalence. -/
theorem indecomposable_auslanderImage_iff
    {M : FGModuleCat.{wR} R} :
    OpConjecture.Foundation.IsIndecomposableModule
        (skeletonAuslanderAlgebra σ)ᵐᵒᵖ
        ((skeletonAuslanderEquivalence σ).functor.obj M).obj ↔
      OpConjecture.Foundation.IsIndecomposableModule R M :=
  ⟨indecomposable_of_auslanderImage σ,
    indecomposable_auslanderImage σ⟩

/-- In particular, every singleton coordinate projective is
indecomposable. -/
theorem coordinateProjective_indecomposable (i : κ) :
    OpConjecture.Foundation.IsIndecomposableModule
      (skeletonAuslanderAlgebra σ)ᵐᵒᵖ
      (coordinateProjective σ i).obj := by
  exact
    (indecomposable_auslanderImage σ (σ.indecomposable i)).of_linearEquiv
      (((AuslanderEquivalence.finiteProjectiveModules
          (skeletonAuslanderAlgebra σ)ᵐᵒᵖ).ι.mapIso
        (auslanderImageIsoCoordinateProjective σ i)).toLinearEquiv)

/-- Every indecomposable finitely generated projective module over the
opposite Auslander algebra is isomorphic to a singleton coordinate
projective. -/
theorem exists_iso_coordinateProjective_of_indec
    (P : skeletonProjectiveTarget σ)
    (hP :
      OpConjecture.Foundation.IsIndecomposableModule
        (skeletonAuslanderAlgebra σ)ᵐᵒᵖ P.obj) :
    ∃ i : κ, Nonempty (P ≅ coordinateProjective σ i) := by
  let E := skeletonAuslanderEquivalence σ
  let M : FGModuleCat.{wR} R := E.inverse.obj P
  have hImage :
      OpConjecture.Foundation.IsIndecomposableModule
        (skeletonAuslanderAlgebra σ)ᵐᵒᵖ
        (E.functor.obj M).obj := by
    exact hP.of_linearEquiv
      (((AuslanderEquivalence.finiteProjectiveModules
          (skeletonAuslanderAlgebra σ)ᵐᵒᵖ).ι.mapIso
        (E.counitIso.app P).symm).toLinearEquiv)
  have hM : OpConjecture.Foundation.IsIndecomposableModule R M :=
    indecomposable_of_auslanderImage σ hImage
  obtain ⟨i, ⟨e⟩⟩ := σ.complete M hM
  refine ⟨i, ⟨?_⟩⟩
  exact
    (E.counitIso.app P).symm ≪≫
      E.functor.mapIso e ≪≫
      auslanderImageIsoCoordinateProjective σ i

/-- The singleton coordinate projectives form a complete,
duplicate-free family of indecomposable finitely generated projectives. -/
structure CoordinateProjectiveClassification : Prop where
  finiteProjective :
    ∀ i,
      AuslanderEquivalence.finiteProjectiveModules
        (skeletonAuslanderAlgebra σ)ᵐᵒᵖ
        (coordinateProjective σ i).obj
  indecomposable :
    ∀ i,
      OpConjecture.Foundation.IsIndecomposableModule
        (skeletonAuslanderAlgebra σ)ᵐᵒᵖ
        (coordinateProjective σ i).obj
  nodup :
    ∀ {i j},
      Nonempty (coordinateProjective σ i ≅
        coordinateProjective σ j) →
      i = j
  complete :
    ∀ (P : skeletonProjectiveTarget σ),
      OpConjecture.Foundation.IsIndecomposableModule
          (skeletonAuslanderAlgebra σ)ᵐᵒᵖ P.obj →
        ∃ i, Nonempty (P ≅ coordinateProjective σ i)

/-- The existing Auslander equivalence and indecomposable skeleton prove
the full coordinate-projective classification without additional
representation-theoretic assumptions. -/
theorem coordinateProjectiveClassification :
    CoordinateProjectiveClassification σ where
  finiteProjective :=
    coordinateProjective_isFiniteProjective σ
  indecomposable :=
    coordinateProjective_indecomposable σ
  nodup := by
    rintro i j ⟨e⟩
    exact coordinateProjective_eq_of_iso σ e
  complete :=
    exists_iso_coordinateProjective_of_indec σ

end OpConjecture.AuslanderEquivalence.CoordinateIdempotent
