import QuotientSubmoduleEquidistribution.RepresentationTheory.MoritaRestriction
import QuotientSubmoduleEquidistribution.RepresentationTheory.EquivalenceTransport

/-!
# Deriving skeleton alignment from an equivalence

The production transport interface asks for a label equivalence and
objectwise isomorphisms between two chosen indecomposable skeletons.  This
file derives those data from the completeness and duplicate-freeness fields
of the skeletons, rather than assuming them.
-/

noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe uR uS vR vS wR wS

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {S : Type uS} [Ring S] [IsNoetherianRing S]
  {ι : Type vR} {κ : Type vS}
  (σ : IndecomposableSkeleton.{uR, vR, wR} R ι)
  (τ : IndecomposableSkeleton.{uS, vS, wS} S κ)

namespace Equivalence

variable (E : FGModuleCat.{wR} R ≌ FGModuleCat.{wS} S)

/-- A category equivalence of finitely generated module categories
preserves the project foundation's module-level indecomposability predicate. -/
theorem indecomposable_map {M : FGModuleCat.{wR} R}
    (hM : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R M) :
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule S (E.functor.obj M) := by
  rw [QuotientSubmoduleEquidistribution.Foundation.isIndecomposableModule_iff_nontrivial_and_forall_isIdempotentElem]
  constructor
  · by_contra h
    letI : Subsingleton (E.functor.obj M) :=
      not_nontrivial_iff_subsingleton.mp h
    have htarget :
        (𝟙 (E.functor.obj M) :
          E.functor.obj M ⟶ E.functor.obj M) = 0 :=
      by
        apply FGModuleCat.hom_ext
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
    let fcat :
        E.functor.obj M ⟶ E.functor.obj M :=
      FGModuleCat.ofHom f
    have fcat_apply (x : E.functor.obj M) :
        fcat.hom.hom x = f x :=
      rfl
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
      apply FGModuleCat.hom_ext
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
      ext x
      have hx :=
        congrArg
          (fun q :
            E.functor.obj M ⟶ E.functor.obj M ↦ q.hom.hom x)
          hfcat
      rw [fcat_apply] at hx
      simpa using hx
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
      ext x
      have hx :=
        congrArg
          (fun q :
            E.functor.obj M ⟶ E.functor.obj M ↦ q.hom.hom x)
          hfcat
      rw [fcat_apply] at hx
      simpa [Module.End.one_eq_id] using hx

/-- An equivalence also reflects indecomposability. -/
theorem indecomposable_map_iff {M : FGModuleCat.{wR} R} :
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule S (E.functor.obj M) ↔
      QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R M := by
  constructor
  · intro h
    have h' :=
      indecomposable_map E.symm h
    exact h'.of_linearEquiv
      (FGModuleCat.isoToLinearEquiv
        (E.unitIso.app M).symm)
  · exact indecomposable_map E

/-- The target representative selected by completeness for the image of a
source representative. -/
def mapLabel (i : ι) : κ :=
  Classical.choose
    (τ.complete (E.functor.obj (σ.obj i))
      (indecomposable_map E (σ.indecomposable i)))

/-- The selected target representative is isomorphic to the image. -/
def mapObjIso (i : ι) :
    E.functor.obj (σ.obj i) ≅ τ.obj (mapLabel σ τ E i) :=
  Classical.choice
    (Classical.choose_spec
      (τ.complete (E.functor.obj (σ.obj i))
        (indecomposable_map E (σ.indecomposable i))))

/-- The source representative selected for the inverse image of a target
representative. -/
def invLabel (j : κ) : ι :=
  mapLabel τ σ E.symm j

/-- Applying the two selected label maps successively returns the source
label. -/
theorem invLabel_mapLabel (i : ι) :
    invLabel σ τ E (mapLabel σ τ E i) = i := by
  apply σ.eq_of_iso
  exact ⟨
    (mapObjIso τ σ E.symm (mapLabel σ τ E i)).symm ≪≫
      E.inverse.mapIso (mapObjIso σ τ E i).symm ≪≫
      (E.unitIso.app (σ.obj i)).symm⟩

/-- Applying the two selected label maps successively returns the target
label. -/
theorem mapLabel_invLabel (j : κ) :
    mapLabel σ τ E (invLabel σ τ E j) = j := by
  apply τ.eq_of_iso
  exact ⟨
    (mapObjIso σ τ E (invLabel σ τ E j)).symm ≪≫
      E.functor.mapIso (mapObjIso τ σ E.symm j).symm ≪≫
      E.counitIso.app (τ.obj j)⟩

/-- The induced equivalence of the two chosen index types. -/
def labelEquiv : ι ≃ κ where
  toFun := mapLabel σ τ E
  invFun := invLabel σ τ E
  left_inv := invLabel_mapLabel σ τ E
  right_inv := mapLabel_invLabel σ τ E

/-- Every equivalence of finitely generated module categories canonically
up to choice supplies the data required by `AlignedEquivalence`. -/
def alignedEquivalence :
    AlignedEquivalence σ τ where
  categoryEquiv := E
  labelEquiv := labelEquiv σ τ E
  objIso := mapObjIso σ τ E

end Equivalence

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton

namespace MoritaEquivalence

universe uK uA uB vA vB

variable {K : Type uK} [CommSemiring K]
  {A : Type uA} [Ring A] [Algebra K A] [IsArtinianRing A]
  {B : Type uB} [Ring B] [Algebra K B] [IsArtinianRing B]
  {ι : Type vA} {κ : Type vB}

/-- A Mathlib Morita equivalence supplies the full aligned-equivalence data
for any two complete duplicate-free indecomposable skeletons. -/
def alignedFgEquivalence
    (e : MoritaEquivalence K A B)
    (σ : QuotientSubmoduleEquidistribution.IndecomposableSkeleton
      A ι)
    (τ : QuotientSubmoduleEquidistribution.IndecomposableSkeleton
      B κ) :
    QuotientSubmoduleEquidistribution.IndecomposableSkeleton.AlignedEquivalence σ τ :=
  QuotientSubmoduleEquidistribution.IndecomposableSkeleton.Equivalence.alignedEquivalence
    σ τ e.fgEquivalence

end MoritaEquivalence
