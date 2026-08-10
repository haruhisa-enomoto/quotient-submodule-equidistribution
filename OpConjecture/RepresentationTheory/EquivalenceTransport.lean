import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import OpConjecture.RepresentationTheory.FacSub

/-!
# Transporting skeleton presentations along a category equivalence

The data here is deliberately weaker than a concrete Morita context: a
category equivalence of finitely generated module categories plus an alignment
of the two chosen indecomposable skeletons.  The equivalence itself preserves
finite products/coproducts, epimorphisms, and monomorphisms.
-/

noncomputable section

open Set
open CategoryTheory CategoryTheory.Limits

namespace OpConjecture.IndecomposableSkeleton

universe uR uS vR vS wR wS

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {S : Type uS} [Ring S] [IsNoetherianRing S]
  {ι : Type vR} {κ : Type vS}
  (σ : IndecomposableSkeleton.{uR, vR, wR} R ι)
  (τ : IndecomposableSkeleton.{uS, vS, wS} S κ)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- A category equivalence together with its action on the two chosen
indecomposable skeletons. -/
structure AlignedEquivalence where
  categoryEquiv : FGModuleCat.{wR} R ≌ FGModuleCat.{wS} S
  labelEquiv : ι ≃ κ
  objIso :
    ∀ i, categoryEquiv.functor.obj (σ.obj i) ≅ τ.obj (labelEquiv i)

namespace AlignedEquivalence

variable (E : AlignedEquivalence σ τ)

/-- An equivalence sends the displayed finite direct sum to the displayed
sum of the corresponding target representatives.

This construction uses the coproduct universal property, so it does not need
an `Additive E.categoryEquiv.functor` instance. -/
def sumIso (J : FintypeCat.{0}) (a : J → ι) :
    E.categoryEquiv.functor.obj (σ.sumOver J a) ≅
      τ.sumOver J (fun j ↦ E.labelEquiv (a j)) :=
  E.categoryEquiv.functor.mapIso
      (biproduct.isoCoproduct (fun j : J ↦ σ.obj (a j))) ≪≫
    PreservesCoproduct.iso E.categoryEquiv.functor
      (fun j : J ↦ σ.obj (a j)) ≪≫
    (biproduct.isoCoproduct
      (fun j : J ↦ E.categoryEquiv.functor.obj (σ.obj (a j)))).symm ≪≫
    biproduct.mapIso (fun j ↦ E.objIso (a j))

/-- Forward transport of a quotient presentation. -/
def mapFacPresentation {T : Set ι} {X : FGModuleCat.{wR} R}
    (P : σ.FacPresentation T X) :
    τ.FacPresentation (E.labelEquiv '' T)
      (E.categoryEquiv.functor.obj X) where
  index := P.index
  label := fun t ↦ E.labelEquiv (P.label t)
  mem t := ⟨P.label t, P.mem t, rfl⟩
  map :=
    (sumIso σ τ E P.index P.label).inv ≫
      E.categoryEquiv.functor.map P.map
  epi := by
    letI : Epi P.map := P.epi
    infer_instance

/-- Forward transport of a submodule presentation. -/
def mapSubPresentation {T : Set ι} {X : FGModuleCat.{wR} R}
    (P : σ.SubPresentation T X) :
    τ.SubPresentation (E.labelEquiv '' T)
      (E.categoryEquiv.functor.obj X) where
  index := P.index
  label := fun t ↦ E.labelEquiv (P.label t)
  mem t := ⟨P.label t, P.mem t, rfl⟩
  map :=
    E.categoryEquiv.functor.map P.map ≫
      (sumIso σ τ E P.index P.label).hom
  mono := by
    letI : Mono P.map := P.mono
    infer_instance

/-- Transport a quotient presentation whose target is a skeleton object,
then use the chosen target-skeleton isomorphism. -/
def mapFacPresentationObj {T : Set ι} {i : ι}
    (P : σ.FacPresentation T (σ.obj i)) :
    τ.FacPresentation (E.labelEquiv '' T)
      (τ.obj (E.labelEquiv i)) where
  index := P.index
  label := fun t ↦ E.labelEquiv (P.label t)
  mem t := ⟨P.label t, P.mem t, rfl⟩
  map :=
    (sumIso σ τ E P.index P.label).inv ≫
      E.categoryEquiv.functor.map P.map ≫
      (E.objIso i).hom
  epi := by
    letI : Epi P.map := P.epi
    infer_instance

/-- Transport a submodule presentation whose source is a skeleton object,
then use the chosen target-skeleton isomorphism. -/
def mapSubPresentationObj {T : Set ι} {i : ι}
    (P : σ.SubPresentation T (σ.obj i)) :
    τ.SubPresentation (E.labelEquiv '' T)
      (τ.obj (E.labelEquiv i)) where
  index := P.index
  label := fun t ↦ E.labelEquiv (P.label t)
  mem t := ⟨P.label t, P.mem t, rfl⟩
  map :=
    (E.objIso i).inv ≫
      E.categoryEquiv.functor.map P.map ≫
      (sumIso σ τ E P.index P.label).hom
  mono := by
    letI : Mono P.map := P.mono
    infer_instance

theorem mem_qSet_image {T : Set ι} {i : ι}
    (hi : i ∈ σ.qSet T) :
    E.labelEquiv i ∈ τ.qSet (E.labelEquiv '' T) :=
  hi.map (mapFacPresentationObj σ τ E ·)

theorem mem_sSet_image {T : Set ι} {i : ι}
    (hi : i ∈ σ.sSet T) :
    E.labelEquiv i ∈ τ.sSet (E.labelEquiv '' T) :=
  hi.map (mapSubPresentationObj σ τ E ·)

/-- The object comparison needed to align the inverse category
equivalence with the inverse label equivalence. -/
def inverseObjIso (j : κ) :
    E.categoryEquiv.inverse.obj (τ.obj j) ≅
      σ.obj (E.labelEquiv.symm j) :=
  E.categoryEquiv.inverse.mapIso
      (eqToIso
          (congrArg τ.obj
            (E.labelEquiv.apply_symm_apply j)).symm ≪≫
        (E.objIso (E.labelEquiv.symm j)).symm) ≪≫
    (E.categoryEquiv.unitIso.app
      (σ.obj (E.labelEquiv.symm j))).symm

/-- The aligned equivalence in the reverse direction. -/
def symm : AlignedEquivalence τ σ where
  categoryEquiv := E.categoryEquiv.symm
  labelEquiv := E.labelEquiv.symm
  objIso := inverseObjIso σ τ E

/-- Quotient generation is conjugated by the label equivalence. -/
theorem mem_qSet_image_iff {T : Set ι} {i : ι} :
    E.labelEquiv i ∈ τ.qSet (E.labelEquiv '' T) ↔
      i ∈ σ.qSet T := by
  constructor
  · intro hi
    have hback :=
      mem_qSet_image τ σ (symm σ τ E) hi
    simpa only [symm, Equiv.symm_apply_apply,
      Equiv.symm_image_image] using hback
  · exact mem_qSet_image σ τ E

/-- Submodule generation is conjugated by the label equivalence. -/
theorem mem_sSet_image_iff {T : Set ι} {i : ι} :
    E.labelEquiv i ∈ τ.sSet (E.labelEquiv '' T) ↔
      i ∈ σ.sSet T := by
  constructor
  · intro hi
    have hback :=
      mem_sSet_image τ σ (symm σ τ E) hi
    simpa only [symm, Equiv.symm_apply_apply,
      Equiv.symm_image_image] using hback
  · exact mem_sSet_image σ τ E

theorem image_qSet (T : Set ι) :
    E.labelEquiv '' σ.qSet T =
      τ.qSet (E.labelEquiv '' T) := by
  ext j
  rw [Set.mem_image_equiv]
  simpa using
    (mem_qSet_image_iff σ τ E
      (T := T) (i := E.labelEquiv.symm j)).symm

theorem image_sSet (T : Set ι) :
    E.labelEquiv '' σ.sSet T =
      τ.sSet (E.labelEquiv '' T) := by
  ext j
  rw [Set.mem_image_equiv]
  simpa using
    (mem_sSet_image_iff σ τ E
      (T := T) (i := E.labelEquiv.symm j)).symm

/-- Morita-style equivalence conjugates quotient closure. -/
theorem image_qClosure (T : Set ι) :
    E.labelEquiv '' σ.qClosure T =
      τ.qClosure (E.labelEquiv '' T) :=
  image_qSet σ τ E T

/-- Morita-style equivalence conjugates submodule closure. -/
theorem image_sClosure (T : Set ι) :
    E.labelEquiv '' σ.sClosure T =
      τ.sClosure (E.labelEquiv '' T) :=
  image_sSet σ τ E T

end AlignedEquivalence

end OpConjecture.IndecomposableSkeleton
