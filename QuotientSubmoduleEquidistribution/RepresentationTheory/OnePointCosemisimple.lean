import Mathlib.RingTheory.Length
import QuotientSubmoduleEquidistribution.RepresentationTheory.AdditiveSubcategory
import QuotientSubmoduleEquidistribution.RepresentationTheory.EndomorphismRadical
import QuotientSubmoduleEquidistribution.RepresentationTheory.SplitInjective
import QuotientSubmoduleEquidistribution.RepresentationTheory.SplitProjective

/-!
# The one-point cosemisimplicity calculation

This file isolates the module-theoretic step in the proof of
`thm:qh-bridge`. If `S` is quotient closed and `x ∈ S`, then every
noninvertible endomorphism of the chosen indecomposable `σ.obj x` factors
through an object of `add (S \ {x})`.

The middle object is the range of the endomorphism. Quotient closedness puts
that range in `add S`; its strictly smaller module length prevents `x` from
occurring in a decomposition of the range.
-/

noncomputable section

open Set
open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe uR uι w

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {ι : Type uι} (σ : IndecomposableSkeleton.{uR, uι, w} R ι)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- A morphism factors through the additive closure of `T`. -/
def FactorsThroughAdd (T : Set ι)
    {X Z : FGModuleCat.{w} R} (f : X ⟶ Z) : Prop :=
  ∃ middle : FGModuleCat.{w} R, σ.InAdd T middle ∧
    ∃ (left : X ⟶ middle) (right : middle ⟶ Z),
      left ≫ right = f

/-- The range object of an endomorphism, regarded as a finitely generated
module. -/
private abbrev endRange {X : FGModuleCat.{w} R} (f : X ⟶ X) :
    FGModuleCat.{w} R :=
  FGModuleCat.of R (LinearMap.range f.hom.hom)

omit [IsNoetherianRing R] in
/-- The canonical factorization of an endomorphism through its range. -/
private theorem range_fac {X : FGModuleCat.{w} R} (f : X ⟶ X) :
    (FGModuleCat.ofHom f.hom.hom.rangeRestrict :
        X ⟶ endRange f) ≫
      (FGModuleCat.ofHom (LinearMap.range f.hom.hom).subtype :
        endRange f ⟶ X) =
      f := by
  apply FGModuleCat.hom_ext
  ext z
  rfl

omit [IsNoetherianRing R] in
/-- The range of a nonunit finite-length endomorphism is proper. -/
private theorem range_ne_top_of_not_isUnit
    {X : FGModuleCat.{w} R} (hX : IsFiniteLength R X)
    (f : X ⟶ X) (hf : ¬ IsUnit f.hom.hom) :
    LinearMap.range f.hom.hom ≠ ⊤ := by
  obtain ⟨hN, hA⟩ :=
    isFiniteLength_iff_isNoetherian_isArtinian.mp hX
  letI : IsNoetherian R X := hN
  letI : IsArtinian R X := hA
  intro hrange
  have hsurj : Function.Surjective f.hom.hom :=
    LinearMap.range_eq_top.mp hrange
  have hinj : Function.Injective f.hom.hom :=
    IsNoetherian.injective_of_surjective_endomorphism
      f.hom.hom hsurj
  exact hf ((Module.End.isUnit_iff f.hom.hom).2 ⟨hinj, hsurj⟩)

/-- Once the range of a nonunit endomorphism belongs to `add S`, its
strictly smaller length ensures that it actually belongs to
`add (S \ {x})`.  This is the common finite-length core of the quotient-
and subobject-closed one-point arguments. -/
private theorem notIsUnit_endomorphism_factorsThroughAdd_sdiff_of_range_inAdd
    {S : Set ι} {x : ι}
    (f : σ.obj x ⟶ σ.obj x)
    (hf : ¬ IsUnit f.hom.hom)
    (hY : σ.InAdd S (endRange f)) :
    FactorsThroughAdd σ (S \ {x}) f := by
  let Y : FGModuleCat.{w} R := endRange f
  let q : σ.obj x ⟶ Y :=
    FGModuleCat.ofHom f.hom.hom.rangeRestrict
  let m : Y ⟶ σ.obj x :=
    FGModuleCat.ofHom (LinearMap.range f.hom.hom).subtype

  obtain ⟨hN, hA⟩ :=
    isFiniteLength_iff_isNoetherian_isArtinian.mp
      (σ.finiteLength x)
  letI : IsNoetherian R (σ.obj x) := hN
  letI : IsArtinian R (σ.obj x) := hA
  have hproper :
      LinearMap.range f.hom.hom ≠ ⊤ :=
    range_ne_top_of_not_isUnit (σ.finiteLength x) f hf
  have hlength :
      Module.length R Y <
        Module.length R (σ.obj x) := by
    exact Submodule.length_lt hproper

  obtain ⟨n, a, ⟨e⟩⟩ := σ.decomposes Y
  have ha : ∀ t : Fin n, a t ∈ S \ {x} := by
    intro t
    let rt : Retract (σ.obj (a t)) Y :=
      { i :=
          biproduct.ι
              (fun j : Fin n ↦ σ.obj (a j)) t ≫
            e.inv
        r :=
          e.hom ≫
            biproduct.π
              (fun j : Fin n ↦ σ.obj (a j)) t
        retract := by simp }
    have hatS : a t ∈ S :=
      index_mem_of_retract_inAdd σ rt hY
    refine ⟨hatS, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro hatx
    have hi :
        Function.Injective rt.i.hom.hom :=
      (fg_mono_iff_injective rt.i).1 inferInstance
    have hle :
        Module.length R (σ.obj (a t)) ≤
          Module.length R Y :=
      Module.length_le_of_injective rt.i.hom.hom hi
    rw [hatx] at hle
    exact (not_le_of_gt hlength) hle

  refine ⟨Y, ?_, q, m, ?_⟩
  · exact ⟨{
      index := FintypeCat.of (Fin n)
      label := a
      mem := ha
      iso := e }⟩
  · exact range_fac f

/-- Every noninvertible endomorphism of a selected indecomposable in a
quotient-closed support factors through the additive closure obtained by
deleting that label.

This is the concrete load-bearing assertion used to show that the one-point
quotient category has zero endomorphism radical. -/
theorem notIsUnit_endomorphism_factorsThroughAdd_sdiff
    {S : Set ι} {x : ι}
    (hS : σ.qClosure.IsClosed S) (hx : x ∈ S)
    (f : σ.obj x ⟶ σ.obj x)
    (hf : ¬ IsUnit f.hom.hom) :
    FactorsThroughAdd σ (S \ {x}) f := by
  let Y : FGModuleCat.{w} R := endRange f
  let q : σ.obj x ⟶ Y :=
    FGModuleCat.ofHom f.hom.hom.rangeRestrict
  let m : Y ⟶ σ.obj x :=
    FGModuleCat.ofHom (LinearMap.range f.hom.hom).subtype

  have hclosed :
      (σ.generated S).carrier.IsClosedUnderQuotients :=
    (qClosed_iff_generated_isClosedUnderQuotients σ S).1 hS
  have hqsurj : Function.Surjective q.hom.hom := by
    exact LinearMap.surjective_rangeRestrict f.hom.hom
  letI : Epi q := (fg_epi_iff_surjective q).2 hqsurj
  have hY : σ.InAdd S Y :=
    hclosed.prop_of_epi q (inAdd_obj σ hx)

  exact
    notIsUnit_endomorphism_factorsThroughAdd_sdiff_of_range_inAdd
      σ f hf hY

/-- Exact dual of the quotient-closed factorization theorem: for a
subobject-closed support, the range of a nonunit endomorphism is a selected
subobject and hence factors through the additive closure after deleting the
indecomposable label. -/
theorem notIsUnit_endomorphism_factorsThroughAdd_sdiff_of_sClosed
    {S : Set ι} {x : ι}
    (hS : σ.sClosure.IsClosed S) (hx : x ∈ S)
    (f : σ.obj x ⟶ σ.obj x)
    (hf : ¬ IsUnit f.hom.hom) :
    FactorsThroughAdd σ (S \ {x}) f := by
  let Y : FGModuleCat.{w} R := endRange f
  let m : Y ⟶ σ.obj x :=
    FGModuleCat.ofHom (LinearMap.range f.hom.hom).subtype
  have hclosed :
      (σ.generated S).carrier.IsClosedUnderSubobjects :=
    (sClosed_iff_generated_isClosedUnderSubobjects σ S).1 hS
  have hminj : Function.Injective m.hom.hom :=
    Subtype.val_injective
  letI : Mono m := (fg_mono_iff_injective m).2 hminj
  have hY : σ.InAdd S Y :=
    hclosed.prop_of_mono m (inAdd_obj σ hx)
  exact
    notIsUnit_endomorphism_factorsThroughAdd_sdiff_of_range_inAdd
      σ f hf hY

/-- Jacobson-radical form of the subobject-closed one-point
factorization theorem. -/
theorem radicalEndomorphism_factorsThroughAdd_sdiff_of_sClosed
    {S : Set ι} {x : ι}
    (hS : σ.sClosure.IsClosed S) (hx : x ∈ S)
    (f : σ.obj x ⟶ σ.obj x)
    (hf :
      f.hom.hom ∈
        Ring.jacobson (Module.End R (σ.obj x))) :
    FactorsThroughAdd σ (S \ {x}) f := by
  apply
    notIsUnit_endomorphism_factorsThroughAdd_sdiff_of_sClosed
      σ hS hx f
  exact
    (QuotientSubmoduleEquidistribution.mem_end_jacobson_iff_not_isUnit
      (σ.indecomposable x) (σ.finiteLength x)
      f.hom.hom).1 hf

/-- Jacobson-radical formulation of the one-point factorization theorem. -/
theorem radicalEndomorphism_factorsThroughAdd_sdiff
    {S : Set ι} {x : ι}
    (hS : σ.qClosure.IsClosed S) (hx : x ∈ S)
    (f : σ.obj x ⟶ σ.obj x)
    (hf :
      f.hom.hom ∈
        Ring.jacobson (Module.End R (σ.obj x))) :
    FactorsThroughAdd σ (S \ {x}) f := by
  apply notIsUnit_endomorphism_factorsThroughAdd_sdiff
    σ hS hx f
  exact
    (QuotientSubmoduleEquidistribution.mem_end_jacobson_iff_not_isUnit
      (σ.indecomposable x) (σ.finiteLength x)
      f.hom.hom).1 hf

/-- A relative split-projective deletion is legal, and all radical
endomorphisms of its removed point factor through the lower additive
subcategory. This packages exactly the one-point module calculation in a
maximal quotient-closed chain. -/
theorem relativeSplitProjective_deletion_radical_factorization
    {S : Set ι} {x : ι}
    (hS : σ.qClosure.IsClosed S) (hx : x ∈ S)
    (hproj : σ.IsRelativeSplitProjective S x) :
    σ.qClosure.IsClosed (S \ {x}) ∧
      ∀ (f : σ.obj x ⟶ σ.obj x),
        f.hom.hom ∈
            Ring.jacobson (Module.End R (σ.obj x)) →
          FactorsThroughAdd σ (S \ {x}) f := by
  constructor
  · exact
      QuotientSubmoduleEquidistribution.SetClosure.isClosed_sdiff_singleton_of_not_mem_closure
        hS
        (not_mem_qClosure_sdiff_of_isRelativeSplitProjective
          σ S x hproj)
  · intro f hf
    exact radicalEndomorphism_factorsThroughAdd_sdiff
      σ hS hx f hf

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
