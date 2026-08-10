import QuotientSubmoduleEquidistribution.RepresentationDirected.EffectiveLiftingComplement
import QuotientSubmoduleEquidistribution.RepresentationTheory.FacSub

/-!
# Additive-closure adapter for effective lifting

Bijectivity of postcomposition on the selected indecomposable
representatives extends to every object in their finite additive closure.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.RepresentationDirected

universe u uIota

variable (K R : Type u) [Field K] [Ring R] [Algebra K R]
  [IsNoetherianRing R]
  {Iota : Type uIota}
  (sigma : IndecomposableSkeleton.{u, uIota, u} R Iota)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- Bijectivity on selected indecomposable representatives extends to
every object with a finite additive presentation by those representatives. -/
theorem postcompLinearMap_bijective_of_addPresentation
    {S : Set Iota} {U T Y : FGModuleCat.{u} R}
    (f : T ⟶ Y) (P : sigma.AddPresentation S U)
    (hf : ∀ a, a ∈ S → Function.Bijective
      (postcompLinearMap (K := K) (X := sigma.obj a) f)) :
    Function.Bijective (postcompLinearMap (K := K) (X := U) f) := by
  constructor
  · intro a b hab
    change a ≫ f = b ≫ f at hab
    apply (cancel_epi P.iso.inv).1
    apply biproduct.hom_ext'
    intro j
    apply (hf (P.label j) (P.mem j)).1
    change
      (biproduct.ι (fun t ↦ sigma.obj (P.label t)) j ≫ P.iso.inv ≫ a) ≫ f =
        (biproduct.ι (fun t ↦ sigma.obj (P.label t)) j ≫ P.iso.inv ≫ b) ≫ f
    simpa only [Category.assoc] using congrArg
      (fun q ↦ biproduct.ι (fun t ↦ sigma.obj (P.label t)) j ≫ P.iso.inv ≫ q) hab
  · intro y
    have hcomponent (j : P.index) : ∃ x : sigma.obj (P.label j) ⟶ T,
        x ≫ f = biproduct.ι (fun t ↦ sigma.obj (P.label t)) j ≫ P.iso.inv ≫ y := by
      exact (hf (P.label j) (P.mem j)).2
        (biproduct.ι (fun t ↦ sigma.obj (P.label t)) j ≫ P.iso.inv ≫ y)
    choose x hx using hcomponent
    let xsum : sigma.sumOver P.index P.label ⟶ T := biproduct.desc x
    refine ⟨P.iso.hom ≫ xsum, ?_⟩
    change (P.iso.hom ≫ xsum) ≫ f = y
    apply (cancel_epi P.iso.inv).1
    apply biproduct.hom_ext'
    intro j
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, xsum,
      biproduct.ι_desc_assoc] using hx j

/-- Pointwise bijectivity on a set of skeleton labels implies bijectivity
on every object of its additive closure. -/
theorem postcompLinearMap_bijective_of_inAdd
    {S : Set Iota} {U T Y : FGModuleCat.{u} R}
    (f : T ⟶ Y) (hU : sigma.InAdd S U)
    (hf : ∀ a, a ∈ S → Function.Bijective
      (postcompLinearMap (K := K) (X := sigma.obj a) f)) :
    Function.Bijective (postcompLinearMap (K := K) (X := U) f) :=
  postcompLinearMap_bijective_of_addPresentation K R sigma f
    (Classical.choice hU) hf

end QuotientSubmoduleEquidistribution.RepresentationDirected
