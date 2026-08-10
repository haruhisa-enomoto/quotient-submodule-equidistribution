import Mathlib.CategoryTheory.Abelian.Subobject
import Mathlib.Algebra.Category.ModuleCat.Subobject
import OpConjecture.RepresentationTheory.ContragredientDuality
import OpConjecture.RepresentationTheory.LengthTwoGabrielBridge

/-!
# Contragredient transport for the length-two pair

An aligned anti-equivalence already preserves composition length: its
equivalence identifies subobjects of the dual object with quotient objects
of the original object.  Consequently it also turns a chosen simple
submodule into a chosen simple quotient with the expected label.
-/

noncomputable section

open Set
open CategoryTheory CategoryTheory.Limits

namespace OpConjecture.LengthTwoGabrielBridge

universe uR uS vR vS wR wS

namespace IndecomposableSkeleton

variable
    {R : Type uR} [Ring R] [IsNoetherianRing R]
    {S : Type uS} [Ring S] [IsNoetherianRing S]
    {ι : Type vR} {κ : Type vS}
    (σ :
      _root_.OpConjecture.IndecomposableSkeleton.{uR, vR, wR}
        R ι)
    (τ :
      _root_.OpConjecture.IndecomposableSkeleton.{uS, vS, wS}
        S κ)

local instance submoduleSubtypeMono
    (M : FGModuleCat.{wR} R) (N : Submodule R M) :
    Mono (FGModuleCat.ofHom N.subtype) :=
  ConcreteCategory.mono_of_injective _
    N.subtype_injective

/--
For a Noetherian ring, categorical subobjects in `FGModuleCat` are the
same as concrete submodules.  This is the finitely generated analogue
of Mathlib's `ModuleCat.subobjectModule`.
-/
noncomputable def fgSubobjectModule (M : FGModuleCat.{wR} R) :
    Subobject M ≃o Submodule R M :=
  OrderIso.symm
    { invFun := fun P =>
        LinearMap.range P.arrow.hom.hom
      toFun := fun N =>
        Subobject.mk (FGModuleCat.ofHom N.subtype)
      right_inv := fun P => Eq.symm (by
        fapply Subobject.eq_mk_of_comm
        · apply LinearEquiv.toFGModuleCatIso
          apply LinearEquiv.ofBijective
            (LinearMap.codRestrict
              (LinearMap.range P.arrow.hom.hom)
              P.arrow.hom.hom _)
          constructor
          · intro x y hxy
            apply
              (_root_.OpConjecture.IndecomposableSkeleton.fg_mono_iff_injective
                P.arrow).1 inferInstance
            exact congrArg Subtype.val hxy
          · rw [← LinearMap.range_eq_top,
              LinearMap.range_codRestrict,
              Submodule.comap_subtype_self]
            exact LinearMap.mem_range_self _
        · ext x
          rfl)
      left_inv := fun N => by
        let f := FGModuleCat.ofHom N.subtype
        let e :=
          FGModuleCat.isoToLinearEquiv
            (Subobject.underlyingIso f).symm
        have hinv :
            (Subobject.underlyingIso f).inv =
              FGModuleCat.ofHom e.toLinearMap := by
          apply FGModuleCat.hom_ext
          ext x
          rfl
        have hcat := Subobject.underlyingIso_arrow f
        rw [hinv] at hcat
        have hlin :=
          congrArg (fun q => q.hom.hom) hcat
        change
          (Subobject.mk f).arrow.hom.hom.comp e.toLinearMap =
            N.subtype at hlin
        have hrange := congrArg LinearMap.range hlin
        rw [LinearEquiv.range_comp] at hrange
        exact hrange.trans (Submodule.range_subtype N)
      map_rel_iff' := fun {P Q} => by
        refine ⟨fun h => ?_, fun h =>
          Subobject.mk_le_mk_of_comm
            (FGModuleCat.ofHom
              (Submodule.inclusion h)) rfl⟩
        convert! LinearMap.range_comp_le_range
          (Subobject.ofMkLEMk _ _ h).hom.hom
          (FGModuleCat.ofHom Q.subtype).hom.hom
        · rw [← FGModuleCat.hom_hom_comp,
            Subobject.ofMkLEMk_comp]
          exact (Submodule.range_subtype _).symm
        · exact (Submodule.range_subtype _).symm }

namespace AlignedAntiEquivalence

variable
    (D :
      _root_.OpConjecture.IndecomposableSkeleton.AlignedAntiEquivalence
        σ τ)

/--
The submodule lattice of an object is order-isomorphic to the order dual
of the submodule lattice of its image under an aligned anti-equivalence.
-/
def subobjectOrderIso (i : ι) :
    Subobject (σ.obj i) ≃o
      (Subobject (τ.obj (D.labelEquiv i)))ᵒᵈ :=
  (CategoryTheory.Abelian.subobjectIsoSubobjectOp (σ.obj i)).trans <|
    ((Subobject.lowerEquivalence
      (MonoOver.congr (Opposite.op (σ.obj i))
        D.categoryEquiv)).toOrderIso.dual).trans <|
      (Subobject.mapIsoToOrderIso (D.objIso i)).dual

/--
The preceding categorical order isomorphism, written on the concrete
module submodule lattices used in the definition of `Module.length`.
-/
def moduleSubobjectOrderIso (i : ι) :
    Submodule R (σ.obj i) ≃o
      (Submodule S (τ.obj (D.labelEquiv i)))ᵒᵈ :=
  (fgSubobjectModule (R := R) (σ.obj i)).symm |>.trans <|
    (subobjectOrderIso σ τ D i).trans <|
      (fgSubobjectModule (R := S)
        (τ.obj (D.labelEquiv i))).dual

/-- An aligned anti-equivalence preserves module composition length. -/
theorem module_length_eq (i : ι) :
    Module.length R (σ.obj i) =
      Module.length S (τ.obj (D.labelEquiv i)) := by
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length]
  calc
    Order.krullDim (Submodule R (σ.obj i)) =
        Order.krullDim
          ((Submodule S (τ.obj (D.labelEquiv i)))ᵒᵈ) :=
      Order.krullDim_eq_of_orderIso
        (moduleSubobjectOrderIso σ τ D i)
    _ = Order.krullDim
          (Submodule S (τ.obj (D.labelEquiv i))) := by
      rw [Order.krullDim_orderDual]

/-- The natural-valued composition length on aligned skeletons is preserved. -/
theorem compositionLength_eq (i : ι) :
    τ.compositionLength (D.labelEquiv i) =
      σ.compositionLength i := by
  unfold _root_.OpConjecture.IndecomposableSkeleton.compositionLength
  rw [module_length_eq σ τ D i]

/--
A chosen simple submodule dualizes to a chosen simple quotient, and its
skeleton label is exactly the image of the original simple label.
-/
def simpleQuotientOfSimpleSubmodule
    {x : ι} (Q : σ.SimpleSubmodule x) :
    τ.SimpleQuotient (D.labelEquiv x) where
  index := D.labelEquiv Q.index
  simple := by
    rw [← τ.compositionLength_eq_one_iff_simple]
    rw [compositionLength_eq σ τ D]
    exact (σ.compositionLength_eq_one_iff_simple Q.index).2 Q.simple
  map :=
    (D.objIso x).inv ≫
      D.categoryEquiv.functor.map Q.map.op ≫
      (D.objIso Q.index).hom
  epi := by
    letI : Mono Q.map := Q.mono
    infer_instance

end AlignedAntiEquivalence

namespace AlignedBiduality

variable
    (D :
      _root_.OpConjecture.IndecomposableSkeleton.AlignedBiduality
        σ τ)

/--
The objectwise data formerly required by the dual endpoint is automatic:
length is preserved, the chosen simple submodule dualizes to the expected
simple quotient, and the dual object has a simple submodule.
-/
def lengthTwoSubPairData
    {x : ι} (hx : σ.compositionLength x = 2)
    (Q : σ.SimpleSubmodule x) :
    _root_.OpConjecture.LengthTwoGabrielBridge.AlignedBiduality.LengthTwoSubPairData
      σ τ D x Q.index where
  length := by
    rw [AlignedAntiEquivalence.compositionLength_eq
      σ τ D.forward]
    exact hx
  top :=
    AlignedAntiEquivalence.simpleQuotientOfSimpleSubmodule
      σ τ D.forward Q
  top_index := rfl
  socle := Classical.choice
    (τ.exists_simpleSubmodule (D.forward.labelEquiv x))

/--
Data-free dual endpoint: a quotient-side isotypic-Loewy-two
classification on the target proves closure of every length-two
source/socle pair.
-/
theorem sClosure_isClosed_length_two_pair_of_dual_isotypicLoewyTwo
    (D :
      _root_.OpConjecture.IndecomposableSkeleton.AlignedBiduality
        σ τ)
    {x : ι} (hx : σ.compositionLength x = 2)
    (Q : σ.SimpleSubmodule x)
    (hclassification :
      _root_.OpConjecture.LengthTwoGabrielBridge.IndecomposableSkeleton.IsotypicLoewyTwoIndecomposablesHaveSimpleTop
        τ) :
    σ.sClosure.IsClosed ({x, Q.index} : Set ι) := by
  rw [
    _root_.OpConjecture.LengthTwoGabrielBridge.AlignedBiduality.sClosure_isClosed_iff_qClosure_image
      σ τ D]
  let top :=
    AlignedAntiEquivalence.simpleQuotientOfSimpleSubmodule
      σ τ D.forward Q
  let socle :=
    Classical.choice
      (τ.exists_simpleSubmodule (D.forward.labelEquiv x))
  have hlength :
      τ.compositionLength (D.forward.labelEquiv x) = 2 := by
    rw [AlignedAntiEquivalence.compositionLength_eq
      σ τ D.forward]
    exact hx
  have hq :=
    _root_.OpConjecture.LengthTwoGabrielBridge.IndecomposableSkeleton.qClosure_isClosed_length_two_top_pair_of_isotypicLoewyTwo
      τ hclassification hlength top socle
  have himage :
      D.forward.labelEquiv '' ({x, Q.index} : Set ι) =
        ({D.forward.labelEquiv x,
          D.forward.labelEquiv Q.index} : Set κ) := by
    rw [Set.image_insert_eq, Set.image_singleton]
  rw [himage]
  exact hq

end AlignedBiduality

end IndecomposableSkeleton

end OpConjecture.LengthTwoGabrielBridge
