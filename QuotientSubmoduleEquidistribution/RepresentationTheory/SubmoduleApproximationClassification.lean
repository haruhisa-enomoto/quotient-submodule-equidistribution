import QuotientSubmoduleEquidistribution.RepresentationTheory.ApproximationClassification
import QuotientSubmoduleEquidistribution.RepresentationTheory.ContragredientDuality
import QuotientSubmoduleEquidistribution.RepresentationTheory.DualityConsequences
import QuotientSubmoduleEquidistribution.RepresentationTheory.ConormalModules

/-!
# Submodule approximation classification

This file transports approximations through anti-equivalences and applies
concrete contragredient duality to complete the submodule-side classification
of compact and functorially finite closed additive subcategories.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe uR uS wR wS

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {S : Type uS} [Ring S] [IsNoetherianRing S]

/-- Pull an object predicate backwards through an anti-equivalence. -/
def AntiPull
    (E : (FGModuleCat.{wR} R)ᵒᵖ ≌ FGModuleCat.{wS} S)
    (C : FGModuleCat.{wR} R → Prop) :
    FGModuleCat.{wS} S → Prop :=
  fun Y ↦ C (E.inverse.obj Y).unop

/-- The repleteness property needed to transport approximations through
the unit isomorphism of an anti-equivalence. -/
def IsRepletePredicate
    (C : FGModuleCat.{wR} R → Prop) : Prop :=
  ∀ {X Y : FGModuleCat.{wR} R}, (X ≅ Y) → C X → C Y

/-- The counit component with its identity-functor target normalized
definitionally to the underlying object. -/
def normalizedCounitIso
    (E : (FGModuleCat.{wR} R)ᵒᵖ ≌ FGModuleCat.{wS} S)
    (Y : FGModuleCat.{wS} S) :
    (E.inverse ⋙ E.functor).obj Y ≅ Y :=
  E.counitIso.app Y

/-- A right approximation becomes a left approximation under an
anti-equivalence. -/
def rightApproximationToLeft
    (E : (FGModuleCat.{wR} R)ᵒᵖ ≌ FGModuleCat.{wS} S)
    {C : FGModuleCat.{wR} R → Prop}
    (hC : IsRepletePredicate C)
    (Y : FGModuleCat.{wS} S)
    (A : RightApproximation C (E.inverse.obj Y).unop) :
    LeftApproximation (AntiPull E C) Y := by
  let pOp :
      E.inverse.obj Y ⟶ Opposite.op A.object := by
    simpa using A.map.op
  let mappedP :
      (E.inverse ⋙ E.functor).obj Y ⟶
        E.functor.obj (Opposite.op A.object) :=
    E.functor.map pOp
  refine {
    object := E.functor.obj (Opposite.op A.object)
    mem := ?_
    map := (normalizedCounitIso E Y).inv ≫ mappedP
    factors := ?_ }
  · apply hC (Iso.unop (E.unitIso.app (Opposite.op A.object))).symm
    exact A.mem
  · intro Z hZ f
    obtain ⟨g, hg⟩ :=
      A.factors hZ (E.inverse.map f).unop
    let gOp :
        Opposite.op A.object ⟶ E.inverse.obj Z := by
      simpa using g.op
    let mappedG :
        E.functor.obj (Opposite.op A.object) ⟶
          (E.inverse ⋙ E.functor).obj Z :=
      E.functor.map gOp
    refine ⟨mappedG ≫ (normalizedCounitIso E Z).hom, ?_⟩
    have hop : pOp ≫ gOp = E.inverse.map f := by
      apply Quiver.Hom.unop_inj
      simpa [pOp, gOp] using hg
    have hmaps :
        mappedP ≫ mappedG =
          (E.inverse ⋙ E.functor).map f := by
      change
        E.functor.map pOp ≫ E.functor.map gOp =
          E.functor.map (E.inverse.map f)
      rw [← E.functor.map_comp, hop]
    have hfg :
        (E.inverse ⋙ E.functor).map f =
          (normalizedCounitIso E Y).hom ≫
            f ≫ (normalizedCounitIso E Z).inv := by
      change
        E.functor.map (E.inverse.map f) =
          (E.counitIso.app Y).hom ≫
            f ≫ (E.counitIso.app Z).inv
      exact E.fun_inv_map Y Z f
    simp only [Category.assoc]
    slice_lhs 2 3 => rw [hmaps, hfg]
    simp

/-- A left approximation becomes a right approximation under an
anti-equivalence. -/
def leftApproximationToRight
    (E : (FGModuleCat.{wR} R)ᵒᵖ ≌ FGModuleCat.{wS} S)
    {C : FGModuleCat.{wR} R → Prop}
    (hC : IsRepletePredicate C)
    (Y : FGModuleCat.{wS} S)
    (A : LeftApproximation C (E.inverse.obj Y).unop) :
    RightApproximation (AntiPull E C) Y := by
  let pOp :
      Opposite.op A.object ⟶ E.inverse.obj Y := by
    simpa using A.map.op
  let mappedP :
      E.functor.obj (Opposite.op A.object) ⟶
        (E.inverse ⋙ E.functor).obj Y :=
    E.functor.map pOp
  refine {
    object := E.functor.obj (Opposite.op A.object)
    mem := ?_
    map := mappedP ≫ (normalizedCounitIso E Y).hom
    factors := ?_ }
  · apply hC (Iso.unop (E.unitIso.app (Opposite.op A.object))).symm
    exact A.mem
  · intro Z hZ f
    obtain ⟨g, hg⟩ :=
      A.factors hZ (E.inverse.map f).unop
    let gOp :
        E.inverse.obj Z ⟶ Opposite.op A.object := by
      simpa using g.op
    let mappedG :
        (E.inverse ⋙ E.functor).obj Z ⟶
          E.functor.obj (Opposite.op A.object) :=
      E.functor.map gOp
    refine ⟨(normalizedCounitIso E Z).inv ≫ mappedG, ?_⟩
    have hop : gOp ≫ pOp = E.inverse.map f := by
      apply Quiver.Hom.unop_inj
      simpa [pOp, gOp] using hg
    have hmaps :
        mappedG ≫ mappedP =
          (E.inverse ⋙ E.functor).map f := by
      change
        E.functor.map gOp ≫ E.functor.map pOp =
          E.functor.map (E.inverse.map f)
      rw [← E.functor.map_comp, hop]
    have hfg :
        (E.inverse ⋙ E.functor).map f =
          (normalizedCounitIso E Z).hom ≫
            f ≫ (normalizedCounitIso E Y).inv := by
      change
        E.functor.map (E.inverse.map f) =
          (E.counitIso.app Z).hom ≫
            f ≫ (E.counitIso.app Y).inv
      exact E.fun_inv_map Z Y f
    simp only [Category.assoc]
    slice_lhs 2 3 => rw [hmaps, hfg]
    simp

omit [IsNoetherianRing R] [IsNoetherianRing S] in
/-- Functorial finiteness transports forward through an anti-equivalence. -/
theorem antiPull_functoriallyFinite
    (E : (FGModuleCat.{wR} R)ᵒᵖ ≌ FGModuleCat.{wS} S)
    {C : FGModuleCat.{wR} R → Prop}
    (hC : IsRepletePredicate C)
    (hff : IsFunctoriallyFinite C) :
    IsFunctoriallyFinite (AntiPull E C) := by
  constructor
  · intro Y
    obtain ⟨A⟩ := hff.2 (E.inverse.obj Y).unop
    exact ⟨leftApproximationToRight E hC Y A⟩
  · intro Y
    obtain ⟨A⟩ := hff.1 (E.inverse.obj Y).unop
    exact ⟨rightApproximationToLeft E hC Y A⟩

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

namespace AlignedAntiEquivalence

universe vR vS

variable {ι : Type vR} {κ : Type vS}
  (σ : IndecomposableSkeleton.{uR, vR, wR} R ι)
  (τ : IndecomposableSkeleton.{uS, vS, wS} S κ)
  (D : AlignedAntiEquivalence σ τ)

/-- Arbitrary-object version of `facToSubObj`: a quotient presentation
dualizes to a submodule presentation of the actual dual object. -/
def facToSub {T : Set ι} {X : FGModuleCat.{wR} R}
    (P : σ.FacPresentation T X) :
    τ.SubPresentation (D.labelEquiv '' T)
      (D.categoryEquiv.functor.obj (Opposite.op X)) where
  index := P.index
  label := fun t ↦ D.labelEquiv (P.label t)
  mem t := ⟨P.label t, P.mem t, rfl⟩
  map :=
    D.categoryEquiv.functor.map P.map.op ≫
      (D.sumIso σ τ P.index P.label).hom
  mono := by
    letI : Epi P.map := P.epi
    infer_instance

/-- Arbitrary-object version of `subToFacObj`: a submodule presentation
dualizes to a quotient presentation of the actual dual object. -/
def subToFac {T : Set ι} {X : FGModuleCat.{wR} R}
    (P : σ.SubPresentation T X) :
    τ.FacPresentation (D.labelEquiv '' T)
      (D.categoryEquiv.functor.obj (Opposite.op X)) where
  index := P.index
  label := fun t ↦ D.labelEquiv (P.label t)
  mem t := ⟨P.label t, P.mem t, rfl⟩
  map :=
    (D.sumIso σ τ P.index P.label).inv ≫
      D.categoryEquiv.functor.map P.map.op
  epi := by
    letI : Mono P.map := P.mono
    infer_instance

end AlignedAntiEquivalence

/-- `InFac` is invariant under isomorphism of the presented object. -/
theorem inFac_iso_iff
    {ι : Type vR}
    (σ : IndecomposableSkeleton.{uR, vR, wR} R ι)
    {T : Set ι} {X Y : FGModuleCat.{wR} R}
    (e : X ≅ Y) :
    σ.InFac T X ↔ σ.InFac T Y := by
  constructor
  · rintro ⟨P⟩
    letI : Epi P.map := P.epi
    exact ⟨{
      index := P.index
      label := P.label
      mem := P.mem
      map := P.map ≫ e.hom
      epi := inferInstance }⟩
  · rintro ⟨P⟩
    letI : Epi P.map := P.epi
    exact ⟨{
      index := P.index
      label := P.label
      mem := P.mem
      map := P.map ≫ e.inv
      epi := inferInstance }⟩

/-- `InSub` is invariant under isomorphism of the presented object. -/
theorem inSub_iso_iff
    {ι : Type vR}
    (σ : IndecomposableSkeleton.{uR, vR, wR} R ι)
    {T : Set ι} {X Y : FGModuleCat.{wR} R}
    (e : X ≅ Y) :
    σ.InSub T X ↔ σ.InSub T Y := by
  constructor
  · rintro ⟨P⟩
    letI : Mono P.map := P.mono
    exact ⟨{
      index := P.index
      label := P.label
      mem := P.mem
      map := e.inv ≫ P.map
      mono := inferInstance }⟩
  · rintro ⟨P⟩
    letI : Mono P.map := P.mono
    exact ⟨{
      index := P.index
      label := P.label
      mem := P.mem
      map := e.hom ≫ P.map
      mono := inferInstance }⟩

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe u v w

variable (K R : Type u)
  [Field K] [Ring R] [Algebra K R] [FiniteDimensional K R]
  [IsNoetherianRing R] [IsNoetherianRing Rᵐᵒᵖ]
  {ι : Type v} {κ : Type w}
  (σ : IndecomposableSkeleton.{u, v, u} R ι)
  (τ : IndecomposableSkeleton.{u, w, u} Rᵐᵒᵖ κ)

/-- Concrete contragredient duality exchanges arbitrary submodule
presentations with quotient presentations, not merely presentations of
chosen indecomposable representatives. -/
theorem inFac_dual_iff_inSub
    (T : Set ι) (X : FGModuleCat.{u} R) :
    τ.InFac
        (Contragredient.dualLabelEquiv K R σ τ '' T)
        ((Contragredient.dualFunctor K R).obj (Opposite.op X)) ↔
      σ.InSub T X := by
  let D := Contragredient.alignedBiduality K R σ τ
  constructor
  · rintro ⟨P⟩
    let Q :=
      AlignedAntiEquivalence.facToSub τ σ D.backward P
    have hQ :
        σ.InSub
            ((Contragredient.dualLabelEquiv K R σ τ).symm ''
              (Contragredient.dualLabelEquiv K R σ τ '' T))
            ((Contragredient.reverseDualFunctor K R).obj
              (Opposite.op
                ((Contragredient.dualFunctor K R).obj
                  (Opposite.op X)))) := by
      exact ⟨Q⟩
    have hQ' :
        σ.InSub T
            ((Contragredient.reverseDualFunctor K R).obj
              (Opposite.op
                ((Contragredient.dualFunctor K R).obj
                  (Opposite.op X)))) := by
      simpa only [Equiv.symm_image_image] using hQ
    exact
      (inSub_iso_iff σ
        (Contragredient.forwardBidualIso K R X)).2 hQ'
  · rintro ⟨P⟩
    exact ⟨AlignedAntiEquivalence.subToFac σ τ D.forward P⟩

/-- The support-level submodule predicate is the pullback of the
dual quotient predicate along the concrete equivalence. -/
theorem antiPull_inSub_eq_inFac
    (T : Set ι) :
    AntiPull (Contragredient.dualityEquivalence K R) (σ.InSub T) =
      τ.InFac
        (Contragredient.dualLabelEquiv K R σ τ '' T) := by
  funext Y
  apply propext
  change
    σ.InSub T
        ((Contragredient.reverseDualFunctor K R).obj
          (Opposite.op Y)) ↔
      τ.InFac
        (Contragredient.dualLabelEquiv K R σ τ '' T) Y
  calc
    σ.InSub T
        ((Contragredient.reverseDualFunctor K R).obj
          (Opposite.op Y)) ↔
        τ.InFac
          (Contragredient.dualLabelEquiv K R σ τ '' T)
          ((Contragredient.dualFunctor K R).obj
            (Opposite.op
              ((Contragredient.reverseDualFunctor K R).obj
                (Opposite.op Y)))) :=
      (inFac_dual_iff_inSub K R σ τ T
        ((Contragredient.reverseDualFunctor K R).obj
          (Opposite.op Y))).symm
    _ ↔
        τ.InFac
          (Contragredient.dualLabelEquiv K R σ τ '' T) Y :=
      (inFac_iso_iff τ
        (Contragredient.reverseBidualIso K R Y)).symm

/-- In the reverse concrete anti-equivalence, pulling back the dual
quotient predicate is exactly the original submodule predicate. -/
theorem antiPull_reverse_inFac_eq_inSub
    (T : Set ι) :
    AntiPull
        (Contragredient.reverseDualityEquivalence K R)
        (τ.InFac
          (Contragredient.dualLabelEquiv K R σ τ '' T)) =
      σ.InSub T := by
  funext X
  exact propext (inFac_dual_iff_inSub K R σ τ T X)

omit [IsNoetherianRing Rᵐᵒᵖ] in
/-- Support-level `InFac` predicates are replete. -/
theorem inFac_isReplete
    {S : Set ι} :
    IsRepletePredicate (σ.InFac S) := by
  intro X Y e hX
  exact (inFac_iso_iff σ e).1 hX

omit [IsNoetherianRing Rᵐᵒᵖ] in
/-- Support-level `InSub` predicates are replete. -/
theorem inSub_isReplete
    {S : Set ι} :
    IsRepletePredicate (σ.InSub S) := by
  intro X Y e hX
  exact (inSub_iso_iff σ e).1 hX

/-- Functorial finiteness is exchanged exactly by concrete
contragredient duality. -/
theorem inSub_functoriallyFinite_iff_dual_inFac
    (T : Set ι) :
    IsFunctoriallyFinite (σ.InSub T) ↔
      IsFunctoriallyFinite
        (τ.InFac
          (Contragredient.dualLabelEquiv K R σ τ '' T)) := by
  constructor
  · intro h
    have h' :=
      antiPull_functoriallyFinite
        (Contragredient.dualityEquivalence K R)
        (inSub_isReplete R σ) h
    rwa [antiPull_inSub_eq_inFac K R σ τ T] at h'
  · intro h
    have h' :=
      antiPull_functoriallyFinite
        (Contragredient.reverseDualityEquivalence K R)
        (fun e hX ↦ (inFac_iso_iff τ e).1 hX) h
    rwa [antiPull_reverse_inFac_eq_inSub K R σ τ T] at h'

/-- Compact submodule-closed supports are exactly the functorially finite
`InSub` predicates.  This is the submodule-side analogue of the production
finite-`Fac` theorem, obtained by concrete duality. -/
theorem isCompactElement_iff_inSub_functoriallyFinite_sameUniverse
    (K : Type u) [Field K] [Algebra K R] [FiniteDimensional K R]
    (τ : IndecomposableSkeleton.{u, w, u} Rᵐᵒᵖ κ)
    {C : σ.sClosure.Closeds} :
    IsCompactElement C ↔
      IsFunctoriallyFinite (σ.InSub (C : Set ι)) := by
  let D := Contragredient.alignedBiduality K R σ τ
  let e :=
    (AlignedBiduality.sToQClosureRelabeling σ τ D).closedsOrderIso
  calc
    IsCompactElement C ↔ IsCompactElement (e C) :=
      Transport.isCompactElement_iff e C
    _ ↔
        IsFunctoriallyFinite
          (τ.InFac (((e C : τ.qClosure.Closeds) : Set κ))) :=
      isCompactElement_iff_inFac_functoriallyFinite_of_finiteDimensional_sameUniverse
        K τ
    _ ↔
        IsFunctoriallyFinite
          (τ.InFac
            (Contragredient.dualLabelEquiv K R σ τ '' (C : Set ι))) := by
      change
        IsFunctoriallyFinite
            (τ.InFac
              (Contragredient.dualLabelEquiv K R σ τ '' (C : Set ι))) ↔
          IsFunctoriallyFinite
            (τ.InFac
              (Contragredient.dualLabelEquiv K R σ τ '' (C : Set ι)))
      rfl
    _ ↔ IsFunctoriallyFinite (σ.InSub (C : Set ι)) :=
      (inSub_functoriallyFinite_iff_dual_inFac
        K R σ τ (C : Set ι)).symm

omit [IsNoetherianRing Rᵐᵒᵖ] in
/-- Submodule generation depends only on submodule closure. -/
theorem inSub_iff_of_sClosure_eq
    {S T : Set ι} (hST : σ.sClosure S = σ.sClosure T)
    (X : FGModuleCat.{u} R) :
    σ.InSub S X ↔ σ.InSub T X := by
  change σ.sSet S = σ.sSet T at hST
  constructor
  · rintro ⟨P⟩
    let Q : σ.SubPresentation (σ.sSet T) X :=
      { index := P.index
        label := P.label
        mem := fun t ↦ by
          rw [← hST]
          exact subset_sSet σ S (P.mem t)
        map := P.map
        mono := P.mono }
    exact inSub_trans σ Q
  · rintro ⟨P⟩
    let Q : σ.SubPresentation (σ.sSet S) X :=
      { index := P.index
        label := P.label
        mem := fun t ↦ by
          rw [hST]
          exact subset_sSet σ T (P.mem t)
        map := P.map
        mono := P.mono }
    exact inSub_trans σ Q

/-- Literal subobject-closed subcategories are compact exactly when they
are functorially finite. -/
theorem subobjectClosed_isCompactElement_iff_isFunctoriallyFinite_sameUniverse
    (K : Type u) [Field K] [Algebra K R] [FiniteDimensional K R]
    (τ : IndecomposableSkeleton.{u, w, u} Rᵐᵒᵖ κ)
    (C : SubobjectClosedAdditiveSubcategory.{u, u} (R := R)) :
    let _ := subobjectClosedCompleteLattice σ
    IsCompactElement C ↔
      IsFunctoriallyFinite C.1.carrier := by
  letI := subobjectClosedCompleteLattice σ
  calc
    IsCompactElement C ↔
        IsCompactElement (σ.subobjectClosedSupportOrderIso C) :=
      SubobjectLattice.isCompactElement_iff σ C
    _ ↔
        IsFunctoriallyFinite
          (σ.InSub
            ((σ.subobjectClosedSupportOrderIso C :
              σ.sClosure.Closeds) : Set ι)) :=
      isCompactElement_iff_inSub_functoriallyFinite_sameUniverse
        R σ K τ
    _ ↔ IsFunctoriallyFinite C.1.carrier := by
      change
        IsFunctoriallyFinite (σ.InSub (σ.support C.1)) ↔
          IsFunctoriallyFinite C.1.carrier
      rw [subobjectClosedAdditiveSubcategory_carrier_eq_inSub_support
        σ C]

/-- The exact canonical form of a witness `C = Sub M` with `M ∈ C`,
using the basic module containing each indecomposable support label once. -/
structure BasicSubGenerator
    (C : SubobjectClosedAdditiveSubcategory.{u, u} (R := R)) where
  support : FiniteSupport (ι := ι)
  mem : C.1.carrier (σ.basicModule support)
  carrier_eq :
    C.1.carrier =
      InSubOfModule (σ.basicModule support)

omit [IsNoetherianRing Rᵐᵒᵖ] in
/-- Compact literal subobject-closed subcategories are exactly those
cogenerated by one finite basic module. -/
theorem subobjectClosed_isCompactElement_iff_basicSubGenerator
    (C : SubobjectClosedAdditiveSubcategory.{u, u} (R := R)) :
    let _ := subobjectClosedCompleteLattice σ
    IsCompactElement C ↔
      Nonempty (BasicSubGenerator R σ C) := by
  letI := subobjectClosedCompleteLattice σ
  let S := σ.support C.1
  have hcarrier :
      C.1.carrier = σ.InSub S :=
    subobjectClosedAdditiveSubcategory_carrier_eq_inSub_support σ C
  constructor
  · intro hcompact
    have hcompactS :
        IsCompactElement (σ.subobjectClosedSupportOrderIso C) :=
      (SubobjectLattice.isCompactElement_iff σ C).1 hcompact
    obtain ⟨B, hBfinite, hBS, hclosure⟩ :=
      QuotientSubmoduleEquidistribution.SetClosure.exists_finite_generator_of_isCompactElement
        hcompactS
    change σ.sClosure B = S at hclosure
    have hSclosed : σ.sClosure S = S := by
      exact
        (σ.subobjectClosedSupportOrderIso C).2.closure_eq
    have hclosure' : σ.sClosure B = σ.sClosure S :=
      hclosure.trans hSclosed.symm
    let Bfin : FiniteSupport (ι := ι) := ⟨B, hBfinite⟩
    have hbasicB : σ.InSub B (σ.basicModule Bfin) :=
      basicModule_inSub σ Bfin
    have hbasicS : σ.InSub S (σ.basicModule Bfin) :=
      (inSub_iff_of_sClosure_eq R σ hclosure'
        (σ.basicModule Bfin)).1 hbasicB
    refine ⟨{
      support := Bfin
      mem := by
        rw [hcarrier]
        exact hbasicS
      carrier_eq := ?_ }⟩
    funext X
    apply propext
    constructor
    · intro hX
      have hXS : σ.InSub S X := by
        rw [← hcarrier]
        exact hX
      have hXB : σ.InSub B X :=
        (inSub_iff_of_sClosure_eq R σ hclosure' X).2 hXS
      exact
        (inSubOfModule_basicModule_iff σ Bfin X).2 hXB
    · intro hX
      have hXB : σ.InSub B X :=
        (inSubOfModule_basicModule_iff σ Bfin X).1 hX
      have hXS : σ.InSub S X :=
        (inSub_iff_of_sClosure_eq R σ hclosure' X).1 hXB
      rw [hcarrier]
      exact hXS
  · rintro ⟨W⟩
    have hclosure : σ.sClosure W.support.1 = S := by
      ext i
      rw [mem_sClosure_iff_inSub σ W.support.1 i]
      change
        σ.InSub W.support.1 (σ.obj i) ↔
          C.1.carrier (σ.obj i)
      rw [W.carrier_eq,
        inSubOfModule_basicModule_iff σ W.support (σ.obj i)]
    have hcompactClosure :
        IsCompactElement
          (σ.sClosure.toCloseds W.support.1) :=
      QuotientSubmoduleEquidistribution.SetClosure.finiteClosure_isCompactElement
        (sClosure_isFinitary σ) W.support.2
    have hEq :
        σ.sClosure.toCloseds W.support.1 =
          σ.subobjectClosedSupportOrderIso C := by
      apply Subtype.ext
      exact hclosure
    apply (SubobjectLattice.isCompactElement_iff σ C).2
    exact hEq ▸ hcompactClosure

/-- A literal subobject-closed subcategory is functorially finite exactly
when it is `Sub` of one finite basic module belonging to it. -/
theorem subobjectClosed_isFunctoriallyFinite_iff_basicSubGenerator_sameUniverse
    (K : Type u) [Field K] [Algebra K R] [FiniteDimensional K R]
    (τ : IndecomposableSkeleton.{u, w, u} Rᵐᵒᵖ κ)
    (C : SubobjectClosedAdditiveSubcategory.{u, u} (R := R)) :
    IsFunctoriallyFinite C.1.carrier ↔
      Nonempty (BasicSubGenerator R σ C) := by
  letI := subobjectClosedCompleteLattice σ
  exact
    (subobjectClosed_isCompactElement_iff_isFunctoriallyFinite_sameUniverse
      R σ K τ C).symm.trans
      (subobjectClosed_isCompactElement_iff_basicSubGenerator R σ C)

/-- The three exact submodule-side paper conditions: compactness,
generation as `Sub` of one finite basic module, and functorial finiteness. -/
theorem subobjectClosed_compact_iff_basicSubGenerator_iff_functoriallyFinite
    (K : Type u) [Field K] [Algebra K R] [FiniteDimensional K R]
    (τ : IndecomposableSkeleton.{u, w, u} Rᵐᵒᵖ κ)
    (C : SubobjectClosedAdditiveSubcategory.{u, u} (R := R)) :
    let _ := subobjectClosedCompleteLattice σ
    (IsCompactElement C ↔
        Nonempty (BasicSubGenerator R σ C)) ∧
      (Nonempty (BasicSubGenerator R σ C) ↔
        IsFunctoriallyFinite C.1.carrier) := by
  letI := subobjectClosedCompleteLattice σ
  have hcompact :=
    subobjectClosed_isCompactElement_iff_basicSubGenerator R σ C
  have hff :=
    subobjectClosed_isCompactElement_iff_isFunctoriallyFinite_sameUniverse
      R σ K τ C
  exact ⟨hcompact, hcompact.symm.trans hff⟩

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
