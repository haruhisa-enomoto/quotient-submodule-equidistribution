import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.CategoryTheory.Adjunction.Basic
import QuotientSubmoduleEquidistribution.RepresentationTheory.Approximation

/-!
# Trace and right rejective subcategories

This file packages the already formalized trace universal property as an
actual right adjoint to the inclusion of the generated full subcategory.
-/

noncomputable section

open Set
open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe u v w

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)

/-- Data expressing the paper's definition of a right rejective full
subcategory: the inclusion has a right adjoint with monic counit. -/
structure RightRejectiveData
    (C : AdditiveRepleteSummandSubcategory.{u, w} (R := R)) where
  coreflector :
    FGModuleCat.{w} R ⥤ C.carrier.FullSubcategory
  adjunction : C.carrier.ι ⊣ coreflector
  counit_mono :
    ∀ X : FGModuleCat.{w} R,
      Mono (adjunction.counit.app X)

/-- Propositional form of right rejectivity. -/
def IsRightRejective
    (C : AdditiveRepleteSummandSubcategory.{u, w} (R := R)) : Prop :=
  Nonempty (RightRejectiveData C)

/-- Additive membership always implies quotient generation. -/
theorem inFac_of_inAdd
    {S : Set ι} {X : FGModuleCat.{w} R}
    (hX : σ.InAdd S X) :
    σ.InFac S X := by
  obtain ⟨P⟩ := hX
  exact ⟨{
    index := P.index
    label := P.label
    mem := P.mem
    map := P.iso.inv
    epi := inferInstance }⟩

/-- The trace object, regarded as an object of `add S` under the explicit
trace-membership hypothesis. -/
def traceCoreflectorObj
    (S : Set ι)
    (htrace : ∀ X : FGModuleCat.{w} R,
      σ.InAdd S (σ.traceObject S X))
    (X : FGModuleCat.{w} R) :
    (σ.generated S).carrier.FullSubcategory :=
  ⟨σ.traceObject S X, htrace X⟩

/-- Maps from an object of `add S` to `X` are uniquely the maps to the
trace object, followed by the trace inclusion. -/
def traceHomEquiv
    (S : Set ι)
    (htrace : ∀ X : FGModuleCat.{w} R,
      σ.InAdd S (σ.traceObject S X))
    (Y : (σ.generated S).carrier.FullSubcategory)
    (X : FGModuleCat.{w} R) :
    ((σ.generated S).carrier.ι.obj Y ⟶ X) ≃
      (Y ⟶ traceCoreflectorObj σ S htrace X) where
  toFun f :=
    ObjectProperty.homMk <|
      ConcreteCategory.ofHom <|
        f.hom.hom.codRestrict (σ.trace S X) fun y ↦
          range_le_trace_of_inFac σ
            (inFac_of_inAdd σ Y.property) f ⟨y, rfl⟩
  invFun g := g.hom ≫ σ.traceι S X
  left_inv f := by
    apply FGModuleCat.hom_ext
    ext y
    rfl
  right_inv g := by
    apply ObjectProperty.hom_ext
    apply FGModuleCat.hom_ext
    ext y
    rfl

/-- Naturality in the object of the full subcategory, the only law needed
by `rightAdjointOfEquiv`. -/
theorem traceHomEquiv_naturality_left
    (S : Set ι)
    (htrace : ∀ X : FGModuleCat.{w} R,
      σ.InAdd S (σ.traceObject S X))
    {Y' Y : (σ.generated S).carrier.FullSubcategory}
    (f : Y' ⟶ Y) (X : FGModuleCat.{w} R)
    (g : (σ.generated S).carrier.ι.obj Y ⟶ X) :
    traceHomEquiv σ S htrace Y' X
        ((σ.generated S).carrier.ι.map f ≫ g) =
      f ≫ traceHomEquiv σ S htrace Y X g := by
  apply ObjectProperty.hom_ext
  apply FGModuleCat.hom_ext
  ext y
  rfl

/-- The trace construction as a genuine right adjoint functor. -/
def traceCoreflector
    (S : Set ι)
    (htrace : ∀ X : FGModuleCat.{w} R,
      σ.InAdd S (σ.traceObject S X)) :
    FGModuleCat.{w} R ⥤
      (σ.generated S).carrier.FullSubcategory :=
  Adjunction.rightAdjointOfEquiv
    (F := (σ.generated S).carrier.ι)
    (e := traceHomEquiv σ S htrace)
    (fun _ _ Y f g ↦
      traceHomEquiv_naturality_left σ S htrace f Y g)

/-- The inclusion of `add S` is left adjoint to the trace functor. -/
def traceAdjunction
    (S : Set ι)
    (htrace : ∀ X : FGModuleCat.{w} R,
      σ.InAdd S (σ.traceObject S X)) :
    (σ.generated S).carrier.ι ⊣
      traceCoreflector σ S htrace :=
  Adjunction.adjunctionOfEquivRight
    (F := (σ.generated S).carrier.ι)
    (e := traceHomEquiv σ S htrace)
    (fun _ _ Y f g ↦
      traceHomEquiv_naturality_left σ S htrace f Y g)

/-- The counit constructed from the hom equivalence is literally the
trace inclusion. -/
theorem traceAdjunction_counit_app
    (S : Set ι)
    (htrace : ∀ X : FGModuleCat.{w} R,
      σ.InAdd S (σ.traceObject S X))
    (X : FGModuleCat.{w} R) :
    (traceAdjunction σ S htrace).counit.app X =
      σ.traceι S X := by
  rfl

/-- Trace membership produces a right-rejective structure. -/
def rightRejectiveDataOfTrace
    (S : Set ι)
    (htrace : ∀ X : FGModuleCat.{w} R,
      σ.InAdd S (σ.traceObject S X)) :
    RightRejectiveData (σ.generated S) where
  coreflector := traceCoreflector σ S htrace
  adjunction := traceAdjunction σ S htrace
  counit_mono X := by
    rw [traceAdjunction_counit_app]
    exact (fg_mono_iff_injective (σ.traceι S X)).2
      Subtype.val_injective

/-- A quotient-closed support contains all of its trace objects. -/
theorem traceObject_inAdd_of_qClosed
    {S : Set ι} (hS : σ.qClosure.IsClosed S)
    (X : FGModuleCat.{w} R) :
    σ.InAdd S (σ.traceObject S X) :=
  (inAdd_iff_inFac_of_qClosed σ hS _).2
    (traceObject_inFac σ S X)

/-- A right-rejective generated subcategory is quotient-closed. -/
theorem qClosed_of_rightRejective
    {S : Set ι}
    (hrr : IsRightRejective (σ.generated S)) :
    σ.qClosure.IsClosed S := by
  apply
    (qClosed_iff_generated_isClosedUnderQuotients σ S).2
  constructor
  intro X Y f hf hX
  obtain ⟨D⟩ := hrr
  let Xc : (σ.generated S).carrier.FullSubcategory :=
    ⟨X, hX⟩
  let fc : (σ.generated S).carrier.ι.obj Xc ⟶ Y :=
    f
  letI hfc : Epi fc := by
    dsimp only [fc, Xc]
    exact hf
  let g : Xc ⟶ D.coreflector.obj Y :=
    D.adjunction.homEquiv Xc Y fc
  have hfac :
      (σ.generated S).carrier.ι.map g ≫
          D.adjunction.counit.app Y = fc := by
    calc
      (σ.generated S).carrier.ι.map g ≫
          D.adjunction.counit.app Y =
        (D.adjunction.homEquiv Xc Y).symm g :=
          (D.adjunction.homEquiv_counit Xc Y g).symm
      _ = fc := by
        dsimp only [g]
        exact Equiv.symm_apply_apply
          (D.adjunction.homEquiv Xc Y) fc
  letI : Mono (D.adjunction.counit.app Y) :=
    D.counit_mono Y
  haveI : Epi
      ((σ.generated S).carrier.ι.map g ≫
        D.adjunction.counit.app Y) := by
    rw [hfac]
    exact hfc
  letI : Epi (D.adjunction.counit.app Y) :=
    epi_of_epi ((σ.generated S).carrier.ι.map g) _
  letI hεiso : IsIso (D.adjunction.counit.app Y) :=
    isIso_of_mono_of_epi _
  exact
    (σ.generated S).iso_mem
      (@asIso _ _ _ _ (D.adjunction.counit.app Y) hεiso)
      (D.coreflector.obj Y).property

/-- Exact quotient-side trace--rejective equivalence for a chosen complete
indecomposable skeleton. -/
theorem qClosed_iff_trace_iff_rightRejective (S : Set ι) :
    σ.qClosure.IsClosed S ↔
      (∀ X : FGModuleCat.{w} R,
        σ.InAdd S (σ.traceObject S X)) ∧
      IsRightRejective (σ.generated S) := by
  constructor
  · intro hS
    have htrace :
        ∀ X : FGModuleCat.{w} R,
          σ.InAdd S (σ.traceObject S X) :=
      traceObject_inAdd_of_qClosed σ hS
    exact
      ⟨htrace, ⟨rightRejectiveDataOfTrace σ S htrace⟩⟩
  · rintro ⟨_, hrr⟩
    exact qClosed_of_rightRejective σ hrr

/-- First equivalence in the manuscript proposition. -/
theorem qClosed_iff_traceObject_inAdd (S : Set ι) :
    σ.qClosure.IsClosed S ↔
      ∀ X : FGModuleCat.{w} R,
        σ.InAdd S (σ.traceObject S X) := by
  constructor
  · exact traceObject_inAdd_of_qClosed σ
  · intro htrace
    exact qClosed_of_rightRejective σ
      ⟨rightRejectiveDataOfTrace σ S htrace⟩

/-- The trace condition and the adjoint formulation are equivalent. -/
theorem traceObject_inAdd_iff_rightRejective (S : Set ι) :
    (∀ X : FGModuleCat.{w} R,
      σ.InAdd S (σ.traceObject S X)) ↔
      IsRightRejective (σ.generated S) := by
  constructor
  · intro htrace
    exact ⟨rightRejectiveDataOfTrace σ S htrace⟩
  · intro hrr
    exact
      traceObject_inAdd_of_qClosed σ
        (qClosed_of_rightRejective σ hrr)

/-- Quotient closure is exactly right rejectivity. -/
theorem qClosed_iff_rightRejective (S : Set ι) :
    σ.qClosure.IsClosed S ↔
      IsRightRejective (σ.generated S) :=
  (qClosed_iff_traceObject_inAdd σ S).trans
    (traceObject_inAdd_iff_rightRejective σ S)

/-- The trace operation is idempotent on its image: once an object is a
trace object lying in `add S`, its own trace is the whole object. -/
theorem trace_traceObject_eq_top
    (S : Set ι)
    (htrace : ∀ X : FGModuleCat.{w} R,
      σ.InAdd S (σ.traceObject S X))
    (X : FGModuleCat.{w} R) :
    σ.trace S (σ.traceObject S X) = ⊤ :=
  (inFac_iff_trace_eq_top σ S (σ.traceObject S X)).1
    (inFac_of_inAdd σ (htrace X))

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton

