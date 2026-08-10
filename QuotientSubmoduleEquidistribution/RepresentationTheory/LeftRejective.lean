import QuotientSubmoduleEquidistribution.RepresentationTheory.TraceRejective

/-!
# Reject quotients and left rejective subcategories
-/

noncomputable section

open Set
open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe u v w

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)

/-- Data expressing left rejectivity: the inclusion has a left adjoint
with epic unit. -/
structure LeftRejectiveData
    (C : AdditiveRepleteSummandSubcategory.{u, w} (R := R)) where
  reflector :
    FGModuleCat.{w} R ⥤ C.carrier.FullSubcategory
  adjunction : reflector ⊣ C.carrier.ι
  unit_epi :
    ∀ X : FGModuleCat.{w} R,
      Epi (adjunction.unit.app X)

def IsLeftRejective
    (C : AdditiveRepleteSummandSubcategory.{u, w} (R := R)) : Prop :=
  Nonempty (LeftRejectiveData C)

/-- Additive membership always implies submodule generation. -/
theorem inSub_of_inAdd
    {S : Set ι} {X : FGModuleCat.{w} R}
    (hX : σ.InAdd S X) :
    σ.InSub S X := by
  obtain ⟨P⟩ := hX
  exact ⟨{
    index := P.index
    label := P.label
    mem := P.mem
    map := P.iso.hom
    mono := inferInstance }⟩

/-- The reject quotient as an object of `add S`. -/
def rejectReflectorObj
    (S : Set ι)
    (hreject : ∀ X : FGModuleCat.{w} R,
      σ.InAdd S (σ.rejectQuotientObject S X))
    (X : FGModuleCat.{w} R) :
    (σ.generated S).carrier.FullSubcategory :=
  ⟨σ.rejectQuotientObject S X, hreject X⟩

/-- Maps out of the reject quotient are uniquely maps out of `X` into
`add S`. -/
def rejectHomEquiv
    (S : Set ι)
    (hreject : ∀ X : FGModuleCat.{w} R,
      σ.InAdd S (σ.rejectQuotientObject S X))
    (X : FGModuleCat.{w} R)
    (Y : (σ.generated S).carrier.FullSubcategory) :
    (rejectReflectorObj σ S hreject X ⟶ Y) ≃
      (X ⟶ (σ.generated S).carrier.ι.obj Y) where
  toFun g := σ.rejectπ S X ≫ g.hom
  invFun f :=
    ObjectProperty.homMk <|
      ConcreteCategory.ofHom <|
        (σ.reject S X).liftQ f.hom.hom
          (reject_le_ker_of_inSub σ
            (inSub_of_inAdd σ Y.property) f)
  left_inv g := by
    haveI : Epi (σ.rejectπ S X) :=
      (fg_epi_iff_surjective (σ.rejectπ S X)).2
        (σ.reject S X).mkQ_surjective
    apply ObjectProperty.hom_ext
    apply (cancel_epi (σ.rejectπ S X)).1
    apply FGModuleCat.hom_ext
    exact
      (σ.reject S X).liftQ_mkQ
        (σ.rejectπ S X ≫ g.hom).hom.hom
        (reject_le_ker_of_inSub σ
          (inSub_of_inAdd σ Y.property)
          (σ.rejectπ S X ≫ g.hom))
  right_inv f := by
    apply FGModuleCat.hom_ext
    exact
      (σ.reject S X).liftQ_mkQ f.hom.hom
        (reject_le_ker_of_inSub σ
          (inSub_of_inAdd σ Y.property) f)

/-- Naturality in the object of the full subcategory. -/
theorem rejectHomEquiv_naturality_right
    (S : Set ι)
    (hreject : ∀ X : FGModuleCat.{w} R,
      σ.InAdd S (σ.rejectQuotientObject S X))
    (X : FGModuleCat.{w} R)
    {Y Y' : (σ.generated S).carrier.FullSubcategory}
    (g : Y ⟶ Y')
    (f : rejectReflectorObj σ S hreject X ⟶ Y) :
    rejectHomEquiv σ S hreject X Y' (f ≫ g) =
      rejectHomEquiv σ S hreject X Y f ≫
        (σ.generated S).carrier.ι.map g := by
  apply FGModuleCat.hom_ext
  rfl

/-- The reject quotient construction as a genuine left adjoint. -/
def rejectReflector
    (S : Set ι)
    (hreject : ∀ X : FGModuleCat.{w} R,
      σ.InAdd S (σ.rejectQuotientObject S X)) :
    FGModuleCat.{w} R ⥤
      (σ.generated S).carrier.FullSubcategory :=
  Adjunction.leftAdjointOfEquiv
    (G := (σ.generated S).carrier.ι)
    (e := rejectHomEquiv σ S hreject)
    (fun X _ _ g f ↦
      rejectHomEquiv_naturality_right σ S hreject X g f)

/-- The reject quotient functor is left adjoint to the inclusion. -/
def rejectAdjunction
    (S : Set ι)
    (hreject : ∀ X : FGModuleCat.{w} R,
      σ.InAdd S (σ.rejectQuotientObject S X)) :
    rejectReflector σ S hreject ⊣
      (σ.generated S).carrier.ι :=
  Adjunction.adjunctionOfEquivLeft
    (G := (σ.generated S).carrier.ι)
    (e := rejectHomEquiv σ S hreject)
    (fun X _ _ g f ↦
      rejectHomEquiv_naturality_right σ S hreject X g f)

/-- The constructed unit is literally the reject projection. -/
theorem rejectAdjunction_unit_app
    (S : Set ι)
    (hreject : ∀ X : FGModuleCat.{w} R,
      σ.InAdd S (σ.rejectQuotientObject S X))
    (X : FGModuleCat.{w} R) :
    (rejectAdjunction σ S hreject).unit.app X =
      σ.rejectπ S X := by
  rfl

def leftRejectiveDataOfReject
    (S : Set ι)
    (hreject : ∀ X : FGModuleCat.{w} R,
      σ.InAdd S (σ.rejectQuotientObject S X)) :
    LeftRejectiveData (σ.generated S) where
  reflector := rejectReflector σ S hreject
  adjunction := rejectAdjunction σ S hreject
  unit_epi X := by
    rw [rejectAdjunction_unit_app]
    exact (fg_epi_iff_surjective (σ.rejectπ S X)).2
      (σ.reject S X).mkQ_surjective

/-- A submodule-closed support contains every reject quotient, provided
all ambient finitely generated modules have finite length. -/
theorem rejectQuotientObject_inAdd_of_sClosed
    (hfinite : ∀ X : FGModuleCat.{w} R, IsFiniteLength R X)
    {S : Set ι} (hS : σ.sClosure.IsClosed S)
    (X : FGModuleCat.{w} R) :
    σ.InAdd S (σ.rejectQuotientObject S X) :=
  (inAdd_iff_inSub_of_sClosed σ hS _).2
    (rejectQuotientObject_inSub σ S X (hfinite X))

/-- A left-rejective generated subcategory is subobject-closed. -/
theorem sClosed_of_leftRejective
    {S : Set ι}
    (hlr : IsLeftRejective (σ.generated S)) :
    σ.sClosure.IsClosed S := by
  apply
    (sClosed_iff_generated_isClosedUnderSubobjects σ S).2
  constructor
  intro X Y f hf hY
  obtain ⟨D⟩ := hlr
  let Yc : (σ.generated S).carrier.FullSubcategory :=
    ⟨Y, hY⟩
  let fc : X ⟶ (σ.generated S).carrier.ι.obj Yc :=
    f
  letI hfc : Mono fc := by
    dsimp only [fc, Yc]
    exact hf
  let g : D.reflector.obj X ⟶ Yc :=
    (D.adjunction.homEquiv X Yc).symm fc
  have hfac :
      D.adjunction.unit.app X ≫
          (σ.generated S).carrier.ι.map g = fc := by
    calc
      D.adjunction.unit.app X ≫
          (σ.generated S).carrier.ι.map g =
        D.adjunction.homEquiv X Yc g :=
          (D.adjunction.homEquiv_unit X Yc g).symm
      _ = fc := by
        dsimp only [g]
        exact Equiv.apply_symm_apply
          (D.adjunction.homEquiv X Yc) fc
  letI : Epi (D.adjunction.unit.app X) :=
    D.unit_epi X
  haveI : Mono
      (D.adjunction.unit.app X ≫
        (σ.generated S).carrier.ι.map g) := by
    rw [hfac]
    exact hfc
  letI : Mono (D.adjunction.unit.app X) :=
    mono_of_mono _ ((σ.generated S).carrier.ι.map g)
  letI hηiso : IsIso (D.adjunction.unit.app X) :=
    isIso_of_mono_of_epi _
  exact
    (σ.generated S).iso_mem
      (@asIso _ _ _ _ (D.adjunction.unit.app X) hηiso).symm
      (D.reflector.obj X).property

/-- Exact dual half of the manuscript proposition. -/
theorem sClosed_iff_rejectQuotient_inAdd_iff_leftRejective
    (hfinite : ∀ X : FGModuleCat.{w} R, IsFiniteLength R X)
    (S : Set ι) :
    σ.sClosure.IsClosed S ↔
      (∀ X : FGModuleCat.{w} R,
        σ.InAdd S (σ.rejectQuotientObject S X)) ∧
      IsLeftRejective (σ.generated S) := by
  constructor
  · intro hS
    have hreject :
        ∀ X : FGModuleCat.{w} R,
          σ.InAdd S (σ.rejectQuotientObject S X) :=
      rejectQuotientObject_inAdd_of_sClosed σ hfinite hS
    exact
      ⟨hreject, ⟨leftRejectiveDataOfReject σ S hreject⟩⟩
  · rintro ⟨_, hlr⟩
    exact sClosed_of_leftRejective σ hlr

theorem sClosed_iff_leftRejective
    (hfinite : ∀ X : FGModuleCat.{w} R, IsFiniteLength R X)
    (S : Set ι) :
    σ.sClosure.IsClosed S ↔
      IsLeftRejective (σ.generated S) := by
  constructor
  · intro hS
    let hreject :=
      rejectQuotientObject_inAdd_of_sClosed σ hfinite hS
    exact ⟨leftRejectiveDataOfReject σ S hreject⟩
  · exact sClosed_of_leftRejective σ

/-- The reject operation vanishes on its own quotient object once that
quotient lies in `add S`, the dual concrete idempotence statement. -/
theorem reject_rejectQuotient_eq_bot
    (S : Set ι)
    (hreject : ∀ X : FGModuleCat.{w} R,
      σ.InAdd S (σ.rejectQuotientObject S X))
    (X : FGModuleCat.{w} R) :
    σ.reject S (σ.rejectQuotientObject S X) = ⊥ :=
  reject_eq_bot_of_inSub σ S (σ.rejectQuotientObject S X)
    (inSub_of_inAdd σ (hreject X))

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton

