import OpConjecture.CategoryTheory.Rejective

/-!
Generic source-faithful form of Iyama's monic-approximation criterion:
objectwise monic right approximations construct a right adjoint to the
full-subcategory inclusion.
-/

noncomputable section

open CategoryTheory

namespace OpConjecture.CategoricalRejective

universe v u

variable {C : Type u} [Category.{v} C]

/-- A monic right `P`-approximation of `X`. -/
structure MonicRightApproximation
    (P : ObjectProperty C) (X : C) where
  obj : P.FullSubcategory
  map : P.ι.obj obj ⟶ X
  mono : Mono map
  factors :
    ∀ (Y : P.FullSubcategory)
      (f : P.ι.obj Y ⟶ X),
      ∃ g : Y ⟶ obj, P.ι.map g ≫ map = f

namespace MonicRightApproximation

variable {P : ObjectProperty C} {X : C}

/-- The factor through a monic approximation is unique. -/
theorem factor_unique
    (A : MonicRightApproximation P X)
    {Y : P.FullSubcategory}
    {f : P.ι.obj Y ⟶ X}
    {g h : Y ⟶ A.obj}
    (hg : P.ι.map g ≫ A.map = f)
    (hh : P.ι.map h ≫ A.map = f) :
    g = h := by
  haveI : Mono A.map := A.mono
  apply P.ι.map_injective
  apply (cancel_mono A.map).1
  rw [hg, hh]

end MonicRightApproximation

variable (P : ObjectProperty C)
  (hA : ∀ X : C, Nonempty (MonicRightApproximation P X))

private def chosenApproximation (X : C) :
    MonicRightApproximation P X :=
  (hA X).some

private def chosenLift
    {X Y : C} (f : X ⟶ Y) :
    (chosenApproximation P hA X).obj ⟶
      (chosenApproximation P hA Y).obj :=
  (chosenApproximation P hA Y).factors
    (chosenApproximation P hA X).obj
    ((chosenApproximation P hA X).map ≫ f) |>.choose

private theorem chosenLift_spec
    {X Y : C} (f : X ⟶ Y) :
    P.ι.map (chosenLift P hA f) ≫
        (chosenApproximation P hA Y).map =
      (chosenApproximation P hA X).map ≫ f :=
  (chosenApproximation P hA Y).factors
    (chosenApproximation P hA X).obj
    ((chosenApproximation P hA X).map ≫ f) |>.choose_spec

/-- The coreflector assembled from chosen monic approximations. -/
private abbrev approximationCoreflector :
    C ⥤ P.FullSubcategory where
  obj X := (chosenApproximation P hA X).obj
  map f := chosenLift P hA f
  map_id X := by
    apply (chosenApproximation P hA X).factor_unique
      (f := (chosenApproximation P hA X).map)
    · simpa using chosenLift_spec P hA (𝟙 X)
    · simp
  map_comp {X Y Z} f g := by
    apply (chosenApproximation P hA Z).factor_unique
      (f := (chosenApproximation P hA X).map ≫ f ≫ g)
    · simpa [Category.assoc] using
        chosenLift_spec P hA (f ≫ g)
    · rw [P.ι.map_comp, Category.assoc, chosenLift_spec,
        ← Category.assoc, chosenLift_spec,
        Category.assoc]

/-- The Hom equivalence represented by a monic approximation. -/
private abbrev approximationHomEquiv
    (X : P.FullSubcategory) (Y : C) :
    (P.ι.obj X ⟶ Y) ≃
      (X ⟶ (approximationCoreflector P hA).obj Y) where
  toFun f :=
    ((chosenApproximation P hA Y).factors X f).choose
  invFun g :=
    P.ι.map g ≫ (chosenApproximation P hA Y).map
  left_inv f :=
    ((chosenApproximation P hA Y).factors X f).choose_spec
  right_inv g := by
    apply (chosenApproximation P hA Y).factor_unique
      (f := P.ι.map g ≫
        (chosenApproximation P hA Y).map)
    · exact
        ((chosenApproximation P hA Y).factors X
          (P.ι.map g ≫
            (chosenApproximation P hA Y).map)).choose_spec
    · rfl

@[simp]
private theorem approximationHomEquiv_apply
    (X : P.FullSubcategory) (Y : C)
    (f : P.ι.obj X ⟶ Y) :
    approximationHomEquiv P hA X Y f =
      ((chosenApproximation P hA Y).factors X f).choose :=
  rfl

@[simp]
private theorem approximationCoreflector_map
    {X Y : C} (f : X ⟶ Y) :
    (approximationCoreflector P hA).map f =
      chosenLift P hA f :=
  rfl

private def approximationCoreHomEquiv :
    Adjunction.CoreHomEquiv P.ι
      (approximationCoreflector P hA) where
  homEquiv := approximationHomEquiv P hA
  homEquiv_naturality_left_symm {X' X Y} f g := by
    change
      P.ι.map (f ≫ g) ≫
          (chosenApproximation P hA Y).map =
        P.ι.map f ≫
          (P.ι.map g ≫
            (chosenApproximation P hA Y).map)
    simp [Category.assoc]
  homEquiv_naturality_right {X Y Y'} f g := by
    apply (chosenApproximation P hA Y').factor_unique
      (f := f ≫ g)
    · exact
        ((chosenApproximation P hA Y').factors X
          (f ≫ g)).choose_spec
    · have hg :
          P.ι.map
                ((approximationCoreflector P hA).map g) ≫
              (chosenApproximation P hA Y').map =
            (chosenApproximation P hA Y).map ≫ g := by
          simpa only [approximationCoreflector_map] using
            chosenLift_spec P hA g
      have hf :
          P.ι.map (approximationHomEquiv P hA X Y f) ≫
              (chosenApproximation P hA Y).map =
            f := by
          exact (approximationHomEquiv P hA X Y).left_inv f
      rw [P.ι.map_comp, Category.assoc, hg,
        ← Category.assoc, hf]

/-- Objectwise monic right approximations imply categorical right
rejectivity. -/
theorem isRightRejective_of_monicRightApproximations
    (hA : ∀ X : C,
      Nonempty (MonicRightApproximation P X)) :
    IsRightRejective P := by
  let core :=
    approximationCoreHomEquiv P hA
  let adj :
      P.ι ⊣ approximationCoreflector P hA :=
    Adjunction.mkOfHomEquiv core
  refine ⟨{
    coreflector := approximationCoreflector P hA
    adjunction := adj
    counit_mono := fun X ↦ ?_ }⟩
  haveI :
      Mono ((chosenApproximation P hA X).map) :=
    (chosenApproximation P hA X).mono
  change Mono
    ((core.homEquiv
      ((approximationCoreflector P hA).obj X) X).symm
        (𝟙 _))
  change Mono
    (P.ι.map (𝟙 _) ≫
      (chosenApproximation P hA X).map)
  simpa

end OpConjecture.CategoricalRejective
