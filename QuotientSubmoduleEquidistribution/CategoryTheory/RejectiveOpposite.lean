import Mathlib.CategoryTheory.Adjunction.Opposites
import Mathlib.CategoryTheory.ObjectProperty.Opposite
import QuotientSubmoduleEquidistribution.CategoryTheory.Rejective

/-!
# Rejectivity and opposite categories

Passing to the opposite category interchanges left and right rejectivity.
The only bookkeeping subtlety is that Mathlib's full subcategory on the
opposite object property is canonically equivalent, rather than definitionally
equal, to the opposite of the original full subcategory.
-/

noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.CategoricalRejective

universe v u

variable {C : Type u} [Category.{v} C]

/-- The canonical comparison between the two ways of including the opposite
full subcategory into the opposite ambient category. -/
private def oppositeInclusionIso (P : ObjectProperty C) :
    (ObjectProperty.opEquivalence P).functor ⋙ P.ι.op ≅
      P.op.ι :=
  NatIso.ofComponents
    (fun X ↦ Iso.refl _)
    (fun f ↦ by
      change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
      simp)

/-- Opposite categories turn left-rejective data into right-rejective data. -/
def RightRejectiveData.ofLeftOpposite
    {P : ObjectProperty C}
    (data : LeftRejectiveData P) :
    RightRejectiveData P.op where
  coreflector :=
    data.reflector.op ⋙
      (ObjectProperty.opEquivalence P).inverse
  adjunction :=
    ((ObjectProperty.opEquivalence P).toAdjunction.comp
      data.adjunction.op).ofNatIsoLeft
        (oppositeInclusionIso P)
  counit_mono X := by
    let E := ObjectProperty.opEquivalence P
    let adj :=
      E.toAdjunction.comp data.adjunction.op
    let i := oppositeInclusionIso P
    change Mono ((adj.ofNatIsoLeft i).counit.app X)
    change Mono
      ((Functor.whiskerLeft _ i.inv ≫ adj.counit).app X)
    rw [NatTrans.comp_app]
    haveI hi :
        Mono
          ((Functor.whiskerLeft
            (data.reflector.op ⋙ E.inverse)
            i.inv).app X) := by
      infer_instance
    haveI hadj : Mono (adj.counit.app X) := by
      rw [Adjunction.comp_counit_app]
      haveI hEcounit :
          IsIso
            (E.toAdjunction.counit.app
              (data.reflector.op.obj X)) := by
        change
          IsIso
            (E.counitIso.hom.app
              (data.reflector.op.obj X))
        infer_instance
      haveI hfirst :
          IsIso
            (P.ι.op.map
              (E.toAdjunction.counit.app
                (data.reflector.op.obj X))) := by
        infer_instance
      haveI hfirstMono :
          Mono
            (P.ι.op.map
              (E.toAdjunction.counit.app
                (data.reflector.op.obj X))) :=
        IsIso.mono_of_iso _
      haveI hunit :
          Epi (data.adjunction.unit.app X.unop) :=
        data.unit_epi X.unop
      haveI hsecond :
          Mono (data.adjunction.op.counit.app X) := by
        change
          Mono (data.adjunction.unit.app X.unop).op
        infer_instance
      exact mono_comp' hfirstMono hsecond
    exact mono_comp' hi hadj

/-- A left-rejective full subcategory becomes right rejective after passing to
the opposite category. -/
theorem isRightRejective_op_of_isLeftRejective
    {P : ObjectProperty C}
    (h : IsLeftRejective P) :
    IsRightRejective P.op :=
  Nonempty.map RightRejectiveData.ofLeftOpposite h

/-- Opposite categories turn right-rejective data into left-rejective data. -/
def LeftRejectiveData.ofRightOpposite
    {P : ObjectProperty C}
    (data : RightRejectiveData P) :
    LeftRejectiveData P.op where
  reflector :=
    data.coreflector.op ⋙
      (ObjectProperty.opEquivalence P).inverse
  adjunction :=
    (data.adjunction.op.comp
      (ObjectProperty.opEquivalence P).symm.toAdjunction).ofNatIsoRight
        (oppositeInclusionIso P)
  unit_epi X := by
    let E := ObjectProperty.opEquivalence P
    let adj :=
      data.adjunction.op.comp E.symm.toAdjunction
    let i := oppositeInclusionIso P
    change Epi ((adj.ofNatIsoRight i).unit.app X)
    change Epi
      ((adj.unit ≫
        Functor.whiskerLeft
          (data.coreflector.op ⋙ E.inverse)
          i.hom).app X)
    rw [NatTrans.comp_app]
    haveI hi :
        Epi
          ((Functor.whiskerLeft
            (data.coreflector.op ⋙ E.inverse)
            i.hom).app X) := by
      infer_instance
    haveI hadj : Epi (adj.unit.app X) := by
      rw [Adjunction.comp_unit_app]
      haveI hcounit :
          Mono (data.adjunction.counit.app X.unop) :=
        data.counit_mono X.unop
      haveI hfirst :
          Epi (data.adjunction.op.unit.app X) := by
        change Epi (data.adjunction.counit.app X.unop).op
        infer_instance
      haveI hEunit :
          IsIso
            (E.symm.toAdjunction.unit.app
              (data.coreflector.op.obj X)) := by
        change
          IsIso
            (E.symm.unitIso.hom.app
              (data.coreflector.op.obj X))
        infer_instance
      haveI hsecondIso :
          IsIso
            (P.ι.op.map
              (E.symm.toAdjunction.unit.app
                (data.coreflector.op.obj X))) := by
        infer_instance
      haveI hsecond :
          Epi
            (P.ι.op.map
              (E.symm.toAdjunction.unit.app
                (data.coreflector.op.obj X))) :=
        IsIso.epi_of_iso _
      exact epi_comp' hfirst hsecond
    exact epi_comp' hadj hi

/-- A right-rejective full subcategory becomes left rejective after passing to
the opposite category. -/
theorem isLeftRejective_op_of_isRightRejective
    {P : ObjectProperty C}
    (h : IsRightRejective P) :
    IsLeftRejective P.op :=
  Nonempty.map LeftRejectiveData.ofRightOpposite h

end QuotientSubmoduleEquidistribution.CategoricalRejective
