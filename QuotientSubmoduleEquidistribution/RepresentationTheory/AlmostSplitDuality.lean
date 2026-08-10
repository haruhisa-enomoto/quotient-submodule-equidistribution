import QuotientSubmoduleEquidistribution.RepresentationTheory.AlmostSplitUniqueness
import Mathlib.CategoryTheory.Abelian.Opposite
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Almost-split morphisms under anti-equivalence

An equivalence from an opposite category turns a right almost-split
morphism into a left almost-split morphism.  The proof uses essential
surjectivity to pull an arbitrary target back across the equivalence and
full faithfulness to reflect the splitting condition.
-/

noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution

universe u v u' v'

variable {C : Type u} [Category.{v} C]
  {D : Type u'} [Category.{v'} D]

/-- A right almost-split morphism becomes left almost split under an
anti-equivalence. -/
theorem IsRightAlmostSplit.map_op_equivalence
    {X Y : C} {f : X ⟶ Y} (hf : IsRightAlmostSplit f)
    (E : Cᵒᵖ ≌ D) :
    IsLeftAlmostSplit (E.functor.map f.op) := by
  constructor
  · intro hs
    apply hf.not_isSplitEpi
    have hop : IsSplitMono f.op :=
      (E.functor.isSplitMono_iff f.op).mp hs
    obtain ⟨s⟩ := hop.exists_splitMono
    exact IsSplitEpi.mk'
      { section_ := s.retraction.unop
        id := by
          apply Quiver.Hom.op_inj
          simpa only [op_comp, Quiver.Hom.op_unop, op_id] using s.id }
  · intro W g hg
    let e : E.functor.obj (E.inverse.obj W) ≅ W :=
      E.counitIso.app W
    let g' : E.functor.obj (Opposite.op Y) ⟶
        E.functor.obj (E.inverse.obj W) := g ≫ e.inv
    let k : Opposite.op Y ⟶ E.inverse.obj W :=
      E.functor.preimage g'
    have hk : E.functor.map k = g' :=
      E.functor.map_preimage g'
    have hknonsplit : ¬ IsSplitEpi k.unop := by
      intro hsplit
      apply hg
      letI : IsSplitEpi k.unop := hsplit
      letI : IsSplitMono k.unop.op := inferInstance
      letI : IsSplitMono k := by
        simpa using (inferInstance : IsSplitMono k.unop.op)
      letI : IsSplitMono (E.functor.map k) := inferInstance
      have hgeq : E.functor.map k ≫ e.hom = g := by
        rw [hk]
        simp [g', Category.assoc]
      rw [← hgeq]
      letI : IsSplitMono e.hom := inferInstance
      infer_instance
    obtain ⟨l, hl⟩ := hf.factors k.unop hknonsplit
    let lop : Opposite.op X ⟶ E.inverse.obj W := by
      simpa only [Opposite.op_unop] using l.op
    have hlop : f.op ≫ lop = k := by
      apply Quiver.Hom.unop_inj
      simpa only [lop, unop_comp, Quiver.Hom.unop_op,
        Quiver.Hom.op_unop] using hl
    refine ⟨E.functor.map lop ≫ e.hom, ?_⟩
    rw [← Category.assoc, ← E.functor.map_comp, hlop, hk]
    simp [g', Category.assoc]

/-- A right-minimal map becomes left minimal after applying an equivalence
from the opposite category. -/
theorem IsRightMinimal.map_op_equivalence
    {X Y : C} {f : X ⟶ Y} (hf : IsRightMinimal f)
    (E : Cᵒᵖ ≌ D) :
    IsLeftMinimal (E.functor.map f.op) := by
  intro e he
  let e' : Opposite.op X ⟶ Opposite.op X :=
    E.functor.preimage e
  have hsource : e'.unop ≫ f = f := by
    apply Quiver.Hom.op_inj
    apply E.functor.map_injective
    simpa only [e', op_comp, Quiver.Hom.op_unop,
      E.functor.map_comp, E.functor.map_preimage] using he
  letI : IsIso e'.unop := hf e'.unop hsource
  haveI : IsIso e' := by
    simpa only [Quiver.Hom.op_unop] using
      (inferInstance : IsIso e'.unop.op)
  haveI : IsIso (E.functor.map e') := E.functor.map_isIso e'
  have heq : E.functor.map e' = e := E.functor.map_preimage e
  rw [← heq]
  infer_instance

/-- Dually, a left-minimal map becomes right minimal after applying an
equivalence from the opposite category. -/
theorem IsLeftMinimal.map_op_equivalence
    {X Y : C} {f : X ⟶ Y} (hf : IsLeftMinimal f)
    (E : Cᵒᵖ ≌ D) :
    IsRightMinimal (E.functor.map f.op) := by
  intro e he
  let e' : Opposite.op Y ⟶ Opposite.op Y :=
    E.functor.preimage e
  have hsource : f ≫ e'.unop = f := by
    apply Quiver.Hom.op_inj
    apply E.functor.map_injective
    simpa only [e', op_comp, Quiver.Hom.op_unop,
      E.functor.map_comp, E.functor.map_preimage] using he
  letI : IsIso e'.unop := hf e'.unop hsource
  haveI : IsIso e' := by
    simpa only [Quiver.Hom.op_unop] using
      (inferInstance : IsIso e'.unop.op)
  haveI : IsIso (E.functor.map e') := E.functor.map_isIso e'
  have heq : E.functor.map e' = e := E.functor.map_preimage e
  rw [← heq]
  infer_instance

/-- Minimal right almost-split maps become minimal left almost-split maps
under an anti-equivalence. -/
theorem minimalRightAlmostSplit_map_op_equivalence
    {X Y : C} {f : X ⟶ Y}
    (has : IsRightAlmostSplit f) (hmin : IsRightMinimal f)
    (E : Cᵒᵖ ≌ D) :
    IsLeftAlmostSplit (E.functor.map f.op) ∧
      IsLeftMinimal (E.functor.map f.op) :=
  ⟨has.map_op_equivalence E, hmin.map_op_equivalence E⟩

/-! ## Irreducible morphisms -/

/-- Opposite-category passage preserves irreducibility and reverses the
direction of the morphism. -/
theorem IsIrreducibleMorphism.op
    {X Y : C} {f : X ⟶ Y} (hf : IsIrreducibleMorphism f) :
    IsIrreducibleMorphism f.op := by
  refine
    { not_isSplitMono := ?_
      not_isSplitEpi := ?_
      factorization := ?_ }
  · intro hs
    apply hf.not_isSplitEpi
    obtain ⟨s⟩ := hs.exists_splitMono
    exact IsSplitEpi.mk'
      { section_ := s.retraction.unop
        id := by
          apply Quiver.Hom.op_inj
          simpa only [op_comp, Quiver.Hom.op_unop, op_id] using s.id }
  · intro hs
    apply hf.not_isSplitMono
    obtain ⟨s⟩ := hs.exists_splitEpi
    exact IsSplitMono.mk'
      { retraction := s.section_.unop
        id := by
          apply Quiver.Hom.op_inj
          simpa only [op_comp, Quiver.Hom.op_unop, op_id] using s.id }
  · intro M g h hgh
    have hunop : h.unop ≫ g.unop = f := by
      apply Quiver.Hom.op_inj
      simpa only [op_comp, Quiver.Hom.op_unop] using hgh
    rcases hf.factorization h.unop g.unop hunop with hh | hg
    · right
      letI : IsSplitMono h.unop := hh
      simpa only [Quiver.Hom.op_unop] using
        (inferInstance : IsSplitEpi h.unop.op)
    · left
      letI : IsSplitEpi g.unop := hg
      simpa only [Quiver.Hom.op_unop] using
        (inferInstance : IsSplitMono g.unop.op)

/-- A categorical equivalence preserves irreducible morphisms. -/
theorem IsIrreducibleMorphism.map_equivalence
    {X Y : C} {f : X ⟶ Y} (hf : IsIrreducibleMorphism f)
    (E : C ≌ D) : IsIrreducibleMorphism (E.functor.map f) := by
  refine
    { not_isSplitMono := ?_
      not_isSplitEpi := ?_
      factorization := ?_ }
  · intro hs
    exact hf.not_isSplitMono ((E.functor.isSplitMono_iff f).mp hs)
  · intro hs
    exact hf.not_isSplitEpi ((E.functor.isSplitEpi_iff f).mp hs)
  · intro M g h hgh
    let e : E.functor.obj (E.inverse.obj M) ≅ M := E.counitIso.app M
    let g' : X ⟶ E.inverse.obj M :=
      E.functor.preimage (g ≫ e.inv)
    let h' : E.inverse.obj M ⟶ Y :=
      E.functor.preimage (e.hom ≫ h)
    have hfactor : g' ≫ h' = f := by
      apply E.functor.map_injective
      simp only [g', h', E.functor.map_comp, E.functor.map_preimage]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, hgh]
    rcases hf.factorization g' h' hfactor with hg' | hh'
    · left
      letI : IsSplitMono g' := hg'
      have hgeq : E.functor.map g' ≫ e.hom = g := by
        simp [g', e, Category.assoc]
      rw [← hgeq]
      infer_instance
    · right
      letI : IsSplitEpi h' := hh'
      have hheq : e.inv ≫ E.functor.map h' = h := by
        simp [h', e]
      rw [← hheq]
      infer_instance

/-- Precomposition by an isomorphism preserves irreducibility. -/
theorem IsIrreducibleMorphism.precomp_iso
    {X Y X' : C} {f : X ⟶ Y} (hf : IsIrreducibleMorphism f)
    (e : X' ≅ X) : IsIrreducibleMorphism (e.hom ≫ f) := by
  refine
    { not_isSplitMono := ?_
      not_isSplitEpi := ?_
      factorization := ?_ }
  · intro hs
    apply hf.not_isSplitMono
    letI : IsSplitMono (e.hom ≫ f) := hs
    have heq : e.inv ≫ (e.hom ≫ f) = f := by simp
    rw [← heq]
    infer_instance
  · intro hs
    apply hf.not_isSplitEpi
    letI : IsSplitEpi (e.hom ≫ f) := hs
    have heq : e.inv ≫ (e.hom ≫ f) = f := by simp
    rw [← heq]
    infer_instance
  · intro M g h hgh
    have hfactor : (e.inv ≫ g) ≫ h = f := by
      rw [Category.assoc, hgh]
      simp
    rcases hf.factorization (e.inv ≫ g) h hfactor with hg | hh
    · left
      letI : IsSplitMono (e.inv ≫ g) := hg
      have hgeq : e.hom ≫ (e.inv ≫ g) = g := by simp
      rw [← hgeq]
      infer_instance
    · exact Or.inr hh

/-- Postcomposition by an isomorphism preserves irreducibility. -/
theorem IsIrreducibleMorphism.postcomp_iso
    {X Y Y' : C} {f : X ⟶ Y} (hf : IsIrreducibleMorphism f)
    (e : Y ≅ Y') : IsIrreducibleMorphism (f ≫ e.hom) := by
  refine
    { not_isSplitMono := ?_
      not_isSplitEpi := ?_
      factorization := ?_ }
  · intro hs
    apply hf.not_isSplitMono
    letI : IsSplitMono (f ≫ e.hom) := hs
    have heq : (f ≫ e.hom) ≫ e.inv = f := by simp
    rw [← heq]
    infer_instance
  · intro hs
    apply hf.not_isSplitEpi
    letI : IsSplitEpi (f ≫ e.hom) := hs
    have heq : (f ≫ e.hom) ≫ e.inv = f := by simp
    rw [← heq]
    infer_instance
  · intro M g h hgh
    have hfactor : g ≫ (h ≫ e.inv) = f := by
      rw [← Category.assoc, hgh]
      simp
    rcases hf.factorization g (h ≫ e.inv) hfactor with hg | hh
    · exact Or.inl hg
    · right
      letI : IsSplitEpi (h ≫ e.inv) := hh
      have hheq : (h ≫ e.inv) ≫ e.hom = h := by simp
      rw [← hheq]
      infer_instance

open CategoryTheory.Limits

section Abelian

variable [Abelian C] [Abelian D]

/-- The cokernel of the contravariant image of a morphism is canonically
isomorphic to the image of its kernel. -/
def cokernelMapOpIsoKernel
    (E : Cᵒᵖ ≌ D) {X Y : C} (f : X ⟶ Y) :
    cokernel (E.functor.map f.op) ≅
      E.functor.obj (Opposite.op (kernel f)) :=
  (PreservesCokernel.iso E.functor f.op).symm ≪≫
    E.functor.mapIso (cokernelOpOp f)

/-- Precomposing the mapped morphism by an endpoint isomorphism does not
change its cokernel. -/
def cokernelPrecompMapOpIsoKernel
    (E : Cᵒᵖ ≌ D) {X Y : C} (f : X ⟶ Y)
    {Y' : D} (i : Y' ≅ E.functor.obj (Opposite.op Y)) :
    cokernel (i.hom ≫ E.functor.map f.op) ≅
      E.functor.obj (Opposite.op (kernel f)) :=
  (cokernel.mapIso
      (i.hom ≫ E.functor.map f.op) (E.functor.map f.op)
      i (Iso.refl _) (by simp)).trans
    (cokernelMapOpIsoKernel E f)

end Abelian

end QuotientSubmoduleEquidistribution
