import QuotientSubmoduleEquidistribution.RepresentationTheory.SeparatedTriangularAlgebraEquivalence
import QuotientSubmoduleEquidistribution.RepresentationTheory.TrivSqZeroExtSeparatedIndecomposable
import QuotientSubmoduleEquidistribution.RepresentationTheory.SimpleLevels
import Mathlib.Algebra.Category.ModuleCat.Simple
import QuotientSubmoduleEquidistribution.Foundation.RingTheory.KrullSchmidt.Indecomposable

/-!
# Indecomposable and simple triangular realizations

The full faithful triangular realization preserves and reflects the
idempotent characterization of indecomposability.  Pure top-side and pure
radical-side separated data realize simple modules whenever their nonzero
layer is simple over the semisimple base.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.SeparatedTriangularAlgebra

open TrivSqZeroExtSeparatedData
open TrivSqZeroExtSeparatedIndecomposable

universe u v w

variable {S : Type u} {J : Type v}
variable [CommRing S] [AddCommGroup J]
variable [Module S J] [Module Sᵐᵒᵖ J]
variable [SMulCommClass S Sᵐᵒᵖ J]

/-- A separated datum is indecomposable exactly when its triangular-algebra
realization is indecomposable. -/
theorem realized_isIndecomposable_iff
    (D : SeparatedData.{u, v, w} (S := S) (J := J)) :
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule (Algebra S J) (Realized D) ↔
      IsIndecomposableSeparatedData D := by
  let F := realizationFunctor (S := S) (J := J)
  constructor
  · intro hD
    refine ⟨hD.nontrivial, ?_⟩
    intro p hp
    have hpmap : F.map p ≫ F.map p = F.map p := by
      rw [← F.map_comp, hp]
    have hpIdem : IsIdempotentElem (F.map p).hom := by
      change (F.map p).hom.comp (F.map p).hom = (F.map p).hom
      exact congrArg ModuleCat.Hom.hom hpmap
    rcases hD.eq_zero_or_eq_one_of_isIdempotentElem hpIdem with
      hzero | hone
    · left
      apply F.map_injective
      apply ModuleCat.Hom.ext
      exact hzero
    · right
      apply F.map_injective
      apply ModuleCat.Hom.ext
      exact hone
  · intro hD
    letI : Nontrivial (Realized D) := hD.1
    apply QuotientSubmoduleEquidistribution.Foundation.isIndecomposableModule_of_forall_isIdempotentElem
    intro f hf
    let fCat : realizedModuleCat D ⟶ realizedModuleCat D :=
      ModuleCat.ofHom f
    obtain ⟨p, hp⟩ := F.map_surjective fCat
    have hpIdem : p ≫ p = p := by
      apply F.map_injective
      rw [F.map_comp, hp]
      apply ModuleCat.Hom.ext
      exact hf
    rcases hD.2 p hpIdem with hzero | hone
    · left
      have hfCat : fCat = 0 := by
        rw [← hp]
        simp [hzero]
        rfl
      exact congrArg ModuleCat.Hom.hom hfCat
    · right
      have hfCat : fCat = 𝟙 _ := by
        rw [← hp]
        simp [hone]
        rfl
      exact congrArg ModuleCat.Hom.hom hfCat

/-- Extracting separated data from an indecomposable triangular module gives
an intrinsically indecomposable separated datum. -/
theorem ofModule_isIndecomposableSeparatedData
    (X : ModuleCat.{w} (Algebra S J))
    (hX : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule (Algebra S J) X) :
    IsIndecomposableSeparatedData (ofModule (S := S) (J := J) X) := by
  let D := ofModule (S := S) (J := J) X
  let e := realizedOfModuleIso (S := S) (J := J) X
  have hRealized : @QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule
      (Algebra S J) (Realized D) _ _ (realizedModule D) :=
    @QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule.of_linearEquiv
      (Algebra S J) X _ _ X.isModule
      (Realized D) _ (realizedModule D)
      hX e.symm.toLinearEquiv
  exact (realized_isIndecomposable_iff D).1 hRealized

omit [SMulCommClass S Sᵐᵒᵖ J] in
/-- If an indecomposable separated datum has zero radical layer, then its top
layer is indecomposable over the base. -/
theorem top_isIndecomposable_of_radical_subsingleton
    (D : SeparatedData.{u, v, w} (S := S) (J := J))
    (hD : IsIndecomposableSeparatedData D) [Subsingleton D.radical] :
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule S D.top := by
  haveI : Nontrivial D.top := by
    rw [← not_subsingleton_iff_nontrivial]
    intro htop
    letI : Subsingleton D.top := htop
    exact not_subsingleton_iff_nontrivial.mpr hD.1
      (inferInstance : Subsingleton (D.top × D.radical))
  apply QuotientSubmoduleEquidistribution.Foundation.isIndecomposableModule_of_forall_isIdempotentElem
  intro f hf
  let p : D ⟶ D :=
    ⟨(f, 0), by
      intro j t
      exact Subsingleton.elim _ _⟩
  have hp : p ≫ p = p := by
    apply Subtype.ext
    apply Prod.ext
    · exact hf
    · ext d
      exact Subsingleton.elim _ _
  rcases hD.2 p hp with hpzero | hpone
  · left
    exact congrArg (fun q ↦ q.val.1) hpzero
  · right
    exact congrArg (fun q ↦ q.val.1) hpone

omit [SMulCommClass S Sᵐᵒᵖ J] in
/-- If an indecomposable separated datum has zero top layer, then its radical
layer is indecomposable over the base. -/
theorem radical_isIndecomposable_of_top_subsingleton
    (D : SeparatedData.{u, v, w} (S := S) (J := J))
    (hD : IsIndecomposableSeparatedData D) [Subsingleton D.top] :
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule S D.radical := by
  haveI : Nontrivial D.radical := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hrad
    letI : Subsingleton D.radical := hrad
    exact not_subsingleton_iff_nontrivial.mpr hD.1
      (inferInstance : Subsingleton (D.top × D.radical))
  apply QuotientSubmoduleEquidistribution.Foundation.isIndecomposableModule_of_forall_isIdempotentElem
  intro f hf
  let p : D ⟶ D :=
    ⟨(0, f), by
      intro j t
      rw [show t = 0 from Subsingleton.elim _ _]
      simp⟩
  have hp : p ≫ p = p := by
    apply Subtype.ext
    apply Prod.ext
    · ext t
      exact Subsingleton.elim _ _
    · exact hf
  rcases hD.2 p hp with hpzero | hpone
  · left
    exact congrArg (fun q ↦ q.val.2) hpzero
  · right
    exact congrArg (fun q ↦ q.val.2) hpone

/-- Projection of the triangular algebra onto the scalar acting on the top
side. -/
def topAugmentation : Algebra S J →+* S :=
  (RingHom.snd S S).comp
    (TrivSqZeroExtRadical.augmentation
      (S := S × S) (J := SeparatedIdeal S J))

/-- Projection of the triangular algebra onto the scalar acting on the
radical side. -/
def radicalAugmentation : Algebra S J →+* S :=
  (RingHom.fst S S).comp
    (TrivSqZeroExtRadical.augmentation
      (S := S × S) (J := SeparatedIdeal S J))

theorem topAugmentation_surjective :
    Function.Surjective (topAugmentation (S := S) (J := J)) := by
  intro s
  exact ⟨TrivSqZeroExt.inl ((0, s) : S × S), rfl⟩

theorem radicalAugmentation_surjective :
    Function.Surjective (radicalAugmentation (S := S) (J := J)) := by
  intro s
  exact ⟨TrivSqZeroExt.inl ((s, 0) : S × S), rfl⟩

/-- If the radical layer is zero and the top layer is simple, the realized
triangular-algebra module is simple. -/
theorem realized_simple_of_top
    (D : SeparatedData.{u, v, w} (S := S) (J := J))
    (hTop : IsSimpleModule S D.top) [Subsingleton D.radical] :
    Simple (realizedModuleCat D) := by
  letI : Module (Algebra S J) D.top :=
    Module.compHom D.top (topAugmentation (S := S) (J := J))
  letI : RingHomSurjective (topAugmentation (S := S) (J := J)) :=
    ⟨topAugmentation_surjective (S := S) (J := J)⟩
  let l : D.top →ₛₗ[topAugmentation (S := S) (J := J)] D.top :=
    { toFun := id
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hl : Function.Bijective l := Function.bijective_id
  have hTopA : IsSimpleModule (Algebra S J) D.top :=
    (l.isSimpleModule_iff_of_bijective hl).2 hTop
  let e : Realized D ≃ₗ[Algebra S J] D.top :=
    { toFun := Prod.fst
      invFun := fun t ↦ (t, 0)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      left_inv := fun x ↦ Prod.ext rfl (Subsingleton.elim _ _)
      right_inv := fun _ ↦ rfl }
  have hRealized : IsSimpleModule (Algebra S J) (Realized D) :=
    (e.isSimpleModule_iff).2 hTopA
  exact (simple_iff_isSimpleModule' (realizedModuleCat D)).2 hRealized

/-- If the top layer is zero and the radical layer is simple, the realized
triangular-algebra module is simple. -/
theorem realized_simple_of_radical
    (D : SeparatedData.{u, v, w} (S := S) (J := J))
    [Subsingleton D.top]
    (hRadical : IsSimpleModule S D.radical) :
    Simple (realizedModuleCat D) := by
  letI : Module (Algebra S J) D.radical :=
    Module.compHom D.radical
      (radicalAugmentation (S := S) (J := J))
  letI : RingHomSurjective
      (radicalAugmentation (S := S) (J := J)) :=
    ⟨radicalAugmentation_surjective (S := S) (J := J)⟩
  let l : D.radical →ₛₗ[radicalAugmentation (S := S) (J := J)]
      D.radical :=
    { toFun := id
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hl : Function.Bijective l := Function.bijective_id
  have hRadicalA : IsSimpleModule (Algebra S J) D.radical :=
    (l.isSimpleModule_iff_of_bijective hl).2 hRadical
  let e : Realized D ≃ₗ[Algebra S J] D.radical :=
    { toFun := Prod.snd
      invFun := fun d ↦ (0, d)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r x ↦ by
        change r.fst.1 • x.2 + D.action r.snd.val x.1 =
          r.fst.1 • x.2
        rw [show x.1 = 0 from Subsingleton.elim _ _, map_zero, add_zero]
      left_inv := fun x ↦ Prod.ext (Subsingleton.elim _ _) rfl
      right_inv := fun _ ↦ rfl }
  have hRealized : IsSimpleModule (Algebra S J) (Realized D) :=
    (e.isSimpleModule_iff).2 hRadicalA
  exact (simple_iff_isSimpleModule' (realizedModuleCat D)).2 hRealized

/-- Separated data concentrated in the radical-side layer. -/
def radicalOnly (M : ModuleCat.{w} S) :
    SeparatedData.{u, v, w} (S := S) (J := J) where
  top := ModuleCat.of S PUnit
  radical := M
  action := 0
  action_left_smul := by intros; simp
  action_right_smul := by intros; simp

instance radicalOnly_top_subsingleton (M : ModuleCat.{w} S) :
    Subsingleton (radicalOnly (J := J) M).top := by
  change Subsingleton PUnit
  infer_instance

/-- A radical-only datum on a simple base module realizes a simple
triangular-algebra module. -/
theorem radicalOnly_simple (M : ModuleCat.{w} S)
    (hM : IsSimpleModule S M) :
    Simple (realizedModuleCat (radicalOnly (J := J) M)) :=
  realized_simple_of_radical (radicalOnly (J := J) M) hM

/-- Over a semisimple base, an indecomposable separated datum concentrated
on its top layer realizes a simple triangular-algebra module. -/
theorem realized_simple_of_indec_of_radical_subsingleton
    [IsSemisimpleRing S]
    (D : SeparatedData.{u, v, w} (S := S) (J := J))
    (hD : IsIndecomposableSeparatedData D) [Subsingleton D.radical] :
    Simple (realizedModuleCat D) := by
  exact realized_simple_of_top D
    (IndecomposableSkeleton.isSimpleModule_of_semisimple_of_indecomposable
      (top_isIndecomposable_of_radical_subsingleton D hD))

/-- Over a semisimple base, an indecomposable separated datum concentrated
on its radical layer realizes a simple triangular-algebra module. -/
theorem realized_simple_of_indec_of_top_subsingleton
    [IsSemisimpleRing S]
    (D : SeparatedData.{u, v, w} (S := S) (J := J))
    (hD : IsIndecomposableSeparatedData D) [Subsingleton D.top] :
    Simple (realizedModuleCat D) := by
  exact realized_simple_of_radical D
    (IndecomposableSkeleton.isSimpleModule_of_semisimple_of_indecomposable
      (radical_isIndecomposable_of_top_subsingleton D hD))

/-- A separated realization with both layers nonzero is not simple. -/
theorem realized_not_simple_of_top_radical_nontrivial
    (D : SeparatedData.{u, v, w} (S := S) (J := J))
    [Nontrivial D.top] [Nontrivial D.radical] :
    ¬ Simple (realizedModuleCat D) := by
  intro hsimple
  letI : IsSimpleModule (Algebra S J) (Realized D) :=
    (simple_iff_isSimpleModule' (realizedModuleCat D)).1 hsimple
  let N : Submodule (Algebra S J) (Realized D) := {
    carrier := {x | x.1 = 0}
    zero_mem' := rfl
    add_mem' := by
      intro x y hx hy
      change x.1 + y.1 = 0
      rw [hx, hy, add_zero]
    smul_mem' := by
      intro r x hx
      change r.fst.2 • x.1 = 0
      rw [hx, smul_zero] }
  rcases eq_bot_or_eq_top N with hbot | htop
  · obtain ⟨d, hd⟩ := exists_ne (0 : D.radical)
    have hm : ((0, d) : Realized D) ∈ N := rfl
    rw [hbot] at hm
    have hz : ((0, d) : Realized D) = 0 := hm
    exact hd (congrArg Prod.snd hz)
  · obtain ⟨t, ht⟩ := exists_ne (0 : D.top)
    have hm : ((t, 0) : Realized D) ∈ N := by
      rw [htop]
      exact Submodule.mem_top
    exact ht hm

end QuotientSubmoduleEquidistribution.SeparatedTriangularAlgebra
