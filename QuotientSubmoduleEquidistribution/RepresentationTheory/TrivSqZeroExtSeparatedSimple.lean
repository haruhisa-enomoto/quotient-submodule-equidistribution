import QuotientSubmoduleEquidistribution.RepresentationTheory.SeparatedTriangularIndecomposable
import QuotientSubmoduleEquidistribution.RepresentationTheory.TrivSqZeroExtSeparatedCorrespondence
import QuotientSubmoduleEquidistribution.RepresentationTheory.TrivSqZeroExtSeparatedModuleFunctor

/-!
# Simple modules and the two pure separated copies

A simple module over a semisimple-base trivial square-zero extension is
already simple after restriction to the base: the square-zero ideal lies in
the ring radical and therefore acts by zero.  Its separated datum is the
covered top-side simple, while the same base simple placed on the radical
side gives the free separated simple.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.TrivSqZeroExtSeparatedSimple

open TrivSqZeroExtRadical
open TrivSqZeroExtSeparatedCorrespondence
open TrivSqZeroExtSeparatedData
open SeparatedTriangularAlgebra

universe u v w

variable {S : Type u} {J : Type v}
variable [CommRing S] [AddCommGroup J]
variable [Module S J] [Module Sᵐᵒᵖ J]
variable [SMulCommClass S Sᵐᵒᵖ J]
variable [IsSemisimpleRing S]

/-- Restriction along the base inclusion preserves simplicity for a simple
module over the trivial extension. -/
theorem restrictInl_isSimpleModule
    (X : ModuleCat.{w} (TrivSqZeroExt S J))
    (hX : IsSimpleModule (TrivSqZeroExt S J) X) :
    @IsSimpleModule S _ X _
      (Module.compHom X (TrivSqZeroExt.inlHom S J)) := by
  let R := TrivSqZeroExt S J
  let i := TrivSqZeroExt.inlHom S J
  let a := augmentation (S := S) (J := J)
  letI : IsSimpleModule R X := hX
  letI : Module S X := Module.compHom X i
  letI : RingHomSurjective a :=
    ⟨fun s ↦ ⟨TrivSqZeroExt.inl s, rfl⟩⟩
  have hinr_zero (j : J) (x : X) :
      (TrivSqZeroExt.inr j : R) • x = 0 := by
    apply Module.mem_annihilator.mp
    apply IsSemisimpleModule.jacobson_le_annihilator R X
    rw [← augmentationIdeal_eq_jacobson (S := S) (J := J)]
    rfl
  let l : X →ₛₗ[a] X :=
    { toFun := id
      map_add' := fun _ _ ↦ rfl
      map_smul' := by
        intro r x
        change r • x = (TrivSqZeroExt.inl r.fst : R) • x
        calc
          r • x = (TrivSqZeroExt.inl r.fst +
              TrivSqZeroExt.inr r.snd : R) • x := by
            exact congrArg (fun q : R ↦ q • x)
              (TrivSqZeroExt.inl_fst_add_inr_snd_eq r).symm
          _ = (TrivSqZeroExt.inl r.fst : R) • x := by
            rw [add_smul, hinr_zero, add_zero] }
  exact (l.isSimpleModule_iff_of_bijective Function.bijective_id).1 hX

/-- The top layer of the separated datum of a simple trivial-extension
module is simple over the semisimple base. -/
theorem moduleSeparatedData_top_isSimpleModule
    (X : ModuleCat.{w} (TrivSqZeroExt S J))
    (hX : IsSimpleModule (TrivSqZeroExt S J) X) :
    IsSimpleModule S
      (moduleSeparatedData (S := S) (J := J) X).top := by
  let R := TrivSqZeroExt S J
  let RX := Module.jacobson R X
  letI : IsSimpleModule R X := hX
  letI : Module S X :=
    Module.compHom X (TrivSqZeroExt.inlHom S J)
  letI : IsSimpleModule S X := restrictInl_isSimpleModule X hX
  have hrad : RX = ⊥ := IsSimpleModule.jacobson_eq_bot R X
  let eR : (X ⧸ RX) ≃ₗ[R] X := RX.quotEquivOfEqBot hrad
  let eS :
      (moduleSeparatedData (S := S) (J := J) X).top ≃ₗ[S] X :=
    { toFun := eR
      invFun := eR.symm
      map_add' := eR.map_add
      map_smul' := by
        intro s x
        exact eR.map_smul (TrivSqZeroExt.inl s) x
      left_inv := eR.left_inv
      right_inv := eR.right_inv }
  exact IsSimpleModule.congr eS

/-- The radical layer of the separated datum of a simple module is zero. -/
theorem moduleSeparatedData_radical_subsingleton
    (X : ModuleCat.{w} (TrivSqZeroExt S J))
    (hX : IsSimpleModule (TrivSqZeroExt S J) X) :
    Subsingleton
      (moduleSeparatedData (S := S) (J := J) X).radical := by
  letI : IsSimpleModule (TrivSqZeroExt S J) X := hX
  change Subsingleton (Module.jacobson (TrivSqZeroExt S J) X)
  rw [IsSimpleModule.jacobson_eq_bot (TrivSqZeroExt S J) X]
  infer_instance

/-- The separated datum of an original simple realizes the covered simple
of the triangular algebra. -/
theorem covered_realized_simple
    (X : ModuleCat.{w} (TrivSqZeroExt S J))
    (hX : IsSimpleModule (TrivSqZeroExt S J) X) :
    Simple (realizedModuleCat
      (moduleSeparatedData (S := S) (J := J) X)) := by
  letI : Subsingleton
      (moduleSeparatedData (S := S) (J := J) X).radical :=
    moduleSeparatedData_radical_subsingleton X hX
  exact realized_simple_of_top _
    (moduleSeparatedData_top_isSimpleModule X hX)

/-- The free separated copy attached to an original simple module. -/
def freeData (X : ModuleCat.{w} (TrivSqZeroExt S J)) :
    SeparatedData.{u, v, w} (S := S) (J := J) :=
  radicalOnly (J := J)
    (moduleSeparatedData (S := S) (J := J) X).top

instance freeData_top_subsingleton
    (X : ModuleCat.{w} (TrivSqZeroExt S J)) :
    Subsingleton (freeData (S := S) (J := J) X).top := by
  change Subsingleton PUnit
  infer_instance

/-- Isomorphic original modules give isomorphic free separated copies. -/
def freeDataIsoOfModuleIso
    {X Y : ModuleCat.{w} (TrivSqZeroExt S J)} (e : X ≅ Y) :
    realizedModuleCat (freeData (S := S) (J := J) X) ≅
      realizedModuleCat (freeData (S := S) (J := J) Y) := by
  let F := TrivSqZeroExtSeparatedModuleFunctor.moduleSeparatedDataFunctor
    (S := S) (J := J)
  let eSep := F.mapIso e
  let DX := freeData (S := S) (J := J) X
  let DY := freeData (S := S) (J := J) Y
  let eData : DX ≅ DY :=
    { hom := ⟨(0, eSep.hom.val.1), by
          intro j t
          change eSep.hom.val.1 (0 : DX.radical) = DY.action j 0
          exact eSep.hom.val.1.map_zero.trans (map_zero (DY.action j)).symm⟩
      inv := ⟨(0, eSep.inv.val.1), by
          intro j t
          change eSep.inv.val.1 (0 : DY.radical) = DX.action j 0
          exact eSep.inv.val.1.map_zero.trans (map_zero (DX.action j)).symm⟩
      hom_inv_id := by
        apply Subtype.ext
        apply Prod.ext
        · ext t
          exact Subsingleton.elim _ _
        · have h := congrArg (fun q ↦ q.val.1) eSep.hom_inv_id
          exact h
      inv_hom_id := by
        apply Subtype.ext
        apply Prod.ext
        · ext t
          exact Subsingleton.elim _ _
        · have h := congrArg (fun q ↦ q.val.1) eSep.inv_hom_id
          exact h }
  exact (realizationFunctor (S := S) (J := J)).mapIso eData

/-- The free separated copy attached to an original simple is simple over
the triangular algebra. -/
theorem free_realized_simple
    (X : ModuleCat.{w} (TrivSqZeroExt S J))
    (hX : IsSimpleModule (TrivSqZeroExt S J) X) :
    Simple (realizedModuleCat (freeData (S := S) (J := J) X)) :=
  radicalOnly_simple _ (moduleSeparatedData_top_isSimpleModule X hX)

omit [IsSemisimpleRing S] in
/-- A reconstructed separated datum with simple top and zero radical is a
simple module over the original trivial extension. -/
theorem reconstructed_simple_of_top
    (D : SeparatedData.{u, v, w} (S := S) (J := J))
    (hTop : IsSimpleModule S D.top) [Subsingleton D.radical] :
    Simple (reconstructedModuleCat D) := by
  let a := augmentation (S := S) (J := J)
  letI : Module (TrivSqZeroExt S J) D.top := Module.compHom D.top a
  letI : RingHomSurjective a :=
    ⟨fun s ↦ ⟨TrivSqZeroExt.inl s, rfl⟩⟩
  let l : D.top →ₛₗ[a] D.top :=
    { toFun := id
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hTopR : IsSimpleModule (TrivSqZeroExt S J) D.top :=
    (l.isSimpleModule_iff_of_bijective Function.bijective_id).2 hTop
  let e : Reconstructed D ≃ₗ[TrivSqZeroExt S J] D.top :=
    { toFun := Prod.fst
      invFun := fun t ↦ (t, 0)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      left_inv := fun x ↦ Prod.ext rfl (Subsingleton.elim _ _)
      right_inv := fun _ ↦ rfl }
  have hRec : IsSimpleModule (TrivSqZeroExt S J) (Reconstructed D) :=
    (e.isSimpleModule_iff).2 hTopR
  exact (simple_iff_isSimpleModule' (reconstructedModuleCat D)).2 hRec

omit [IsSemisimpleRing S] in
/-- A reconstructed separated datum with zero top and simple radical is a
simple module over the original trivial extension. -/
theorem reconstructed_simple_of_radical
    (D : SeparatedData.{u, v, w} (S := S) (J := J))
    [Subsingleton D.top]
    (hRadical : IsSimpleModule S D.radical) :
    Simple (reconstructedModuleCat D) := by
  let a := augmentation (S := S) (J := J)
  letI : Module (TrivSqZeroExt S J) D.radical := Module.compHom D.radical a
  letI : RingHomSurjective a :=
    ⟨fun s ↦ ⟨TrivSqZeroExt.inl s, rfl⟩⟩
  let l : D.radical →ₛₗ[a] D.radical :=
    { toFun := id
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hRadicalR : IsSimpleModule (TrivSqZeroExt S J) D.radical :=
    (l.isSimpleModule_iff_of_bijective Function.bijective_id).2 hRadical
  let e : Reconstructed D ≃ₗ[TrivSqZeroExt S J] D.radical :=
    { toFun := Prod.snd
      invFun := fun d ↦ (0, d)
      map_add' := fun _ _ ↦ rfl
      map_smul' := by
        intro r x
        change r.fst • x.2 + D.action r.snd x.1 = r.fst • x.2
        rw [show x.1 = 0 from Subsingleton.elim _ _, map_zero, add_zero]
      left_inv := fun x ↦ Prod.ext (Subsingleton.elim _ _) rfl
      right_inv := fun _ ↦ rfl }
  have hRec : IsSimpleModule (TrivSqZeroExt S J) (Reconstructed D) :=
    (e.isSimpleModule_iff).2 hRadicalR
  exact (simple_iff_isSimpleModule' (reconstructedModuleCat D)).2 hRec

omit [IsSemisimpleRing S] in
/-- A reconstructed separated module with both layers nonzero is not simple. -/
theorem reconstructed_not_simple_of_top_radical_nontrivial
    (D : SeparatedData.{u, v, w} (S := S) (J := J))
    [Nontrivial D.top] [Nontrivial D.radical] :
    ¬ Simple (reconstructedModuleCat D) := by
  intro hsimple
  letI : IsSimpleModule (TrivSqZeroExt S J) (Reconstructed D) :=
    (simple_iff_isSimpleModule' (reconstructedModuleCat D)).1 hsimple
  let N := declaredRadical D
  rcases eq_bot_or_eq_top N with hbot | htop
  · obtain ⟨d, hd⟩ := exists_ne (0 : D.radical)
    have hm : ((0, d) : Reconstructed D) ∈ N := rfl
    rw [hbot] at hm
    have hz : ((0, d) : Reconstructed D) = 0 := hm
    exact hd (congrArg Prod.snd hz)
  · obtain ⟨t, ht⟩ := exists_ne (0 : D.top)
    have hm : ((t, 0) : Reconstructed D) ∈ N := by
      rw [htop]
      exact Submodule.mem_top
    exact ht hm

/-- For a radical-only indecomposable datum, taking the module top of its
simple reconstruction and then forming the free copy recovers the original
datum after triangular realization. -/
def freeDataReconstructedIso
    (D : SeparatedData.{u, v, w} (S := S) (J := J))
    [Subsingleton D.top]
    (hRadical : IsSimpleModule S D.radical) :
    realizedModuleCat
        (freeData (S := S) (J := J) (reconstructedModuleCat D)) ≅
      realizedModuleCat D := by
  let R := TrivSqZeroExt S J
  let X := reconstructedModuleCat D
  have hSimpleCat : Simple X := reconstructed_simple_of_radical D hRadical
  letI : IsSimpleModule R X :=
    (simple_iff_isSimpleModule' X).1 hSimpleCat
  letI : Module S X :=
    Module.compHom X (TrivSqZeroExt.inlHom S J)
  let RX := Module.jacobson R X
  have hRX : RX = ⊥ := IsSimpleModule.jacobson_eq_bot R X
  let eR : (X ⧸ RX) ≃ₗ[R] X := RX.quotEquivOfEqBot hRX
  let eTopX :
      (moduleSeparatedData (S := S) (J := J) X).top ≃ₗ[S] X :=
    { toFun := eR
      invFun := eR.symm
      map_add' := eR.map_add
      map_smul' := by
        intro s x
        exact eR.map_smul (TrivSqZeroExt.inl s) x
      left_inv := eR.left_inv
      right_inv := eR.right_inv }
  let eRad : X ≃ₗ[S] D.radical :=
    { toFun := Prod.snd
      invFun := fun d ↦ (0, d)
      map_add' := fun _ _ ↦ rfl
      map_smul' := by
        intro s x
        change s • x.2 + D.action 0 x.1 = s • x.2
        rw [map_zero, AddMonoidHom.zero_apply, add_zero]
      left_inv := fun x ↦ Prod.ext (Subsingleton.elim _ _) rfl
      right_inv := fun _ ↦ rfl }
  let eTop :
      (moduleSeparatedData (S := S) (J := J) X).top ≃ₗ[S]
        D.radical :=
    eTopX.trans eRad
  let E := freeData (S := S) (J := J) X
  let eData : E ≅ D :=
    { hom := ⟨(0, eTop.toLinearMap), by
          intro j t
          change eTop (0 : E.radical) = D.action j 0
          exact eTop.map_zero.trans (map_zero (D.action j)).symm⟩
      inv := ⟨(0, eTop.symm.toLinearMap), by
          intro j t
          rw [show t = 0 from Subsingleton.elim _ _]
          simp⟩
      hom_inv_id := by
        apply Subtype.ext
        apply Prod.ext
        · ext t
          exact Subsingleton.elim _ _
        · ext d
          exact eTop.symm_apply_apply d
      inv_hom_id := by
        apply Subtype.ext
        apply Prod.ext
        · ext t
          exact Subsingleton.elim _ _
        · ext d
          exact eTop.apply_symm_apply d }
  exact (realizationFunctor (S := S) (J := J)).mapIso eData

end QuotientSubmoduleEquidistribution.TrivSqZeroExtSeparatedSimple
