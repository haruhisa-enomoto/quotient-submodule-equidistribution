import OpConjecture.RepresentationTheory.TrivSqZeroExtSeparatedCorrespondence

/-!
# The module-to-separated-data functor

Module homomorphisms induce action-compatible maps on the top and radical.
This file packages those maps as an additive functor and records that its
Hom-kernel is square-zero.  The latter is the precise categorical mechanism
behind preservation and reflection of indecomposability.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace OpConjecture.TrivSqZeroExtSeparatedModuleFunctor

open ModuleRadicalLayerComparison
open TrivSqZeroExtSeparatedFunctor
open TrivSqZeroExtSeparatedData
open TrivSqZeroExtSeparatedCorrespondence
open TrivSqZeroExtRadical

universe u v w

variable {S : Type u} {J : Type v}
variable [CommRing S] [AddCommGroup J]
variable [Module S J] [Module Sᵐᵒᵖ J]
variable [SMulCommClass S Sᵐᵒᵖ J]
variable [IsSemisimpleRing S]

/-- Restriction to `S` of the map induced on module tops. -/
def moduleTopMapS
    {X Y : ModuleCat.{w} (TrivSqZeroExt S J)} (f : X ⟶ Y) :
    moduleTopS (S := S) (J := J) X →ₗ[S]
      moduleTopS (S := S) (J := J) Y where
  toFun := topMap f.hom
  map_add' := (topMap f.hom).map_add
  map_smul' s q := by
    change topMap f.hom
      ((TrivSqZeroExt.inl s : TrivSqZeroExt S J) • q) =
      (TrivSqZeroExt.inl s : TrivSqZeroExt S J) • topMap f.hom q
    exact (topMap f.hom).map_smul (TrivSqZeroExt.inl s) q

/-- Restriction to `S` of the map induced on module radicals. -/
def moduleRadicalMapS
    {X Y : ModuleCat.{w} (TrivSqZeroExt S J)} (f : X ⟶ Y) :
    moduleRadicalS (S := S) (J := J) X →ₗ[S]
      moduleRadicalS (S := S) (J := J) Y where
  toFun := radicalMap f.hom
  map_add' := (radicalMap f.hom).map_add
  map_smul' s x := by
    change radicalMap f.hom
      ((TrivSqZeroExt.inl s : TrivSqZeroExt S J) • x) =
      (TrivSqZeroExt.inl s : TrivSqZeroExt S J) • radicalMap f.hom x
    exact (radicalMap f.hom).map_smul (TrivSqZeroExt.inl s) x

/-- A module homomorphism induces a morphism of its separated data. -/
def moduleSeparatedDataMap
    {X Y : ModuleCat.{w} (TrivSqZeroExt S J)} (f : X ⟶ Y) :
    moduleSeparatedData (S := S) (J := J) X ⟶
      moduleSeparatedData (S := S) (J := J) Y := by
  refine ⟨(moduleTopMapS f, moduleRadicalMapS f), ?_⟩
  intro j q
  exact radicalAction_natural f.hom
    (idealInr (S := S) (J := J) j) q

/-- The functor taking a module to its abstract separated datum. -/
def moduleSeparatedDataFunctor :
    ModuleCat.{w} (TrivSqZeroExt S J) ⥤
      SeparatedData.{u, v, w} (S := S) (J := J) where
  obj := moduleSeparatedData
  map := moduleSeparatedDataMap
  map_id X := by
    apply Subtype.ext
    apply Prod.ext
    · ext x
      exact LinearMap.congr_fun
        (topMap_id (R := TrivSqZeroExt S J) (M := X)) x
    · ext x
      exact LinearMap.congr_fun
        (radicalMap_id (R := TrivSqZeroExt S J) (M := X)) x
  map_comp f g := by
    apply Subtype.ext
    apply Prod.ext
    · ext x
      exact LinearMap.congr_fun (topMap_comp g.hom f.hom) x
    · ext x
      exact LinearMap.congr_fun (radicalMap_comp g.hom f.hom) x

instance moduleSeparatedDataFunctor_additive :
    (moduleSeparatedDataFunctor (S := S) (J := J)).Additive where
  map_add := by
    intro X Y f g
    apply Subtype.ext
    apply Prod.ext
    · ext x
      obtain ⟨x, rfl⟩ :=
        (Module.jacobson (TrivSqZeroExt S J) X).mkQ_surjective x
      change (Module.jacobson (TrivSqZeroExt S J) Y).mkQ
          ((f + g).hom x) =
        (Module.jacobson (TrivSqZeroExt S J) Y).mkQ (f.hom x) +
          (Module.jacobson (TrivSqZeroExt S J) Y).mkQ (g.hom x)
      simp
    · ext x
      change radicalMap (f + g).hom x =
        radicalMap f.hom x + radicalMap g.hom x
      rfl

/-- Every action-compatible pair of maps on the separated data lifts to a
module homomorphism. -/
instance moduleSeparatedDataFunctor_full :
    (moduleSeparatedDataFunctor (S := S) (J := J)).Full where
  map_surjective := by
    intro X Y p
    let i := TrivSqZeroExt.inlHom S J
    letI : Module S X := Module.compHom X i
    letI : Module S Y := Module.compHom Y i
    letI : Module S (Module.jacobson (TrivSqZeroExt S J) X) :=
      Module.compHom (Module.jacobson (TrivSqZeroExt S J) X) i
    letI : Module S (Module.jacobson (TrivSqZeroExt S J) Y) :=
      Module.compHom (Module.jacobson (TrivSqZeroExt S J) Y) i
    letI : Module S (X ⧸ Module.jacobson (TrivSqZeroExt S J) X) :=
      Module.compHom (X ⧸ Module.jacobson (TrivSqZeroExt S J) X) i
    letI : Module S (Y ⧸ Module.jacobson (TrivSqZeroExt S J) Y) :=
      Module.compHom (Y ⧸ Module.jacobson (TrivSqZeroExt S J) Y) i
    let pRad : Module.jacobson (TrivSqZeroExt S J) X →ₗ[TrivSqZeroExt S J]
        Module.jacobson (TrivSqZeroExt S J) Y :=
      { toFun := p.val.2
        map_add' := p.val.2.map_add
        map_smul' := by
          intro r x
          have hx : r • x = r.fst • x := by
            apply Subtype.ext
            change r • (x : X) =
              (TrivSqZeroExt.inl r.fst : TrivSqZeroExt S J) • (x : X)
            conv_lhs =>
              rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq r]
            rw [add_smul]
            have hz :
                (TrivSqZeroExt.inr r.snd : TrivSqZeroExt S J) •
                    (x : X) = 0 :=
              augmentation_smul_module_jacobson_eq_zero
                (TrivSqZeroExt.inr r.snd)
                ((mem_augmentationIdeal_iff
                  (TrivSqZeroExt.inr r.snd : TrivSqZeroExt S J)).mpr rfl)
                x.val x.property
            rw [hz, add_zero]
          let y : Module.jacobson (TrivSqZeroExt S J) Y :=
            ⟨(p.val.2 x).val, (p.val.2 x).property⟩
          have hy : r • y = r.fst • y := by
            apply Subtype.ext
            change r • (y : Y) =
              (TrivSqZeroExt.inl r.fst : TrivSqZeroExt S J) •
                (y : Y)
            conv_lhs =>
              rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq r]
            rw [add_smul]
            have hz :
                (TrivSqZeroExt.inr r.snd : TrivSqZeroExt S J) •
                    (y : Y) = 0 :=
              augmentation_smul_module_jacobson_eq_zero
                (TrivSqZeroExt.inr r.snd)
                ((mem_augmentationIdeal_iff
                  (TrivSqZeroExt.inr r.snd : TrivSqZeroExt S J)).mpr rfl)
                y.val y.property
            rw [hz, add_zero]
          change p.val.2 (r • x) = r • y
          rw [hx, hy]
          exact p.val.2.map_smul r.fst x }
    let pTop : (X ⧸ Module.jacobson (TrivSqZeroExt S J) X) →ₗ[TrivSqZeroExt S J]
        (Y ⧸ Module.jacobson (TrivSqZeroExt S J) Y) :=
      { toFun := p.val.1
        map_add' := p.val.1.map_add
        map_smul' := by
          intro r x
          let RX := Module.jacobson (TrivSqZeroExt S J) X
          let RY := Module.jacobson (TrivSqZeroExt S J) Y
          have hx : r • x = r.fst • x := by
            obtain ⟨z, rfl⟩ := RX.mkQ_surjective x
            change RX.mkQ (r • z) =
              RX.mkQ ((TrivSqZeroExt.inl r.fst : TrivSqZeroExt S J) • z)
            conv_lhs =>
              rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq r]
            rw [add_smul, map_add]
            have hz : RX.mkQ
                ((TrivSqZeroExt.inr r.snd : TrivSqZeroExt S J) • z) = 0 := by
              apply (Submodule.Quotient.mk_eq_zero RX).mpr
              change (TrivSqZeroExt.inr r.snd : TrivSqZeroExt S J) • z ∈
                Module.jacobson (TrivSqZeroExt S J) X
              rw [module_jacobson_eq_radicalPart]
              exact Submodule.smul_mem_smul
                ((mem_augmentationIdeal_iff
                  (TrivSqZeroExt.inr r.snd : TrivSqZeroExt S J)).mpr rfl)
                Submodule.mem_top
            rw [hz, add_zero]
          let y : Y ⧸ Module.jacobson (TrivSqZeroExt S J) Y := p.val.1 x
          have hy : r • y = r.fst • y := by
            obtain ⟨z, hz⟩ := RY.mkQ_surjective y
            rw [← hz]
            change RY.mkQ (r • z) =
              RY.mkQ ((TrivSqZeroExt.inl r.fst : TrivSqZeroExt S J) • z)
            conv_lhs =>
              rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq r]
            rw [add_smul, map_add]
            have hz' : RY.mkQ
                ((TrivSqZeroExt.inr r.snd : TrivSqZeroExt S J) • z) = 0 := by
              apply (Submodule.Quotient.mk_eq_zero RY).mpr
              change (TrivSqZeroExt.inr r.snd : TrivSqZeroExt S J) • z ∈
                Module.jacobson (TrivSqZeroExt S J) Y
              rw [module_jacobson_eq_radicalPart]
              exact Submodule.smul_mem_smul
                ((mem_augmentationIdeal_iff
                  (TrivSqZeroExt.inr r.snd : TrivSqZeroExt S J)).mpr rfl)
                Submodule.mem_top
            rw [hz', add_zero]
          change p.val.1 (r • x) = r • y
          rw [hx, hy]
          exact p.val.1.map_smul r.fst x }
    let pLayer :
        (separatedLayerFunctor (S := S) (J := J)).obj X ⟶
          (separatedLayerFunctor (S := S) (J := J)).obj Y :=
      ⟨(pRad, pTop), by
        intro r q
        have hp := p.property r.val.snd q
        have hr : r = idealInr (S := S) (J := J) r.val.snd := by
          apply Subtype.ext
          exact eq_inr_snd_of_mem_augmentationIdeal r.property
        rw [hr]
        exact hp⟩
    obtain ⟨f, hf⟩ := separatedLayerFunctor_map_surjective pLayer
    refine ⟨f, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · ext x
      have h := congrArg (fun q ↦ q.val.2) hf
      exact LinearMap.congr_fun h x
    · ext x
      have h := congrArg (fun q ↦ q.val.1) hf
      exact LinearMap.congr_fun h x

/-- The Hom-kernel of the module-to-separated-data functor is square-zero. -/
theorem moduleSeparatedDataFunctor_kernelSquareZero :
    OpConjecture.CategoryTheory.IdempotentLifting.FunctorKernelSquareZero
      (moduleSeparatedDataFunctor (S := S) (J := J)) := by
  intro X Y Z f g hf hg
  apply separatedLayerFunctor_kernelSquareZero f g
  · apply Subtype.ext
    apply Prod.ext
    · ext x
      have hf' := congrArg (fun p ↦ p.val.2) hf
      let x' : moduleRadicalS (S := S) (J := J) X := x
      exact congrArg Subtype.val (LinearMap.congr_fun hf' x')
    · ext x
      have hf' := congrArg (fun p ↦ p.val.1) hf
      let x' : moduleTopS (S := S) (J := J) X :=
        (Module.jacobson (TrivSqZeroExt S J) X).mkQ x
      exact LinearMap.congr_fun hf' x'
  · apply Subtype.ext
    apply Prod.ext
    · ext x
      have hg' := congrArg (fun p ↦ p.val.2) hg
      let x' : moduleRadicalS (S := S) (J := J) Y := x
      exact congrArg Subtype.val (LinearMap.congr_fun hg' x')
    · ext x
      have hg' := congrArg (fun p ↦ p.val.1) hg
      let x' : moduleTopS (S := S) (J := J) Y :=
        (Module.jacobson (TrivSqZeroExt S J) Y).mkQ x
      exact LinearMap.congr_fun hg' x'

end OpConjecture.TrivSqZeroExtSeparatedModuleFunctor
