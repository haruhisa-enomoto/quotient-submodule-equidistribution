import QuotientSubmoduleEquidistribution.RepresentationTheory.TrivSqZeroExtRadical
import QuotientSubmoduleEquidistribution.RepresentationTheory.ModuleRadicalLayerFunctor

/-!
# The radical-action-compatible separated-layer functor

For a module over a semisimple-base trivial square-zero extension, the previous
files constructed its top, radical, and the descended action of the
augmentation ideal from the top to the radical.  This file defines the
corresponding separated-layer category.

Its objects are module-labelled layer data.  A morphism is a pair consisting
of a map on radicals and a map on tops, subject to the equation that it commute
with every descended radical-action map.  Ordinary module homomorphisms induce
such morphisms, giving an additive functor.  The functor's Hom-kernel is proved
square-zero.

The remaining fullness theorem is deliberately separate: it must construct a
module homomorphism from an action-compatible pair by choosing splittings of
the semisimple tops.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.TrivSqZeroExtSeparatedFunctor

open ModuleRadicalLayerComparison
open TrivSqZeroExtRadical

universe u v w

variable {S : Type u} {J : Type v}
variable [CommRing S] [AddCommGroup J]
variable [Module S J] [Module Sᵐᵒᵖ J]
variable [SMulCommClass S Sᵐᵒᵖ J]
variable [IsSemisimpleRing S]

variable {X : Type w} {Y : Type w}
variable [AddCommGroup X] [Module (TrivSqZeroExt S J) X]
variable [AddCommGroup Y] [Module (TrivSqZeroExt S J) Y]

/-- A module homomorphism intertwines the descended radical actions on its top
and radical layers. -/
theorem radicalAction_natural
    (f : X →ₗ[TrivSqZeroExt S J] Y)
    (r : augmentationIdeal (S := S) (J := J))
    (q : X ⧸ Module.jacobson (TrivSqZeroExt S J) X) :
    radicalMap f (radicalAction r q) =
      radicalAction r (topMap f q) := by
  obtain ⟨x, rfl⟩ :=
    (Module.jacobson (TrivSqZeroExt S J) X).mkQ_surjective q
  apply Subtype.ext
  exact f.map_smul (r : TrivSqZeroExt S J) x

/-- A module-labelled separated-layer object.  Its categorical morphisms will
remember only the top, radical, and radical action. -/
structure SeparatedLayerObject where
  module : ModuleCat.{w} (TrivSqZeroExt S J)

/-- Compatibility of a pair of layer maps with every radical-action arrow. -/
def ActionCompatible
    (X Y : SeparatedLayerObject (S := S) (J := J))
    (p : RadicalLayerHom (R := TrivSqZeroExt S J)
      X.module Y.module) : Prop :=
  ∀ (r : augmentationIdeal (S := S) (J := J))
      (q : X.module ⧸
        Module.jacobson (TrivSqZeroExt S J) X.module),
    p.1 (radicalAction r q) = radicalAction r (p.2 q)

/-- Action-compatible pairs form an additive subgroup of all radical/top
layer pairs. -/
def compatibleHomAddSubgroup
    (X Y : SeparatedLayerObject (S := S) (J := J)) :
    AddSubgroup (RadicalLayerHom (R := TrivSqZeroExt S J)
      X.module Y.module) where
  carrier := ActionCompatible X Y
  zero_mem' := by
    intro r q
    change 0 = radicalAction r 0
    exact (radicalAction r).map_zero.symm
  add_mem' := by
    intro f g hf hg r q
    change f.1 (radicalAction r q) + g.1 (radicalAction r q) =
      radicalAction r (f.2 q + g.2 q)
    rw [hf r q, hg r q, map_add]
  neg_mem' := by
    intro f hf r q
    change -f.1 (radicalAction r q) = radicalAction r (-f.2 q)
    rw [hf r q, map_neg]

/-- Morphisms in the separated-layer category. -/
abbrev SeparatedLayerHom
    (X Y : SeparatedLayerObject (S := S) (J := J)) :=
  ↥(compatibleHomAddSubgroup X Y)

instance separatedLayerCategory :
    Category.{w} (SeparatedLayerObject (S := S) (J := J)) where
  Hom := SeparatedLayerHom
  id _ := ⟨(LinearMap.id, LinearMap.id), by intro r q; rfl⟩
  comp f g :=
    ⟨(g.val.1.comp f.val.1, g.val.2.comp f.val.2), by
      intro r q
      change g.val.1 (f.val.1 (radicalAction r q)) =
        radicalAction r (g.val.2 (f.val.2 q))
      rw [f.property r q, g.property r (f.val.2 q)]⟩
  assoc := by intros; rfl
  id_comp := by intros; rfl
  comp_id := by intros; rfl

instance separatedLayerPreadditive :
    Preadditive (SeparatedLayerObject (S := S) (J := J)) where
  homGroup := fun X Y ↦
    inferInstanceAs (AddCommGroup (compatibleHomAddSubgroup X Y))
  add_comp := by
    intro P Q T f f' g
    apply Subtype.ext
    apply Prod.ext
    · ext x
      exact congrArg Subtype.val
        (g.val.1.map_add (f.val.1 x) (f'.val.1 x))
    · ext x
      exact g.val.2.map_add
        (f.val.2
          ((Module.jacobson (TrivSqZeroExt S J) P.module).mkQ x))
        (f'.val.2
          ((Module.jacobson (TrivSqZeroExt S J) P.module).mkQ x))
  comp_add := by
    intro P Q T f g g'
    apply Subtype.ext
    apply Prod.ext
    · ext x
      rfl
    · ext x
      rfl

/-- The separated-layer functor from modules over the trivial extension. -/
def separatedLayerFunctor :
    ModuleCat.{w} (TrivSqZeroExt S J) ⥤
      SeparatedLayerObject (S := S) (J := J) where
  obj X := ⟨X⟩
  map f := ⟨layerMap f.hom, radicalAction_natural f.hom⟩
  map_id _ := by
    apply Subtype.ext
    apply Prod.ext
    · exact radicalMap_id
    · exact topMap_id
  map_comp f g := by
    apply Subtype.ext
    apply Prod.ext
    · exact radicalMap_comp g.hom f.hom
    · exact topMap_comp g.hom f.hom

instance separatedLayerFunctor_additive :
    (separatedLayerFunctor (S := S) (J := J)).Additive where
  map_add := by
    intro X Y f g
    apply Subtype.ext
    apply Prod.ext
    · ext x
      rfl
    · ext x
      change (Module.jacobson (TrivSqZeroExt S J) Y).mkQ
          ((f + g).hom x) =
        (Module.jacobson (TrivSqZeroExt S J) Y).mkQ (f.hom x) +
          (Module.jacobson (TrivSqZeroExt S J) Y).mkQ (g.hom x)
      simp

/-- Every radical-action-compatible pair of maps on top and radical lifts to
an actual module homomorphism.  The proof chooses `S`-linear splittings of the
two tops, constructs the evident block lift, and uses action compatibility for
the augmentation-ideal part of scalar linearity. -/
theorem separatedLayerFunctor_map_surjective
    {X Y : ModuleCat.{w} (TrivSqZeroExt S J)}
    (p : (separatedLayerFunctor (S := S) (J := J)).obj X ⟶
      (separatedLayerFunctor (S := S) (J := J)).obj Y) :
    ∃ f : X ⟶ Y,
      (separatedLayerFunctor (S := S) (J := J)).map f = p := by
  change SeparatedLayerHom
    (SeparatedLayerObject.mk X) (SeparatedLayerObject.mk Y) at p
  let i := TrivSqZeroExt.inlHom S J
  letI : Module S X := Module.compHom X i
  letI : Module S Y := Module.compHom Y i
  let RX := Module.jacobson (TrivSqZeroExt S J) X
  let RY := Module.jacobson (TrivSqZeroExt S J) Y
  let TX := X ⧸ RX
  let TY := Y ⧸ RY
  letI : Module S RX := Module.compHom RX i
  letI : Module S RY := Module.compHom RY i
  letI : Module S TX := Module.compHom TX i
  letI : Module S TY := Module.compHom TY i
  let qX : X →ₗ[S] TX :=
    { toFun := RX.mkQ
      map_add' := fun _ _ ↦ map_add RX.mkQ _ _
      map_smul' := fun s x ↦
        RX.mkQ.map_smul (TrivSqZeroExt.inl s) x }
  let qY : Y →ₗ[S] TY :=
    { toFun := RY.mkQ
      map_add' := fun _ _ ↦ map_add RY.mkQ _ _
      map_smul' := fun s y ↦
        RY.mkQ.map_smul (TrivSqZeroExt.inl s) y }
  let pTop : TX →ₗ[S] TY :=
    { toFun := p.val.2
      map_add' := fun _ _ ↦ p.val.2.map_add _ _
      map_smul' := fun s x ↦
        p.val.2.map_smul (TrivSqZeroExt.inl s) x }
  let pRad : RX →ₗ[S] RY :=
    { toFun := p.val.1
      map_add' := fun _ _ ↦ p.val.1.map_add _ _
      map_smul' := fun s x ↦
        p.val.1.map_smul (TrivSqZeroExt.inl s) x }
  obtain ⟨sX, hsX⟩ := IsSemisimpleModule.lifting_property
    qX RX.mkQ_surjective (LinearMap.id (R := S) (M := TX))
  obtain ⟨sY, hsY⟩ := IsSemisimpleModule.lifting_property
    qY RY.mkQ_surjective (LinearMap.id (R := S) (M := TY))
  let projX : X →ₗ[S] RX :=
    { toFun := fun x ↦ ⟨x - sX (qX x), by
          apply (Submodule.Quotient.mk_eq_zero RX).mp
          change qX (x - sX (qX x)) = 0
          rw [map_sub]
          have h := LinearMap.congr_fun hsX (qX x)
          change qX (sX (qX x)) = qX x at h
          rw [h, sub_self]⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        change (x + y) - sX (qX (x + y)) =
          (x - sX (qX x)) + (y - sX (qX y))
        simp only [map_add]
        abel
      map_smul' := by
        intro s x
        apply Subtype.ext
        change s • x - sX (qX (s • x)) =
          s • (x - sX (qX x))
        simp only [map_smul, smul_sub] }
  let inclY : RY →ₗ[S] Y :=
    { toFun := fun y ↦ y
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let liftS : X →ₗ[S] Y :=
    sY.comp (pTop.comp qX) + inclY.comp (pRad.comp projX)
  have hqY_sY (q : TY) : qY (sY q) = q := by
    have h := LinearMap.congr_fun hsY q
    exact h
  have hqX_inr (j : J) (x : X) :
      qX ((TrivSqZeroExt.inr j : TrivSqZeroExt S J) • x) = 0 := by
    apply (Submodule.Quotient.mk_eq_zero RX).mpr
    change (TrivSqZeroExt.inr j : TrivSqZeroExt S J) • x ∈
      Module.jacobson (TrivSqZeroExt S J) X
    rw [module_jacobson_eq_radicalPart (S := S) (J := J)]
    apply Submodule.smul_mem_smul
    · exact (mem_augmentationIdeal_iff
        (TrivSqZeroExt.inr j : TrivSqZeroExt S J)).mpr rfl
    · exact Submodule.mem_top
  have hprojX_inr (j : J) (x : X) :
      projX ((TrivSqZeroExt.inr j : TrivSqZeroExt S J) • x) =
        ⟨(TrivSqZeroExt.inr j : TrivSqZeroExt S J) • x, by
          change (TrivSqZeroExt.inr j : TrivSqZeroExt S J) • x ∈
            Module.jacobson (TrivSqZeroExt S J) X
          rw [module_jacobson_eq_radicalPart (S := S) (J := J)]
          exact Submodule.smul_mem_smul
            ((mem_augmentationIdeal_iff
              (TrivSqZeroExt.inr j : TrivSqZeroExt S J)).mpr rfl)
            Submodule.mem_top⟩ := by
    apply Subtype.ext
    change (TrivSqZeroExt.inr j : TrivSqZeroExt S J) • x -
      sX (qX ((TrivSqZeroExt.inr j : TrivSqZeroExt S J) • x)) =
        (TrivSqZeroExt.inr j : TrivSqZeroExt S J) • x
    rw [hqX_inr, map_zero, sub_zero]
  have hliftS_inr (j : J) (x : X) :
      liftS ((TrivSqZeroExt.inr j : TrivSqZeroExt S J) • x) =
        (TrivSqZeroExt.inr j : TrivSqZeroExt S J) • liftS x := by
    let a : augmentationIdeal (S := S) (J := J) :=
      ⟨(TrivSqZeroExt.inr j : TrivSqZeroExt S J),
        (mem_augmentationIdeal_iff _).mpr rfl⟩
    have hcompat := p.property a (qX x)
    have hqx : qX x = RX.mkQ x := rfl
    have hactionY (q : TY) :
        radicalAction a q =
          ⟨(a : TrivSqZeroExt S J) • sY q, by
            rw [module_jacobson_eq_radicalPart (S := S) (J := J)]
            exact Submodule.smul_mem_smul
              a.property Submodule.mem_top⟩ := by
      calc
        radicalAction a q = radicalAction a (qY (sY q)) :=
          congrArg (radicalAction a) (hqY_sY q).symm
        _ = ⟨(a : TrivSqZeroExt S J) • sY q, _⟩ := by
          change radicalAction a (RY.mkQ (sY q)) = _
          exact radicalAction_mk a (sY q)
    have hcompat' := congrArg Subtype.val hcompat
    rw [hqx, radicalAction_mk (S := S) (J := J) (X := X),
      hactionY] at hcompat'
    change ((pRad
      ⟨(TrivSqZeroExt.inr j : TrivSqZeroExt S J) • x, by
        change (TrivSqZeroExt.inr j : TrivSqZeroExt S J) • x ∈
          Module.jacobson (TrivSqZeroExt S J) X
        rw [module_jacobson_eq_radicalPart (S := S) (J := J)]
        exact Submodule.smul_mem_smul
          a.property Submodule.mem_top⟩ : RY) : Y) =
      (TrivSqZeroExt.inr j : TrivSqZeroExt S J) •
        sY (pTop (qX x)) at hcompat'
    change sY (pTop (qX
        ((TrivSqZeroExt.inr j : TrivSqZeroExt S J) • x))) +
        (pRad (projX
          ((TrivSqZeroExt.inr j : TrivSqZeroExt S J) • x)) : Y) =
      (TrivSqZeroExt.inr j : TrivSqZeroExt S J) •
        (sY (pTop (qX x)) + (pRad (projX x) : Y))
    rw [hqX_inr, map_zero, map_zero, zero_add, hprojX_inr,
      smul_add, hcompat']
    have hzero := augmentation_smul_module_jacobson_eq_zero
      (S := S) (J := J)
      (TrivSqZeroExt.inr j : TrivSqZeroExt S J) a.property
      (pRad (projX x) : Y) (pRad (projX x)).property
    rw [hzero, add_zero]
  let liftR : X →ₗ[TrivSqZeroExt S J] Y :=
    { toFun := liftS
      map_add' := fun x y ↦ liftS.map_add x y
      map_smul' := fun r x ↦ by
        have hdecomp : r = TrivSqZeroExt.inl r.fst +
            TrivSqZeroExt.inr r.snd := by
          apply TrivSqZeroExt.ext <;> simp
        rw [hdecomp, add_smul, liftS.map_add]
        simp only [RingHom.id_apply]
        rw [add_smul]
        exact congrArg₂ (· + ·) (liftS.map_smul r.fst x)
          (hliftS_inr r.snd x) }
  have hqY_rad (y : RY) : qY (y : Y) = 0 := by
    apply (Submodule.Quotient.mk_eq_zero RY).mpr
    exact y.property
  have hqX_rad (x : RX) : qX (x : X) = 0 := by
    apply (Submodule.Quotient.mk_eq_zero RX).mpr
    exact x.property
  have hprojX_rad (x : RX) : projX (x : X) = x := by
    apply Subtype.ext
    change (x : X) - sX (qX (x : X)) = x
    rw [hqX_rad, map_zero, sub_zero]
  have htop : topMap liftR = p.val.2 := by
    ext x
    change qY (liftS x) = pTop (qX x)
    change qY (sY (pTop (qX x)) + (pRad (projX x) : Y)) =
      pTop (qX x)
    rw [map_add, hqY_sY, hqY_rad, add_zero]
  have hrad : radicalMap liftR = p.val.1 := by
    ext x
    change liftS (x : X) = (pRad x : Y)
    change sY (pTop (qX (x : X))) +
        (pRad (projX (x : X)) : Y) = (pRad x : Y)
    rw [hqX_rad, map_zero, map_zero, zero_add, hprojX_rad]
  refine ⟨ModuleCat.ofHom liftR, ?_⟩
  apply Subtype.ext
  exact Prod.ext hrad htop

instance separatedLayerFunctor_full :
    (separatedLayerFunctor (S := S) (J := J)).Full where
  map_surjective := separatedLayerFunctor_map_surjective

/-- The concrete separated-layer functor has square-zero Hom-kernel. -/
theorem separatedLayerFunctor_kernelSquareZero :
    QuotientSubmoduleEquidistribution.CategoryTheory.IdempotentLifting.FunctorKernelSquareZero
      (separatedLayerFunctor (S := S) (J := J)) := by
  intro X Y Z f g hf hg
  have hf' := congrArg Subtype.val hf
  have hg' := congrArg Subtype.val hg
  change layerMap f.hom =
    (0 : RadicalLayerHom (R := TrivSqZeroExt S J) X Y) at hf'
  change layerMap g.hom =
    (0 : RadicalLayerHom (R := TrivSqZeroExt S J) Y Z) at hg'
  ext m
  exact LinearMap.congr_fun
    (comp_eq_zero_of_layerMap_eq_zero f.hom g.hom hf' hg') m

instance separatedLayerFunctor_reflectsIsomorphisms :
    (separatedLayerFunctor (S := S) (J := J)).ReflectsIsomorphisms :=
  QuotientSubmoduleEquidistribution.CategoryTheory.IdempotentLifting.reflectsIsomorphisms_of_kernelSquareZero
    (separatedLayerFunctor (S := S) (J := J))
    separatedLayerFunctor_kernelSquareZero

/-- Any isomorphism between the separated layers of two modules lifts to an
isomorphism of the modules themselves. -/
def isoOfSeparatedLayerIso
    {X Y : ModuleCat.{w} (TrivSqZeroExt S J)}
    (e : (separatedLayerFunctor (S := S) (J := J)).obj X ≅
      (separatedLayerFunctor (S := S) (J := J)).obj Y) :
    X ≅ Y :=
  QuotientSubmoduleEquidistribution.CategoryTheory.IdempotentLifting.isoOfMapIsoOfKernelSquareZero
    (separatedLayerFunctor (S := S) (J := J))
    separatedLayerFunctor_kernelSquareZero e

end QuotientSubmoduleEquidistribution.TrivSqZeroExtSeparatedFunctor
