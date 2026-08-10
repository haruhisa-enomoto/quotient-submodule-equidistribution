import OpConjecture.RepresentationTheory.TrivSqZeroExtRadical
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Module.MinimalAxioms

/-!
# Arbitrary separated data for a trivial square-zero extension

Let `R = S ⋉ J`, where `S` is commutative and `J` is an `S`-bimodule.  A
separated datum consists of two `S`-modules, called its top and radical, and a
balanced additive action of `J` from the top into the radical.  This file
reconstructs an `R`-module from every such datum and packages reconstruction as
an additive functor.

Two intrinsic conditions single out the data arising from nonsimple modules:
the action must generate the radical, and its common kernel on the top must be
zero.  Under semisimplicity of `S`, generation already implies that the
declared radical is exactly the module Jacobson radical of the reconstruction.
-/

set_option autoImplicit false

noncomputable section

open scoped RightActions
open CategoryTheory

namespace OpConjecture.TrivSqZeroExtSeparatedData

universe u v w

variable {S : Type u} {J : Type v}
variable [CommRing S] [AddCommGroup J]
variable [Module S J] [Module Sᵐᵒᵖ J]
variable [SMulCommClass S Sᵐᵒᵖ J]

/-- Abstract top/radical data with a balanced action of the square-zero
ideal. -/
structure SeparatedData where
  top : ModuleCat.{w} S
  radical : ModuleCat.{w} S
  action : J →+ (top →+ radical)
  action_left_smul : ∀ (s : S) (j : J) (t : top),
    action (s • j) t = s • action j t
  action_right_smul : ∀ (j : J) (s : S) (t : top),
    action (j <• s) t = action j (s • t)

/-- The underlying additive group of the reconstructed module. -/
abbrev Reconstructed (D : SeparatedData (S := S) (J := J)) :=
  D.top × D.radical

/-- The scalar action `(s,j) • (t,d) = (s•t, s•d + j•t)` on the
reconstruction. -/
instance reconstructedSMul
    (D : SeparatedData (S := S) (J := J)) :
    SMul (TrivSqZeroExt S J) (Reconstructed D) where
  smul r x := (r.fst • x.1, r.fst • x.2 + D.action r.snd x.1)

/-- The balanced-action identities make the reconstruction a module over the
trivial square-zero extension. -/
instance reconstructedModule
    (D : SeparatedData (S := S) (J := J)) :
    Module (TrivSqZeroExt S J) (Reconstructed D) :=
  Module.ofMinimalAxioms
    (by
      intro r x y
      apply Prod.ext
      · exact smul_add r.fst x.1 y.1
      · change r.fst • (x.2 + y.2) + D.action r.snd (x.1 + y.1) =
          (r.fst • x.2 + D.action r.snd x.1) +
            (r.fst • y.2 + D.action r.snd y.1)
        rw [smul_add, map_add]
        abel)
    (by
      intro r s x
      apply Prod.ext
      · exact add_smul r.fst s.fst x.1
      · change (r.fst + s.fst) • x.2 +
          D.action (r.snd + s.snd) x.1 =
        (r.fst • x.2 + D.action r.snd x.1) +
          (s.fst • x.2 + D.action s.snd x.1)
        rw [add_smul, map_add, AddMonoidHom.add_apply]
        abel)
    (by
      intro r s x
      apply Prod.ext
      · exact mul_smul r.fst s.fst x.1
      · change (r.fst * s.fst) • x.2 +
          D.action (r.fst • s.snd + r.snd <• s.fst) x.1 =
        r.fst • (s.fst • x.2 + D.action s.snd x.1) +
          D.action r.snd (s.fst • x.1)
        rw [map_add, AddMonoidHom.add_apply,
          D.action_left_smul, D.action_right_smul,
          mul_smul, smul_add]
        abel)
    (by
      intro x
      apply Prod.ext
      · exact one_smul S x.1
      · change (1 : S) • x.2 + D.action 0 x.1 = x.2
        rw [one_smul, map_zero, AddMonoidHom.zero_apply, add_zero])

/-- The reconstructed module as an object of `ModuleCat`. -/
abbrev reconstructedModuleCat
    (D : SeparatedData (S := S) (J := J)) :
    ModuleCat.{w} (TrivSqZeroExt S J) :=
  ModuleCat.of (TrivSqZeroExt S J) (Reconstructed D)

/-- A pair of linear maps on the top and radical layers. -/
abbrev LayerMap
    (D E : SeparatedData (S := S) (J := J)) :=
  (D.top →ₗ[S] E.top) × (D.radical →ₗ[S] E.radical)

/-- Compatibility of a layer-map pair with the square-zero action. -/
def Compatible
    (D E : SeparatedData (S := S) (J := J))
    (f : LayerMap D E) : Prop :=
  ∀ (j : J) (t : D.top),
    f.2 (D.action j t) = E.action j (f.1 t)

/-- Compatible layer-map pairs form an additive subgroup. -/
def homAddSubgroup
    (D E : SeparatedData (S := S) (J := J)) :
    AddSubgroup (LayerMap D E) where
  carrier := Compatible D E
  zero_mem' := by
    intro j t
    change 0 = E.action j 0
    rw [map_zero]
  add_mem' := by
    intro f g hf hg j t
    change f.2 (D.action j t) + g.2 (D.action j t) =
      E.action j (f.1 t + g.1 t)
    rw [hf, hg, map_add]
  neg_mem' := by
    intro f hf j t
    change -f.2 (D.action j t) = E.action j (-f.1 t)
    rw [hf, map_neg]

/-- Morphisms of separated data. -/
abbrev SeparatedDataHom
    (D E : SeparatedData (S := S) (J := J)) :=
  ↥(homAddSubgroup D E)

instance separatedDataCategory :
    Category.{w} (SeparatedData (S := S) (J := J)) where
  Hom := SeparatedDataHom
  id D := ⟨(LinearMap.id, LinearMap.id), by intro j t; rfl⟩
  comp f g :=
    ⟨(g.val.1.comp f.val.1, g.val.2.comp f.val.2), by
      intro j t
      simp only [LinearMap.comp_apply]
      rw [f.property j t, g.property j (f.val.1 t)]⟩
  assoc := by intros; rfl
  id_comp := by intros; rfl
  comp_id := by intros; rfl

instance separatedDataPreadditive :
    Preadditive (SeparatedData (S := S) (J := J)) where
  homGroup := fun D E ↦ inferInstanceAs (AddCommGroup (homAddSubgroup D E))
  add_comp := by
    intro P Q T f f' g
    apply Subtype.ext
    apply Prod.ext
    · ext x
      exact g.val.1.map_add (f.val.1 x) (f'.val.1 x)
    · ext x
      exact g.val.2.map_add (f.val.2 x) (f'.val.2 x)
  comp_add := by
    intro P Q T f g g'
    apply Subtype.ext
    apply Prod.ext
    · ext x
      rfl
    · ext x
      rfl

/-- An isomorphism of separated data induces a linear equivalence on top
layers. -/
def isoTopLinearEquiv {D E : SeparatedData (S := S) (J := J)}
    (e : D ≅ E) : D.top ≃ₗ[S] E.top where
  toFun := e.hom.val.1
  invFun := e.inv.val.1
  map_add' := e.hom.val.1.map_add
  map_smul' := e.hom.val.1.map_smul
  left_inv t := by
    have h := congrArg (fun q ↦ q.val.1) e.hom_inv_id
    exact LinearMap.congr_fun h t
  right_inv t := by
    have h := congrArg (fun q ↦ q.val.1) e.inv_hom_id
    exact LinearMap.congr_fun h t

/-- An isomorphism of separated data induces a linear equivalence on radical
layers. -/
def isoRadicalLinearEquiv {D E : SeparatedData (S := S) (J := J)}
    (e : D ≅ E) : D.radical ≃ₗ[S] E.radical where
  toFun := e.hom.val.2
  invFun := e.inv.val.2
  map_add' := e.hom.val.2.map_add
  map_smul' := e.hom.val.2.map_smul
  left_inv d := by
    have h := congrArg (fun q ↦ q.val.2) e.hom_inv_id
    exact LinearMap.congr_fun h d
  right_inv d := by
    have h := congrArg (fun q ↦ q.val.2) e.inv_hom_id
    exact LinearMap.congr_fun h d

/-- A compatible layer map induces a homomorphism of reconstructed modules. -/
def mapReconstructed
    {D E : SeparatedData (S := S) (J := J)}
    (f : D ⟶ E) :
    Reconstructed D →ₗ[TrivSqZeroExt S J] Reconstructed E where
  toFun x := (f.val.1 x.1, f.val.2 x.2)
  map_add' _ _ := by ext <;> simp
  map_smul' r x := by
    apply Prod.ext
    · exact f.val.1.map_smul r.fst x.1
    · change f.val.2 (r.fst • x.2 + D.action r.snd x.1) =
        r.fst • f.val.2 x.2 + E.action r.snd (f.val.1 x.1)
      rw [map_add, f.val.2.map_smul, f.property]

/-- Reconstruction is a functor from separated data to modules. -/
def reconstructionFunctor :
    SeparatedData.{u, v, w} (S := S) (J := J) ⥤
      ModuleCat.{w} (TrivSqZeroExt S J) where
  obj := reconstructedModuleCat
  map f := ModuleCat.ofHom (mapReconstructed f)
  map_id _ := by ext <;> rfl
  map_comp _ _ := by ext <;> rfl

instance reconstructionFunctor_additive :
    (reconstructionFunctor (S := S) (J := J)).Additive where
  map_add := by
    intro X Y f g
    ext x
    rfl

/-- Reconstruction remembers both component maps, so it is faithful. -/
instance reconstructionFunctor_faithful :
    (reconstructionFunctor (S := S) (J := J)).Faithful where
  map_injective := by
    intro D E f g h
    apply Subtype.ext
    apply Prod.ext
    · ext t
      have ht := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h)
        ((t, 0) : Reconstructed D)
      exact congrArg Prod.fst ht
    · ext d
      have hd := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h)
        (((0 : D.top), d) : Reconstructed D)
      exact congrArg Prod.snd hd

/-- The radical layer generated by the square-zero action. -/
def actionRange (D : SeparatedData (S := S) (J := J)) :
    Submodule S D.radical :=
  Submodule.span S {d | ∃ (j : J) (t : D.top), D.action j t = d}

/-- A separated datum is generated when its declared radical is generated by
the action of the square-zero ideal on its top. -/
def IsGenerated (D : SeparatedData (S := S) (J := J)) : Prop :=
  actionRange D = ⊤

/-- The common kernel of all square-zero action maps. -/
def commonKernel (D : SeparatedData (S := S) (J := J)) :
    Submodule S D.top where
  carrier := {t | ∀ j, D.action j t = 0}
  zero_mem' := by
    intro j
    rw [map_zero]
  add_mem' := by
    intro x y hx hy j
    rw [map_add, hx j, hy j, add_zero]
  smul_mem' := by
    intro s t ht j
    rw [← D.action_right_smul j s t, ht (j <• s)]

/-- A separated datum is kernel-free when no nonzero top vector is killed by
every square-zero action map. -/
def IsKernelFree (D : SeparatedData (S := S) (J := J)) : Prop :=
  commonKernel D = ⊥

omit [SMulCommClass S Sᵐᵒᵖ J] in
/-- A morphism from generated separated data to data with zero top has zero
radical component.  Compatibility kills every action generator, and
generatedness says that these span the whole source radical. -/
theorem radicalMap_eq_zero_of_generated_of_target_top_subsingleton
    {D E : SeparatedData (S := S) (J := J)}
    (hD : IsGenerated D) [Subsingleton E.top]
    (f : D ⟶ E) :
    f.val.2 = 0 := by
  apply LinearMap.ext
  intro d
  have hd : d ∈ actionRange D := by
    rw [hD]
    exact Submodule.mem_top
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hd
  · intro x hx
    rcases hx with ⟨j, t, rfl⟩
    rw [f.property]
    have htop : f.val.1 t = 0 := Subsingleton.elim _ _
    rw [htop, map_zero]
    rfl
  · exact map_zero f.val.2
  · intro x y _ _ hx hy
    simp [map_add, hx, hy]
  · intro s x _ hx
    simp [map_smul, hx]

omit [SMulCommClass S Sᵐᵒᵖ J] in
/-- Hence every morphism of separated data from a generated source to a
zero-top target is zero. -/
theorem hom_eq_zero_of_generated_of_target_top_subsingleton
    {D E : SeparatedData (S := S) (J := J)}
    (hD : IsGenerated D) [Subsingleton E.top]
    (f : D ⟶ E) :
    f = 0 := by
  apply Subtype.ext
  apply Prod.ext
  · apply LinearMap.ext
    intro t
    exact Subsingleton.elim _ _
  · exact radicalMap_eq_zero_of_generated_of_target_top_subsingleton
      hD f

/-- The declared radical inside the reconstructed module. -/
def declaredRadical (D : SeparatedData (S := S) (J := J)) :
    Submodule (TrivSqZeroExt S J) (Reconstructed D) where
  carrier := {x | x.1 = 0}
  zero_mem' := rfl
  add_mem' := by
    intro x y hx hy
    change x.1 + y.1 = 0
    rw [hx, hy, add_zero]
  smul_mem' := by
    intro r x hx
    change r.fst • x.1 = 0
    rw [hx, smul_zero]

/-- If the declared radical is generated by the square-zero action, then it is
exactly the module Jacobson radical of the reconstructed module. -/
theorem module_jacobson_eq_declaredRadical_of_generated
    [IsSemisimpleRing S]
    (D : SeparatedData (S := S) (J := J)) (hD : IsGenerated D) :
    Module.jacobson (TrivSqZeroExt S J) (Reconstructed D) =
      declaredRadical D := by
  rw [TrivSqZeroExtRadical.module_jacobson_eq_radicalPart]
  apply le_antisymm
  · apply Submodule.smul_le.mpr
    intro r hr x _
    change r.fst • x.1 = 0
    rw [(TrivSqZeroExtRadical.mem_augmentationIdeal_iff r).mp hr,
      zero_smul]
  · intro x hx
    have hx1 : x.1 = 0 := hx
    have hx2 : x.2 ∈ actionRange D := by
      rw [hD]
      exact Submodule.mem_top
    have hpair : (0, x.2) ∈
        TrivSqZeroExtRadical.augmentationIdeal (S := S) (J := J) •
          (⊤ : Submodule (TrivSqZeroExt S J) (Reconstructed D)) := by
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hx2
      · intro d hd
        obtain ⟨j, t, rfl⟩ := hd
        have hmem :
            (TrivSqZeroExt.inr j : TrivSqZeroExt S J) • (t, 0) ∈
              TrivSqZeroExtRadical.augmentationIdeal
                  (S := S) (J := J) •
                (⊤ : Submodule (TrivSqZeroExt S J) (Reconstructed D)) :=
          Submodule.smul_mem_smul
            ((TrivSqZeroExtRadical.mem_augmentationIdeal_iff
              (TrivSqZeroExt.inr j : TrivSqZeroExt S J)).mpr rfl)
            Submodule.mem_top
        have heq :
            (TrivSqZeroExt.inr j : TrivSqZeroExt S J) • (t, 0) =
              (0, D.action j t) := by
          change ((0 : S) • t,
            (0 : S) • (0 : D.radical) + D.action j t) = _
          simp
        rwa [heq] at hmem
      · exact Submodule.zero_mem _
      · intro a b _ _ ha hb
        simpa using Submodule.add_mem _ ha hb
      · intro s d _ hd
        have hsmul := Submodule.smul_mem
          (TrivSqZeroExtRadical.augmentationIdeal (S := S) (J := J) •
            (⊤ : Submodule (TrivSqZeroExt S J) (Reconstructed D)))
          (TrivSqZeroExt.inl s) hd
        have heq :
            (TrivSqZeroExt.inl s : TrivSqZeroExt S J) •
                ((0 : D.top), d) =
              ((0 : D.top), s • d) := by
          change (s • (0 : D.top),
            s • d + D.action 0 (0 : D.top)) = _
          simp
        rwa [heq] at hsmul
    have hxpair : x = (0, x.2) := by
      apply Prod.ext
      · exact hx1
      · rfl
    rwa [hxpair]

end OpConjecture.TrivSqZeroExtSeparatedData
