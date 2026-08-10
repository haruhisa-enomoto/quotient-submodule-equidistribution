import OpConjecture.RepresentationTheory.TrivSqZeroExtSeparatedData
import Mathlib.Algebra.Module.MinimalAxioms

/-!
# The triangular algebra of separated top/radical data

For a commutative ring `S` and an `S`-bimodule `J`, put

`T(S,J) = (S × S) ⋉ J`,

where the first copy of `S` acts on `J` from the left and the second copy acts
from the right.  A separated datum `(top, radical, action)` then has the
tautological `T(S,J)`-module structure

`((sRad, sTop), j) • (t,d) = (sTop • t, sRad • d + j • t)`.

This file constructs the resulting additive functor and proves that it is
full and faithful.  Thus the abstract separated-data category is realized as
a full subcategory of modules over the triangular separated algebra, without
choosing quiver-arrow bases.
-/

set_option autoImplicit false

noncomputable section

open scoped RightActions
open CategoryTheory

namespace OpConjecture.SeparatedTriangularAlgebra

open TrivSqZeroExtSeparatedData

universe u v w

variable {S : Type u} {J : Type v}
variable [CommRing S] [AddCommGroup J]
variable [Module S J] [Module Sᵐᵒᵖ J]
variable [SMulCommClass S Sᵐᵒᵖ J]

/-- A tagged copy of `J`, used to register the two coordinate actions of
`S × S` without creating an orphan module instance on `J`. -/
structure SeparatedIdeal (S : Type u) (J : Type v) where
  val : J

namespace SeparatedIdeal

/-- Forget the tag on the separated ideal. -/
def equiv : SeparatedIdeal S J ≃ J where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

omit [CommRing S] [AddCommGroup J] [Module S J] [Module Sᵐᵒᵖ J]
    [SMulCommClass S Sᵐᵒᵖ J] in
@[ext]
theorem ext {x y : SeparatedIdeal S J} (h : x.val = y.val) : x = y := by
  cases x
  cases y
  cases h
  rfl

instance : AddCommGroup (SeparatedIdeal S J) := equiv.addCommGroup

instance : Module S (SeparatedIdeal S J) := equiv.module S

instance : Module Sᵐᵒᵖ (SeparatedIdeal S J) := equiv.module Sᵐᵒᵖ

/-- The first coordinate of `S × S` acts from the left. -/
instance : Module (S × S) (SeparatedIdeal S J) :=
  Module.compHom _ (RingHom.fst S S)

/-- The second coordinate of `S × S` acts from the right. -/
instance : Module (S × S)ᵐᵒᵖ (SeparatedIdeal S J) :=
  Module.compHom _ (RingHom.op (RingHom.snd S S))

instance : SMulCommClass (S × S) (S × S)ᵐᵒᵖ
    (SeparatedIdeal S J) where
  smul_comm s t j := by
    apply ext
    change s.1 • (j.val <• (MulOpposite.unop t).2) =
      (s.1 • j.val) <• (MulOpposite.unop t).2
    exact SMulCommClass.smul_comm s.1
      (MulOpposite.op (MulOpposite.unop t).2) j.val

end SeparatedIdeal

/-- The triangular separated algebra `(S × S) ⋉ J`. -/
abbrev Algebra (S : Type u) (J : Type v) [CommRing S] [AddCommGroup J]
    [Module S J] [Module Sᵐᵒᵖ J] [SMulCommClass S Sᵐᵒᵖ J] :=
  TrivSqZeroExt (S × S) (SeparatedIdeal S J)

/-- The underlying additive group of the triangular-algebra realization. -/
abbrev Realized (D : SeparatedData (S := S) (J := J)) :=
  D.top × D.radical

/-- The tautological action of the triangular separated algebra. -/
instance realizedSMul (D : SeparatedData (S := S) (J := J)) :
    SMul (Algebra S J) (Realized D) where
  smul r x :=
    (r.fst.2 • x.1, r.fst.1 • x.2 + D.action r.snd.val x.1)

/-- The balanced-action identities make the realization a module over the
triangular separated algebra. -/
instance realizedModule (D : SeparatedData (S := S) (J := J)) :
    Module (Algebra S J) (Realized D) :=
  Module.ofMinimalAxioms
    (by
      intro r x y
      apply Prod.ext
      · exact smul_add r.fst.2 x.1 y.1
      · change r.fst.1 • (x.2 + y.2) +
            D.action r.snd.val (x.1 + y.1) =
          (r.fst.1 • x.2 + D.action r.snd.val x.1) +
            (r.fst.1 • y.2 + D.action r.snd.val y.1)
        rw [smul_add, map_add]
        abel)
    (by
      intro r s x
      apply Prod.ext
      · exact add_smul r.fst.2 s.fst.2 x.1
      · change (r.fst.1 + s.fst.1) • x.2 +
            D.action (r.snd.val + s.snd.val) x.1 =
          (r.fst.1 • x.2 + D.action r.snd.val x.1) +
            (s.fst.1 • x.2 + D.action s.snd.val x.1)
        rw [add_smul, map_add, AddMonoidHom.add_apply]
        abel)
    (by
      intro r s x
      apply Prod.ext
      · exact mul_smul r.fst.2 s.fst.2 x.1
      · change (r.fst.1 * s.fst.1) • x.2 +
            D.action
              (r.fst.1 • s.snd.val + r.snd.val <• s.fst.2) x.1 =
          r.fst.1 •
              (s.fst.1 • x.2 + D.action s.snd.val x.1) +
            D.action r.snd.val (s.fst.2 • x.1)
        rw [map_add, AddMonoidHom.add_apply, D.action_left_smul,
          D.action_right_smul, mul_smul, smul_add]
        abel)
    (by
      intro x
      apply Prod.ext
      · exact one_smul S x.1
      · change (1 : S) • x.2 + D.action 0 x.1 = x.2
        rw [one_smul, map_zero, AddMonoidHom.zero_apply, add_zero])

@[simp]
theorem inl_smul_realized (D : SeparatedData (S := S) (J := J))
    (sRad sTop : S) (x : Realized D) :
    (TrivSqZeroExt.inl ((sRad, sTop) : S × S) : Algebra S J) • x =
      (sTop • x.1, sRad • x.2) := by
  rcases x with ⟨t, d⟩
  apply Prod.ext
  · rfl
  · change sRad • d + D.action 0 t = sRad • d
    rw [map_zero, AddMonoidHom.zero_apply, add_zero]

@[simp]
theorem inr_smul_realized (D : SeparatedData (S := S) (J := J))
    (j : J) (x : Realized D) :
    (TrivSqZeroExt.inr (⟨j⟩ : SeparatedIdeal S J) : Algebra S J) • x =
      (0, D.action j x.1) := by
  apply Prod.ext
  · exact zero_smul S x.1
  · change (0 : S) • x.2 + D.action j x.1 = D.action j x.1
    rw [zero_smul, zero_add]

/-- A separated datum as a module over the triangular separated algebra. -/
abbrev realizedModuleCat (D : SeparatedData (S := S) (J := J)) :
    ModuleCat.{w} (Algebra S J) :=
  ModuleCat.of (Algebra S J) (Realized D)

/-- A compatible pair of layer maps is linear for the triangular algebra. -/
def mapRealized {D E : SeparatedData (S := S) (J := J)} (f : D ⟶ E) :
    Realized D →ₗ[Algebra S J] Realized E where
  toFun x := (f.val.1 x.1, f.val.2 x.2)
  map_add' _ _ := by ext <;> simp
  map_smul' r x := by
    apply Prod.ext
    · exact f.val.1.map_smul r.fst.2 x.1
    · change f.val.2
          (r.fst.1 • x.2 + D.action r.snd.val x.1) =
        r.fst.1 • f.val.2 x.2 +
          E.action r.snd.val (f.val.1 x.1)
      rw [map_add, f.val.2.map_smul, f.property]

/-- Realization as modules over the triangular separated algebra. -/
def realizationFunctor :
    CategoryTheory.Functor
      (SeparatedData.{u, v, w} (S := S) (J := J))
      (ModuleCat.{w} (Algebra S J)) where
  obj := realizedModuleCat
  map f := ModuleCat.ofHom (mapRealized f)
  map_id _ := by ext <;> rfl
  map_comp _ _ := by ext <;> rfl

instance realizationFunctor_additive :
    (realizationFunctor (S := S) (J := J)).Additive where
  map_add := by
    intro D E f g
    ext x
    rfl

/-- The triangular-algebra realization remembers both layer maps. -/
instance realizationFunctor_faithful :
    (realizationFunctor (S := S) (J := J)).Faithful where
  map_injective := by
    intro D E f g h
    apply Subtype.ext
    apply Prod.ext
    · ext t
      have ht := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h)
        ((t, 0) : Realized D)
      exact congrArg Prod.fst ht
    · ext d
      have hd := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h)
        (((0 : D.top), d) : Realized D)
      exact congrArg Prod.snd hd

/-- Every triangular-algebra map between realized separated data is induced
by a unique compatible pair of layer maps. -/
instance realizationFunctor_full :
    (realizationFunctor (S := S) (J := J)).Full where
  map_surjective := by
    intro D E f
    let F : Realized D →ₗ[Algebra S J] Realized E := f.hom
    let fTop : D.top →ₗ[S] E.top :=
      { toFun := fun t ↦ (F (t, 0)).1
        map_add' := by
          intro x y
          have h := congrArg Prod.fst
            (F.map_add (x, 0) (y, 0))
          simpa only [Prod.mk_add_mk, Prod.fst_add, add_zero] using h
        map_smul' := by
          intro s t
          have h := F.map_smul
            (TrivSqZeroExt.inl ((0, s) : S × S) : Algebra S J)
            ((t, 0) : Realized D)
          rw [inl_smul_realized D, inl_smul_realized E] at h
          simpa only [zero_smul, RingHom.id_apply] using
            congrArg Prod.fst h }
    let fRad : D.radical →ₗ[S] E.radical :=
      { toFun := fun d ↦ (F (0, d)).2
        map_add' := by
          intro x y
          have h := congrArg Prod.snd
            (F.map_add (0, x) (0, y))
          simpa only [Prod.mk_add_mk, Prod.snd_add, add_zero] using h
        map_smul' := by
          intro s d
          have h := F.map_smul
            (TrivSqZeroExt.inl ((s, 0) : S × S) : Algebra S J)
            (((0 : D.top), d) : Realized D)
          rw [inl_smul_realized D, inl_smul_realized E] at h
          simpa only [zero_smul, RingHom.id_apply] using
            congrArg Prod.snd h }
    have hcompat (j : J) (t : D.top) :
        fRad (D.action j t) = E.action j (fTop t) := by
      let jt : SeparatedIdeal S J := ⟨j⟩
      have h := F.map_smul
        (TrivSqZeroExt.inr jt : Algebra S J)
        ((t, 0) : Realized D)
      rw [inr_smul_realized D, inr_smul_realized E] at h
      exact congrArg Prod.snd h
    let g : D ⟶ E := ⟨(fTop, fRad), hcompat⟩
    refine ⟨g, ?_⟩
    ext x
    rcases x with ⟨t, d⟩
    have htopZero : (F ((0, d) : Realized D)).1 = 0 := by
      have h := F.map_smul
        (TrivSqZeroExt.inl ((1, 0) : S × S) : Algebra S J)
        (((0 : D.top), d) : Realized D)
      rw [inl_smul_realized D, inl_smul_realized E] at h
      simpa only [one_smul, zero_smul] using congrArg Prod.fst h
    have hradZero : (F ((t, 0) : Realized D)).2 = 0 := by
      have h := F.map_smul
        (TrivSqZeroExt.inl ((0, 1) : S × S) : Algebra S J)
        ((t, 0) : Realized D)
      rw [inl_smul_realized D, inl_smul_realized E] at h
      simpa only [one_smul, zero_smul] using congrArg Prod.snd h
    have hadd := F.map_add
      ((t, 0) : Realized D) (((0 : D.top), d) : Realized D)
    apply Prod.ext
    · change fTop t = (F (t, d)).1
      change (F (t, 0)).1 = (F (t, d)).1
      simpa only [Prod.mk_add_mk, Prod.fst_add, add_zero, zero_add,
        htopZero] using
        (congrArg Prod.fst hadd).symm
    · change fRad d = (F (t, d)).2
      change (F (0, d)).2 = (F (t, d)).2
      simpa only [Prod.mk_add_mk, Prod.snd_add, add_zero, zero_add, hradZero] using
        (congrArg Prod.snd hadd).symm

/-- A triangular-algebra map from the realization of generated separated
data to the realization of zero-top data vanishes. -/
theorem realizedHom_eq_zero_of_generated_of_target_top_subsingleton
    {D E : SeparatedData.{u, v, w} (S := S) (J := J)}
    (hD : IsGenerated D) [Subsingleton E.top]
    (f : realizedModuleCat D ⟶ realizedModuleCat E) :
    f = 0 := by
  change (realizationFunctor (S := S) (J := J)).obj D ⟶
    (realizationFunctor (S := S) (J := J)).obj E at f
  change f = 0
  obtain ⟨g, hg⟩ :=
    (realizationFunctor (S := S) (J := J)).map_surjective f
  rw [hom_eq_zero_of_generated_of_target_top_subsingleton hD g] at hg
  simpa using hg.symm

end OpConjecture.SeparatedTriangularAlgebra
