import OpConjecture.RepresentationTheory.FiniteHereditaryIrreducibleAcyclic
import OpConjecture.RepresentationTheory.SeparatedTriangularAlgebraEquivalence
import Mathlib.RingTheory.SimpleModule.InjectiveProjective

/-!
# Projective boundaries for a separated triangular algebra

For the triangular algebra `(S × S) ⋉ J`, modules supported on the
radical-side diagonal idempotent are projective when `S` is semisimple.
The Jacobson radical of every module is supported on that side.  Thus the
radical of an indecomposable projective is projective, which is exactly the
local input needed by the classification-free AR acyclicity argument.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open scoped RightActions

namespace OpConjecture.SeparatedTriangularAlgebra

open TrivSqZeroExtSeparatedData

universe u v

variable {S J : Type u}
variable [CommRing S] [IsSemisimpleRing S]
variable [AddCommGroup J] [Module S J] [Module Sᵐᵒᵖ J]
variable [SMulCommClass S Sᵐᵒᵖ J]

abbrev T := Algebra S J

/-- A morphism of triangular modules restricts to an `S`-linear map on
the radical-idempotent summands. -/
def mapRadicalPart {X Y : ModuleCat.{u} (T (S := S) (J := J))}
    (f : X ⟶ Y) :
    RadicalPart (S := S) (J := J) X →ₗ[S]
      RadicalPart (S := S) (J := J) Y where
  toFun x := ⟨f x.val, by
    change (radicalIdempotent : T) • f x.val = f x.val
    rw [← f.hom.map_smul, radicalPart_fixed]⟩
  map_add' x y := by
    apply Subtype.ext
    exact f.hom.map_add x.val y.val
  map_smul' s x := by
    apply Subtype.ext
    exact f.hom.map_smul (radicalScalar s : T) x.val

omit [IsSemisimpleRing S] in
/-- An epimorphism of triangular modules is surjective on the
radical-idempotent summands. -/
theorem mapRadicalPart_surjective
    {X Y : ModuleCat.{u} (T (S := S) (J := J))}
    (f : X ⟶ Y) [Epi f] : Function.Surjective (mapRadicalPart f) := by
  intro y
  have hsurjective : Function.Surjective f :=
    (ModuleCat.epi_iff_surjective f).mp inferInstance
  obtain ⟨x, hx⟩ := hsurjective y.val
  let xRad : RadicalPart (S := S) (J := J) X :=
    ⟨(radicalIdempotent : T (S := S) (J := J)) • x, by
      change (radicalIdempotent : T (S := S) (J := J)) •
          ((radicalIdempotent : T (S := S) (J := J)) • x) =
        (radicalIdempotent : T (S := S) (J := J)) • x
      rw [← mul_smul, radicalIdempotent_mul_self]⟩
  refine ⟨xRad, ?_⟩
  apply Subtype.ext
  change f ((radicalIdempotent : T (S := S) (J := J)) • x) = y.val
  rw [f.hom.map_smul, hx, radicalPart_fixed]

/-- A separated datum with zero top layer realizes a projective triangular
module.  The lift is constructed on the radical layer over the semisimple
base and then included by the radical diagonal idempotent. -/
theorem realized_projective_of_top_subsingleton
    (D : SeparatedData.{u, u, u} (S := S) (J := J))
    [Subsingleton D.top] : Projective (realizedModuleCat D) where
  factors {E X} f e _ := by
    let fRad : D.radical →ₗ[S]
        RadicalPart (S := S) (J := J) X :=
      { toFun := fun d ↦ ⟨f (0, d), by
          change (radicalIdempotent : T (S := S) (J := J)) •
              f (0, d) = f (0, d)
          rw [← f.hom.map_smul]
          rw [show (radicalIdempotent : T (S := S) (J := J)) =
              TrivSqZeroExt.inl ((1, 0) : S × S) by rfl,
            inl_smul_realized, one_smul]
          simp⟩
        map_add' := by
          intro d d'
          apply Subtype.ext
          change f (0, d + d') = f (0, d) + f (0, d')
          simpa using f.hom.map_add (0, d) (0, d')
        map_smul' := by
          intro s d
          apply Subtype.ext
          change f (0, s • d) =
            (radicalScalar s : T (S := S) (J := J)) • f (0, d)
          rw [← f.hom.map_smul]
          rw [show (radicalScalar s : T (S := S) (J := J)) =
              TrivSqZeroExt.inl ((s, 0) : S × S) by rfl,
            inl_smul_realized]
          simp }
    let eRad : RadicalPart (S := S) (J := J) E →ₗ[S]
        RadicalPart (S := S) (J := J) X := mapRadicalPart e
    letI : Module.Projective S D.radical :=
      Module.projective_of_isSemisimpleRing S D.radical
    obtain ⟨gRad, hgRad⟩ := Module.projective_lifting_property
      eRad fRad (mapRadicalPart_surjective e)
    let g : Realized D →ₗ[T (S := S) (J := J)] E :=
      { toFun := fun x ↦ (gRad x.2).val
        map_add' := by
          intro x y
          exact congrArg Subtype.val (gRad.map_add x.2 y.2)
        map_smul' := by
          intro r x
          have hxzero : x.1 = 0 := Subsingleton.elim _ _
          have hr : r =
              (radicalScalar r.fst.1 : T (S := S) (J := J)) +
                topScalar r.fst.2 + TrivSqZeroExt.inr ⟨r.snd.val⟩ := by
            rcases r with ⟨⟨sRad, sTop⟩, ⟨j⟩⟩
            exact scalar_decomposition sRad sTop j
          change
            (gRad (r.fst.1 • x.2 + D.action r.snd.val x.1)).val =
              r • (gRad x.2).val
          rw [hxzero, map_zero, add_zero, gRad.map_smul]
          change
            (radicalScalar r.fst.1 : T (S := S) (J := J)) •
                (gRad x.2).val = r • (gRad x.2).val
          conv_rhs => rw [hr]
          rw [add_smul, add_smul,
            topScalar_smul_radical_eq_zero,
            inr_smul_radical_eq_zero, add_zero, add_zero] }
    refine ⟨ModuleCat.ofHom g, ?_⟩
    apply ModuleCat.hom_ext
    ext x
    have hgx := LinearMap.congr_fun hgRad x.2
    have hxzero : x.1 = 0 := Subsingleton.elim _ _
    calc
      e ((gRad x.2).val) = f (0, x.2) := congrArg Subtype.val hgx
      _ = f x := congrArg f (Prod.ext hxzero.symm rfl)

/-- The top diagonal idempotent annihilates the module Jacobson radical. -/
theorem topIdempotent_smul_eq_zero_of_mem_jacobson
    (X : ModuleCat.{u} (T (S := S) (J := J))) (x : X)
    (hx : x ∈ Module.jacobson (T (S := S) (J := J)) X) :
    (topIdempotent : T (S := S) (J := J)) • x = 0 := by
  rw [TrivSqZeroExtRadical.module_jacobson_eq_radicalPart] at hx
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro a ha y _hy
    rw [← mul_smul]
    have hprod :
        (topIdempotent : T (S := S) (J := J)) * a = 0 := by
      rw [TrivSqZeroExtRadical.eq_inr_snd_of_mem_augmentationIdeal ha]
      change
        TrivSqZeroExt.inl ((0, 1) : S × S) *
            TrivSqZeroExt.inr a.snd = 0
      rw [TrivSqZeroExt.inl_mul_inr]
      change TrivSqZeroExt.inr ((0 : S) • a.snd) = 0
      rw [zero_smul, TrivSqZeroExt.inr_zero]
    rw [hprod, zero_smul]
  · intro x y hx hy
    rw [smul_add, hx, hy, add_zero]

/-- Any triangular module whose top-idempotent summand is zero is
projective. -/
theorem projective_of_topPart_subsingleton
    (X : ModuleCat.{u} (T (S := S) (J := J)))
    [Subsingleton (TopPart (S := S) (J := J) X)] : Projective X := by
  have hRealized : Projective
      (realizedModuleCat (ofModule (S := S) (J := J) X)) :=
    realized_projective_of_top_subsingleton
      (ofModule (S := S) (J := J) X)
  exact Projective.of_iso (realizedOfModuleIso (S := S) (J := J) X)
    hRealized

/-- The Jacobson radical of every triangular module is projective: it is
supported on the radical-side diagonal idempotent. -/
theorem projective_moduleJacobian
    (X : ModuleCat.{u} (T (S := S) (J := J))) :
    Projective
      (ModuleCat.of (T (S := S) (J := J))
        (Module.jacobson (T (S := S) (J := J)) X)) := by
  let Rad := ModuleCat.of (T (S := S) (J := J))
    (Module.jacobson (T (S := S) (J := J)) X)
  letI : Subsingleton (TopPart (S := S) (J := J) Rad) :=
    ⟨by
      intro a b
      apply Subtype.ext
      apply Subtype.ext
      have haFixed := congrArg Subtype.val (topPart_fixed Rad a)
      have hbFixed := congrArg Subtype.val (topPart_fixed Rad b)
      have haZero := topIdempotent_smul_eq_zero_of_mem_jacobson
        X a.val.val a.val.property
      have hbZero := topIdempotent_smul_eq_zero_of_mem_jacobson
        X b.val.val b.val.property
      exact (haFixed.symm.trans haZero).trans
        (hbFixed.symm.trans hbZero).symm⟩
  exact projective_of_topPart_subsingleton Rad

section FiniteSkeleton

variable [IsNoetherianRing (T (S := S) (J := J))]
variable {ι : Type v} [Fintype ι]
variable (σ : IndecomposableSkeleton.{u, v, u}
  (T (S := S) (J := J)) ι)
variable (AR : σ.FiniteARTranslationData)

omit [Fintype ι] in
/-- For a separated triangular algebra, every irreducible predecessor of
an indecomposable projective is projective.  Such a predecessor is a
retract of the projective's Jacobson radical, and that radical is supported
on the projective radical-side diagonal. -/
theorem irreduciblePredecessorsOfProjectivesAreProjective :
    AR.IrreduciblePredecessorsOfProjectivesAreProjective σ := by
  intro x p hp hxp
  let Rad := ModuleCat.of (T (S := S) (J := J))
    (Module.jacobson (T (S := S) (J := J)) (σ.obj p))
  have hRadCat : Projective Rad := projective_moduleJacobian (σ.obj p).obj
  letI : Projective Rad := hRadCat
  have hRadModule : Module.Projective (T (S := S) (J := J)) Rad :=
    ModuleCat.projective_of_module_projective Rad
  letI : Module.Projective (T (S := S) (J := J))
      (Module.jacobson (T (S := S) (J := J)) (σ.obj p)) := hRadModule
  have hRadFG : Projective (σ.projectiveBoundaryRadical p) :=
    OpConjecture.RingelStable.fgProjective_of_moduleProjective
      (σ.projectiveBoundaryRadical p) inferInstance
  letI : Projective (σ.projectiveBoundaryRadical p) := hRadFG
  obtain ⟨r⟩ :=
    (σ.indecomposableRetract_projectiveBoundaryRadical_iff_irreducible
      p hp x).2 hxp
  exact r.projective

end FiniteSkeleton

end OpConjecture.SeparatedTriangularAlgebra
