import OpConjecture.RepresentationTheory.NakayamaMatlisComparison
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The counit pairing for a finite projective module

For a finitely generated projective left module `P`, the regular Hom-duality
produces a finitely generated projective right module `Q`.  Its counit
identifies `P` with the right-linear dual of `Q`.  This file records that
identification on carriers and chooses a finite dual frame on `Q`, yielding
the reconstruction formula used by the finite-dimensional
Nakayama--Matlis comparison.

No concrete algebra, presentation by a quiver, or module classification is
used here.
-/

noncomputable section

open CategoryTheory Opposite

namespace OpConjecture.AuslanderTranspose.TwoStepProjectivePresentation

open OpConjecture.RingelStable

universe u

namespace FiniteProjectiveNakayama

/-- A finite dual frame for a finitely generated projective module. -/
structure FiniteProjectiveFrame
    (S Q : Type u) [Semiring S] [AddCommMonoid Q] [Module S Q] where
  n : ℕ
  q : Fin n → Q
  phi : Fin n → (Q →ₗ[S] S)
  total : ∀ x : Q, ∑ i, phi i x • q i = x

/-- A chosen finite dual frame obtained from a finite free splitting. -/
noncomputable def finiteProjectiveFrame
    (S Q : Type u) [Semiring S] [AddCommMonoid Q] [Module S Q]
    [Module.Finite S Q] [Module.Projective S Q] :
    FiniteProjectiveFrame S Q := by
  classical
  let h := Module.Finite.exists_comp_eq_id_of_projective S Q
  let n := h.choose
  let hf := h.choose_spec
  let f := hf.choose
  let hg := hf.choose_spec
  let g := hg.choose
  let hfg := hg.choose_spec.2.2
  let b := Pi.basisFun S (Fin n)
  refine
    { n := n
      q := fun i ↦ f (b i)
      phi := fun i ↦ (LinearMap.proj i).comp g
      total := ?_ }
  intro x
  calc
    ∑ i, ((LinearMap.proj i).comp g) x • f (b i) =
        f (∑ i, (b.repr (g x)) i • b i) := by
          rw [map_sum]
          congr 1
          funext i
          rw [map_smul]
          simp [b, Pi.basisFun_repr]
    _ = f (g x) := by rw [b.sum_repr]
    _ = x := by
      exact LinearMap.congr_fun hfg x

variable (R : Type u) [Ring R]
  [IsNoetherianRing R] [IsNoetherianRing Rᵐᵒᵖ]

abbrev regularHomDuality :=
  OpConjecture.CPSLeftStandardLayers.regularHomDualityEquivalence R

variable (P : FGProjectives (R := R))

abbrev finiteProjectiveObject :=
  (fgProjectivesEquivFiniteProjectives (R := R)).functor.obj P

abbrev projectiveHomDual :=
  (fgProjectiveHomDuality (R := R)).functor.obj (Opposite.op P)

def counitEvaluation (p : P.obj) :
    (projectiveHomDual (R := R) P).obj →ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ :=
  (((regularHomDuality R).counitIso.app
    (finiteProjectiveObject (R := R) P)).inv.hom.hom p).unop.hom

omit [IsNoetherianRing R] in
@[simp]
theorem counitEvaluation_add (p p' : P.obj) :
    counitEvaluation (R := R) P (p + p') =
      counitEvaluation (R := R) P p +
        counitEvaluation (R := R) P p' := by
  have h :=
    (((regularHomDuality R).counitIso.app
      (finiteProjectiveObject (R := R) P)).inv.hom.hom).map_add p p'
  exact congrArg (fun f ↦ f.unop.hom) h

omit [IsNoetherianRing R] in
@[simp]
theorem counitEvaluation_smul (r : R) (p : P.obj) :
    counitEvaluation (R := R) P (r • p) =
      r • counitEvaluation (R := R) P p := by
  have h :=
    (((regularHomDuality R).counitIso.app
      (finiteProjectiveObject (R := R) P)).inv.hom.hom).map_smul r p
  exact congrArg (fun f ↦ f.unop.hom) h

def counitEvaluationLinearMap :
    P.obj →ₗ[R]
      ((projectiveHomDual (R := R) P).obj →ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ) where
  toFun := counitEvaluation (R := R) P
  map_add' := counitEvaluation_add (R := R) P
  map_smul' := counitEvaluation_smul (R := R) P

def counitReconstruction
    (phi : (projectiveHomDual (R := R) P).obj →ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ) :
    P.obj :=
  ((regularHomDuality R).counitIso.app
    (finiteProjectiveObject (R := R) P)).hom.hom.hom
      (ModuleCat.ofHom phi).op

omit [IsNoetherianRing R] in
theorem counitReconstruction_evaluation (p : P.obj) :
    counitReconstruction (R := R) P
      (counitEvaluation (R := R) P p) = p := by
  change
    ((regularHomDuality R).counitIso.app
      (finiteProjectiveObject (R := R) P)).hom.hom.hom
        (((regularHomDuality R).counitIso.app
          (finiteProjectiveObject (R := R) P)).inv.hom.hom p) = p
  have h :=
    congrArg
      (fun f ↦ f.hom.hom p)
      (((regularHomDuality R).counitIso.app
        (finiteProjectiveObject (R := R) P)).inv_hom_id)
  change
    ((regularHomDuality R).counitIso.app
      (finiteProjectiveObject (R := R) P)).hom.hom.hom
        (((regularHomDuality R).counitIso.app
          (finiteProjectiveObject (R := R) P)).inv.hom.hom p) = p at h
  exact h

omit [IsNoetherianRing R] in
theorem counitEvaluation_reconstruction
    (phi : (projectiveHomDual (R := R) P).obj →ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ) :
    counitEvaluation (R := R) P
      (counitReconstruction (R := R) P phi) = phi := by
  apply LinearMap.ext
  intro q
  change
    (((regularHomDuality R).counitIso.app
      (finiteProjectiveObject (R := R) P)).inv.hom.hom
        (((regularHomDuality R).counitIso.app
          (finiteProjectiveObject (R := R) P)).hom.hom.hom
            (ModuleCat.ofHom phi).op)).unop.hom q = phi q
  have h := congrArg
    (fun f ↦ f.hom.hom (ModuleCat.ofHom phi).op)
    (((regularHomDuality R).counitIso.app
      (finiteProjectiveObject (R := R) P)).hom_inv_id)
  have hq := congrArg (fun f ↦ f.unop.hom q) h
  exact hq

def counitCarrierLinearEquiv :
    P.obj ≃ₗ[R]
      ((projectiveHomDual (R := R) P).obj →ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ) where
  toFun := counitEvaluation (R := R) P
  invFun := counitReconstruction (R := R) P
  left_inv := counitReconstruction_evaluation (R := R) P
  right_inv := counitEvaluation_reconstruction (R := R) P
  map_add' := counitEvaluation_add (R := R) P
  map_smul' := counitEvaluation_smul (R := R) P

omit [IsNoetherianRing R] in
@[simp]
theorem counitHom_smul_apply
    (r : R)
    (phi : (projectiveHomDual (R := R) P).obj →ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ)
    (q : (projectiveHomDual (R := R) P).obj) :
    (r • phi) q = phi q * MulOpposite.op r := by
  rfl

/-- A chosen finite dual frame on the abstract Hom-dual projective `Q`. -/
noncomputable def projectiveHomDualFrame :
    FiniteProjectiveFrame Rᵐᵒᵖ (projectiveHomDual (R := R) P).obj := by
  letI : Module.Projective Rᵐᵒᵖ (projectiveHomDual (R := R) P).obj :=
    moduleProjective_of_fgProjective
      (projectiveHomDual (R := R) P).obj
      (projectiveHomDual (R := R) P).property
  exact finiteProjectiveFrame Rᵐᵒᵖ (projectiveHomDual (R := R) P).obj

/-- The element of `P` reconstructed from the `i`th dual-frame
functional on `Q`. -/
noncomputable def finiteProjectiveFrameElement
    (i : Fin (projectiveHomDualFrame (R := R) P).n) : P.obj :=
  counitReconstruction (R := R) P
    ((projectiveHomDualFrame (R := R) P).phi i)

omit [IsNoetherianRing R] in
@[simp]
theorem counitEvaluation_frameElement
    (i : Fin (projectiveHomDualFrame (R := R) P).n) :
    counitEvaluation (R := R) P
        (finiteProjectiveFrameElement (R := R) P i) =
      (projectiveHomDualFrame (R := R) P).phi i := by
  exact counitEvaluation_reconstruction (R := R) P _

omit [IsNoetherianRing R] in
/-- Transporting the dual-frame reconstruction of `Q` through the counit
recovers every element of `P`. -/
theorem finiteProjectiveFrameReconstruction (p : P.obj) :
    ∑ i, MulOpposite.unop
          (counitEvaluation (R := R) P p
            ((projectiveHomDualFrame (R := R) P).q i)) •
        finiteProjectiveFrameElement (R := R) P i = p := by
  apply (counitCarrierLinearEquiv (R := R) P).injective
  apply LinearMap.ext
  intro q
  change
    counitEvaluation (R := R) P
        (∑ i, MulOpposite.unop
            (counitEvaluation (R := R) P p
              ((projectiveHomDualFrame (R := R) P).q i)) •
          finiteProjectiveFrameElement (R := R) P i) q =
      counitEvaluation (R := R) P p q
  calc
    _ = ∑ i, counitEvaluation (R := R) P
          (MulOpposite.unop
              (counitEvaluation (R := R) P p
                ((projectiveHomDualFrame (R := R) P).q i)) •
            finiteProjectiveFrameElement (R := R) P i) q := by
          have h := map_sum
            (counitEvaluationLinearMap (R := R) P)
            (fun i : Fin (projectiveHomDualFrame (R := R) P).n ↦
              MulOpposite.unop
                  (counitEvaluation (R := R) P p
                    ((projectiveHomDualFrame (R := R) P).q i)) •
                finiteProjectiveFrameElement (R := R) P i)
            Finset.univ
          simpa only [counitEvaluationLinearMap, LinearMap.coe_mk,
            AddHom.coe_mk, LinearMap.sum_apply] using
            congrArg (fun phi ↦ phi q) h
    _ = ∑ i, (projectiveHomDualFrame (R := R) P).phi i q *
          counitEvaluation (R := R) P p
            ((projectiveHomDualFrame (R := R) P).q i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [counitEvaluation_smul, counitEvaluation_frameElement,
            counitHom_smul_apply]
          simp
    _ = counitEvaluation (R := R) P p
          (∑ i, (projectiveHomDualFrame (R := R) P).phi i q •
            (projectiveHomDualFrame (R := R) P).q i) := by
          rw [map_sum]
          simp
    _ = counitEvaluation (R := R) P p q := by
          rw [(projectiveHomDualFrame (R := R) P).total]

end FiniteProjectiveNakayama

end OpConjecture.AuslanderTranspose.TwoStepProjectivePresentation
