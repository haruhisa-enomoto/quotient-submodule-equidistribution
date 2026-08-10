import OpConjecture.RepresentationTheory.FiniteDimensionalAlmostSplit
import OpConjecture.RepresentationTheory.FiniteDimensionalRecurrence
import OpConjecture.RepresentationTheory.SeparatedTriangularIndecomposable
import OpConjecture.RepresentationTheory.SingleCrossTriangularEquivalence
import OpConjecture.RepresentationTheory.TrivSqZeroExtSeparatedFinite
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.SimpleModule.Rank

/-!
# The three indecomposable modules of the one-arrow triangular algebra

For a field `K`, separated data with square-zero arrow space `K` are exactly
two vector spaces and one linear map.  This file classifies their finite
indecomposable realizations without choosing bases: the map is either
concentrated at one endpoint, or is an isomorphism between one-dimensional
spaces.  The resulting three candidates are the fixed `A₂` module types.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped RightActions

namespace OpConjecture.A2Separated

open SeparatedTriangularAlgebra
open TrivSqZeroExtSeparatedData
open TrivSqZeroExtSeparatedFinite
open TrivSqZeroExtSeparatedIndecomposable

universe u

variable (K : Type u) [Field K]

abbrev Data := SeparatedData.{u, u, u} (S := K) (J := K)
abbrev Triangular := SeparatedTriangularAlgebra.Algebra K K

@[simp]
theorem separatedIdeal_zero_val : (0 : SeparatedIdeal K K).val = 0 := rfl

@[simp]
theorem separatedIdeal_add_val (x y : SeparatedIdeal K K) :
    (x + y).val = x.val + y.val := rfl

@[simp]
theorem separatedIdeal_scalar_val (c : K) (j : SeparatedIdeal K K) :
    (c • j).val = c * j.val := rfl

@[simp]
theorem separatedIdeal_left_val (r : K × K) (j : SeparatedIdeal K K) :
    (r • j).val = r.1 * j.val := rfl

@[simp]
theorem separatedIdeal_right_val (j : SeparatedIdeal K K) (r : K × K) :
    (j <• r).val = j.val * r.2 := by
  rfl

/-- A one-arrow separated datum is controlled by the action of `1`. -/
def actionOne (D : Data K) : D.top →ₗ[K] D.radical where
  toFun := D.action 1
  map_add' := map_add _
  map_smul' c t := by
    calc
      D.action 1 (c • t) = D.action (1 <• c) t :=
        (D.action_right_smul 1 c t).symm
      _ = D.action (c • (1 : K)) t := by simp
      _ = c • D.action 1 t := D.action_left_smul c 1 t

theorem action_eq_smul_actionOne (D : Data K) (j : K) (t : D.top) :
    D.action j t = j • actionOne K D t := by
  simpa [actionOne] using D.action_left_smul j 1 t

/-- Generation of the radical layer is surjectivity of the one arrow map. -/
theorem actionOne_range_eq_top (D : Data K) (hD : IsGenerated D) :
    LinearMap.range (actionOne K D) = ⊤ := by
  have hle : actionRange D ≤ LinearMap.range (actionOne K D) := by
    apply Submodule.span_le.mpr
    rintro d ⟨j, t, rfl⟩
    rw [action_eq_smul_actionOne]
    exact Submodule.smul_mem _ j ⟨t, rfl⟩
  rw [hD] at hle
  exact top_unique hle

/-- The common kernel of all arrow actions is the kernel of the action of
`1`. -/
theorem actionOne_ker_eq_commonKernel (D : Data K) :
    LinearMap.ker (actionOne K D) = commonKernel D := by
  ext t
  constructor
  · intro ht j
    rw [action_eq_smul_actionOne, ht, smul_zero]
  · intro ht
    exact ht 1

/-- Kernel-freeness is injectivity of the one arrow map. -/
theorem actionOne_ker_eq_bot (D : Data K) (hD : IsKernelFree D) :
    LinearMap.ker (actionOne K D) = ⊥ := by
  rw [actionOne_ker_eq_commonKernel, hD]

/-- A generated and kernel-free one-arrow datum has an invertible arrow. -/
def actionOneEquiv (D : Data K) (hgen : IsGenerated D)
    (hker : IsKernelFree D) : D.top ≃ₗ[K] D.radical :=
  LinearEquiv.ofBijective (actionOne K D)
    ⟨LinearMap.ker_eq_bot.mp (actionOne_ker_eq_bot K D hker),
      LinearMap.range_eq_top.mp (actionOne_range_eq_top K D hgen)⟩

/-- If both layers occur in an indecomposable one-arrow datum, its top
vector space is itself indecomposable.  Conjugation through the invertible
arrow transports every idempotent on the top to the radical layer. -/
theorem top_isIndecomposable_of_bisupported
    (D : Data K) (hD : IsIndecomposableSeparatedData D)
    (hgen : IsGenerated D) (hker : IsKernelFree D)
    [Nontrivial D.top] :
    OpConjecture.Foundation.IsIndecomposableModule K D.top := by
  let e := actionOneEquiv K D hgen hker
  apply OpConjecture.Foundation.isIndecomposableModule_of_forall_isIdempotentElem
  intro f hf
  let g : D.radical →ₗ[K] D.radical :=
    e.toLinearMap.comp (f.comp e.symm.toLinearMap)
  let p : D ⟶ D := ⟨(f, g), by
    intro j t
    rw [action_eq_smul_actionOne, action_eq_smul_actionOne]
    change e (f (e.symm (j • e t))) = j • e (f t)
    rw [e.symm.map_smul, e.symm_apply_apply, f.map_smul, e.map_smul]⟩
  have hp : p ≫ p = p := by
    apply Subtype.ext
    apply Prod.ext
    · exact hf
    · ext d
      change e (f (e.symm (e (f (e.symm d))))) =
        e (f (e.symm d))
      rw [e.symm_apply_apply]
      have hf' : f.comp f = f := hf
      exact congrArg e (LinearMap.congr_fun hf' (e.symm d))
  rcases hD.2 p hp with hpzero | hpone
  · left
    exact congrArg (fun q ↦ q.val.1) hpzero
  · right
    exact congrArg (fun q ↦ q.val.1) hpone

/-- Both nonzero layers of an indecomposable one-arrow datum are
one-dimensional. -/
theorem top_finrank_eq_one_of_bisupported
    (D : Data K) (hD : IsIndecomposableSeparatedData D)
    (hgen : IsGenerated D) (hker : IsKernelFree D)
    [Nontrivial D.top] :
    Module.finrank K D.top = 1 := by
  have hs : IsSimpleModule K D.top :=
    OpConjecture.IndecomposableSkeleton.isSimpleModule_of_semisimple_of_indecomposable
      (top_isIndecomposable_of_bisupported K D hD hgen hker)
  exact isSimpleModule_iff_finrank_eq_one.mp hs

/-! ## The three standard data -/

/-- The simple supported on the top endpoint. -/
abbrev topData : Data K where
  top := ModuleCat.of K K
  radical := ModuleCat.of K PUnit
  action := 0
  action_left_smul := by intros; simp
  action_right_smul := by intros; simp

/-- The simple supported on the radical endpoint. -/
abbrev radicalData : Data K where
  top := ModuleCat.of K PUnit
  radical := ModuleCat.of K K
  action := 0
  action_left_smul := by intros; simp
  action_right_smul := by intros; simp

instance topData_radical_subsingleton : Subsingleton (topData K).radical := by
  change Subsingleton PUnit
  infer_instance

instance radicalData_top_subsingleton : Subsingleton (radicalData K).top := by
  change Subsingleton PUnit
  infer_instance

instance topData_top_simple : IsSimpleModule K (topData K).top := by
  change IsSimpleModule K K
  infer_instance

instance radicalData_radical_simple :
    IsSimpleModule K (radicalData K).radical := by
  change IsSimpleModule K K
  infer_instance

/-- The unique bisupported one-dimensional arrow datum. -/
abbrev arrowData : Data K where
  top := ModuleCat.of K K
  radical := ModuleCat.of K K
  action :=
    { toFun := fun j ↦
        { toFun := fun t ↦ j * t
          map_zero' := mul_zero j
          map_add' := mul_add j }
      map_zero' := by ext t; exact zero_mul t
      map_add' := by intro j k; ext t; exact add_mul j k t }
  action_left_smul := by intros; simp [mul_assoc]
  action_right_smul := by intros; simp [mul_assoc]

@[simp]
theorem arrowData_action (j t : K) :
    (arrowData K).action j t = j * t := rfl

instance arrowData_top_nontrivial : Nontrivial (arrowData K).top := by
  change Nontrivial K
  infer_instance

instance arrowData_radical_nontrivial : Nontrivial (arrowData K).radical := by
  change Nontrivial K
  infer_instance

/-- Candidate order: the arrow module, the top simple, and the radical
simple. -/
def candidateData : Fin 3 → Data K
  | 0 => arrowData K
  | 1 => topData K
  | 2 => radicalData K

/-- Diagonal field scalars associate with the target-coordinate action on
the tagged arrow ideal. -/
instance separatedIdealLeftScalarTower :
    IsScalarTower K (K × K) (SeparatedIdeal K K) where
  smul_assoc c r j := by
    apply SeparatedIdeal.ext
    change (c * r.1) * j.val = c * (r.1 * j.val)
    exact mul_assoc _ _ _

/-- Diagonal field scalars associate with the source-coordinate right action
on the tagged arrow ideal. -/
instance separatedIdealRightScalarTower :
    IsScalarTower K (K × K)ᵐᵒᵖ (SeparatedIdeal K K) where
  smul_assoc c r j := by
    apply SeparatedIdeal.ext
    change j.val * (c * (MulOpposite.unop r).2) =
      c * (j.val * (MulOpposite.unop r).2)
    ring

/-- The diagonal scalar map makes the triangular ring a `K`-algebra. -/
instance triangularAlgebra : _root_.Algebra K (Triangular K) := by
  exact TrivSqZeroExt.algebra' K (K × K) (SeparatedIdeal K K)

noncomputable instance triangularFiniteDimensional :
    FiniteDimensional K (Triangular K) := by
  exact triangularAlgebra_moduleFinite

noncomputable instance triangularNoetherian :
    IsNoetherianRing (Triangular K) :=
  IsNoetherianRing.of_finite K (Triangular K)

noncomputable instance triangularOppositeNoetherian :
    IsNoetherianRing (Triangular K)ᵐᵒᵖ :=
  IsNoetherianRing.of_finite K (Triangular K)ᵐᵒᵖ

instance arrowDataModule : Module (Triangular K) (Realized (arrowData K)) :=
  realizedModule (arrowData K)

instance topDataModule : Module (Triangular K) (Realized (topData K)) :=
  realizedModule (topData K)

instance radicalDataModule :
    Module (Triangular K) (Realized (radicalData K)) :=
  realizedModule (radicalData K)

instance candidateModule (i : Fin 3) :
    Module (Triangular K) (Realized (candidateData K i)) :=
  realizedModule (candidateData K i)

noncomputable instance candidateModuleFinite (i : Fin 3) :
    Module.Finite (Triangular K) (Realized (candidateData K i)) := by
  fin_cases i
  ·
    letI : Module.Finite K (arrowData K).top := by infer_instance
    letI : Module.Finite K (arrowData K).radical := by infer_instance
    exact realized_moduleFinite (arrowData K)
  ·
    letI : Module.Finite K (topData K).top := by infer_instance
    letI : Module.Finite K (topData K).radical := by infer_instance
    exact realized_moduleFinite (topData K)
  ·
    letI : Module.Finite K (radicalData K).top := by infer_instance
    letI : Module.Finite K (radicalData K).radical := by infer_instance
    exact realized_moduleFinite (radicalData K)

/-- The three standard data as finitely generated modules. -/
abbrev candidateFG (i : Fin 3) : FGModuleCat.{u} (Triangular K) :=
  FGModuleCat.of (Triangular K) (Realized (candidateData K i))

private theorem field_isIndecomposable :
    OpConjecture.Foundation.IsIndecomposableModule K K := by
  letI : IsSimpleModule K K := inferInstance
  exact OpConjecture.Foundation.IsSimpleModule.isIndecomposableModule

private theorem arrowData_isIndecomposableSeparatedData :
    IsIndecomposableSeparatedData (arrowData K) := by
  have hnontrivial : Nontrivial (Reconstructed (arrowData K)) := by
    change Nontrivial (K × K)
    infer_instance
  refine ⟨hnontrivial, ?_⟩
  intro p hp
  have hcomponents : p.val.2 = p.val.1 := by
    apply LinearMap.ext
    intro t
    have h := p.property 1 t
    change K at t
    change p.val.2 (1 * t) = 1 * p.val.1 t at h
    simpa using h
  have hfirst : p.val.1.comp p.val.1 = p.val.1 := by
    have h := congrArg (fun q ↦ q.val.1) hp
    exact h
  rcases (field_isIndecomposable K).eq_zero_or_eq_one_of_isIdempotentElem
      hfirst with hzero | hone
  · left
    apply Subtype.ext
    apply Prod.ext
    · exact hzero
    · rw [hcomponents, hzero]
      rfl
  · right
    apply Subtype.ext
    apply Prod.ext
    · exact hone
    · rw [hcomponents, hone]
      rfl

/-- Each of the three standard modules is indecomposable. -/
theorem candidateFG_indecomposable (i : Fin 3) :
    OpConjecture.Foundation.IsIndecomposableModule (Triangular K) (candidateFG K i) := by
  fin_cases i
  ·
    exact (realized_isIndecomposable_iff (arrowData K)).2
      (arrowData_isIndecomposableSeparatedData K)
  ·
    change OpConjecture.Foundation.IsIndecomposableModule (Triangular K)
      (Realized (topData K))
    have hs := realized_simple_of_top (topData K)
      (topData_top_simple K)
    letI : IsSimpleModule (Triangular K) (Realized (topData K)) :=
      (simple_iff_isSimpleModule' _).1 hs
    exact OpConjecture.Foundation.IsSimpleModule.isIndecomposableModule
  ·
    change OpConjecture.Foundation.IsIndecomposableModule (Triangular K)
      (Realized (radicalData K))
    have hs := realized_simple_of_radical (radicalData K)
      (radicalData_radical_simple K)
    letI : IsSimpleModule (Triangular K) (Realized (radicalData K)) :=
      (simple_iff_isSimpleModule' _).1 hs
    exact OpConjecture.Foundation.IsSimpleModule.isIndecomposableModule

/-- Exactly the two endpoint candidates are simple. -/
theorem candidateFG_simple_iff (i : Fin 3) :
    Simple (candidateFG K i) ↔ i = 1 ∨ i = 2 := by
  fin_cases i
  · constructor
    · intro hs
      exfalso
      apply realized_not_simple_of_top_radical_nontrivial (arrowData K)
      apply (simple_iff_isSimpleModule' _).2
      exact (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
        (candidateFG K 0)).1 hs
    · rintro (h | h)
      · exact ((by decide : (0 : Fin 3) ≠ 1) h).elim
      · exact ((by decide : (0 : Fin 3) ≠ 2) h).elim
  · constructor
    · intro _
      exact Or.inl rfl
    · intro _
      apply (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
        (candidateFG K 1)).2
      exact (simple_iff_isSimpleModule' _).1
        (realized_simple_of_top (topData K) (topData_top_simple K))
  · constructor
    · intro _
      exact Or.inr rfl
    · intro _
      apply (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
        (candidateFG K 2)).2
      exact (simple_iff_isSimpleModule' _).1
        (realized_simple_of_radical (radicalData K)
          (radicalData_radical_simple K))

/-! ## Isomorphisms to the standard data -/

/-- A one-dimensional pure top datum is the standard top candidate. -/
def topDataIso (D : Data K) [Subsingleton D.radical]
    (e : K ≃ₗ[K] D.top) : topData K ≅ D where
  hom := ⟨(e.toLinearMap, 0), by
    intro j t
    exact Subsingleton.elim _ _⟩
  inv := ⟨(e.symm.toLinearMap, 0), by
    intro j t
    exact Subsingleton.elim _ _⟩
  hom_inv_id := by
    apply Subtype.ext
    apply Prod.ext
    · apply LinearMap.ext
      intro t
      exact e.symm_apply_apply t
    · apply LinearMap.ext
      intro d
      exact Subsingleton.elim _ _
  inv_hom_id := by
    apply Subtype.ext
    apply Prod.ext
    · apply LinearMap.ext
      intro t
      exact e.apply_symm_apply t
    · apply LinearMap.ext
      intro d
      exact Subsingleton.elim _ _

/-- A one-dimensional pure radical datum is the standard radical
candidate. -/
def radicalDataIso (D : Data K) [Subsingleton D.top]
    (e : K ≃ₗ[K] D.radical) : radicalData K ≅ D where
  hom := ⟨(0, e.toLinearMap), by
    intro j t
    change e 0 = D.action j 0
    simp⟩
  inv := ⟨(0, e.symm.toLinearMap), by
    intro j t
    change e.symm (D.action j t) = 0
    rw [show t = 0 from Subsingleton.elim _ _, map_zero, map_zero]⟩
  hom_inv_id := by
    apply Subtype.ext
    apply Prod.ext
    · apply LinearMap.ext
      intro t
      exact Subsingleton.elim _ _
    · apply LinearMap.ext
      intro d
      exact e.symm_apply_apply d
  inv_hom_id := by
    apply Subtype.ext
    apply Prod.ext
    · apply LinearMap.ext
      intro t
      exact Subsingleton.elim _ _
    · apply LinearMap.ext
      intro d
      exact e.apply_symm_apply d

/-- An invertible arrow between one-dimensional layers is the standard
arrow datum. -/
def arrowDataIso (D : Data K) (hgen : IsGenerated D)
    (hker : IsKernelFree D) (eTop : K ≃ₗ[K] D.top) :
    arrowData K ≅ D := by
  let eArrow := actionOneEquiv K D hgen hker
  let eRad : K ≃ₗ[K] D.radical := eTop.trans eArrow
  exact
    { hom := ⟨(eTop.toLinearMap, eRad.toLinearMap), by
        intro j t
        change K at t
        rw [arrowData_action, action_eq_smul_actionOne]
        change eArrow (eTop (j * t)) = j • eArrow (eTop t)
        calc
          eArrow (eTop (j * t)) = eArrow (j • eTop t) := by
            congr 1
            simpa using eTop.map_smul j t
          _ = j • eArrow (eTop t) := eArrow.map_smul j (eTop t)⟩
      inv := ⟨(eTop.symm.toLinearMap, eRad.symm.toLinearMap), by
        intro j t
        rw [action_eq_smul_actionOne, arrowData_action]
        change eRad.symm (j • eArrow t) = j * eTop.symm t
        rw [eRad.symm.map_smul]
        change j • eTop.symm (eArrow.symm (eArrow t)) =
          j * eTop.symm t
        rw [eArrow.symm_apply_apply]
        rfl⟩
      hom_inv_id := by
        apply Subtype.ext
        apply Prod.ext
        · apply LinearMap.ext
          intro x
          exact eTop.symm_apply_apply x
        · apply LinearMap.ext
          intro x
          exact eRad.symm_apply_apply x
      inv_hom_id := by
        apply Subtype.ext
        apply Prod.ext
        · apply LinearMap.ext
          intro x
          exact eTop.apply_symm_apply x
        · apply LinearMap.ext
          intro x
          exact eRad.apply_symm_apply x }

/-! ## Exhaustiveness -/

/-- A normalization isomorphism of separated data yields the corresponding
isomorphism of finitely generated triangular-algebra modules. -/
def candidateFGIsoOfDataIso (X : FGModuleCat.{u} (Triangular K))
    (i : Fin 3) (e : candidateData K i ≅
      ofModule (S := K) (J := K) X.obj) :
    candidateFG K i ≅ X := by
  let U := forget₂ (FGModuleCat.{u} (Triangular K))
    (ModuleCat.{u} (Triangular K))
  exact U.preimageIso
    ((realizationFunctor (S := K) (J := K)).mapIso e ≪≫
      realizedOfModuleIso (S := K) (J := K) X.obj)

/-- Every finite indecomposable module over the one-arrow triangular algebra
is isomorphic to exactly one of the three standard candidates (existence is
proved here; uniqueness is proved below). -/
theorem exists_candidateFG_iso
    (X : FGModuleCat.{u} (Triangular K))
    (hX : OpConjecture.Foundation.IsIndecomposableModule (Triangular K) X) :
    ∃ i : Fin 3, Nonempty (candidateFG K i ≅ X) := by
  let D : Data K := ofModule (S := K) (J := K) X.obj
  letI : Module.Finite K D.top := ofModule_top_moduleFinite X
  letI : Module.Finite K D.radical := ofModule_radical_moduleFinite X
  have hD : IsIndecomposableSeparatedData D :=
    ofModule_isIndecomposableSeparatedData X.obj hX
  rcases subsingleton_or_nontrivial D.top with htop | htop
  · letI : Subsingleton D.top := htop
    have hind : OpConjecture.Foundation.IsIndecomposableModule K D.radical :=
      radical_isIndecomposable_of_top_subsingleton D hD
    have hs : IsSimpleModule K D.radical :=
      OpConjecture.IndecomposableSkeleton.isSimpleModule_of_semisimple_of_indecomposable
        hind
    have hrank : Module.finrank K D.radical = 1 :=
      isSimpleModule_iff_finrank_eq_one.mp hs
    let e : K ≃ₗ[K] D.radical :=
      (Module.nonempty_linearEquiv_of_finrank_eq_one hrank).some
    refine ⟨2, ⟨?_⟩⟩
    exact candidateFGIsoOfDataIso K X 2 (radicalDataIso K D e)
  · letI : Nontrivial D.top := htop
    rcases subsingleton_or_nontrivial D.radical with hrad | hrad
    · letI : Subsingleton D.radical := hrad
      have hind : OpConjecture.Foundation.IsIndecomposableModule K D.top :=
        top_isIndecomposable_of_radical_subsingleton D hD
      have hs : IsSimpleModule K D.top :=
        OpConjecture.IndecomposableSkeleton.isSimpleModule_of_semisimple_of_indecomposable
          hind
      have hrank : Module.finrank K D.top = 1 :=
        isSimpleModule_iff_finrank_eq_one.mp hs
      let e : K ≃ₗ[K] D.top :=
        (Module.nonempty_linearEquiv_of_finrank_eq_one hrank).some
      refine ⟨1, ⟨?_⟩⟩
      exact candidateFGIsoOfDataIso K X 1 (topDataIso K D e)
    · letI : Nontrivial D.radical := hrad
      have hgen : IsGenerated D :=
        isGenerated_of_indecomposable_of_top_nontrivial D hD
      have hker : IsKernelFree D :=
        isKernelFree_of_indecomposable_of_radical_nontrivial D hD
      have hrank : Module.finrank K D.top = 1 :=
        top_finrank_eq_one_of_bisupported K D hD hgen hker
      let e : K ≃ₗ[K] D.top :=
        (Module.nonempty_linearEquiv_of_finrank_eq_one hrank).some
      refine ⟨0, ⟨?_⟩⟩
      exact candidateFGIsoOfDataIso K X 0
        (arrowDataIso K D hgen hker e)

/-- An isomorphism of candidate modules lifts back to an isomorphism of the
underlying separated data. -/
def candidateDataIsoOfFGIso {i j : Fin 3}
    (e : candidateFG K i ≅ candidateFG K j) :
    candidateData K i ≅ candidateData K j := by
  let U := forget₂ (FGModuleCat.{u} (Triangular K))
    (ModuleCat.{u} (Triangular K))
  exact (realizationFunctor (S := K) (J := K)).preimageIso (U.mapIso e)

private theorem topData_not_iso_radicalData
    (e : topData K ≅ radicalData K) : False := by
  have hmaps := congrArg (fun q ↦ q.val.1) e.hom_inv_id
  have hone := LinearMap.congr_fun hmaps (1 : K)
  change e.inv.val.1 (e.hom.val.1 (1 : K)) = 1 at hone
  have hzero : e.hom.val.1 (1 : K) = 0 := Subsingleton.elim _ _
  rw [hzero, map_zero] at hone
  exact zero_ne_one hone

private theorem arrow_not_iso_endpoint {j : Fin 3}
    (hj : j = 1 ∨ j = 2) (e : candidateFG K 0 ≅ candidateFG K j) :
    False := by
  have hsimpleTarget : Simple (candidateFG K j) :=
    (candidateFG_simple_iff K j).2 hj
  letI : Simple (candidateFG K j) := hsimpleTarget
  have hsimpleArrow : Simple (candidateFG K 0) := Simple.of_iso e
  have h := (candidateFG_simple_iff K 0).1 hsimpleArrow
  omega

/-- The three standard candidates are pairwise nonisomorphic. -/
theorem candidateFG_eq_of_iso {i j : Fin 3}
    (e : candidateFG K i ≅ candidateFG K j) : i = j := by
  fin_cases i <;> fin_cases j
  · rfl
  · exact (arrow_not_iso_endpoint K (Or.inl rfl) e).elim
  · exact (arrow_not_iso_endpoint K (Or.inr rfl) e).elim
  · exact (arrow_not_iso_endpoint K (Or.inl rfl) e.symm).elim
  · rfl
  · exact (topData_not_iso_radicalData K
      (candidateDataIsoOfFGIso K e)).elim
  · exact (arrow_not_iso_endpoint K (Or.inr rfl) e.symm).elim
  · exact (topData_not_iso_radicalData K
      (candidateDataIsoOfFGIso K e).symm).elim
  · rfl

/-! ## The canonical finite skeleton and its exact ranks -/

/-- The canonical indecomposable skeleton of the one-arrow triangular
algebra. -/
noncomputable abbrev sigma :
    IndecomposableSkeleton (Triangular K)
      (CanonicalIndecomposableIndex.{u, u} (Triangular K)) :=
  indecomposableSkeletonOfFiniteLength
    (OpConjecture.IndecomposableSkeleton.fgModule_isFiniteLength_of_finiteDimensional
      K (Triangular K))

/-- The canonical skeleton label selected for a standard candidate. -/
noncomputable def candidateIndex (i : Fin 3) :
    CanonicalIndecomposableIndex.{u, u} (Triangular K) :=
  Classical.choose ((sigma K).complete (candidateFG K i)
    (candidateFG_indecomposable K i))

/-- Each standard candidate is isomorphic to its selected canonical
representative. -/
noncomputable def candidateIndexIso (i : Fin 3) :
    candidateFG K i ≅ (sigma K).obj (candidateIndex K i) :=
  Classical.choice (Classical.choose_spec
    ((sigma K).complete (candidateFG K i)
      (candidateFG_indecomposable K i)))

theorem candidateIndex_injective : Function.Injective (candidateIndex K) := by
  intro i j hij
  apply candidateFG_eq_of_iso K
  exact candidateIndexIso K i ≪≫ eqToIso (congrArg (sigma K).obj hij) ≪≫
    (candidateIndexIso K j).symm

theorem candidateIndex_surjective : Function.Surjective (candidateIndex K) := by
  intro j
  obtain ⟨i, ⟨e⟩⟩ := exists_candidateFG_iso K ((sigma K).obj j)
    ((sigma K).indecomposable j)
  refine ⟨i, ?_⟩
  apply (sigma K).eq_of_iso
  exact ⟨(candidateIndexIso K i).symm ≪≫ e⟩

/-- The three explicit candidates enumerate the canonical skeleton. -/
noncomputable def candidateIndexEquiv :
    Fin 3 ≃ CanonicalIndecomposableIndex.{u, u} (Triangular K) :=
  Equiv.ofBijective (candidateIndex K)
    ⟨candidateIndex_injective K, candidateIndex_surjective K⟩

noncomputable instance canonicalIndexFinite :
    Finite (CanonicalIndecomposableIndex.{u, u} (Triangular K)) :=
  Finite.of_equiv (Fin 3) (candidateIndexEquiv K)

/-- The fixed one-arrow triangular algebra has exactly three
indecomposable finite-module isomorphism classes. -/
theorem natCard_canonicalIndex_eq_three :
    Nat.card (CanonicalIndecomposableIndex.{u, u} (Triangular K)) = 3 := by
  calc
    Nat.card (CanonicalIndecomposableIndex.{u, u} (Triangular K)) =
        Nat.card (Fin 3) := Nat.card_congr (candidateIndexEquiv K).symm
    _ = 3 := by simp

/-- Restricting the candidate enumeration to the two endpoints enumerates
the simple canonical representatives. -/
noncomputable def endpointEquivSimpleIndex :
    {i : Fin 3 // i = 1 ∨ i = 2} ≃ (sigma K).SimpleIndex where
  toFun i :=
    ⟨candidateIndex K i.1,
      (Simple.iff_of_iso (candidateIndexIso K i.1)).1
        ((candidateFG_simple_iff K i.1).2 i.2)⟩
  invFun j := by
    let i := (candidateIndexEquiv K).symm j.1
    refine ⟨i, ?_⟩
    apply (candidateFG_simple_iff K i).1
    apply (Simple.iff_of_iso (candidateIndexIso K i)).2
    have hidx := (candidateIndexEquiv K).apply_symm_apply j.1
    change candidateIndex K i = j.1 at hidx
    rw [hidx]
    exact j.2
  left_inv i := by
    apply Subtype.ext
    exact (candidateIndexEquiv K).left_inv i.1
  right_inv j := by
    apply Subtype.ext
    exact (candidateIndexEquiv K).right_inv j.1

/-- Exactly two canonical indecomposable representatives are simple. -/
theorem natCard_simpleIndex_eq_two : Nat.card (sigma K).SimpleIndex = 2 := by
  calc
    Nat.card (sigma K).SimpleIndex =
        Nat.card {i : Fin 3 // i = 1 ∨ i = 2} :=
      Nat.card_congr (endpointEquivSimpleIndex K).symm
    _ = 2 := by
      rw [Nat.card_eq_fintype_card]
      decide

/-! ## Identification with the abstract `A₂` model -/

/-- Swap the two diagonal coordinates and unwrap the arrow coordinate.  The
swap aligns the endpoint convention of `A2Triangular.Model` with the
top/radical convention of the separated triangular algebra. -/
def modelToTriangularAlgHom :
    OpConjecture.A2Triangular.Model K →ₐ[K] Triangular K where
  toFun x := ((x.fst.2, x.fst.1), ⟨x.snd.value⟩)
  map_one' := rfl
  map_mul' x y := by
    apply TrivSqZeroExt.ext
    · apply Prod.ext <;> rfl
    · apply SeparatedIdeal.ext
      change x.fst.2 * y.snd.value + y.fst.1 * x.snd.value =
        x.fst.2 * y.snd.value + x.snd.value * y.fst.1
      ring
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

theorem modelToTriangularAlgHom_bijective :
    Function.Bijective (modelToTriangularAlgHom K) := by
  constructor
  · intro x y hxy
    apply TrivSqZeroExt.ext
    · apply Prod.ext
      · simpa [modelToTriangularAlgHom] using
          congrArg (fun z : Triangular K ↦ z.fst.2) hxy
      · simpa [modelToTriangularAlgHom] using
          congrArg (fun z : Triangular K ↦ z.fst.1) hxy
    · apply OpConjecture.A2Triangular.Arrow.ext
      simpa [modelToTriangularAlgHom] using
        congrArg (fun z : Triangular K ↦ z.snd.val) hxy
  · intro z
    refine ⟨((z.fst.2, z.fst.1),
      OpConjecture.A2Triangular.Arrow.mk z.snd.val), ?_⟩
    apply TrivSqZeroExt.ext
    · apply Prod.ext <;> rfl
    · apply SeparatedIdeal.ext
      rfl

/-- The two fixed presentations of the one-arrow algebra are isomorphic as
`K`-algebras. -/
noncomputable def modelAlgEquiv :
    OpConjecture.A2Triangular.Model K ≃ₐ[K] Triangular K :=
  AlgEquiv.ofBijective (modelToTriangularAlgHom K)
    (modelToTriangularAlgHom_bijective K)

/-- The separated one-arrow algebra with its canonical finite complete
indecomposable skeleton. -/
noncomputable def node :
    OpConjecture.BottomLevels.FiniteDimensionalRecurrence.AlgebraNode K where
  Carrier := Triangular K
  ring := inferInstance
  algebra := inferInstance
  finiteDimensional := inferInstance
  noetherian := inferInstance
  noetherianOpposite := inferInstance
  Index := CanonicalIndecomposableIndex.{u, u} (Triangular K)
  finiteIndex := inferInstance
  skeleton := sigma K

end OpConjecture.A2Separated
