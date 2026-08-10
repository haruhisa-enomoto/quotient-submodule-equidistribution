import OpConjecture.RepresentationTheory.ProjectiveInjectiveMiddle
import OpConjecture.RepresentationTheory.FactorCategoryFactorLadderRecurrence
import OpConjecture.RepresentationTheory.ReverseFactorLadderRecurrence
import OpConjecture.RepresentationTheory.AlmostSplitDuality
import OpConjecture.RepresentationTheory.IndecomposableBiproduct

/-!
# Module-category bridge for projective-injective AR middles
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace OpConjecture.IndecomposableSkeleton

universe u v w

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} [Fintype ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)

section DualityUtilities

variable {S : Type u} [Ring S] [IsNoetherianRing S]
  {κ : Type w} [Fintype κ]
  (τ : IndecomposableSkeleton.{u, w, u} S κ)

namespace AlignedAntiEquivalence

variable (E : AlignedAntiEquivalence σ τ)

omit [Fintype ι] [Fintype κ] in
/-- An aligned anti-equivalence identifies projective source labels with
injective target labels. -/
theorem projective_iff_injective_image (i : ι) :
    Projective (σ.obj i) ↔ Injective (τ.obj (E.labelEquiv i)) := by
  constructor
  · intro hSource
    have hOp : Injective (Opposite.op (σ.obj i)) :=
      Injective.projective_iff_injective_op.mp hSource
    have hMap : Injective
        (E.categoryEquiv.functor.obj (Opposite.op (σ.obj i))) :=
      (E.categoryEquiv.map_injective_iff
        (Opposite.op (σ.obj i))).2 hOp
    exact Injective.of_iso (E.objIso i) hMap
  · intro hTarget
    have hMap : Injective
        (E.categoryEquiv.functor.obj (Opposite.op (σ.obj i))) :=
      Injective.of_iso (E.objIso i).symm hTarget
    have hOp : Injective (Opposite.op (σ.obj i)) :=
      (E.categoryEquiv.map_injective_iff
        (Opposite.op (σ.obj i))).1 hMap
    exact Injective.projective_iff_injective_op.mpr hOp

omit [Fintype ι] [Fintype κ] in
/-- An aligned anti-equivalence sends an irreducible arrow to the reversed
arrow between the aligned target representatives. -/
theorem hasIrreducibleMorphism_image {x y : ι}
    (h : HasIrreducibleMorphism (σ.obj x) (σ.obj y)) :
    HasIrreducibleMorphism
      (τ.obj (E.labelEquiv y)) (τ.obj (E.labelEquiv x)) := by
  obtain ⟨f, hf⟩ := h
  refine ⟨(E.objIso y).inv ≫ E.categoryEquiv.functor.map f.op ≫
      (E.objIso x).hom, ?_⟩
  exact ((hf.op.map_equivalence E.categoryEquiv).precomp_iso
    (E.objIso y).symm).postcomp_iso (E.objIso x)

end AlignedAntiEquivalence

namespace AlignedBiduality

variable (E : AlignedBiduality σ τ)

omit [Fintype ι] [Fintype κ] in
/-- Biduality identifies irreducible arrows with the reversed arrows on the
dual skeleton. -/
theorem hasIrreducibleMorphism_image_iff {x y : ι} :
    HasIrreducibleMorphism
        (τ.obj (E.forward.labelEquiv y))
        (τ.obj (E.forward.labelEquiv x)) ↔
      HasIrreducibleMorphism (σ.obj x) (σ.obj y) := by
  constructor
  · intro h
    have hback := E.backward.hasIrreducibleMorphism_image τ σ h
    rw [E.backward_label] at hback
    simpa only [Equiv.symm_apply_apply] using hback
  · exact E.forward.hasIrreducibleMorphism_image σ τ

end AlignedBiduality

end DualityUtilities

namespace MinimalRightAlmostSplitDecomposition

omit [Fintype ι] in
/-- If the middle object is indecomposable, its displayed finite
indecomposable decomposition has exactly one index. -/
theorem unique_index_of_middle_indecomposable
    {z : ι} (A : σ.MinimalRightAlmostSplitDecomposition z)
    (hA : OpConjecture.Foundation.IsIndecomposableModule R A.middle) :
    Nonempty (Unique A.index) := by
  classical
  letI : Fintype A.index := FintypeCat.fintype
  let Y : A.index → FGModuleCat R := fun t ↦ σ.obj (A.label t)
  obtain ⟨j₀, ⟨e₀⟩⟩ :=
    OpConjecture.IndecomposableBiproduct.exists_iso_summand
      A.middle A.finiteLength hA Y (fun t ↦ σ.indecomposable (A.label t))
        A.decomposition
  have htotal :
      Module.length R A.middle =
        ∑ t : A.index, Module.length R (σ.obj (A.label t)) := by
    let ePi : A.middle ≃ₗ[R] ((t : A.index) → σ.obj (A.label t)) :=
      (FGModuleCat.isoToLinearEquiv A.decomposition).trans
        (FGModuleCat.isoToLinearEquiv
          (OpConjecture.IndecomposableSkeleton.biproductIsoPiFG Y))
    exact ePi.length_eq.trans (Module.length_pi_of_fintype R _)
  have hsingle :
      Module.length R A.middle =
        Module.length R (σ.obj (A.label j₀)) :=
    (FGModuleCat.isoToLinearEquiv e₀).length_eq
  have hsum :
      (∑ t : A.index, Module.length R (σ.obj (A.label t))) =
        Module.length R (σ.obj (A.label j₀)) :=
    htotal.symm.trans hsingle
  have hsubsingleton : ∀ j : A.index, j = j₀ := by
    intro j
    by_contra hj
    let f : A.index → ℕ∞ :=
      fun t ↦ Module.length R (σ.obj (A.label t))
    have hsplit : f j₀ + (∑ t ∈ Finset.univ.erase j₀, f t) = f j₀ := by
      calc
        f j₀ + (∑ t ∈ Finset.univ.erase j₀, f t) =
            (∑ t ∈ Finset.univ.erase j₀, f t) + f j₀ := add_comm _ _
        _ = ∑ t ∈ Finset.univ, f t :=
          Finset.sum_erase_add Finset.univ f (Finset.mem_univ j₀)
        _ = f j₀ := by simpa [f] using hsum
    have hrest : (∑ t ∈ Finset.univ.erase j₀, f t) = 0 := by
      exact (ENat.addLECancellable_of_ne_top
        (Module.length_ne_top_iff.mpr
          (σ.finiteLength (A.label j₀)))).inj_left.mp (by
            simpa [add_comm] using hsplit)
    have hjmem : j ∈ Finset.univ.erase j₀ := by
      exact Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩
    have hjle : f j ≤ ∑ t ∈ Finset.univ.erase j₀, f t := by
      exact Finset.single_le_sum (fun _ _ ↦ bot_le) hjmem
    have hjzero : f j = 0 := by
      rw [hrest] at hjle
      exact le_antisymm hjle bot_le
    have htrivial : Subsingleton (σ.obj (A.label j)) := by
      apply (Module.length_eq_zero_iff
        (R := R) (M := σ.obj (A.label j))).mp
      simpa [f] using hjzero
    exact (not_subsingleton_iff_nontrivial.mpr
      (σ.indecomposable (A.label j)).nontrivial) htrivial
  exact ⟨Unique.mk ⟨j₀⟩ hsubsingleton⟩

end MinimalRightAlmostSplitDecomposition

namespace FiniteARTranslationData

variable (D : σ.FiniteARTranslationData)

/-- Every vertex as a label deleted from the empty kept support. -/
def allDeletedLabel (i : ι) : DeletedLabel (∅ : Set ι) :=
  ⟨i, by simp⟩

omit [Fintype ι] in
/-- At a nonprojective endpoint the unified right-AR decomposition is the
chosen genuine right almost-split decomposition. -/
theorem factorLadderRightARAt_nonprojective
    (x : σ.NonprojectiveLabel) :
    factorLadderRightARAt σ D x.1 = D.chosenRightAR σ x := by
  simp only [factorLadderRightARAt, dif_neg x.2]
  congr 1

/-- If the displayed right-AR middle has a unique summand and that summand
survives deletion, the restricted middle operator sends the endpoint basis
to that summand basis. -/
theorem factorLadderTheta_basis_eq_basis_of_unique
    (K : Set ι) (x : DeletedLabel K)
    (hU : Nonempty (Unique (factorLadderRightARAt σ D x.1).index))
    (hsurvives :
      (factorLadderRightARAt σ D x.1).label hU.some.default ∉ K) :
    factorLadderTheta (σ := σ) (D := D) K
        (FactorLadder.basis x) =
      FactorLadder.basis
        ⟨(factorLadderRightARAt σ D x.1).label hU.some.default,
          hsurvives⟩ := by
  classical
  letI : Unique (factorLadderRightARAt σ D x.1).index := hU.some
  letI : Fintype (factorLadderRightARAt σ D x.1).index :=
    FintypeCat.fintype
  funext y
  rw [factorLadderTheta_basis_apply]
  simp only [deletedMiddleMultiplicity, FactorLadder.basis]
  by_cases hy : y = ⟨(factorLadderRightARAt σ D x.1).label default,
      hsurvives⟩
  · subst y
    have hfilter :
        (Finset.univ.filter fun t :
          (factorLadderRightARAt σ D x.1).index ↦
            (factorLadderRightARAt σ D x.1).label t =
              (factorLadderRightARAt σ D x.1).label default) =
          Finset.univ := by
      apply Finset.filter_eq_self.2
      intro t _
      exact congrArg (factorLadderRightARAt σ D x.1).label
        (Subsingleton.elim t default)
    rw [hfilter]
    simp
  · have hlabel :
        (factorLadderRightARAt σ D x.1).label default ≠ y.1 := by
      intro h
      apply hy
      apply Subtype.ext
      exact h.symm
    simp [Finset.univ_unique, hy, hlabel]

/-- Every indecomposable summand of every genuine right AR middle is both
projective and injective. -/
def HasProjectiveInjectiveMiddle : Prop :=
  ∀ x : σ.NonprojectiveLabel,
    ∀ y : ι,
      HasIrreducibleMorphism (σ.obj y) (σ.obj x.1) →
        Projective (σ.obj y) ∧ Injective (σ.obj y)

/-- Every chosen genuine right almost-split middle object is indecomposable. -/
def HasIndecomposableAlmostSplitMiddle : Prop :=
  ∀ x : σ.NonprojectiveLabel,
    OpConjecture.Foundation.IsIndecomposableModule R (D.chosenRightAR σ x).middle

/-- The marked finite translation system read from the chosen AR middles. -/
def projectiveInjectiveMiddleData
    (hPI : HasProjectiveInjectiveMiddle σ) :
    ProjectiveInjectiveMiddle.Data ι where
  projective := {i | Projective (σ.obj i)}
  injective := {i | Injective (σ.obj i)}
  tau := D.arTranslationEquiv σ
  middle x := {y | HasIrreducibleMorphism (σ.obj y) (σ.obj x.1)}
  middle_subset_projective_injective := by
    intro x y hy
    exact hPI x y hy

section Duality

variable {S : Type u} [Ring S] [IsNoetherianRing S]
  {κ : Type w} [Fintype κ]
  (τ : IndecomposableSkeleton.{u, w, u} S κ)

omit [Fintype κ] in
/-- The projective-injective-middle condition is preserved by an aligned
biduality.  The reversal of a target middle arrow is rotated back to a
source middle arrow by source AR translation. -/
theorem hasProjectiveInjectiveMiddle_image
    (D : σ.FiniteARTranslationData)
    (E : AlignedBiduality σ τ)
    (hPI : HasProjectiveInjectiveMiddle σ) :
    HasProjectiveInjectiveMiddle τ := by
  intro q p hpq
  let qpre : ι := E.forward.labelEquiv.symm q.1
  let ppre : ι := E.forward.labelEquiv.symm p
  have hqNoninjective : ¬ Injective (σ.obj qpre) := by
    intro hqI
    apply q.2
    simpa [qpre] using
      (E.forward.injective_iff_projective_image σ τ qpre).1 hqI
  let z : σ.NoninjectiveLabel := ⟨qpre, hqNoninjective⟩
  let x : σ.NonprojectiveLabel := (D.arTranslationEquiv σ).symm z
  have htau : (D.arTranslation σ x).1 = qpre := by
    have h := (D.arTranslationEquiv σ).apply_symm_apply z
    exact congrArg Subtype.val h
  have hreverse :
      HasIrreducibleMorphism (σ.obj qpre) (σ.obj ppre) := by
    apply (E.hasIrreducibleMorphism_image_iff σ τ
      (x := qpre) (y := ppre)).1
    simpa [qpre, ppre] using hpq
  have hmiddle :
      HasIrreducibleMorphism (σ.obj ppre) (σ.obj x.1) :=
    (D.arTranslation_incidence σ x ppre).2 (by
      simpa [htau] using hreverse)
  have hpPI := hPI x ppre hmiddle
  constructor
  · simpa [ppre] using
      (E.forward.injective_iff_projective_image σ τ ppre).1 hpPI.2
  · simpa [ppre] using
      (E.forward.projective_iff_injective_image σ τ ppre).1 hpPI.1

/-- After applying the dual label equivalence to the deleted set, the target
forward first-mesh clauses are exactly the source reverse first-mesh clauses. -/
theorem qGood_image_iff_sGood
    (D : σ.FiniteARTranslationData)
    (Dτ : τ.FiniteARTranslationData)
    (E : AlignedBiduality σ τ)
    (hPI : HasProjectiveInjectiveMiddle σ)
    (Deleted : Set ι) :
    (Dτ.projectiveInjectiveMiddleData τ
        (D.hasProjectiveInjectiveMiddle_image σ τ E hPI)).QGood
          (E.forward.labelEquiv '' Deleted) ↔
      (D.projectiveInjectiveMiddleData σ hPI).SGood Deleted := by
  constructor
  · intro hQ x hxD
    let z : σ.NoninjectiveLabel := D.arTranslationEquiv σ x
    have htargetNonprojective :
        ¬ Projective (τ.obj (E.forward.labelEquiv z.1)) := by
      intro hP
      exact z.2
        ((E.forward.injective_iff_projective_image σ τ z.1).2 hP)
    let q : τ.NonprojectiveLabel :=
      ⟨E.forward.labelEquiv z.1, htargetNonprojective⟩
    have hqD : q.1 ∈ E.forward.labelEquiv '' Deleted :=
      ⟨z.1, hxD, rfl⟩
    obtain ⟨p, hpD, hpq⟩ := hQ q hqD
    obtain ⟨c, hcD, hcp⟩ := hpD
    change HasIrreducibleMorphism (τ.obj p) (τ.obj q.1) at hpq
    have hreverse :
        HasIrreducibleMorphism (σ.obj z.1) (σ.obj c) := by
      apply (E.hasIrreducibleMorphism_image_iff σ τ
        (x := z.1) (y := c)).1
      simpa [q, hcp] using hpq
    exact ⟨c, hcD, (D.arTranslation_incidence σ x c).2 hreverse⟩
  · intro hS q hqD
    obtain ⟨z, hzD, hzq⟩ := hqD
    have hqNonprojective : ¬ Projective (τ.obj q.1) := by
      simpa [projectiveInjectiveMiddleData] using q.2
    have hzNoninjective : ¬ Injective (σ.obj z) := by
      intro hzI
      apply hqNonprojective
      have hzP :=
        (E.forward.injective_iff_projective_image σ τ z).1 hzI
      simpa [hzq] using hzP
    let zni : σ.NoninjectiveLabel := ⟨z, hzNoninjective⟩
    let x : σ.NonprojectiveLabel := (D.arTranslationEquiv σ).symm zni
    have htau : (D.arTranslation σ x).1 = z := by
      have h := (D.arTranslationEquiv σ).apply_symm_apply zni
      exact congrArg Subtype.val h
    have htauD : (D.arTranslationEquiv σ x).1 ∈ Deleted := by
      simpa [FiniteARTranslationData.arTranslationEquiv, htau] using hzD
    obtain ⟨c, hcD, hcx⟩ := hS x htauD
    change HasIrreducibleMorphism (σ.obj c) (σ.obj x.1) at hcx
    refine ⟨E.forward.labelEquiv c, ⟨c, hcD, rfl⟩, ?_⟩
    change HasIrreducibleMorphism
      (τ.obj (E.forward.labelEquiv c)) (τ.obj q.1)
    rw [← hzq]
    apply (E.hasIrreducibleMorphism_image_iff σ τ
      (x := z) (y := c)).2
    have hzc := (D.arTranslation_incidence σ x c).1 hcx
    simpa [htau] using hzc

end Duality

/-- Under the PI-middle hypothesis, a forward factor ladder reaches a
deleted projective exactly at layer zero for a projective start or at layer
one through a surviving genuine AR-middle summand. -/
theorem factorLadder_reaches_projective_iff
    (hPI : HasProjectiveInjectiveMiddle σ)
    (K : Set ι) (x : DeletedLabel K) :
    (factorLadderData (σ := σ) (D := D) K).ReachesBoundary
        (deletedProjectiveSet σ K) x ↔
      Projective (σ.obj x.1) ∨
        ∃ _ : ¬ Projective (σ.obj x.1),
          ∃ t : (factorLadderRightARAt σ D x.1).index,
            (factorLadderRightARAt σ D x.1).label t ∉ K := by
  classical
  by_cases hx : Projective (σ.obj x.1)
  · constructor
    · intro _
      exact Or.inl hx
    · intro _
      refine ⟨0, x, hx, ?_⟩
      simp
  · have hright :
        (factorLadderData (σ := σ) (D := D) K).ReachesBoundary
            (deletedProjectiveSet σ K) x ↔
          ∃ t : (factorLadderRightARAt σ D x.1).index,
            (factorLadderRightARAt σ D x.1).label t ∉ K := by
      constructor
      · intro hreach
        by_contra hnone
        push Not at hnone
        have hθ :
            factorLadderTheta (σ := σ) (D := D) K
              (FactorLadder.basis x) = 0 := by
          apply not_ne_iff.mp
          intro hne
          obtain ⟨t, ht⟩ :=
            (factorLadderTheta_basis_ne_zero_iff σ D K x).1 hne
          exact ht (hnone t)
        have htarget :
            factorLadderTauTarget (σ := σ) (D := D) K x = none :=
          factorLadderTauTarget_eq_none_of_theta_eq_zero
            σ D K x hx hθ
        have hτ :
            factorLadderTau (σ := σ) (D := D) K
              (FactorLadder.basis x) = 0 :=
          factorLadderTau_basis_eq_zero_of_target_eq_none
            σ D K x htarget
        obtain ⟨n, p, hp, hpos⟩ := hreach
        by_cases hn : n = 0
        · subst n
          have hpx : p = x := by
            by_contra hne
            simp [FactorLadder.basis, hne] at hpos
          subst p
          exact hx hp
        · have hn1 : 1 ≤ n := by omega
          have hzero :=
            FactorLadder.Data.ladder_eq_zero_of_theta_basis_eq_zero_of_tau_basis_eq_zero
              (factorLadderData (σ := σ) (D := D) K) x hθ hτ n hn1
          rw [hzero] at hpos
          simp at hpos
      · rintro ⟨t, ht⟩
        let y : DeletedLabel K :=
          ⟨(factorLadderRightARAt σ D x.1).label t, ht⟩
        have hyIrr : HasIrreducibleMorphism (σ.obj y.1) (σ.obj x.1) :=
          ((factorLadderRightARAt σ D x.1).summandIrreducibleCorrespondence
            y.1).1 ⟨t, rfl⟩
        have hyP : Projective (σ.obj y.1) :=
          (hPI ⟨x.1, hx⟩ y.1 hyIrr).1
        letI : Fintype (factorLadderRightARAt σ D x.1).index :=
          FintypeCat.fintype
        refine ⟨1, y, hyP, ?_⟩
        rw [FactorLadder.Data.ladder_one,
          factorLadderData_theta,
          factorLadderTheta_basis_apply]
        change 0 < (((Finset.univ.filter fun s :
          (factorLadderRightARAt σ D x.1).index ↦
            (factorLadderRightARAt σ D x.1).label s = y.1).card : ℕ) : ℤ)
        have htmem : t ∈ (Finset.univ.filter fun s :
            (factorLadderRightARAt σ D x.1).index ↦
              (factorLadderRightARAt σ D x.1).label s = y.1) := by
          exact Finset.mem_filter.2 ⟨Finset.mem_univ t, rfl⟩
        exact_mod_cast Finset.card_pos.mpr ⟨t, htmem⟩
    rw [hright]
    simp [hx]

section FiniteDimensional

variable {k : Type u} [Field k] [Algebra k R]
  [FiniteDimensional k R]

include k in
/-- Two consecutive singleton nonprojective meshes cannot cancel in the
factor ladder: quotient-closure of the zero subcategory forces every full
ladder to reach a projective. -/
theorem finiteDimensional_no_two_mesh_cancellation
    (x y : σ.NonprojectiveLabel)
    (hθx :
      factorLadderTheta
          (σ := σ) (D := σ.finiteDimensionalARTranslationData k R) ∅
          (FactorLadder.basis (allDeletedLabel x.1)) =
        FactorLadder.basis (allDeletedLabel y.1))
    (hθy :
      factorLadderTheta
          (σ := σ) (D := σ.finiteDimensionalARTranslationData k R) ∅
          (FactorLadder.basis (allDeletedLabel y.1)) =
        FactorLadder.basis
          (allDeletedLabel
            ((σ.finiteDimensionalARTranslationData k R).arTranslation σ x).1)) :
    False := by
  classical
  let D₀ := σ.finiteDimensionalARTranslationData k R
  let xd := allDeletedLabel x.1
  let yd := allDeletedLabel y.1
  let zd := allDeletedLabel (D₀.arTranslation σ x).1
  let A := factorLadderData (σ := σ) (D := D₀) ∅
  have hθx' : A.theta (FactorLadder.basis xd) =
      FactorLadder.basis yd := by
    simpa [A, D₀, xd, yd] using hθx
  have hθy' : A.theta (FactorLadder.basis yd) =
      FactorLadder.basis zd := by
    simpa [A, D₀, yd, zd] using hθy
  have hθxne :
      factorLadderTheta (σ := σ) (D := D₀) ∅
          (FactorLadder.basis xd) ≠ 0 := by
    intro hzero
    have hcoord := congrFun (hzero.symm.trans hθx') yd
    simp at hcoord
  have htarget :
      factorLadderTauTarget (σ := σ) (D := D₀) ∅ xd = some zd := by
    let x₀ : σ.NonprojectiveLabel :=
      ⟨xd.1, by simpa [xd, allDeletedLabel] using x.2⟩
    have hx₀ : x₀ = x := by
      apply Subtype.ext
      rfl
    have hraw := factorLadderTauTarget_eq_some
      σ D₀ ∅ xd x₀.2 (by simp) hθxne
    rw [hraw]
    apply congrArg some
    apply Subtype.ext
    simp [D₀, zd, x₀, hx₀, allDeletedLabel]
  have hτx : A.tau (FactorLadder.basis xd) =
      FactorLadder.basis zd := by
    exact factorLadderTau_basis_eq_basis_of_target_eq_some
      σ D₀ ∅ xd zd htarget
  have h₂ : A.ladder xd 2 = 0 := by
    rw [show 2 = 0 + 2 by omega, FactorLadder.Data.ladder_add_two,
      FactorLadder.Data.ladder_one, FactorLadder.Data.ladder_zero,
      hθx', hθy', hτx, sub_self]
    funext p
    simp [FactorLadder.positivePart]
  have hτy_nonneg : ∀ p, 0 ≤ A.tau (FactorLadder.basis yd) p := by
    intro p
    change 0 ≤ factorLadderTau (σ := σ) (D := D₀) ∅
      (FactorLadder.basis yd) p
    rw [factorLadderTau_basis_apply]
    simp only [factorLadderTauEntry]
    split <;> omega
  have h₃ : A.ladder xd 3 = 0 := by
    rw [show 3 = 1 + 2 by omega, FactorLadder.Data.ladder_add_two,
      h₂, map_zero, FactorLadder.Data.ladder_one, hθx']
    funext p
    rw [FactorLadder.positivePart_apply]
    simp only [Pi.zero_apply, zero_sub]
    exact max_eq_right (neg_nonpos.mpr (hτy_nonneg p))
  have hlater : ∀ n, 2 ≤ n → A.ladder xd n = 0 :=
    A.ladder_eq_zero_of_consecutive xd 2 h₂ h₃
  have hclosed :
      (σ.generated (∅ : Set ι)).carrier.IsClosedUnderQuotients :=
    (qClosed_iff_generated_isClosedUnderQuotients σ ∅).1
      (qClosure_isClosed_empty σ)
  have hreach :=
    (σ.finiteDimensional_generated_isClosedUnderQuotients_iff_factorLadder_reaches_projective
      (k := k) (R := R) ∅).1 hclosed xd
  change A.ReachesBoundary (deletedProjectiveSet σ ∅) xd at hreach
  obtain ⟨n, p, hp, hpos⟩ := hreach
  by_cases hn₂ : 2 ≤ n
  · rw [hlater n hn₂] at hpos
    simp at hpos
  · have hn : n = 0 ∨ n = 1 := by omega
    rcases hn with rfl | rfl
    · have hpx : p = xd := by
        by_contra hne
        simp [A, FactorLadder.basis, hne] at hpos
      subst p
      exact x.2 hp
    · rw [FactorLadder.Data.ladder_one, hθx'] at hpos
      have hpy : p = yd := by
        by_contra hne
        simp [FactorLadder.basis, hne] at hpos
      subst p
      exact y.2 hp

include k in
/-- If every chosen almost-split middle is indecomposable, then every
almost-split middle summand is projective-injective. -/
theorem finiteDimensional_hasProjectiveInjectiveMiddle_of_indec
    (hIndec :
      (σ.finiteDimensionalARTranslationData k R).HasIndecomposableAlmostSplitMiddle σ) :
    HasProjectiveInjectiveMiddle σ := by
  classical
  let D₀ := σ.finiteDimensionalARTranslationData k R
  intro x y hyx
  let Aₓ := factorLadderRightARAt σ D₀ x.1
  have hAₓindec : OpConjecture.Foundation.IsIndecomposableModule R Aₓ.middle := by
    rw [show Aₓ = D₀.chosenRightAR σ x from
      D₀.factorLadderRightARAt_nonprojective σ x]
    exact hIndec x
  let Uₓ : Unique Aₓ.index :=
    (Aₓ.unique_index_of_middle_indecomposable σ hAₓindec).some
  letI : Unique Aₓ.index := Uₓ
  letI : Fintype Aₓ.index := FintypeCat.fintype
  obtain ⟨tₓ, htₓ⟩ := (Aₓ.summandIrreducibleCorrespondence y).2 hyx
  have hlabelₓ : Aₓ.label default = y := by
    rw [← htₓ]
    exact congrArg Aₓ.label (Subsingleton.elim default tₓ)
  have hθₓ :
      factorLadderTheta (σ := σ) (D := D₀) ∅
          (FactorLadder.basis (allDeletedLabel x.1)) =
        FactorLadder.basis (allDeletedLabel y) := by
    have hU : Nonempty (Unique Aₓ.index) := ⟨Uₓ⟩
    have h := D₀.factorLadderTheta_basis_eq_basis_of_unique
      σ ∅ (allDeletedLabel x.1) hU (by simp)
    exact h.trans (congrArg
      (FactorLadder.basis (D := DeletedLabel (∅ : Set ι))) (by
        apply Subtype.ext
        change Aₓ.label default = y
        exact hlabelₓ))
  constructor
  · by_contra hyP
    let yNP : σ.NonprojectiveLabel := ⟨y, hyP⟩
    let Aᵧ := factorLadderRightARAt σ D₀ y
    have hAᵧindec : OpConjecture.Foundation.IsIndecomposableModule R Aᵧ.middle := by
      rw [show Aᵧ = D₀.chosenRightAR σ yNP from
        D₀.factorLadderRightARAt_nonprojective σ yNP]
      exact hIndec yNP
    let Uᵧ : Unique Aᵧ.index :=
      (Aᵧ.unique_index_of_middle_indecomposable σ hAᵧindec).some
    letI : Unique Aᵧ.index := Uᵧ
    letI : Fintype Aᵧ.index := FintypeCat.fintype
    let z : ι := (D₀.arTranslation σ x).1
    have hzy : HasIrreducibleMorphism (σ.obj z) (σ.obj y) :=
      (D₀.arTranslation_incidence σ x y).1 hyx
    obtain ⟨tᵧ, htᵧ⟩ := (Aᵧ.summandIrreducibleCorrespondence z).2 hzy
    have hlabelᵧ : Aᵧ.label default = z := by
      rw [← htᵧ]
      exact congrArg Aᵧ.label (Subsingleton.elim default tᵧ)
    have hθᵧ :
        factorLadderTheta (σ := σ) (D := D₀) ∅
            (FactorLadder.basis (allDeletedLabel y)) =
          FactorLadder.basis (allDeletedLabel z) := by
      have hU : Nonempty (Unique Aᵧ.index) := ⟨Uᵧ⟩
      have h := D₀.factorLadderTheta_basis_eq_basis_of_unique
        σ ∅ (allDeletedLabel y) hU (by simp)
      exact h.trans (congrArg
        (FactorLadder.basis (D := DeletedLabel (∅ : Set ι))) (by
          apply Subtype.ext
          change Aᵧ.label default = z
          exact hlabelᵧ))
    exact finiteDimensional_no_two_mesh_cancellation
      (k := k) (R := R) σ x yNP hθₓ (by simpa [D₀, z] using hθᵧ)
  · by_contra hyI
    let yNI : σ.NoninjectiveLabel := ⟨y, hyI⟩
    let w : σ.NonprojectiveLabel := (D₀.arTranslationEquiv σ).symm yNI
    have hτw : (D₀.arTranslation σ w).1 = y := by
      have h := (D₀.arTranslationEquiv σ).apply_symm_apply yNI
      exact congrArg Subtype.val h
    let Aw := factorLadderRightARAt σ D₀ w.1
    have hAwIndec : OpConjecture.Foundation.IsIndecomposableModule R Aw.middle := by
      rw [show Aw = D₀.chosenRightAR σ w from
        D₀.factorLadderRightARAt_nonprojective σ w]
      exact hIndec w
    let Uw : Unique Aw.index :=
      (Aw.unique_index_of_middle_indecomposable σ hAwIndec).some
    letI : Unique Aw.index := Uw
    letI : Fintype Aw.index := FintypeCat.fintype
    have hxw : HasIrreducibleMorphism (σ.obj x.1) (σ.obj w.1) :=
      (D₀.arTranslation_incidence σ w x.1).2 (by
        simpa [hτw] using hyx)
    obtain ⟨tw, htw⟩ := (Aw.summandIrreducibleCorrespondence x.1).2 hxw
    have hlabelw : Aw.label default = x.1 := by
      rw [← htw]
      exact congrArg Aw.label (Subsingleton.elim default tw)
    have hθw :
        factorLadderTheta (σ := σ) (D := D₀) ∅
            (FactorLadder.basis (allDeletedLabel w.1)) =
          FactorLadder.basis (allDeletedLabel x.1) := by
      have hU : Nonempty (Unique Aw.index) := ⟨Uw⟩
      have h := D₀.factorLadderTheta_basis_eq_basis_of_unique
        σ ∅ (allDeletedLabel w.1) hU (by simp)
      exact h.trans (congrArg
        (FactorLadder.basis (D := DeletedLabel (∅ : Set ι))) (by
          apply Subtype.ext
          change Aw.label default = x.1
          exact hlabelw))
    exact finiteDimensional_no_two_mesh_cancellation
      (k := k) (R := R) σ w x hθw (by simpa [D₀, hτw] using hθₓ)

include k in
/-- The literal quotient-closure criterion collapses to the forward
first-mesh hitting clauses under the PI-middle hypothesis. -/
theorem generated_compl_isClosedUnderQuotients_iff_qGood
    (hPI : HasProjectiveInjectiveMiddle σ) (Deleted : Set ι) :
    (σ.generated Deletedᶜ).carrier.IsClosedUnderQuotients ↔
      (D.projectiveInjectiveMiddleData σ hPI).QGood Deleted := by
  let M := D.projectiveInjectiveMiddleData σ hPI
  rw [σ.finiteDimensional_generated_isClosedUnderQuotients_iff_factorLadder_reaches_projective
    (k := k) (R := R) Deletedᶜ]
  constructor
  · intro h x hxD
    let xd : DeletedLabel Deletedᶜ := ⟨x.1, by simpa using hxD⟩
    have hreach := h xd
    have hcase := (D.factorLadder_reaches_projective_iff σ hPI Deletedᶜ xd).1 hreach
    rcases hcase with hp | hmiddle
    · exact False.elim (x.2 hp)
    · obtain ⟨_hx, t, ht⟩ := hmiddle
      refine ⟨(factorLadderRightARAt σ D x.1).label t, ?_, ?_⟩
      simpa using ht
      exact ((factorLadderRightARAt σ D x.1).summandIrreducibleCorrespondence
        ((factorLadderRightARAt σ D x.1).label t)).1 ⟨t, rfl⟩
  · intro h xd
    apply (D.factorLadder_reaches_projective_iff σ hPI Deletedᶜ xd).2
    by_cases hp : Projective (σ.obj xd.1)
    · exact Or.inl hp
    · right
      refine ⟨hp, ?_⟩
      let x : σ.NonprojectiveLabel := ⟨xd.1, hp⟩
      have hxD : x.1 ∈ Deleted := by simpa using xd.2
      obtain ⟨y, hyD, hyIrr⟩ := h x hxD
      obtain ⟨t, ht⟩ :=
        ((factorLadderRightARAt σ D x.1).summandIrreducibleCorrespondence y).2
          hyIrr
      refine ⟨t, ?_⟩
      have hlabel :
          (factorLadderRightARAt σ D xd.1).label t = y := by
        simpa [x] using ht
      simpa [hlabel] using hyD

/-- Complementing the deleted set identifies the forward mesh clauses with
the actual quotient-closed supports. -/
def qGoodEquivQCloseds
    (hPI : HasProjectiveInjectiveMiddle σ) :
    {Deleted : Set ι //
      (D.projectiveInjectiveMiddleData σ hPI).QGood Deleted} ≃
      σ.qClosure.Closeds where
  toFun Deleted := ⟨Deleted.1ᶜ, by
    apply (qClosed_iff_generated_isClosedUnderQuotients σ Deleted.1ᶜ).2
    exact (D.generated_compl_isClosedUnderQuotients_iff_qGood
      (k := k) σ hPI Deleted.1).2 Deleted.2⟩
  invFun K := ⟨K.1ᶜ, by
    apply (D.generated_compl_isClosedUnderQuotients_iff_qGood
      (k := k) σ hPI K.1ᶜ).1
    simpa using
      (qClosed_iff_generated_isClosedUnderQuotients σ K.1).1 K.2⟩
  left_inv Deleted := by
    apply Subtype.ext
    simp
  right_inv K := by
    apply Subtype.ext
    simp

section Duality

variable {S : Type u} [Ring S] [Algebra k S]
  [FiniteDimensional k S] [IsNoetherianRing S]
  {κ : Type w} [Fintype κ]
  (τ : IndecomposableSkeleton.{u, w, u} S κ)

omit [Algebra k R] [FiniteDimensional k R] in
include k in
/-- Under an aligned biduality, the literal subobject-closure criterion is
the reverse first-mesh condition on the source skeleton. -/
theorem generated_compl_isClosedUnderSubobjects_iff_sGood
    (Dτ : τ.FiniteARTranslationData)
    (E : AlignedBiduality σ τ)
    (hPI : HasProjectiveInjectiveMiddle σ)
    (Deleted : Set ι) :
    (σ.generated Deletedᶜ).carrier.IsClosedUnderSubobjects ↔
      (D.projectiveInjectiveMiddleData σ hPI).SGood Deleted := by
  let e := E.forward.labelEquiv
  let hPIτ := D.hasProjectiveInjectiveMiddle_image σ τ E hPI
  have hclosure :
      (σ.generated Deletedᶜ).carrier.IsClosedUnderSubobjects ↔
        (τ.generated (e '' Deletedᶜ)).carrier.IsClosedUnderQuotients :=
    (sClosed_iff_generated_isClosedUnderSubobjects σ Deletedᶜ).symm.trans <|
      (E.sClosure_isClosed_iff_qClosure_image σ τ Deletedᶜ).trans <|
        qClosed_iff_generated_isClosedUnderQuotients τ (e '' Deletedᶜ)
  have himage : e '' Deletedᶜ = (e '' Deleted)ᶜ := by
    exact Equiv.image_compl e Deleted
  rw [himage] at hclosure
  exact hclosure.trans <|
    (Dτ.generated_compl_isClosedUnderQuotients_iff_qGood
      (k := k) τ hPIτ (e '' Deleted)).trans <|
      D.qGood_image_iff_sGood σ τ Dτ E hPI Deleted

/-- Complementing the deleted set identifies the reverse mesh clauses with
the actual submodule-closed supports. -/
def sGoodEquivSCloseds
    (Dτ : τ.FiniteARTranslationData)
    (E : AlignedBiduality σ τ)
    (hPI : HasProjectiveInjectiveMiddle σ) :
    {Deleted : Set ι //
      (D.projectiveInjectiveMiddleData σ hPI).SGood Deleted} ≃
      σ.sClosure.Closeds where
  toFun Deleted := ⟨Deleted.1ᶜ, by
    apply (sClosed_iff_generated_isClosedUnderSubobjects σ Deleted.1ᶜ).2
    exact (D.generated_compl_isClosedUnderSubobjects_iff_sGood
      (k := k) σ τ Dτ E hPI Deleted.1).2 Deleted.2⟩
  invFun K := ⟨K.1ᶜ, by
    apply (D.generated_compl_isClosedUnderSubobjects_iff_sGood
      (k := k) σ τ Dτ E hPI K.1ᶜ).1
    simpa using
      (sClosed_iff_generated_isClosedUnderSubobjects σ K.1).1 K.2⟩
  left_inv Deleted := by
    apply Subtype.ext
    simp
  right_inv K := by
    apply Subtype.ext
    simp

include k in
/-- Projective-injective AR middles force the paper's quotient and submodule
level-generating polynomials to agree. -/
theorem projectiveInjectiveMiddle_levelPolynomial_eq
    (D : σ.FiniteARTranslationData)
    (Dτ : τ.FiniteARTranslationData)
    (E : AlignedBiduality σ τ)
    (hPI : HasProjectiveInjectiveMiddle σ) :
    σ.qClosure.levelPolynomial = σ.sClosure.levelPolynomial := by
  let M := D.projectiveInjectiveMiddleData σ hPI
  let qParam := D.qGoodEquivQCloseds (k := k) σ hPI
  let sParam : {Deleted : Set ι // M.QGood Deleted} ≃
      σ.sClosure.Closeds :=
    M.qGoodEquivSGood.trans
      (D.sGoodEquivSCloseds (k := k) σ τ Dτ E hPI)
  letI : Fintype {Deleted : Set ι // M.QGood Deleted} :=
    Fintype.ofFinite _
  have hq := OpConjecture.SetClosure.levelPolynomial_eq_sum_stat
    σ.qClosure qParam
    (fun Deleted : {Deleted : Set ι // M.QGood Deleted} ↦
      Nat.card ι - Deleted.1.ncard) (by
        intro Deleted
        change Deleted.1ᶜ.ncard = Nat.card ι - Deleted.1.ncard
        exact Set.ncard_compl Deleted.1)
  have hs := OpConjecture.SetClosure.levelPolynomial_eq_sum_stat
    σ.sClosure sParam
    (fun Deleted : {Deleted : Set ι // M.QGood Deleted} ↦
      Nat.card ι - Deleted.1.ncard) (by
        intro Deleted
        change (M.vertexPerm '' Deleted.1)ᶜ.ncard =
          Nat.card ι - Deleted.1.ncard
        rw [Set.ncard_compl,
          Set.ncard_image_of_injective Deleted.1 M.vertexPerm.injective])
  exact hq.trans hs.symm

end Duality

end FiniteDimensional

end FiniteARTranslationData

end OpConjecture.IndecomposableSkeleton

namespace OpConjecture

universe u

variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
  [FiniteDimensional k A]

/-- Canonical right-module form of the projective-injective-middle
corollary: the quotient- and submodule-closed level polynomials agree. -/
theorem right_projectiveInjectiveMiddle_levelPolynomial_eq
    (hA : IsRightRepresentationFinite.{u, u, u} k A) :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional k A
    letI : Finite (CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) := hA
    letI : Fintype (CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) :=
      Fintype.ofFinite _
    let σ := rightIndecomposableSkeleton.{u, u, u} k A
    IndecomposableSkeleton.FiniteARTranslationData.HasProjectiveInjectiveMiddle σ →
      σ.qClosure.levelPolynomial = σ.sClosure.levelPolynomial := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional k A
  letI : Finite (CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) := hA
  letI : Fintype (CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) :=
    Fintype.ofFinite _
  let σ := rightIndecomposableSkeleton.{u, u, u} k A
  dsimp only
  intro hPI
  letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional k Aᵐᵒᵖ
  let hAop : IsRightRepresentationFinite.{u, u, u} k Aᵐᵒᵖ :=
    (rightRepresentationFinite_op_iff k A).1 hA
  letI : Finite
      (CanonicalIndecomposableIndex.{u, u} (Aᵐᵒᵖ)ᵐᵒᵖ) := hAop
  letI : Fintype
      (CanonicalIndecomposableIndex.{u, u} (Aᵐᵒᵖ)ᵐᵒᵖ) :=
    Fintype.ofFinite _
  let τ := rightIndecomposableSkeleton.{u, u, u} k Aᵐᵒᵖ
  let Dσ := σ.finiteDimensionalARTranslationData k Aᵐᵒᵖ
  let Dτ := τ.finiteDimensionalARTranslationData k (Aᵐᵒᵖ)ᵐᵒᵖ
  let E := rightOppositeAlignedBiduality k A
  exact Dσ.projectiveInjectiveMiddle_levelPolynomial_eq
    (k := k) σ τ Dτ E hPI

/-- Canonical "in particular" clause: if each chosen genuine almost-split
middle is indecomposable, the quotient- and submodule-closed level
polynomials agree.  The manuscript's universal hypothesis implies this
choice-independent sufficient condition. -/
theorem right_indecAlmostSplitMiddle_levelPolynomial_eq
    (hA : IsRightRepresentationFinite.{u, u, u} k A) :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional k A
    letI : Finite (CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) := hA
    letI : Fintype (CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) :=
      Fintype.ofFinite _
    let σ := rightIndecomposableSkeleton.{u, u, u} k A
    let D := σ.finiteDimensionalARTranslationData k Aᵐᵒᵖ
    D.HasIndecomposableAlmostSplitMiddle σ →
      σ.qClosure.levelPolynomial = σ.sClosure.levelPolynomial := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional k A
  letI : Finite (CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) := hA
  letI : Fintype (CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) :=
    Fintype.ofFinite _
  let σ := rightIndecomposableSkeleton.{u, u, u} k A
  let D := σ.finiteDimensionalARTranslationData k Aᵐᵒᵖ
  dsimp only
  intro hIndec
  have hPI :=
    IndecomposableSkeleton.FiniteARTranslationData.finiteDimensional_hasProjectiveInjectiveMiddle_of_indec
      (k := k) σ hIndec
  exact right_projectiveInjectiveMiddle_levelPolynomial_eq k A hA hPI

end OpConjecture
