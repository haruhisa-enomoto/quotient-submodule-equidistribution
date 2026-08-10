import OpConjecture.CategoryTheory.IyamaReversedRightPrefix
import OpConjecture.CategoryTheory.IyamaRightLadderRadicalResolution
import OpConjecture.CategoryTheory.IyamaStrongDomination

/-!
# Radical orthogonality in Iyama right ladders

This file formalizes the first part of Iyama, *Tau-categories I*, Theorem
7.1.  We use the elementwise form of semisimplicity of `Cok H^a`: postcomposing
any class represented by a map out of the source of `a` with a radical map
makes that class zero.  The reversed finite-ladder comparison transports this
property to the terminal arrow of the left ladder from `U_n`.  The left-ladder
radical-power presentation then gives `J^(n+1) H^{U_n} = 0`, and the right
ladder presentation implies that every map `U_n ⟶ Y_(n+1)` is radical.

The argument is entirely categorical and uses no concrete algebra or module
classification.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace OpConjecture.Iyama

open CategoricalIdeal CategoricalRadical

universe v u w

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Elementwise semisimplicity of the covariant representable cokernel
`Cok H^a`.  A class represented by `s : X ⟶ W` is annihilated by every
radical map precisely when `s ≫ j` factors through `a`. -/
def RepresentableCokernelSemisimple
    {X Y : C} (a : X ⟶ Y) : Prop :=
  ∀ {W V : C} (s : X ⟶ W) (j : W ⟶ V),
    IsRadicalMorphism j →
      ∃ t : Y ⟶ V, s ≫ j = a ≫ t

namespace RepresentableCokernelSemisimple

/-- Semisimplicity of a representable cokernel is invariant under an
isomorphism in the arrow category. -/
theorem of_arrowIso
    {A B : Arrow C}
    (ha : RepresentableCokernelSemisimple A.hom)
    (e : A ≅ B) :
    RepresentableCokernelSemisimple B.hom := by
  intro W V s j hj
  obtain ⟨t, ht⟩ := ha (e.hom.left ≫ s) j hj
  refine ⟨e.inv.right ≫ t, ?_⟩
  have eright : e.hom.right ≫ e.inv.right = 𝟙 A.right := by
    have h := congrArg Arrow.Hom.right e.hom_inv_id
    simpa only [Arrow.comp_right, Arrow.id_right] using h
  rw [← cancel_epi e.hom.left]
  simp only [← Category.assoc]
  rw [e.hom.w]
  simpa only [Category.assoc, eright, Category.comp_id] using ht

/-- A quotient of a semisimple representable cokernel along a square whose
source component is split monic is again semisimple. -/
theorem of_splitMono_square
    {A B : Arrow C}
    (ha : RepresentableCokernelSemisimple A.hom)
    (d : B ⟶ A) (hdleft : IsSplitMono d.left) :
    RepresentableCokernelSemisimple B.hom := by
  intro W V s j hj
  letI : IsSplitMono d.left := hdleft
  obtain ⟨t, ht⟩ := ha (retraction d.left ≫ s) j hj
  refine ⟨d.right ≫ t, ?_⟩
  calc
    s ≫ j = d.left ≫ (retraction d.left ≫ s) ≫ j := by simp
    _ = d.left ≫ ((retraction d.left ≫ s) ≫ j) := by
      simp only [Category.assoc]
    _ = d.left ≫ (A.hom ≫ t) := by rw [ht]
    _ = (d.left ≫ A.hom) ≫ t := (Category.assoc _ _ _).symm
    _ = (B.hom ≫ d.right) ≫ t := by rw [d.w]
    _ = B.hom ≫ (d.right ≫ t) := Category.assoc _ _ _

/-- If the source of an arrow is zero, its covariant representable cokernel
is semisimple. -/
theorem of_isZero_source
    {X Y : C} (hX : IsZero X) (a : X ⟶ Y) :
    RepresentableCokernelSemisimple a := by
  intro W V s j _hj
  refine ⟨0, ?_⟩
  rw [hX.eq_of_src s 0, zero_comp, comp_zero]

end RepresentableCokernelSemisimple

namespace LeftLadder

variable [HasBinaryBiproducts C]

set_option linter.unusedSectionVars false in
/-- The first `n` horizontal maps of a left ladder followed by its `n`th
essential arrow equal the initial essential arrow followed by the first `n`
target maps. -/
theorem forwardComposite_comp_essential
    (Y Z : ℕ → C)
    (b : ∀ n : ℕ, Y n ⟶ Z n)
    (f : ∀ n : ℕ, Y n ⟶ Y (n + 1))
    (g : ∀ n : ℕ, Z n ⟶ Z (n + 1))
    (comm : ∀ n : ℕ, f n ≫ b (n + 1) = b n ≫ g n) :
    ∀ n : ℕ,
      forwardComposite Y f n ≫ b n =
        b 0 ≫ forwardComposite Z g n
  | 0 => by simp
  | n + 1 => by
      calc
        forwardComposite Y f (n + 1) ≫ b (n + 1) =
            forwardComposite Y f n ≫ (f n ≫ b (n + 1)) := by
          simp only [forwardComposite_succ, Category.assoc]
        _ = forwardComposite Y f n ≫ (b n ≫ g n) := by
          rw [comm n]
        _ = (forwardComposite Y f n ≫ b n) ≫ g n :=
          (Category.assoc _ _ _).symm
        _ = (b 0 ≫ forwardComposite Z g n) ≫ g n := by
          rw [forwardComposite_comp_essential Y Z b f g comm n]
        _ = b 0 ≫ forwardComposite Z g (n + 1) := by
          simp only [forwardComposite_succ, Category.assoc]

/-- Semisimplicity at the terminal arrow of a zero-initial left ladder
annihilates the next radical power out of its initial source.  This is the
elementwise content of `Cok H^{d_n} = J^n H^{U_0}` used in Iyama 7.1. -/
theorem eq_zero_of_mem_pow_succ_of_terminalSemisimple
    (R : NilpotentRadicalData C)
    (n : ℕ)
    (S : ℕ → ShortComplex C)
    (Y Z U : ℕ → C)
    (b : ∀ k : ℕ, Y k ⟶ Z k)
    (f : ∀ k : ℕ, Y k ⟶ Y (k + 1))
    (g : ∀ k : ℕ, Z k ⟶ Z (k + 1))
    (h : ∀ k : ℕ, Z k ⟶ U (k + 1))
    (comm : ∀ k : ℕ, f k ≫ b (k + 1) = b k ≫ g k)
    (hzero : ∀ k : ℕ, b k ≫ h k = 0)
    (hS : ∀ k : ℕ, LeftTauSequence (S k))
    (e : ∀ k : ℕ, Nonempty
      (S k ≅ stepComplex (b k) (b (k + 1)) (f k) (g k) (h k)
        (comm k) (hzero k)))
    (hbzero : b 0 = 0)
    (hsemisimple : RepresentableCokernelSemisimple (b n))
    {W : C} (r : Y 0 ⟶ W)
    (hr : r ∈ (R.ideal.pow (n + 1)).hom (Y 0) W) :
    r = 0 := by
  rw [R.ideal.pow_succ] at hr
  change r ∈ AddSubgroup.closure
    (HomIdeal.compositeGenerators (R.ideal.pow n) R.ideal (Y 0) W) at hr
  induction hr using AddSubgroup.closure_induction with
  | mem r hr =>
      obtain ⟨V, q, j, hq, hj, rfl⟩ := hr
      obtain ⟨t, ht⟩ :=
        exists_factor_through_forwardComposite R n S Y Z U b f g h
          comm hzero hS e (𝟙 (Y 0)) (by simp [hbzero]) hq
      have ht' : q = forwardComposite Y f n ≫ t := by
        simpa only [Category.id_comp] using ht
      have hjrad : IsRadicalMorphism j := (R.mem_ideal_iff j).1 hj
      obtain ⟨k, hk⟩ := hsemisimple t j hjrad
      calc
        q ≫ j = (forwardComposite Y f n ≫ t) ≫ j := by rw [ht']
        _ = forwardComposite Y f n ≫ (t ≫ j) := Category.assoc _ _ _
        _ = forwardComposite Y f n ≫ (b n ≫ k) := by rw [hk]
        _ = (forwardComposite Y f n ≫ b n) ≫ k :=
          (Category.assoc _ _ _).symm
        _ = (b 0 ≫ forwardComposite Z g n) ≫ k := by
          rw [forwardComposite_comp_essential Y Z b f g comm n]
        _ = 0 := by simp [hbzero]
  | zero => rfl
  | add r s _ _ hr hs => simp only [hr, hs, add_zero]
  | neg r _ hr => simp only [hr, neg_zero]

/-- Finite-prefix interface for the preceding radical-power vanishing
theorem. -/
theorem InfiniteSpecialLeftLadderFromZero.eq_zero_of_mem_pow_succ
    [HasFiniteBiproducts C] [IsIdempotentComplete C]
    {Ind : Type w} [Fintype Ind]
    {T : FiniteTauCategoryData C Ind} {U₀ : C}
    (L : InfiniteSpecialLeftLadderFromZero T U₀)
    (n : ℕ)
    (hsemisimple : RepresentableCokernelSemisimple (L.b n))
    {W : C} (r : U₀ ⟶ W)
    (hr : r ∈ (T.radical.ideal.pow (n + 1)).hom U₀ W) :
    r = 0 := by
  let r' : L.Y 0 ⟶ W := L.initialSourceIso.inv ≫ r
  have hr' : r' ∈ (T.radical.ideal.pow (n + 1)).hom (L.Y 0) W :=
    (T.radical.ideal.pow (n + 1)).precomp L.initialSourceIso.inv hr
  have hrzero : r' = 0 :=
    eq_zero_of_mem_pow_succ_of_terminalSemisimple T.radical n
      (fun k ↦ T.leftMesh (L.Y k)) L.Y L.Z L.U L.b L.f L.g L.h
      L.comm L.hzero (fun k ↦ T.leftTau (L.Y k)) L.meshIso
      L.b_zero hsemisimple r' hr'
  calc
    r = L.initialSourceIso.hom ≫ r' := by simp [r']
    _ = 0 := by rw [hrzero, comp_zero]

end LeftLadder

namespace RightLadder

variable [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind]

/-- Radical-power vanishing out of the `n`th discarded term forces every
map from that term to the next right-ladder target to be radical. -/
theorem InfiniteSpecialRightLadder.radicalOrthogonal_of_pow_succ_vanishing
    {T : FiniteRightTauCategoryData C Ind}
    {X₀ Y₀ : C} {a₀ : X₀ ⟶ Y₀}
    (L : InfiniteSpecialRightLadder T a₀) (n : ℕ)
    (hvanish : ∀ {W : C} (r : L.U n ⟶ W),
      r ∈ (T.radical.ideal.pow (n + 1)).hom (L.U n) W → r = 0) :
    ∀ q : L.U n ⟶ L.Y (n + 1),
      q ∈ T.radical.ideal.hom (L.U n) (L.Y (n + 1)) := by
  intro q
  apply (T.radical.mem_ideal_iff q).2
  by_contra hq
  have hf := previousMaps_mem_radical T.radical
    (fun k ↦ T.rightMesh (L.Y k)) L.Z L.Y L.U L.b L.f L.g L.h
    L.comm L.hzero (fun k ↦ T.rightTau (L.Y k)) L.meshIso
  have hc : backwardComposite L.Y L.f (n + 1) ∈
      (T.radical.ideal.pow (n + 1)).hom (L.Y (n + 1)) (L.Y 0) :=
    backwardComposite_mem_pow T.radical.ideal L.Y L.f hf (n + 1)
  let r : L.U n ⟶ L.Y 0 := q ≫ backwardComposite L.Y L.f (n + 1)
  have hr : r ∈
      (T.radical.ideal.pow (n + 1)).hom (L.U n) (L.Y 0) :=
    (T.radical.ideal.pow (n + 1)).precomp q hc
  have hrzero : r = 0 := hvanish r hr
  have hfactorInitial : ∃ t : L.U n ⟶ L.Z 0,
      q ≫ backwardComposite L.Y L.f (n + 1) = t ≫ L.b 0 := by
    exact ⟨0, by simpa only [r, zero_comp] using hrzero⟩
  obtain ⟨s, hs⟩ :=
    (factorsThrough_initial_iff_factorsThrough_nth T.radical
      (fun k ↦ T.rightMesh (L.Y k)) L.Z L.Y L.U L.b L.f L.g L.h
      L.comm L.hzero (fun k ↦ T.rightTau (L.Y k)) L.meshIso
      (n + 1) q).1 hfactorInitial
  have hb : IsRadicalMorphism (L.b (n + 1)) := (L.b_special (n + 1)).1
  exact hq (by
    rw [← hs]
    exact isRadicalMorphism_precomp s hb)

/-- Iyama 7.1, radical-orthogonality part: if `Cok H^{a₀}` is semisimple,
then every map from the discarded term `U_n` to the next target `Y_(n+1)`
of a right ladder lies in the categorical radical. -/
theorem InfiniteSpecialRightLadder.discarded_radicalOrthogonal
    {T : FiniteTauCategoryData C Ind}
    {X₀ Y₀ : C} {a₀ : X₀ ⟶ Y₀}
    (R : InfiniteSpecialRightLadder
      (T : FiniteRightTauCategoryData C Ind) a₀)
    (hsemisimple : RepresentableCokernelSemisimple a₀) (n : ℕ) :
    ∀ q : R.U n ⟶ R.Y (n + 1),
      q ∈ T.radical.ideal.hom (R.U n) (R.Y (n + 1)) := by
  let RR :=
    TauSequenceComparison.ReversedRightPrefix.ofInfiniteSpecialRightLadder
      (T := T) R n
  let Linf := LeftLadder.chosenInfiniteSpecialLeftLadderFromZero T (RR.U 0)
  let L := Linf.prefix n
  let eTerminal :
      Arrow.mk (RR.paddedArrow (Fin.last n)) ≅ Arrow.mk a₀ :=
    TauSequenceComparison.ReversedRightPrefix.ofInfiniteSpecialRightLadder_paddedArrowIso_last R n
      ≪≫ (Classical.choice R.initialIso).symm
  have hsemisimpleTerminalPadding :
      RepresentableCokernelSemisimple (RR.paddedArrow (Fin.last n)) :=
    hsemisimple.of_arrowIso eTerminal.symm
  obtain ⟨d, hdleft, hdright⟩ :=
    TauSequenceComparison.diagonalComparisonAt_all RR L (Fin.last n)
  have hsemisimpleTerminal :
      RepresentableCokernelSemisimple (L.b (Fin.last n)) :=
    hsemisimpleTerminalPadding.of_splitMono_square d hdleft
  have hsemisimpleLinf :
      RepresentableCokernelSemisimple (Linf.b n) := by
    intro W V s j hj
    have h := hsemisimpleTerminal s j hj
    simpa only [L, LeftLadder.InfiniteSpecialLeftLadderFromZero.prefix,
      Fin.val_last] using h
  apply R.radicalOrthogonal_of_pow_succ_vanishing n
  intro W r hr
  have eU : RR.U 0 = R.U n := by
    simp [RR,
      TauSequenceComparison.ReversedRightPrefix.ofInfiniteSpecialRightLadder]
  let r' : RR.U 0 ⟶ W := eqToHom eU ≫ r
  have hr' : r' ∈
      (T.radical.ideal.pow (n + 1)).hom (RR.U 0) W :=
    (T.radical.ideal.pow (n + 1)).precomp (eqToHom eU) hr
  have hzero := Linf.eq_zero_of_mem_pow_succ n hsemisimpleLinf r' hr'
  rw [← cancel_epi (eqToHom eU)]
  simpa only [r', comp_zero] using hzero

/-- The zero-initial specialization used by factor ladders. -/
theorem FiniteTauCategoryData.zeroInitialRightLadder_discarded_radicalOrthogonal
    (T : FiniteTauCategoryData C Ind) (X : C) (n : ℕ) :
    let L := zeroInitialRightLadder
      (T : FiniteRightTauCategoryData C Ind) X
    ∀ q : L.U n ⟶ L.Y (n + 1),
      q ∈ T.radical.ideal.hom (L.U n) (L.Y (n + 1)) := by
  let L := zeroInitialRightLadder
    (T : FiniteRightTauCategoryData C Ind) X
  apply L.discarded_radicalOrthogonal
  exact RepresentableCokernelSemisimple.of_isZero_source
    (isZero_zero C) (0 : (0 : C) ⟶ X)

/-- A two-sided extension of fixed right tau-category data supplies the
zero-initial radical orthogonality for those exact chosen right meshes. -/
theorem FiniteTauCategoryExtension.zeroInitialRightLadder_discarded_radicalOrthogonal
    (Tr : FiniteRightTauCategoryData C Ind)
    (E : FiniteTauCategoryExtension Tr) (X : C) (n : ℕ) :
    let L := zeroInitialRightLadder Tr X
    ∀ q : L.U n ⟶ L.Y (n + 1),
      q ∈ Tr.radical.ideal.hom (L.U n) (L.Y (n + 1)) := by
  obtain ⟨T, rfl⟩ := E
  exact
    FiniteTauCategoryData.zeroInitialRightLadder_discarded_radicalOrthogonal
      T X n

end RightLadder

end OpConjecture.Iyama
