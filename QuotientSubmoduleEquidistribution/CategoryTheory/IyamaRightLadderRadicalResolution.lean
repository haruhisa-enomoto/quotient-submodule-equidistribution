import QuotientSubmoduleEquidistribution.CategoryTheory.IyamaLeftSuccessorSpecialness
import QuotientSubmoduleEquidistribution.CategoryTheory.IyamaRightLadderIteration
import QuotientSubmoduleEquidistribution.CategoryTheory.IyamaRightLadderPropagation
import QuotientSubmoduleEquidistribution.CategoryTheory.RadicalLayerFiltration

/-!
# Radical-power presentations from Iyama right ladders

This file proves the objectwise content of Iyama's minimal projective
resolution of the radical powers of a representable functor.  For a right
ladder, composition with the first `n` horizontal maps presents the `n`th
radical power modulo the image of the initial essential arrow.  Its kernel
is exactly the image of the `n`th essential arrow.

When the initial essential arrow is zero, the semisimple top of this
presentation identifies the `n`th radical layer with the non-radical maps
to the `n`th ladder object.  On a chosen indecomposable in a finite
Krull--Schmidt category, this is equivalent to being a retract of that
ladder object.  These are precisely the proof-essential consequences of
the projective-cover statement in Iyama, *Tau-categories I*, Theorem 7.2.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace QuotientSubmoduleEquidistribution.Iyama.RightLadder

open CategoricalIdeal CategoricalRadical

universe v u w

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Transport a tau-approximation across an isomorphism of short
complexes. -/
theorem tauApproximationOfIso {S T : ShortComplex C}
    (hS : TauApproximation S) (e : S ≅ T) : TauApproximation T where
  f_radical := hS.f_radical_of_iso e
  g_radical := hS.g_radical_of_iso e
  factors_from_left := by
    intro W a ha
    have haS : IsRadicalMorphism (e.hom.τ₁ ≫ a) :=
      isRadicalMorphism_precomp e.hom.τ₁ ha
    obtain ⟨b, hb⟩ := hS.factors_from_left (e.hom.τ₁ ≫ a) haS
    refine ⟨e.inv.τ₂ ≫ b, ?_⟩
    calc
      T.f ≫ e.inv.τ₂ ≫ b = e.inv.τ₁ ≫ S.f ≫ b := by
        rw [← e.inv.comm₁₂_assoc]
      _ = e.inv.τ₁ ≫ (e.hom.τ₁ ≫ a) := by rw [hb]
      _ = a := by
        have he₁ := congrArg ShortComplex.Hom.τ₁ e.inv_hom_id
        change e.inv.τ₁ ≫ e.hom.τ₁ = 𝟙 T.X₁ at he₁
        rw [← Category.assoc, he₁, Category.id_comp]
  factors_into_right := by
    intro W a ha
    have haS : IsRadicalMorphism (a ≫ e.inv.τ₃) :=
      isRadicalMorphism_postcomp e.inv.τ₃ ha
    obtain ⟨b, hb⟩ := hS.factors_into_right (a ≫ e.inv.τ₃) haS
    refine ⟨b ≫ e.hom.τ₂, ?_⟩
    calc
      (b ≫ e.hom.τ₂) ≫ T.g = b ≫ S.g ≫ e.hom.τ₃ := by
        rw [Category.assoc, e.hom.comm₂₃, ← Category.assoc]
      _ = (a ≫ e.inv.τ₃) ≫ e.hom.τ₃ := by
        rw [← Category.assoc, hb]
      _ = a := by
        have he₃ := congrArg ShortComplex.Hom.τ₃ e.inv_hom_id
        change e.inv.τ₃ ≫ e.hom.τ₃ = 𝟙 T.X₃ at he₃
        rw [Category.assoc, he₃, Category.comp_id]

section Step

variable [HasBinaryBiproducts C]

/-- The horizontal map between the two right-ladder targets is radical.
It is the first component of the second map of the corresponding right
tau-sequence. -/
theorem previousMap_mem_radical_of_rightTauSequence_iso_stepComplex
    (R : NilpotentRadicalData C)
    {ZPrev YPrev ZNext YNext U : C}
    {bPrev : ZPrev ⟶ YPrev} {bNext : ZNext ⟶ YNext}
    {f : YNext ⟶ YPrev} {g : ZNext ⟶ ZPrev}
    {h : U ⟶ ZPrev}
    {comm : bNext ≫ f = g ≫ bPrev}
    {hzero : h ≫ bPrev = 0}
    {S : ShortComplex C}
    (hS : RightTauSequence S)
    (e : S ≅ stepComplex bPrev bNext f g h comm hzero) :
    f ∈ R.ideal.hom YNext YPrev := by
  let hT : TauApproximation
      (stepComplex bPrev bNext f g h comm hzero) :=
    tauApproximationOfIso hS.toTauApproximation e
  have hcomponent : IsRadicalMorphism
      ((biprod.inl : YNext ⟶ YNext ⊞ ZPrev) ≫
        (stepComplex bPrev bNext f g h comm hzero).g) :=
    isRadicalMorphism_precomp biprod.inl hT.g_radical
  apply (R.mem_ideal_iff f).2
  convert hcomponent using 1 <;> simp [stepComplex]

/-- A radical-power arrow into the previous target of a right-ladder step
lifts to the two displayed summands of the middle term, with both
coefficients one radical degree lower. -/
theorem exists_step_factor_of_mem_pow_succ
    (R : NilpotentRadicalData C)
    {ZPrev YPrev ZNext YNext U W : C}
    {bPrev : ZPrev ⟶ YPrev} {bNext : ZNext ⟶ YNext}
    {f : YNext ⟶ YPrev} {g : ZNext ⟶ ZPrev}
    {h : U ⟶ ZPrev}
    {comm : bNext ≫ f = g ≫ bPrev}
    {hzero : h ≫ bPrev = 0}
    {S : ShortComplex C}
    (hS : RightTauSequence S)
    (e : S ≅ stepComplex bPrev bNext f g h comm hzero)
    (n : ℕ) {r : W ⟶ YPrev}
    (hr : r ∈ (R.ideal.pow (n + 1)).hom W YPrev) :
    ∃ (qNext : W ⟶ YNext),
      qNext ∈ (R.ideal.pow n).hom W YNext ∧
        ∃ (qPrev : W ⟶ ZPrev),
          qPrev ∈ (R.ideal.pow n).hom W ZPrev ∧
            r = qNext ≫ f + qPrev ≫ bPrev := by
  let hT : TauApproximation
      (stepComplex bPrev bNext f g h comm hzero) :=
    tauApproximationOfIso hS.toTauApproximation e
  obtain ⟨qT, hqT, hfactor⟩ :=
    LeftLadder.exists_factor_through_tau_g_of_mem_pow_succ
      R hT n hr
  let qNext : W ⟶ YNext := qT ≫ biprod.fst
  let qPrev : W ⟶ ZPrev := qT ≫ biprod.snd
  have hqNext : qNext ∈ (R.ideal.pow n).hom W YNext :=
    (R.ideal.pow n).postcomp biprod.fst hqT
  have hqPrev : qPrev ∈ (R.ideal.pow n).hom W ZPrev :=
    (R.ideal.pow n).postcomp biprod.snd hqT
  have hqT_decomp : qT = biprod.lift qNext qPrev := by
    apply biprod.hom_ext <;> simp [qNext, qPrev] <;> rfl
  refine ⟨qNext, hqNext, qPrev, hqPrev, ?_⟩
  rw [hqT_decomp] at hfactor
  simpa [stepComplex] using hfactor.symm

end Step

section Family

variable [HasBinaryBiproducts C]

variable
    (R : NilpotentRadicalData C)
    (S : ℕ → ShortComplex C)
    (Z Y U : ℕ → C)
    (b : ∀ n : ℕ, Z n ⟶ Y n)
    (f : ∀ n : ℕ, Y (n + 1) ⟶ Y n)
    (g : ∀ n : ℕ, Z (n + 1) ⟶ Z n)
    (h : ∀ n : ℕ, U (n + 1) ⟶ Z n)
    (comm : ∀ n : ℕ, b (n + 1) ≫ f n = g n ≫ b n)
    (hzero : ∀ n : ℕ, h n ≫ b n = 0)
    (hS : ∀ n : ℕ, RightTauSequence (S n))
    (e : ∀ n : ℕ, Nonempty
      (S n ≅ stepComplex (b n) (b (n + 1)) (f n) (g n) (h n)
        (comm n) (hzero n)))

include R S Z Y U b f g h comm hzero hS e

set_option linter.unusedSectionVars false in
/-- The `n`th essential arrow followed by the first `n` target maps is the
first `n` source maps followed by the initial essential arrow. -/
theorem essential_comp_backwardComposite : ∀ n : ℕ,
    b n ≫ backwardComposite Y f n =
      backwardComposite Z g n ≫ b 0
  | 0 => by simp
  | n + 1 => by
      calc
        b (n + 1) ≫ backwardComposite Y f (n + 1) =
            (b (n + 1) ≫ f n) ≫
              backwardComposite Y f n := by simp [Category.assoc]
        _ = (g n ≫ b n) ≫ backwardComposite Y f n := by
          rw [comm n]
        _ = g n ≫ (b n ≫ backwardComposite Y f n) :=
          Category.assoc _ _ _
        _ = g n ≫ (backwardComposite Z g n ≫ b 0) := by
          rw [essential_comp_backwardComposite n]
        _ = backwardComposite Z g (n + 1) ≫ b 0 := by
          simp [Category.assoc]

/-- Every target-to-target map in the right ladder belongs to the
categorical radical. -/
theorem previousMaps_mem_radical : ∀ n : ℕ,
    f n ∈ R.ideal.hom (Y (n + 1)) (Y n) := by
  intro n
  obtain ⟨en⟩ := e n
  exact previousMap_mem_radical_of_rightTauSequence_iso_stepComplex
    R (hS n) en

/-- Every essential arrow in a zero-initial right ladder belongs to the
categorical radical. -/
theorem essentialMaps_mem_radical
    (hbzero : b 0 = 0) : ∀ n : ℕ,
    b n ∈ R.ideal.hom (Z n) (Y n) := by
  intro n
  cases n with
  | zero => simp [hbzero]
  | succ n =>
      exact nextMap_mem_radical_of_rightTauSequence_nonempty_iso_stepComplex
        R (hS n) (e n)

/-- Kernel part of Iyama's radical-power presentation: a map from `W` to
the `n`th ladder target becomes zero modulo the initial essential arrow if
and only if it factors through the `n`th essential arrow. -/
theorem factorsThrough_initial_iff_factorsThrough_nth
    (n : ℕ) {W : C} (q : W ⟶ Y n) :
    (∃ t : W ⟶ Z 0,
        q ≫ backwardComposite Y f n = t ≫ b 0) ↔
      ∃ s : W ⟶ Z n, s ≫ b n = q := by
  induction n with
  | zero =>
      constructor
      · rintro ⟨t, ht⟩
        exact ⟨t, by simpa using ht.symm⟩
      · rintro ⟨s, rfl⟩
        exact ⟨s, by simp⟩
  | succ n ih =>
      constructor
      · rintro ⟨t₀, ht₀⟩
        have hprev : ∃ t : W ⟶ Z 0,
            (q ≫ f n) ≫ backwardComposite Y f n = t ≫ b 0 := by
          exact ⟨t₀, by simpa [Category.assoc] using ht₀⟩
        obtain ⟨t, ht⟩ := (ih (q ≫ f n)).1 hprev
        let k : W ⟶ Y (n + 1) ⊞ Z n := biprod.lift q (-t)
        have hk : k ≫
            (stepComplex (b n) (b (n + 1)) (f n) (g n) (h n)
              (comm n) (hzero n)).g = 0 := by
          change biprod.lift q (-t) ≫ biprod.desc (f n) (b n) = 0
          rw [biprod.lift_desc, Preadditive.neg_comp, ht]
          simp
        have hweak : ShortComplex.IsWeakKernel
            (stepComplex (b n) (b (n + 1)) (f n) (g n) (h n)
              (comm n) (hzero n)) :=
          isWeakKernel_stepComplex_of_rightTauSequence_nonempty_iso
            (hS n) (e n)
        obtain ⟨l, hl⟩ :=
          (ShortComplex.isWeakKernel_iff _).mp hweak k hk
        let s : W ⟶ Z (n + 1) := l ≫ biprod.fst
        refine ⟨s, ?_⟩
        have ldecomp :
            l = biprod.lift (l ≫ biprod.fst) (l ≫ biprod.snd) := by
          apply biprod.hom_ext <;> simp <;> rfl
        rw [ldecomp] at hl
        have hcomponent := congrArg (fun z ↦ z ≫ biprod.fst) hl
        simpa [s, k, stepComplex, Category.assoc] using hcomponent
      · rintro ⟨s, rfl⟩
        refine ⟨s ≫ backwardComposite Z g (n + 1), ?_⟩
        calc
          (s ≫ b (n + 1)) ≫ backwardComposite Y f (n + 1) =
              s ≫ (b (n + 1) ≫ backwardComposite Y f (n + 1)) :=
            Category.assoc _ _ _
          _ = s ≫ (backwardComposite Z g (n + 1) ≫ b 0) := by
            rw [essential_comp_backwardComposite R S Z Y U b f g h comm
              hzero hS e (n + 1)]
          _ = (s ≫ backwardComposite Z g (n + 1)) ≫ b 0 :=
            (Category.assoc _ _ _).symm

/-- Surjectivity part of Iyama's radical-power presentation, with a
filtration-sensitive coefficient.  An arrow in `J^(n+m)` is, modulo the
initial essential arrow, represented from the `n`th ladder target by a
coefficient in `J^m`. -/
theorem exists_radical_power_representative
    (n m : ℕ) {W : C} {r : W ⟶ Y 0}
    (hr : r ∈ (R.ideal.pow (n + m)).hom W (Y 0)) :
    ∃ (q : W ⟶ Y n),
      q ∈ (R.ideal.pow m).hom W (Y n) ∧
        ∃ (t : W ⟶ Z 0),
          r = q ≫ backwardComposite Y f n + t ≫ b 0 := by
  induction n generalizing m with
  | zero =>
      refine ⟨r, ?_, 0, ?_⟩
      · simpa using hr
      · simp
  | succ n ih =>
      have hr' : r ∈ (R.ideal.pow (n + (m + 1))).hom W (Y 0) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hr
      obtain ⟨q, hq, t₀, hrq⟩ := ih (m + 1) hr'
      obtain ⟨en⟩ := e n
      obtain ⟨qNext, hqNext, qPrev, _hqPrev, hqfactor⟩ :=
        exists_step_factor_of_mem_pow_succ R (hS n) en m hq
      refine ⟨qNext, hqNext,
        qPrev ≫ backwardComposite Z g n + t₀, ?_⟩
      calc
        r = q ≫ backwardComposite Y f n + t₀ ≫ b 0 := hrq
        _ = (qNext ≫ f n + qPrev ≫ b n) ≫
              backwardComposite Y f n + t₀ ≫ b 0 := by rw [hqfactor]
        _ = qNext ≫ backwardComposite Y f (n + 1) +
              qPrev ≫ (backwardComposite Z g n ≫ b 0) +
                t₀ ≫ b 0 := by
              simp only [Preadditive.add_comp, Category.assoc,
                backwardComposite_succ]
              rw [essential_comp_backwardComposite R S Z Y U b f g h
                comm hzero hS e n]
        _ = qNext ≫ backwardComposite Y f (n + 1) +
              (qPrev ≫ backwardComposite Z g n + t₀) ≫ b 0 := by
              simp only [Preadditive.add_comp, Category.assoc]
              abel

/-- For a zero-initial right ladder, the `n`th radical layer from `W` to
the initial target is nonzero exactly when there is a non-radical map from
`W` to the `n`th ladder target. -/
theorem layerNonzero_iff_exists_not_radical
    (hbzero : b 0 = 0) (n : ℕ) (W : C) :
    R.LayerNonzero n W (Y 0) ↔
      ∃ q : W ⟶ Y n, ¬ IsRadicalMorphism q := by
  have hf := previousMaps_mem_radical R S Z Y U b f g h comm hzero hS e
  have hc : backwardComposite Y f n ∈
      (R.ideal.pow n).hom (Y n) (Y 0) :=
    backwardComposite_mem_pow R.ideal Y f hf n
  have hb := essentialMaps_mem_radical R S Z Y U b f g h comm hzero hS e
    hbzero
  constructor
  · rintro ⟨r, hr, hrnext⟩
    obtain ⟨q, _hq, t, hrepr⟩ :=
      exists_radical_power_representative R S Z Y U b f g h comm hzero
        hS e n 0 hr
    refine ⟨q, ?_⟩
    intro hqrad
    apply hrnext
    have hq : q ∈ R.ideal.hom W (Y n) :=
      (R.mem_ideal_iff q).2 hqrad
    have hcomp : q ≫ backwardComposite Y f n ∈
        (R.ideal.pow (n + 1)).hom W (Y 0) := by
      rw [R.ideal.pow_succ_eq_mul_pow]
      exact HomIdeal.comp_mem_mul hq hc
    have hrEq : r = q ≫ backwardComposite Y f n := by
      simpa [hbzero] using hrepr
    rw [hrEq]
    exact hcomp
  · rintro ⟨q, hq⟩
    let r : W ⟶ Y 0 := q ≫ backwardComposite Y f n
    refine ⟨r, (R.ideal.pow n).precomp q hc, ?_⟩
    intro hrnext
    obtain ⟨q', hq', t, hrepr⟩ :=
      exists_radical_power_representative R S Z Y U b f g h comm hzero
        hS e n 1 (by simpa using hrnext)
    have heq :
        (q - q') ≫ backwardComposite Y f n =
          (0 : W ⟶ Z 0) ≫ b 0 := by
      dsimp only [r] at hrepr
      simp only [hbzero, comp_zero, add_zero] at hrepr
      rw [Preadditive.sub_comp, hrepr, sub_self, zero_comp]
    obtain ⟨s, hs⟩ :=
      (factorsThrough_initial_iff_factorsThrough_nth
        R S Z Y U b f g h comm hzero hS e n (q - q')).1 ⟨0, heq⟩
    have hdiff : q - q' ∈ R.ideal.hom W (Y n) := by
      rw [← hs]
      exact R.ideal.precomp s (hb n)
    have hq' : q' ∈ R.ideal.hom W (Y n) := by
      simpa using hq'
    have hqmem : q ∈ R.ideal.hom W (Y n) := by
      have hsum := (R.ideal.hom W (Y n)).add_mem hdiff hq'
      (convert hsum using 1; abel)
    exact hq ((R.mem_ideal_iff q).1 hqmem)

end Family

section FiniteTauCategory

variable [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind]

set_option linter.unusedSectionVars false in
/-- Any arrow whose source is zero is special. -/
theorem isSpecial_of_isZero_source
    (R : NilpotentRadicalData C)
    {X Y : C} (hX : IsZero X) (a : X ⟶ Y) :
    IsSpecial R a := by
  have ha : a = 0 := hX.eq_of_src a 0
  constructor
  · rw [ha]
    intro g
    simpa only [zero_comp, sub_zero] using
      (inferInstance : IsIso (𝟙 X))
  · intro r _hr
    have hr0 : r = 0 := hX.eq_of_src r 0
    rw [ha, hr0, add_zero]
    exact ⟨Iso.refl _⟩

/-- The canonical infinite right ladder beginning with `0 ⟶ X`. -/
def zeroInitialRightLadder
    (T : FiniteRightTauCategoryData C Ind) (X : C) :
    InfiniteSpecialRightLadder T (0 : (0 : C) ⟶ X) :=
  infiniteSpecialRightLadder T (0 : (0 : C) ⟶ X)
    (isSpecial_of_isZero_source T.radical (isZero_zero C) 0)

/-- If the source of the initial arrow is zero, then the initial essential
arrow in its normalized right ladder is itself zero. -/
theorem InfiniteSpecialRightLadder.initial_b_eq_zero_of_isZero_source
    {T : FiniteRightTauCategoryData C Ind}
    {X₀ Y₀ : C} {a₀ : X₀ ⟶ Y₀}
    (L : InfiniteSpecialRightLadder T a₀)
    (hX₀ : IsZero X₀) : L.b 0 = 0 := by
  obtain ⟨e⟩ := L.initialIso
  let eX : X₀ ≅ L.Z 0 ⊞ L.U 0 := Arrow.leftFunc.mapIso e
  have hZU : IsZero (L.Z 0 ⊞ L.U 0) := hX₀.of_iso eX.symm
  have hZ : IsZero (L.Z 0) := by
    rw [IsZero.iff_id_eq_zero]
    calc
      𝟙 (L.Z 0) =
          (biprod.inl : L.Z 0 ⟶ L.Z 0 ⊞ L.U 0) ≫ biprod.fst := by simp
      _ = 0 := by
        rw [hZU.eq_of_tgt
          (biprod.inl : L.Z 0 ⟶ L.Z 0 ⊞ L.U 0) 0, zero_comp]
  exact hZ.eq_of_src (L.b 0) 0

/-- On a chosen indecomposable, the preceding radical-layer criterion is
equivalent to occurrence as a retract of the `n`th ladder target. -/
theorem FiniteRightTauCategoryData.layerNonzero_iff_retract_of_zeroInitialLadder
    (T : FiniteRightTauCategoryData C Ind)
    (S : ℕ → ShortComplex C)
    (Z Y U : ℕ → C)
    (b : ∀ n : ℕ, Z n ⟶ Y n)
    (f : ∀ n : ℕ, Y (n + 1) ⟶ Y n)
    (g : ∀ n : ℕ, Z (n + 1) ⟶ Z n)
    (h : ∀ n : ℕ, U (n + 1) ⟶ Z n)
    (comm : ∀ n : ℕ, b (n + 1) ≫ f n = g n ≫ b n)
    (hzero : ∀ n : ℕ, h n ≫ b n = 0)
    (hS : ∀ n : ℕ, RightTauSequence (S n))
    (e : ∀ n : ℕ, Nonempty
      (S n ≅ stepComplex (b n) (b (n + 1)) (f n) (g n) (h n)
        (comm n) (hzero n)))
    (hbzero : b 0 = 0) (n : ℕ) (p : Ind) :
    T.radical.LayerNonzero n (T.obj p) (Y 0) ↔
      Nonempty (Retract (T.obj p) (Y n)) := by
  rw [layerNonzero_iff_exists_not_radical T.radical S Z Y U b f g h
    comm hzero hS e hbzero n (T.obj p)]
  constructor
  · rintro ⟨q, hq⟩
    have hsplit : IsSplitMono q := by
      by_contra hn
      exact hq ((T.isRadicalMorphism_iff_not_isSplitMono_from_obj q).2 hn)
    letI : IsSplitMono q := hsplit
    exact ⟨{ i := q, r := retraction q, retract := IsSplitMono.id q }⟩
  · rintro ⟨d⟩
    refine ⟨d.i, ?_⟩
    intro hrad
    have hn :=
      (T.isRadicalMorphism_iff_not_isSplitMono_from_obj d.i).1 hrad
    exact hn (IsSplitMono.mk'
      { retraction := d.r, id := d.retract })

/-- Paper-facing form of the objectwise projective-cover theorem.  In the
canonical right ladder beginning with `0 ⟶ X`, the `n`th radical layer from
a chosen indecomposable is nonzero exactly when that indecomposable occurs
as a retract of the `n`th ladder target. -/
theorem FiniteRightTauCategoryData.zeroInitialRightLadder_layerNonzero_iff_retract
    (T : FiniteRightTauCategoryData C Ind) (X : C) (n : ℕ) (p : Ind) :
    let L := zeroInitialRightLadder T X
    T.radical.LayerNonzero n (T.obj p) X ↔
      Nonempty (Retract (T.obj p) (L.Y n)) := by
  let L := zeroInitialRightLadder T X
  have hbzero : L.b 0 = 0 :=
    L.initial_b_eq_zero_of_isZero_source (isZero_zero C)
  have h := layerNonzero_iff_retract_of_zeroInitialLadder T
    (fun k ↦ T.rightMesh (L.Y k)) L.Z L.Y L.U L.b L.f L.g L.h
    L.comm L.hzero (fun k ↦ T.rightTau (L.Y k)) L.meshIso hbzero n p
  have hYzero : L.Y 0 = X := rfl
  simpa only [hYzero] using h

end FiniteTauCategory

end QuotientSubmoduleEquidistribution.Iyama.RightLadder
