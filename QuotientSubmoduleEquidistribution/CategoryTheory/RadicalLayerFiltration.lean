import QuotientSubmoduleEquidistribution.CategoryTheory.CategoricalRadicalIdeal
import QuotientSubmoduleEquidistribution.CategoryTheory.NilpotentCategoricalRadical

/-!
# Radical layers in a nilpotent categorical radical

For a Hom ideal `I`, the `n`-th layer between two objects is nonzero when
some morphism belongs to `I^n` but not to `I^(n+1)`.  Nilpotence implies
that a Hom group is nonzero exactly when at least one such layer is nonzero,
and that all sufficiently high layers vanish.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.CategoricalIdeal.HomIdeal

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Nonvanishing of the quotient `I^n(X,Y) / I^(n+1)(X,Y)`, expressed
without constructing the quotient additive group. -/
def LayerNonzero (I : HomIdeal C) (n : ℕ) (X Y : C) : Prop :=
  ∃ f : X ⟶ Y,
    f ∈ (I.pow n).hom X Y ∧
      f ∉ (I.pow (n + 1)).hom X Y

/-- A nonzero layer contains a nonzero morphism. -/
theorem exists_ne_zero_of_layerNonzero
    {I : HomIdeal C} {n : ℕ} {X Y : C}
    (h : I.LayerNonzero n X Y) :
    ∃ f : X ⟶ Y, f ≠ 0 := by
  obtain ⟨f, -, hfnext⟩ := h
  refine ⟨f, fun hf ↦ hfnext ?_⟩
  subst f
  exact zero_mem _

/-- Under nilpotence, every nonzero morphism has a last power of `I` to
which it belongs and hence determines a nonzero layer. -/
theorem exists_layerNonzero_of_ne_zero
    {I : HomIdeal C} (hI : I.IsNilpotent)
    {X Y : C} {f : X ⟶ Y} (hf : f ≠ 0) :
    ∃ n, I.LayerNonzero n X Y := by
  classical
  obtain ⟨N, hN⟩ := hI
  have hfN : f ∉ (I.pow N).hom X Y := by
    rw [hN]
    simpa using hf
  have hexists : ∃ k, f ∉ (I.pow k).hom X Y := ⟨N, hfN⟩
  let k := Nat.find hexists
  have hknot : f ∉ (I.pow k).hom X Y :=
    Nat.find_spec hexists
  have hkzero : k ≠ 0 := by
    intro hk
    apply hknot
    rw [hk, pow_zero]
    exact AddSubgroup.mem_top f
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hkzero
  refine ⟨n, f, ?_, ?_⟩
  · by_contra hnmem
    have hminimal : k ≤ n := by
      dsimp only [k]
      exact Nat.find_min' hexists hnmem
    rw [hn] at hminimal
    exact (Nat.not_succ_le_self n) hminimal
  · simpa [hn] using hknot

/-- For a nilpotent Hom ideal, a Hom group is nonzero exactly when one of
its ideal-power layers is nonzero. -/
theorem exists_ne_zero_iff_exists_layerNonzero
    {I : HomIdeal C} (hI : I.IsNilpotent) (X Y : C) :
    (∃ f : X ⟶ Y, f ≠ 0) ↔
      ∃ n, I.LayerNonzero n X Y := by
  constructor
  · rintro ⟨f, hf⟩
    exact exists_layerNonzero_of_ne_zero hI hf
  · rintro ⟨n, hn⟩
    exact exists_ne_zero_of_layerNonzero hn

/-- Once a power is zero, no layer at that or a larger exponent can be
nonzero. -/
theorem not_layerNonzero_of_pow_eq_bot
    {I : HomIdeal C} {N n : ℕ} (hN : I.pow N = ⊥)
    (hn : N ≤ n) (X Y : C) :
    ¬ I.LayerNonzero n X Y := by
  rintro ⟨f, hfn, hfnext⟩
  have hfN : f ∈ (I.pow N).hom X Y :=
    (pow_le_pow_of_le I hn) _ _ hfn
  rw [hN] at hfN
  have hfzero : f = 0 := by simpa using hfN
  apply hfnext
  subst f
  exact zero_mem _

/-- Nilpotence makes all sufficiently high layers vanish. -/
theorem eventually_not_layerNonzero
    {I : HomIdeal C} (hI : I.IsNilpotent) (X Y : C) :
    ∃ N, ∀ n, N ≤ n → ¬ I.LayerNonzero n X Y := by
  obtain ⟨N, hN⟩ := hI
  exact ⟨N, fun n hn ↦
    not_layerNonzero_of_pow_eq_bot hN hn X Y⟩

end QuotientSubmoduleEquidistribution.CategoricalIdeal.HomIdeal

namespace QuotientSubmoduleEquidistribution.CategoricalRadical

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

open CategoricalIdeal

/-- The canonical radical ideal, equipped with a supplied nilpotence proof. -/
def nilpotentRadicalData
    (h : (homIdeal : HomIdeal C).IsNilpotent) :
    NilpotentRadicalData C where
  ideal := homIdeal
  mem_iff := mem_homIdeal_iff
  nilpotent := h

namespace NilpotentRadicalData

/-- Nonvanishing of the `n`-th categorical radical layer. -/
def LayerNonzero (R : NilpotentRadicalData C)
    (n : ℕ) (X Y : C) : Prop :=
  R.ideal.LayerNonzero n X Y

/-- In a category with nilpotent radical, Hom is nonzero exactly when one
of its radical layers is nonzero. -/
theorem exists_ne_zero_iff_exists_layerNonzero
    (R : NilpotentRadicalData C) (X Y : C) :
    (∃ f : X ⟶ Y, f ≠ 0) ↔
      ∃ n, R.LayerNonzero n X Y :=
  R.ideal.exists_ne_zero_iff_exists_layerNonzero R.nilpotent X Y

/-- All sufficiently high radical layers between fixed objects vanish. -/
theorem eventually_not_layerNonzero
    (R : NilpotentRadicalData C) (X Y : C) :
    ∃ N, ∀ n, N ≤ n → ¬ R.LayerNonzero n X Y :=
  R.ideal.eventually_not_layerNonzero R.nilpotent X Y

end NilpotentRadicalData

end QuotientSubmoduleEquidistribution.CategoricalRadical
