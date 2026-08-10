import OpConjecture.RepresentationDirected.ARWordMeshExactnessInterface

/-!
# Iyama's finite translation-quiver strictness reduction

This file formalizes the numerical sign argument in Iyama's implication

`positive right-additive function -> strict tau-category`.

The genuinely deep input is isolated one step earlier as
`NakayamaStrictnessBridge`: failure of monicity of a first mesh map produces a
Nakayama pair, and right-additive weights agree at the two endpoint maps of
its ladder.  Once that bridge is available, strictness is the immediate sign
contradiction from Iyama's proof.

No representable mesh recurrence, exactness conclusion, concrete algebra,
quiver presentation, module enumeration, or classification is assumed here.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace OpConjecture.RepresentationDirected.IyamaMesh

universe uV

/-! ## Finite admissible translation quivers -/

/-- The finite translation-quiver data used in Iyama's strictness theorem.

The convention is that `valuation y x` is the multiplicity of `y` in the
middle term of the right mesh ending at `x`. -/
structure FiniteAdmissibleTranslationQuiver
    (V : Type uV) [Fintype V] where
  projective : Set V
  injective : Set V
  tau : {x : V // x ∉ projective} ≃ {x : V // x ∉ injective}
  valuation : V → V → ℕ
  covaluation : V → V → ℕ
  translation_pairing :
    ∀ (x : {x : V // x ∉ projective}) (y : V),
      valuation y x.1 = covaluation (tau x).1 y
  projective_of_no_incoming :
    ∀ x : V, (∀ y : V, valuation y x = 0) → x ∈ projective
  symmetrizer : V → ℕ
  symmetrizer_pos : ∀ x : V, 0 < symmetrizer x
  admissible :
    ∀ x y : V,
      symmetrizer x * valuation x y =
        covaluation x y * symmetrizer y

namespace FiniteAdmissibleTranslationQuiver

variable {V : Type uV} [Fintype V]

/-- The translated vertex underlying the subtype equivalence. -/
def tauVertex (Q : FiniteAdmissibleTranslationQuiver V)
    (x : V) (hx : x ∉ Q.projective) : V :=
  (Q.tau ⟨x, hx⟩).1

/-- Evaluation of the right middle term against an integral weight. -/
def thetaWeight (Q : FiniteAdmissibleTranslationQuiver V)
    (weight : V → ℤ) (x : V) : ℤ :=
  ∑ y : V, (Q.valuation y x : ℤ) * weight y

/-- Iyama's positive-valued right-additivity condition.

The defect vanishes away from the projective boundary and is nonnegative on
that boundary.  The word-quiver function used in the manuscript satisfies
the stronger condition that every projective defect is positive. -/
def IsPositiveRightAdditive
    (Q : FiniteAdmissibleTranslationQuiver V) (weight : V → ℤ) : Prop :=
  (∀ x : V, 0 < weight x) ∧
    (∀ (x : V) (hx : x ∉ Q.projective),
      weight x - Q.thetaWeight weight x + weight (Q.tauVertex x hx) = 0) ∧
    ∀ (x : V), x ∈ Q.projective →
      0 ≤ weight x - Q.thetaWeight weight x

/-- Weight of the first map in the right mesh ending at `x`. -/
def nuWeight (Q : FiniteAdmissibleTranslationQuiver V)
    (weight : V → ℤ) (x : V) (hx : x ∉ Q.projective) : ℤ :=
  weight (Q.tauVertex x hx) - Q.thetaWeight weight x

/-- Weight of the second map in the right mesh ending at `x`. -/
def muWeight (Q : FiniteAdmissibleTranslationQuiver V)
    (weight : V → ℤ) (x : V) : ℤ :=
  Q.thetaWeight weight x - weight x

/-- Right additivity makes the weight of the first mesh map ending at `x`
equal to `-weight x`. -/
theorem nuWeight_eq_neg
    (Q : FiniteAdmissibleTranslationQuiver V) (weight : V → ℤ)
    (hadd : Q.IsPositiveRightAdditive weight)
    (x : V) (hx : x ∉ Q.projective) :
    Q.nuWeight weight x hx = -weight x := by
  dsimp [nuWeight]
  linarith [hadd.2.1 x hx]

/-- Right additivity makes the weight of the second mesh map ending at `x`
equal to the weight of its translate. -/
theorem muWeight_eq_tau
    (Q : FiniteAdmissibleTranslationQuiver V) (weight : V → ℤ)
    (hadd : Q.IsPositiveRightAdditive weight)
    (x : V) (hx : x ∉ Q.projective) :
    Q.muWeight weight x = weight (Q.tauVertex x hx) := by
  dsimp [muWeight]
  linarith [hadd.2.1 x hx]

/-! ## The Nakayama-pair boundary and strictness -/

/-- The exact earlier theorem boundary in Iyama's proof of strictness.

`firstMapMonic x` records monicity of the first map in the right mesh ending
at `x`.  The first field is the nonmonic-to-Nakayama-pair extraction theorem;
the second is invariance of a right-additive endpoint-map weight along the
Nakayama ladder.

This structure deliberately does not assume strictness, representable mesh
exactness, or the inverse mesh recurrence. -/
structure NakayamaStrictnessBridge
    (Q : FiniteAdmissibleTranslationQuiver V)
    (firstMapMonic : V → Prop) where
  nakayamaPair : V → V → Prop
  pair_of_not_monic :
    ∀ (x : V) (hx : x ∉ Q.projective), ¬ firstMapMonic x →
      ∃ y : V, y ∉ Q.projective ∧
        nakayamaPair (Q.tauVertex x hx) y
  endpoint_weight_eq :
    ∀ (weight : V → ℤ), Q.IsPositiveRightAdditive weight →
      ∀ (x : V) (hx : x ∉ Q.projective) (y : V),
        nakayamaPair (Q.tauVertex x hx) y →
          Q.nuWeight weight x hx = Q.muWeight weight y

/-- Iyama's sign contradiction: the Nakayama extraction and endpoint
identity force every nonprojective first mesh map to be monic. -/
theorem strict_of_positiveRightAdditive
    (Q : FiniteAdmissibleTranslationQuiver V)
    (firstMapMonic : V → Prop)
    (B : NakayamaStrictnessBridge Q firstMapMonic)
    (weight : V → ℤ) (hadd : Q.IsPositiveRightAdditive weight) :
    ∀ (x : V), x ∉ Q.projective → firstMapMonic x := by
  intro x hx
  by_contra hmono
  obtain ⟨y, hy, hpair⟩ := B.pair_of_not_monic x hx hmono
  have heq := B.endpoint_weight_eq weight hadd x hx y hpair
  rw [Q.nuWeight_eq_neg weight hadd x hx,
    Q.muWeight_eq_tau weight hadd y hy] at heq
  have hxpos := hadd.1 x
  have hytaupos := hadd.1 (Q.tauVertex y hy)
  linarith

/-- Adding the automatic projective-boundary maps gives strictness at every
vertex. -/
theorem strict_all_of_positiveRightAdditive
    (Q : FiniteAdmissibleTranslationQuiver V)
    (firstMapMonic : V → Prop)
    (B : NakayamaStrictnessBridge Q firstMapMonic)
    (projective_monic : ∀ x : V, x ∈ Q.projective → firstMapMonic x)
    (weight : V → ℤ) (hadd : Q.IsPositiveRightAdditive weight) :
    ∀ x : V, firstMapMonic x := by
  intro x
  by_cases hx : x ∈ Q.projective
  · exact projective_monic x hx
  · exact Q.strict_of_positiveRightAdditive firstMapMonic B weight hadd x hx

end FiniteAdmissibleTranslationQuiver

/-! ## The finite translation quiver carried by a boundary-run word -/

namespace Word

open OpConjecture.RepresentationDirected.PrincipalPositivity

universe uL

variable {L : Type uL}

/-- A word position is nonprojective exactly when it has a previous
occurrence of the same label. -/
def HasPrevious (Q : List L) (x : Fin Q.length) : Prop :=
  ∃ p, ARWord.IsPrevious Q p x

/-- A word position is noninjective exactly when it has a next occurrence of
the same label. -/
def HasNext (Q : List L) (p : Fin Q.length) : Prop :=
  ∃ x, ARWord.IsPrevious Q p x

/-- The next occurrence after a fixed position is unique. -/
theorem isPrevious_target_unique
    {Q : List L} {p x y : Fin Q.length}
    (hx : ARWord.IsPrevious Q p x) (hy : ARWord.IsPrevious Q p y) :
    x = y := by
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · exact False.elim
      (hy.2.2 x hx.1 hxy (hx.2.1.symm.trans hy.2.1))
  · exact hxy
  · exact False.elim
      (hx.2.2 y hy.1 hyx (hy.2.1.symm.trans hx.2.1))

/-- Projective-boundary positions of the word translation quiver. -/
def projectiveSet (Q : List L) : Set (Fin Q.length) :=
  {x | ¬ HasPrevious Q x}

/-- Injective-boundary positions of the word translation quiver. -/
def injectiveSet (Q : List L) : Set (Fin Q.length) :=
  {p | ¬ HasNext Q p}

private theorem hasPrevious_of_not_projective
    (Q : List L) (x : {x : Fin Q.length // x ∉ projectiveSet Q}) :
    HasPrevious Q x.1 := by
  by_contra h
  exact x.2 h

private theorem hasNext_of_not_injective
    (Q : List L) (p : {p : Fin Q.length // p ∉ injectiveSet Q}) :
    HasNext Q p.1 := by
  by_contra h
  exact p.2 h

/-- The predecessor chosen at a nonprojective word position. -/
def tauTo (Q : List L)
    (x : {x : Fin Q.length // x ∉ projectiveSet Q}) : Fin Q.length :=
  Classical.choose (hasPrevious_of_not_projective Q x)

theorem tauTo_spec (Q : List L)
    (x : {x : Fin Q.length // x ∉ projectiveSet Q}) :
    ARWord.IsPrevious Q (tauTo Q x) x.1 :=
  Classical.choose_spec (hasPrevious_of_not_projective Q x)

/-- The next occurrence chosen at a noninjective word position. -/
def tauInv (Q : List L)
    (p : {p : Fin Q.length // p ∉ injectiveSet Q}) : Fin Q.length :=
  Classical.choose (hasNext_of_not_injective Q p)

theorem tauInv_spec (Q : List L)
    (p : {p : Fin Q.length // p ∉ injectiveSet Q}) :
    ARWord.IsPrevious Q p.1 (tauInv Q p) :=
  Classical.choose_spec (hasNext_of_not_injective Q p)

/-- Previous and next occurrence give the translation bijection between
nonprojective and noninjective word positions. -/
def tauEquiv (Q : List L) :
    {x : Fin Q.length // x ∉ projectiveSet Q} ≃
      {p : Fin Q.length // p ∉ injectiveSet Q} where
  toFun x := ⟨tauTo Q x, by
    intro h
    exact h ⟨x.1, tauTo_spec Q x⟩⟩
  invFun p := ⟨tauInv Q p, by
    intro h
    exact h ⟨p.1, tauInv_spec Q p⟩⟩
  left_inv x := by
    apply Subtype.ext
    exact isPrevious_target_unique
      (tauInv_spec Q ⟨tauTo Q x, by
        intro h
        exact h ⟨x.1, tauTo_spec Q x⟩⟩)
      (tauTo_spec Q x)
  right_inv p := by
    apply Subtype.ext
    exact ARWord.isPrevious_unique
      (tauTo_spec Q ⟨tauInv Q p, by
        intro h
        exact h ⟨p.1, tauInv_spec Q p⟩⟩)
      (tauInv_spec Q p)

/-- The unvalued multiplicity of a middle arrow. -/
def arrowMultiplicity (G : SimpleGraph L) (Q : List L)
    (y x : Fin Q.length) : ℕ := by
  classical
  exact if ARWord.IsMiddle G Q y x then 1 else 0

/-- A positive right-additive function rules out an empty nonprojective
mesh. -/
theorem nonprojective_hasIncoming_of_positiveRightAdditive
    (G : SimpleGraph L) (Q : List L)
    (weight : Fin Q.length → ℤ)
    (hweight : IsPositiveRightAdditive G Q weight)
    (x : {x : Fin Q.length // HasPrevious Q x}) :
    ∃ y, ARWord.IsMiddle G Q y x := by
  obtain ⟨p, hp⟩ := x.2
  by_contra hnone
  push Not at hnone
  have hsum : scalarMiddleSum G Q weight x = 0 := by
    classical
    unfold scalarMiddleSum
    apply Finset.sum_eq_zero
    intro y hy
    have hymiddle : ARWord.IsMiddle G Q y x := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hy
    exact False.elim (hnone y hymiddle)
  have hadd := hweight.2.1 p x hp
  rw [hsum] at hadd
  have hxpositive := hweight.1 x
  have hppositive := hweight.1 p
  omega

/-- Boundary-run rotation, finiteness, and a positive right-additive weight
supply the manuscript's finite unvalued admissible translation quiver. -/
def translationQuiver
    (G : SimpleGraph L) (Q : List L)
    (hRuns : ARWord.HasOnlyBoundaryRepeatedRuns G Q)
    (weight : Fin Q.length → ℤ)
    (hweight : IsPositiveRightAdditive G Q weight) :
    FiniteAdmissibleTranslationQuiver (Fin Q.length) where
  projective := projectiveSet Q
  injective := injectiveSet Q
  tau := tauEquiv Q
  valuation := arrowMultiplicity G Q
  covaluation := arrowMultiplicity G Q
  translation_pairing x y := by
    classical
    unfold arrowMultiplicity
    change (if ARWord.IsMiddle G Q y x then 1 else 0) =
      if ARWord.IsMiddle G Q (tauTo Q x) y then 1 else 0
    exact if_congr
      (ARWord.isMiddle_iff_previous_isMiddle
        hRuns.hasInteriorAlternation (tauTo_spec Q x) y) rfl rfl
  projective_of_no_incoming x hzero := by
    intro hxprojective
    obtain ⟨y, hy⟩ :=
      nonprojective_hasIncoming_of_positiveRightAdditive
        G Q weight hweight ⟨x, hxprojective⟩
    have := hzero y
    simp [arrowMultiplicity, hy] at this
  symmetrizer := fun _ ↦ 1
  symmetrizer_pos := by simp
  admissible := by simp

@[simp]
theorem translationQuiver_thetaWeight
    (G : SimpleGraph L) (Q : List L)
    (hRuns : ARWord.HasOnlyBoundaryRepeatedRuns G Q)
    (weight : Fin Q.length → ℤ)
    (hweight : IsPositiveRightAdditive G Q weight)
    (f : Fin Q.length → ℤ) (x : Fin Q.length) :
    (translationQuiver G Q hRuns weight hweight).thetaWeight f x =
      scalarMiddleSum G Q f x := by
  classical
  simp [FiniteAdmissibleTranslationQuiver.thetaWeight,
    translationQuiver, arrowMultiplicity, scalarMiddleSum,
    Finset.sum_filter]

@[simp]
theorem translationQuiver_tauVertex
    (G : SimpleGraph L) (Q : List L)
    (hRuns : ARWord.HasOnlyBoundaryRepeatedRuns G Q)
    (weight : Fin Q.length → ℤ)
    (hweight : IsPositiveRightAdditive G Q weight)
    (x : Fin Q.length)
    (hx : x ∉ (translationQuiver G Q hRuns weight hweight).projective) :
    (translationQuiver G Q hRuns weight hweight).tauVertex x hx =
      tauTo Q ⟨x, hx⟩ := rfl

/-- The manuscript's word-level positive right-additive function is a
right-additive function on the associated finite admissible translation
quiver in Iyama's convention. -/
theorem translationQuiver_isPositiveRightAdditive
    (G : SimpleGraph L) (Q : List L)
    (hRuns : ARWord.HasOnlyBoundaryRepeatedRuns G Q)
    (weight : Fin Q.length → ℤ)
    (hweight : IsPositiveRightAdditive G Q weight) :
    (translationQuiver G Q hRuns weight hweight).IsPositiveRightAdditive
      weight := by
  let T := translationQuiver G Q hRuns weight hweight
  refine ⟨hweight.1, ?_, ?_⟩
  · intro x hx
    let xt : {x : Fin Q.length // x ∉ projectiveSet Q} := ⟨x, hx⟩
    have hp := tauTo_spec Q xt
    simpa only [T, translationQuiver_thetaWeight,
      translationQuiver_tauVertex] using hweight.2.1 (tauTo Q xt) x hp
  · intro x hx
    have hfirst : ¬ ∃ p, ARWord.IsPrevious Q p x := hx
    simpa only [T, translationQuiver_thetaWeight] using
      (hweight.2.2 x hfirst).le

/-- Word-level specialization of Iyama's sign argument.  Once the genuine
Nakayama extraction and endpoint identity are supplied for the word mesh
category, every first mesh map is monic. -/
theorem strict_all_of_nakayamaBridge
    (G : SimpleGraph L) (Q : List L)
    (hRuns : ARWord.HasOnlyBoundaryRepeatedRuns G Q)
    (weight : Fin Q.length → ℤ)
    (hweight : IsPositiveRightAdditive G Q weight)
    (firstMapMonic : Fin Q.length → Prop)
    (B : FiniteAdmissibleTranslationQuiver.NakayamaStrictnessBridge
      (translationQuiver G Q hRuns weight hweight) firstMapMonic)
    (projective_monic : ∀ x : Fin Q.length,
      x ∈ (translationQuiver G Q hRuns weight hweight).projective →
        firstMapMonic x) :
    ∀ x, firstMapMonic x :=
  FiniteAdmissibleTranslationQuiver.strict_all_of_positiveRightAdditive
    (translationQuiver G Q hRuns weight hweight) firstMapMonic B
    projective_monic weight
    (translationQuiver_isPositiveRightAdditive G Q hRuns weight hweight)

end Word

end OpConjecture.RepresentationDirected.IyamaMesh
