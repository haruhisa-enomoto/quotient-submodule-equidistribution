import QuotientSubmoduleEquidistribution.RepresentationTheory.FactorHomCriterion
import QuotientSubmoduleEquidistribution.RepresentationTheory.FiniteDimensionalARNonvanishing
import QuotientSubmoduleEquidistribution.RepresentationTheory.ProjectiveBoundaryAlmostSplit

/-!
# Auslander--Reiten operators for factor ladders

This file constructs the two additive operators in the paper's factor-ladder
recursion.  The `theta` operator records, with multiplicity, the deleted
summands in a minimal right almost-split middle term.  At a projective endpoint
that middle term is the module radical.  The restricted translation operator
is zero unless the endpoint is nonprojective, its translate remains deleted,
and its restricted middle term is nonzero.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open CategoryTheory

namespace QuotientSubmoduleEquidistribution.FactorLadder

universe u

/-- The integer matrix action on finite-rank integer vectors, with columns
indexed by the input basis and rows by the output coordinate. -/
def matrixAddHom {D : Type u} [Fintype D]
    (entry : D → D → ℤ) : IntVector D →+ IntVector D where
  toFun v y := ∑ x : D, v x * entry x y
  map_zero' := by
    funext y
    simp
  map_add' v w := by
    funext y
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

@[simp]
theorem matrixAddHom_apply {D : Type u} [Fintype D]
    (entry : D → D → ℤ) (v : IntVector D) (y : D) :
    matrixAddHom entry v y = ∑ x : D, v x * entry x y :=
  rfl

@[simp]
theorem matrixAddHom_basis {D : Type u} [Fintype D]
    (entry : D → D → ℤ) (x y : D) :
    matrixAddHom entry (basis x) y = entry x y := by
  classical
  simp [matrixAddHom, basis]

end QuotientSubmoduleEquidistribution.FactorLadder

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe u v

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} [Fintype ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)

namespace FiniteARTranslationData

variable (D : σ.FiniteARTranslationData)

omit [Fintype ι] in
/-- The unified minimal right almost-split decomposition at a skeleton label.
For a projective this is `rad P ⟶ P`; otherwise it is the chosen AR map. -/
def factorLadderRightARAt (x : ι) :
    σ.MinimalRightAlmostSplitDecomposition x := by
  classical
  by_cases hx : Projective (σ.obj x)
  · exact σ.projectiveBoundaryMinimalRightAlmostSplitDecomposition x hx
  · exact D.chosenRightAR σ ⟨x, hx⟩

/-- Multiplicity of a deleted label `y` in the unified right AR middle term
ending at the deleted label `x`. -/
def deletedMiddleMultiplicity (K : Set ι)
    (x y : DeletedLabel K) : ℤ := by
  classical
  let A := factorLadderRightARAt σ D x.1
  letI : Fintype A.index := FintypeCat.fintype
  exact ((Finset.univ.filter fun t : A.index ↦
    A.label t = y.1).card : ℤ)

omit [Fintype ι] in
/-- Restricted right-AR multiplicities are nonnegative. -/
theorem deletedMiddleMultiplicity_nonneg (K : Set ι)
    (x y : DeletedLabel K) :
    0 ≤ deletedMiddleMultiplicity (σ := σ) (D := D) K x y := by
  classical
  simp only [deletedMiddleMultiplicity]
  exact Int.natCast_nonneg _

omit [Fintype ι] in
/-- A deleted middle-term multiplicity is positive exactly when the
corresponding deleted label is the source of an irreducible morphism to the
endpoint. -/
theorem deletedMiddleMultiplicity_pos_iff_irreducible
    (K : Set ι) (x y : DeletedLabel K) :
    0 < deletedMiddleMultiplicity (σ := σ) (D := D) K x y ↔
      HasIrreducibleMorphism (σ.obj y.1) (σ.obj x.1) := by
  classical
  let A := factorLadderRightARAt σ D x.1
  letI : Fintype A.index := FintypeCat.fintype
  constructor
  · intro hpos
    change 0 < (((Finset.univ.filter fun t : A.index ↦
      A.label t = y.1).card : ℕ) : ℤ) at hpos
    have hcard : 0 <
        (Finset.univ.filter fun t : A.index ↦
          A.label t = y.1).card := by
      exact_mod_cast hpos
    obtain ⟨t, ht⟩ := Finset.card_pos.mp hcard
    have htlabel := (Finset.mem_filter.mp ht).2
    exact
      (A.summandIrreducibleCorrespondence y.1).1
        ⟨t, htlabel⟩
  · intro hirr
    obtain ⟨t, ht⟩ :=
      (A.summandIrreducibleCorrespondence y.1).2 hirr
    have htmem : t ∈
        Finset.univ.filter fun s : A.index ↦ A.label s = y.1 :=
      Finset.mem_filter.2 ⟨Finset.mem_univ t, ht⟩
    have hcard : 0 <
        (Finset.univ.filter fun s : A.index ↦
          A.label s = y.1).card :=
      Finset.card_pos.mpr ⟨t, htmem⟩
    change 0 < (((Finset.univ.filter fun s : A.index ↦
      A.label s = y.1).card : ℕ) : ℤ)
    exact_mod_cast hcard

/-- The paper's additive `theta_D` operator, retaining exactly the deleted
summands of each right almost-split middle term. -/
def factorLadderTheta (K : Set ι) :
    FactorLadder.IntVector (DeletedLabel K) →+
      FactorLadder.IntVector (DeletedLabel K) := by
  classical
  exact FactorLadder.matrixAddHom
    (deletedMiddleMultiplicity (σ := σ) (D := D) K)

@[simp]
theorem factorLadderTheta_basis_apply
    (K : Set ι) (x y : DeletedLabel K) :
    factorLadderTheta (σ := σ) (D := D) K
        (FactorLadder.basis x) y =
      deletedMiddleMultiplicity (σ := σ) (D := D) K x y := by
  classical
  exact FactorLadder.matrixAddHom_basis _ x y

/-- A deleted label has a nonzero restricted middle term exactly when some
coordinate of the chosen right AR decomposition remains deleted. -/
theorem factorLadderTheta_basis_ne_zero_iff
    (K : Set ι) (x : DeletedLabel K) :
    factorLadderTheta (σ := σ) (D := D) K
        (FactorLadder.basis x) ≠ 0 ↔
      ∃ t : (factorLadderRightARAt σ D x.1).index,
        (factorLadderRightARAt σ D x.1).label t ∉ K := by
  classical
  letI : Fintype (factorLadderRightARAt σ D x.1).index :=
    FintypeCat.fintype
  constructor
  · intro htheta
    by_contra hnone
    push Not at hnone
    apply htheta
    funext y
    rw [factorLadderTheta_basis_apply]
    simp only [Pi.zero_apply]
    change ((Finset.univ.filter fun t :
      (factorLadderRightARAt σ D x.1).index ↦
        (factorLadderRightARAt σ D x.1).label t = y.1).card : ℤ) = 0
    apply Int.ofNat_eq_zero.2
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.2
    intro t _ ht
    apply y.2
    simpa only [ht] using hnone t
  · rintro ⟨t, ht⟩ hzero
    let y : DeletedLabel K :=
      ⟨(factorLadderRightARAt σ D x.1).label t, ht⟩
    have hcoord := congrFun hzero y
    rw [factorLadderTheta_basis_apply] at hcoord
    have hpos : 0 <
        deletedMiddleMultiplicity (σ := σ) (D := D) K x y := by
      change 0 < (((Finset.univ.filter fun s :
        (factorLadderRightARAt σ D x.1).index ↦
          (factorLadderRightARAt σ D x.1).label s = y.1).card : ℕ) : ℤ)
      have htmem : t ∈ (Finset.univ.filter fun s :
          (factorLadderRightARAt σ D x.1).index ↦
            (factorLadderRightARAt σ D x.1).label s = y.1) :=
        Finset.mem_filter.2 ⟨Finset.mem_univ t, rfl⟩
      exact_mod_cast Finset.card_pos.mpr ⟨t, htmem⟩
    rw [Pi.zero_apply] at hcoord
    omega

/-- The optional target of the restricted `tau_D` basis vector.  The three
failure cases are exactly those in the manuscript definition. -/
def factorLadderTauTarget (K : Set ι)
    (x : DeletedLabel K) : Option (DeletedLabel K) := by
  classical
  by_cases hx : Projective (σ.obj x.1)
  · exact none
  · let tx : ι := (D.arTranslation σ ⟨x.1, hx⟩).1
    by_cases htx : tx ∈ K
    · exact none
    · by_cases hmiddle :
        factorLadderTheta (σ := σ) (D := D) K
          (FactorLadder.basis x) = 0
      · exact none
      · exact some ⟨tx, htx⟩

/-- Matrix entry of the paper's restricted translation operator. -/
def factorLadderTauEntry (K : Set ι)
    (x y : DeletedLabel K) : ℤ := by
  classical
  exact if factorLadderTauTarget (σ := σ) (D := D) K x = some y
    then 1 else 0

/-- The paper's additive `tau_D` operator. -/
def factorLadderTau (K : Set ι) :
    FactorLadder.IntVector (DeletedLabel K) →+
      FactorLadder.IntVector (DeletedLabel K) := by
  classical
  exact FactorLadder.matrixAddHom
    (factorLadderTauEntry (σ := σ) (D := D) K)

@[simp]
theorem factorLadderTau_basis_apply
    (K : Set ι) (x y : DeletedLabel K) :
    factorLadderTau (σ := σ) (D := D) K
        (FactorLadder.basis x) y =
      factorLadderTauEntry (σ := σ) (D := D) K x y := by
  classical
  rw [factorLadderTau, FactorLadder.matrixAddHom_basis]

/-- A restricted translation matrix entry is one exactly at its optional
target. -/
theorem factorLadderTauEntry_eq_one_iff
    (K : Set ι) (x y : DeletedLabel K) :
    factorLadderTauEntry (σ := σ) (D := D) K x y = 1 ↔
      factorLadderTauTarget (σ := σ) (D := D) K x = some y := by
  classical
  simp [factorLadderTauEntry]

/-- A retained optional target makes the restricted translation of a basis
vector the corresponding basis vector. -/
theorem factorLadderTau_basis_eq_basis_of_target_eq_some
    (K : Set ι) (x y : DeletedLabel K)
    (hxy : factorLadderTauTarget (σ := σ) (D := D) K x = some y) :
    factorLadderTau (σ := σ) (D := D) K
        (FactorLadder.basis x) = FactorLadder.basis y := by
  classical
  funext z
  rw [factorLadderTau_basis_apply]
  simp [factorLadderTauEntry, FactorLadder.basis, hxy, eq_comm]

/-- A missing optional target makes the restricted translation of a basis
vector zero. -/
theorem factorLadderTau_basis_eq_zero_of_target_eq_none
    (K : Set ι) (x : DeletedLabel K)
    (hx : factorLadderTauTarget (σ := σ) (D := D) K x = none) :
    factorLadderTau (σ := σ) (D := D) K
        (FactorLadder.basis x) = 0 := by
  classical
  funext y
  rw [factorLadderTau_basis_apply]
  simp [factorLadderTauEntry, hx]

/-- At a projective endpoint the restricted translation is zero. -/
theorem factorLadderTauTarget_eq_none_of_projective
    (K : Set ι) (x : DeletedLabel K)
    (hx : Projective (σ.obj x.1)) :
    factorLadderTauTarget (σ := σ) (D := D) K x = none := by
  simp [factorLadderTauTarget, hx]

/-- If the ordinary translate belongs to `K`, the restricted translation is
zero. -/
theorem factorLadderTauTarget_eq_none_of_translation_mem
    (K : Set ι) (x : DeletedLabel K)
    (hx : ¬ Projective (σ.obj x.1))
    (htx : (D.arTranslation σ ⟨x.1, hx⟩).1 ∈ K) :
    factorLadderTauTarget (σ := σ) (D := D) K x = none := by
  simp [factorLadderTauTarget, hx, htx]

/-- If the ordinary translate is retained, the restricted translation still
vanishes when the restricted middle term vanishes. -/
theorem factorLadderTauTarget_eq_none_of_theta_eq_zero
    (K : Set ι) (x : DeletedLabel K)
    (hx : ¬ Projective (σ.obj x.1))
    (hmiddle :
      factorLadderTheta (σ := σ) (D := D) K
        (FactorLadder.basis x) = 0) :
    factorLadderTauTarget (σ := σ) (D := D) K x = none := by
  simp [factorLadderTauTarget, hx, hmiddle]

/-- In the nonprojective, retained-translate, nonzero-middle case, the
restricted translation is the ordinary AR translate. -/
theorem factorLadderTauTarget_eq_some
    (K : Set ι) (x : DeletedLabel K)
    (hx : ¬ Projective (σ.obj x.1))
    (htx : (D.arTranslation σ ⟨x.1, hx⟩).1 ∉ K)
    (hmiddle :
      factorLadderTheta (σ := σ) (D := D) K
        (FactorLadder.basis x) ≠ 0) :
    factorLadderTauTarget (σ := σ) (D := D) K x =
      some ⟨(D.arTranslation σ ⟨x.1, hx⟩).1, htx⟩ := by
  simp [factorLadderTauTarget, hx, htx, hmiddle]

/-- The exact pair of additive AR operators entering the factor-ladder
recursion. -/
def factorLadderData (K : Set ι) :
    FactorLadder.Data (DeletedLabel K) where
  theta := factorLadderTheta (σ := σ) (D := D) K
  tau := factorLadderTau (σ := σ) (D := D) K

@[simp]
theorem factorLadderData_theta
    (K : Set ι) :
    (factorLadderData (σ := σ) (D := D) K).theta =
      factorLadderTheta (σ := σ) (D := D) K :=
  rfl

@[simp]
theorem factorLadderData_tau
    (K : Set ι) :
    (factorLadderData (σ := σ) (D := D) K).tau =
      factorLadderTau (σ := σ) (D := D) K :=
  rfl

/-- Every coefficient of the AR factor ladder is nonnegative.  The initial
basis term and the restricted-middle term are nonnegative by construction;
all later terms use coefficientwise positive part. -/
theorem factorLadderData_ladder_nonneg
    (K : Set ι) (x : DeletedLabel K) (n : ℕ)
    (p : DeletedLabel K) :
    0 ≤
      (factorLadderData (σ := σ) (D := D) K).ladder x n p := by
  cases n with
  | zero =>
      classical
      by_cases h : p = x
      · simp [FactorLadder.basis, h]
      · simp [FactorLadder.basis, h]
  | succ n =>
      cases n with
      | zero =>
          change 0 ≤
            (factorLadderData (σ := σ) (D := D) K).ladder x 1 p
          rw [FactorLadder.Data.ladder_one,
            factorLadderData_theta,
            factorLadderTheta_basis_apply]
          exact deletedMiddleMultiplicity_nonneg
            (σ := σ) (D := D) K x p
      | succ n =>
          exact
            FactorLadder.Data.ladder_nonneg_of_two_le
              (factorLadderData (σ := σ) (D := D) K)
              x (by omega) p

/-- The restricted translation operator preserves coefficientwise
nonnegativity. -/
theorem factorLadderTau_apply_nonneg
    (K : Set ι) (v : FactorLadder.IntVector (DeletedLabel K))
    (hv : ∀ x, 0 ≤ v x) (p : DeletedLabel K) :
    0 ≤ factorLadderTau (σ := σ) (D := D) K v p := by
  classical
  rw [factorLadderTau, FactorLadder.matrixAddHom_apply]
  apply Finset.sum_nonneg
  intro x _
  apply mul_nonneg (hv x)
  by_cases hx :
      factorLadderTauTarget (σ := σ) (D := D) K x = some p
  · simp [factorLadderTauEntry, hx]
  · simp [factorLadderTauEntry, hx]

/-- A positive coefficient in an AR factor ladder lies on an irreducible
path, inside the deleted labels, from that coefficient's label to the
starting label. -/
theorem factorLadderData_ladder_pos_reflTransGen_irreducible
    (K : Set ι) (x p : DeletedLabel K) (n : ℕ)
    (hpos : 0 <
      (factorLadderData (σ := σ) (D := D) K).ladder x n p) :
    Relation.ReflTransGen
      (fun y z : DeletedLabel K ↦
        HasIrreducibleMorphism (σ.obj y.1) (σ.obj z.1))
      p x := by
  classical
  induction n using Nat.strong_induction_on generalizing p with
  | h n ih =>
      rcases n with _ | n
      · rw [FactorLadder.Data.ladder_zero] at hpos
        have hp : p = x := by
          by_contra hne
          rw [FactorLadder.basis_apply_of_ne hne] at hpos
          omega
        subst p
        exact Relation.ReflTransGen.refl
      · rcases n with _ | n
        · rw [FactorLadder.Data.ladder_one,
            factorLadderData_theta,
            factorLadderTheta_basis_apply] at hpos
          exact Relation.ReflTransGen.single <|
            (deletedMiddleMultiplicity_pos_iff_irreducible
              (σ := σ) (D := D) K x p).1 hpos
        · rw [FactorLadder.Data.ladder_add_two] at hpos
          simp only [FactorLadder.positivePart_apply] at hpos
          have htau : 0 ≤
              (factorLadderData (σ := σ) (D := D) K).tau
                ((factorLadderData (σ := σ) (D := D) K).ladder
                  x n) p := by
            rw [factorLadderData_tau]
            exact factorLadderTau_apply_nonneg (σ := σ) (D := D)
              K _
                (fun y ↦ factorLadderData_ladder_nonneg
                  (σ := σ) D K x n y) p
          have htheta : 0 <
              (factorLadderData (σ := σ) (D := D) K).theta
                ((factorLadderData (σ := σ) (D := D) K).ladder
                  x (n + 1)) p := by
            change 0 < max
              ((factorLadderData (σ := σ) (D := D) K).theta
                  ((factorLadderData (σ := σ) (D := D) K).ladder
                    x (n + 1)) p -
                (factorLadderData (σ := σ) (D := D) K).tau
                  ((factorLadderData (σ := σ) (D := D) K).ladder
                    x n) p) 0 at hpos
            omega
          rw [factorLadderData_theta, factorLadderTheta,
            FactorLadder.matrixAddHom_apply] at htheta
          have hterms : ∀ y ∈ (Finset.univ : Finset (DeletedLabel K)),
              0 ≤
                (factorLadderData (σ := σ) (D := D) K).ladder
                    x (n + 1) y *
                  deletedMiddleMultiplicity (σ := σ) (D := D)
                    K y p := by
            intro y _
            exact mul_nonneg
              (factorLadderData_ladder_nonneg
                (σ := σ) D K x (n + 1) y)
              (deletedMiddleMultiplicity_nonneg
                (σ := σ) D K y p)
          rw [Finset.sum_pos_iff_of_nonneg hterms] at htheta
          obtain ⟨y, _, hypos⟩ := htheta
          rcases mul_pos_iff.mp hypos with hy | hy
          · exact Relation.ReflTransGen.head
              ((deletedMiddleMultiplicity_pos_iff_irreducible
                (σ := σ) (D := D) K y p).1 hy.2)
              (ih (n + 1) (by omega) y hy.1)
          · exact False.elim <|
              (not_lt_of_ge
                (factorLadderData_ladder_nonneg
                  (σ := σ) D K x (n + 1) y)) hy.1

end FiniteARTranslationData

section FiniteDimensional

variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
  [FiniteDimensional k R] [IsNoetherianRing R]
  {ι : Type v} [Fintype ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)

/-- Paper-facing finite-dimensional specialization: the module category
constructs the AR datum, hence the factor-ladder operators, automatically. -/
def finiteDimensionalFactorLadderData (K : Set ι) :
    FactorLadder.Data (DeletedLabel K) :=
  FiniteARTranslationData.factorLadderData
    (σ := σ) (D := σ.finiteDimensionalARTranslationData k R) K

end FiniteDimensional

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
