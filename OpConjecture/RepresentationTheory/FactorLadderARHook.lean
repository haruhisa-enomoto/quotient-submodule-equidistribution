import OpConjecture.RepresentationTheory.FactorLadderARData
import OpConjecture.RepresentationTheory.FactorLadderHook
import OpConjecture.RepresentationTheory.FactorHomRealization
import OpConjecture.RepresentationTheory.AlgebraicallyClosedIrreducibleMultiplicityOne

/-!
# AR-quiver hooks as killed factor ladders

This file gives the exact bridge from the manuscript's hook vocabulary to
the numerical factor-ladder hook.  The only valuation input is stated
explicitly: every retained irreducible middle summand has multiplicity one.
That is the point at which the algebraically closed-field hypothesis of the
four-vertex appendix enters.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace OpConjecture.IndecomposableSkeleton

universe u v

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} [Fintype ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)

/-- `y` is the unique retained predecessor of `x` in the induced deleted
AR quiver. -/
def HasUniqueDeletedPredecessor (K : Set ι)
    (x y : DeletedLabel K) : Prop :=
  HasIrreducibleMorphism (σ.obj y.1) (σ.obj x.1) ∧
    ∀ z : DeletedLabel K,
      HasIrreducibleMorphism (σ.obj z.1) (σ.obj x.1) → z = y

namespace FiniteARTranslationData

variable (AR : σ.FiniteARTranslationData)

/-- Trivial valuation on all irreducible arrows retained in the deleted
support. -/
def HasUnitDeletedMiddleMultiplicities (K : Set ι) : Prop :=
  ∀ x y : DeletedLabel K,
    HasIrreducibleMorphism (σ.obj y.1) (σ.obj x.1) →
      deletedMiddleMultiplicity (σ := σ) (D := AR) K x y = 1

/-- Representation-finiteness over an algebraically closed field supplies
the trivial retained valuation required by every factor-ladder hook. -/
theorem hasUnitDeletedMiddleMultiplicities_of_isAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k]
    [Algebra k R] [FiniteDimensional k R]
    (K : Set ι) : AR.HasUnitDeletedMiddleMultiplicities σ K := by
  classical
  intro x y hirr
  let A := factorLadderRightARAt σ AR x.1
  letI : Fintype A.index := FintypeCat.fintype
  have hinj : Function.Injective A.label :=
    σ.rightARLabel_injective_of_finiteARTranslationData_of_isAlgClosed
      (K := k) (R := R) AR A
  obtain ⟨t, ht⟩ :=
    (A.summandIrreducibleCorrespondence y.1).2 hirr
  change (((Finset.univ.filter fun s : A.index ↦
    A.label s = y.1).card : ℕ) : ℤ) = 1
  have hfilter :
      Finset.univ.filter (fun s : A.index ↦ A.label s = y.1) =
        {t} := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · intro hs
      exact hinj (hs.trans ht.symm)
    · intro hs
      subst s
      exact ht
  rw [hfilter]
  simp

/-- A hook in the manuscript's full hook family `H(D)`.  Its first vertex
need not be projective; this is what permits two consecutive hooks on a
four-vertex support. -/
@[ext]
structure AdmissibleHook (K : Set ι) where
  a : DeletedLabel K
  u : DeletedLabel K
  b : DeletedLabel K
  u_nonprojective : ¬ Projective (σ.obj u.1)
  b_nonprojective : ¬ Projective (σ.obj b.1)
  predecessor_u : HasUniqueDeletedPredecessor σ K u a
  predecessor_b : HasUniqueDeletedPredecessor σ K b u
  tau_b : (AR.arTranslation σ ⟨b.1, b_nonprojective⟩).1 = a.1

noncomputable instance admissibleHookFinite (K : Set ι) :
    Finite (AR.AdmissibleHook σ K) :=
  Finite.of_injective
    (fun H ↦ (H.a, H.u, H.b)) (by
      intro H₁ H₂ h
      ext
      · exact congrArg Subtype.val (congrArg (fun q ↦ q.1) h)
      · exact congrArg Subtype.val (congrArg (fun q ↦ q.2.1) h)
      · exact congrArg Subtype.val (congrArg (fun q ↦ q.2.2) h))

/-- A manuscript hook `(a,u,b)` inside the deleted support. -/
structure QuotientHook (K : Set ι) where
  a : DeletedLabel K
  u : DeletedLabel K
  b : DeletedLabel K
  a_projective : Projective (σ.obj a.1)
  u_nonprojective : ¬ Projective (σ.obj u.1)
  b_nonprojective : ¬ Projective (σ.obj b.1)
  predecessor_u : HasUniqueDeletedPredecessor σ K u a
  predecessor_b : HasUniqueDeletedPredecessor σ K b u
  tau_b : (AR.arTranslation σ ⟨b.1, b_nonprojective⟩).1 = a.1

/-- Forget that the first vertex of a killed hook is projective. -/
def QuotientHook.toAdmissibleHook {K : Set ι}
    (H : AR.QuotientHook σ K) : AR.AdmissibleHook σ K where
  a := H.a
  u := H.u
  b := H.b
  u_nonprojective := H.u_nonprojective
  b_nonprojective := H.b_nonprojective
  predecessor_u := H.predecessor_u
  predecessor_b := H.predecessor_b
  tau_b := H.tau_b

/-- A unique retained predecessor has basis-vector middle term when all
retained irreducible multiplicities are one. -/
theorem factorLadderTheta_basis_eq_basis_of_uniquePredecessor
    (K : Set ι) (U : AR.HasUnitDeletedMiddleMultiplicities σ K)
    {x y : DeletedLabel K}
    (hxy : HasUniqueDeletedPredecessor σ K x y) :
    factorLadderTheta (σ := σ) (D := AR) K
        (FactorLadder.basis x) = FactorLadder.basis y := by
  classical
  funext z
  rw [factorLadderTheta_basis_apply]
  by_cases hzy : z = y
  · subst z
    rw [U x y hxy.1]
    simp
  · have hnotirr :
        ¬ HasIrreducibleMorphism (σ.obj z.1) (σ.obj x.1) := by
      intro hirr
      exact hzy (hxy.2 z hirr)
    have hnotpos :
        ¬ 0 < deletedMiddleMultiplicity
          (σ := σ) (D := AR) K x z :=
      (deletedMiddleMultiplicity_pos_iff_irreducible
        (σ := σ) (D := AR) K x z).not.mpr hnotirr
    have hnonneg :=
      deletedMiddleMultiplicity_nonneg
        (σ := σ) (D := AR) K x z
    have hzero :
        deletedMiddleMultiplicity (σ := σ) (D := AR) K x z = 0 := by
      omega
    rw [hzero]
    exact (FactorLadder.basis_apply_of_ne hzy).symm

namespace AdmissibleHook

variable {AR : σ.FiniteARTranslationData} {K : Set ι}
  (H : AR.AdmissibleHook σ K)

/-- A graph-theoretic hook with trivial retained valuations supplies the
exact numerical killed-hook data for the AR factor ladder. -/
def killedHook (U : AR.HasUnitDeletedMiddleMultiplicities σ K) :
    (AR.factorLadderData σ K).KilledHook
      (deletedProjectiveSet σ K) := by
  let hthetaB := AR.factorLadderTheta_basis_eq_basis_of_uniquePredecessor
    σ K U H.predecessor_b
  let hthetaU := AR.factorLadderTheta_basis_eq_basis_of_uniquePredecessor
    σ K U H.predecessor_u
  have hthetaBNonzero :
      factorLadderTheta (σ := σ) (D := AR) K
          (FactorLadder.basis H.b) ≠ 0 := by
    rw [hthetaB]
    intro hzero
    have hcoord := congrFun hzero H.u
    have hone : (1 : ℤ) = 0 := by
      simpa only [FactorLadder.basis_apply_self, Pi.zero_apply] using hcoord
    exact one_ne_zero hone
  have htauDeleted :
      (AR.arTranslation σ ⟨H.b.1, H.b_nonprojective⟩).1 ∉ K := by
    rw [H.tau_b]
    exact H.a.2
  have htarget := AR.factorLadderTauTarget_eq_some σ K H.b
    H.b_nonprojective htauDeleted hthetaBNonzero
  have htranslated :
      (⟨(AR.arTranslation σ
          ⟨H.b.1, H.b_nonprojective⟩).1, htauDeleted⟩ :
        DeletedLabel K) = H.a :=
    Subtype.ext H.tau_b
  have htargetA :
      factorLadderTauTarget (σ := σ) (D := AR) K H.b =
        some H.a := by
    simpa only [htranslated] using htarget
  exact
    { a := H.a
      u := H.u
      b := H.b
      theta_b := by simpa using hthetaB
      theta_u := by simpa using hthetaU
      tau_b := by
        rw [factorLadderData_tau]
        exact AR.factorLadderTau_basis_eq_basis_of_target_eq_some
          σ K H.b H.a htargetA
      tau_u_nonneg := by
        intro d
        rw [factorLadderData_tau]
        apply AR.factorLadderTau_apply_nonneg σ K
        intro z
        classical
        by_cases hzu : z = H.u
        · subst z
          simp
        · simp [FactorLadder.basis_apply_of_ne hzu]
      u_not_mem := H.u_nonprojective
      b_not_mem := H.b_nonprojective }

/-- Over an algebraically closed ground field, a graph-theoretic hook
automatically supplies the exact numerical killed-hook data. -/
def killedHookOfIsAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k]
    [Algebra k R] [FiniteDimensional k R] :
    (AR.factorLadderData σ K).KilledHook
      (deletedProjectiveSet σ K) :=
  H.killedHook σ
    (AR.hasUnitDeletedMiddleMultiplicities_of_isAlgClosed σ (k := k) K)

/-- Every manuscript hook is a bad forward factor ladder. -/
theorem not_reaches_deletedProjective
    (U : AR.HasUnitDeletedMiddleMultiplicities σ K) :
    ¬ (AR.factorLadderData σ K).ReachesBoundary
      (deletedProjectiveSet σ K) H.b := by
  let KH := H.killedHook σ U
  have hb : KH.b = H.b := by rfl
  rw [← hb]
  exact KH.not_reachesBoundary

/-- Every manuscript hook is a bad forward factor ladder over an
algebraically closed ground field, without any extra valuation hypothesis. -/
theorem not_reaches_deletedProjective_of_isAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k]
    [Algebra k R] [FiniteDimensional k R] :
    ¬ (AR.factorLadderData σ K).ReachesBoundary
      (deletedProjectiveSet σ K) H.b :=
  H.not_reaches_deletedProjective σ
    (AR.hasUnitDeletedMiddleMultiplicities_of_isAlgClosed σ (k := k) K)

end AdmissibleHook

namespace QuotientHook

variable {AR : σ.FiniteARTranslationData} {K : Set ι}
  (H : AR.QuotientHook σ K)

/-- A projectively based hook inherits the numerical hook attached to its
underlying admissible occurrence. -/
def killedHook (U : AR.HasUnitDeletedMiddleMultiplicities σ K) :
    (AR.factorLadderData σ K).KilledHook
      (deletedProjectiveSet σ K) :=
  H.toAdmissibleHook.killedHook σ U

/-- Algebraically closed specialization for a projectively based hook. -/
def killedHookOfIsAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k]
    [Algebra k R] [FiniteDimensional k R] :
    (AR.factorLadderData σ K).KilledHook
      (deletedProjectiveSet σ K) :=
  H.toAdmissibleHook.killedHookOfIsAlgClosed (k := k) σ

/-- Every projectively based hook is a bad forward factor ladder. -/
theorem not_reaches_deletedProjective
    (U : AR.HasUnitDeletedMiddleMultiplicities σ K) :
    ¬ (AR.factorLadderData σ K).ReachesBoundary
      (deletedProjectiveSet σ K) H.b :=
  H.toAdmissibleHook.not_reaches_deletedProjective σ U

/-- Algebraically closed specialization for a projectively based hook. -/
theorem not_reaches_deletedProjective_of_isAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k]
    [Algebra k R] [FiniteDimensional k R] :
    ¬ (AR.factorLadderData σ K).ReachesBoundary
      (deletedProjectiveSet σ K) H.b :=
  H.toAdmissibleHook.not_reaches_deletedProjective_of_isAlgClosed
    (k := k) σ

end QuotientHook

end FiniteARTranslationData

end OpConjecture.IndecomposableSkeleton
