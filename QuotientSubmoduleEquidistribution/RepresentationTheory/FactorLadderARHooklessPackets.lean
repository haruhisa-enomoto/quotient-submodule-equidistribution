import QuotientSubmoduleEquidistribution.RepresentationTheory.FactorLadderARHook
import QuotientSubmoduleEquidistribution.RepresentationTheory.FactorLadderHooklessPackets

/-!
# AR-quiver realization of the hookless four-vertex packets

This file records rows `F` and `T` of the manuscript as literal retained
Auslander--Reiten configurations and turns their predecessor and translation
conditions into the numerical packet data for the factor-ladder recursion.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe u v

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} [Fintype ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)

/-- `y` and `z` are exactly the two retained predecessors of `x`. -/
def HasExactlyTwoDeletedPredecessors (K : Set ι)
    (x y z : DeletedLabel K) : Prop :=
  y ≠ z ∧
    HasIrreducibleMorphism (σ.obj y.1) (σ.obj x.1) ∧
    HasIrreducibleMorphism (σ.obj z.1) (σ.obj x.1) ∧
    ∀ w : DeletedLabel K,
      HasIrreducibleMorphism (σ.obj w.1) (σ.obj x.1) →
        w = y ∨ w = z

namespace FiniteARTranslationData

variable (AR : σ.FiniteARTranslationData)

/-- With trivial retained valuations, exactly two predecessors give the
sum of their two basis vectors. -/
theorem factorLadderTheta_basis_eq_add_basis_of_exactlyTwoPredecessors
    (K : Set ι) (U : AR.HasUnitDeletedMiddleMultiplicities σ K)
    {x y z : DeletedLabel K}
    (h : HasExactlyTwoDeletedPredecessors σ K x y z) :
    factorLadderTheta (σ := σ) (D := AR) K
        (FactorLadder.basis x) =
      FactorLadder.basis y + FactorLadder.basis z := by
  classical
  funext w
  rw [factorLadderTheta_basis_apply]
  by_cases hwy : w = y
  · subst w
    rw [U x y h.2.1]
    simp [FactorLadder.basis, h.1]
  · by_cases hwz : w = z
    · subst w
      rw [U x z h.2.2.1]
      simp [FactorLadder.basis, hwy]
    · have hnotirr :
          ¬ HasIrreducibleMorphism (σ.obj w.1) (σ.obj x.1) := by
        intro hirr
        rcases h.2.2.2 w hirr with hw | hw
        · exact hwy hw
        · exact hwz hw
      have hnotpos :
          ¬ 0 < deletedMiddleMultiplicity
            (σ := σ) (D := AR) K x w :=
        (deletedMiddleMultiplicity_pos_iff_irreducible
          (σ := σ) (D := AR) K x w).not.mpr hnotirr
      have hnonneg := deletedMiddleMultiplicity_nonneg
        (σ := σ) (D := AR) K x w
      have hzero : deletedMiddleMultiplicity
          (σ := σ) (D := AR) K x w = 0 := by
        omega
      rw [hzero]
      simp [FactorLadder.basis, hwy, hwz]

/-- A retained ordinary translate and any retained middle predecessor give
the corresponding restricted translation basis vector. -/
theorem factorLadderTau_basis_eq_basis_of_translation_eq
    (K : Set ι) (x y w : DeletedLabel K)
    (hx : ¬ Projective (σ.obj x.1))
    (hxy : (AR.arTranslation σ ⟨x.1, hx⟩).1 = y.1)
    (hwx : HasIrreducibleMorphism (σ.obj w.1) (σ.obj x.1)) :
    factorLadderTau (σ := σ) (D := AR) K
        (FactorLadder.basis x) = FactorLadder.basis y := by
  have htheta : factorLadderTheta (σ := σ) (D := AR) K
      (FactorLadder.basis x) ≠ 0 := by
    intro hzero
    have hcoord := congrFun hzero w
    rw [factorLadderTheta_basis_apply, Pi.zero_apply] at hcoord
    have hpos :=
      (deletedMiddleMultiplicity_pos_iff_irreducible
        (σ := σ) (D := AR) K x w).2 hwx
    omega
  have htarget := AR.factorLadderTauTarget_eq_some σ K x hx (by
    rw [hxy]
    exact y.2) htheta
  have htranslated :
      (⟨(AR.arTranslation σ ⟨x.1, hx⟩).1, by
          rw [hxy]
          exact y.2⟩ : DeletedLabel K) = y :=
    Subtype.ext hxy
  apply AR.factorLadderTau_basis_eq_basis_of_target_eq_some σ K x y
  simpa only [htranslated] using htarget

/-- Row `F` of the manuscript's hookless packet list. -/
@[ext]
structure FixedPacket (K : Set ι) where
  p : DeletedLabel K
  a : DeletedLabel K
  c : DeletedLabel K
  z : DeletedLabel K
  p_projective : Projective (σ.obj p.1)
  a_nonprojective : ¬ Projective (σ.obj a.1)
  c_nonprojective : ¬ Projective (σ.obj c.1)
  z_nonprojective : ¬ Projective (σ.obj z.1)
  p_to_a : HasIrreducibleMorphism (σ.obj p.1) (σ.obj a.1)
  c_to_a : HasIrreducibleMorphism (σ.obj c.1) (σ.obj a.1)
  predecessor_z : HasUniqueDeletedPredecessor σ K z c
  predecessor_c : HasExactlyTwoDeletedPredecessors σ K c a z
  tau_z : (AR.arTranslation σ ⟨z.1, z_nonprojective⟩).1 = a.1
  tau_c : (AR.arTranslation σ ⟨c.1, c_nonprojective⟩).1 = c.1
  tau_a_eq_z_or_mem :
    (AR.arTranslation σ ⟨a.1, a_nonprojective⟩).1 = z.1 ∨
      (AR.arTranslation σ ⟨a.1, a_nonprojective⟩).1 ∈ K
  p_not_to_z : ¬ HasIrreducibleMorphism (σ.obj p.1) (σ.obj z.1)

noncomputable instance fixedPacketFinite (K : Set ι) :
    Finite (AR.FixedPacket σ K) :=
  Finite.of_injective
    (fun F ↦ (F.p, F.a, F.c, F.z)) (by
      intro F₁ F₂ h
      ext
      · exact congrArg Subtype.val (congrArg (fun q ↦ q.1) h)
      · exact congrArg Subtype.val (congrArg (fun q ↦ q.2.1) h)
      · exact congrArg Subtype.val (congrArg (fun q ↦ q.2.2.1) h)
      · exact congrArg Subtype.val (congrArg (fun q ↦ q.2.2.2) h))

namespace FixedPacket

variable {AR : σ.FiniteARTranslationData} {K : Set ι}
  (F : AR.FixedPacket σ K)

/-- An actual row-`F` AR configuration supplies the numerical fixed packet
when retained irreducible multiplicities are one. -/
def killedFixedPacket (U : AR.HasUnitDeletedMiddleMultiplicities σ K) :
    (AR.factorLadderData σ K).KilledFixedPacket
      (deletedProjectiveSet σ K) where
  p := F.p
  a := F.a
  c := F.c
  z := F.z
  theta_z := by
    simpa using AR.factorLadderTheta_basis_eq_basis_of_uniquePredecessor
      σ K U F.predecessor_z
  theta_c := by
    simpa using
      AR.factorLadderTheta_basis_eq_add_basis_of_exactlyTwoPredecessors
        σ K U F.predecessor_c
  tau_z := by
    rw [factorLadderData_tau]
    exact AR.factorLadderTau_basis_eq_basis_of_translation_eq
      σ K F.z F.a F.c F.z_nonprojective F.tau_z
        F.predecessor_z.1
  tau_c := by
    rw [factorLadderData_tau]
    exact AR.factorLadderTau_basis_eq_basis_of_translation_eq
      σ K F.c F.c F.a F.c_nonprojective F.tau_c
        F.predecessor_c.2.1
  p_mem := F.p_projective
  c_not_mem := F.c_nonprojective
  z_not_mem := F.z_nonprojective

/-- Over an algebraically closed ground field, row `F` automatically gives
the terminating numerical fixed packet. -/
def killedFixedPacketOfIsAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k]
    [Algebra k R] [FiniteDimensional k R] :
    (AR.factorLadderData σ K).KilledFixedPacket
      (deletedProjectiveSet σ K) :=
  F.killedFixedPacket σ
    (AR.hasUnitDeletedMiddleMultiplicities_of_isAlgClosed
      (k := k) (R := R) σ K)

/-- An actual row-`F` configuration cannot reach a retained projective in
the forward factor ladder. -/
theorem not_reachesBoundary_of_isAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k]
    [Algebra k R] [FiniteDimensional k R] :
    ¬ (AR.factorLadderData σ K).ReachesBoundary
      (deletedProjectiveSet σ K) F.z :=
  (F.killedFixedPacketOfIsAlgClosed (k := k) σ).not_reachesBoundary

end FixedPacket

/-- Row `T` of the manuscript's hookless packet list. -/
@[ext]
structure TrianglePacket (K : Set ι) where
  p : DeletedLabel K
  A₁ : DeletedLabel K
  A₂ : DeletedLabel K
  x : DeletedLabel K
  p_projective : Projective (σ.obj p.1)
  A₁_nonprojective : ¬ Projective (σ.obj A₁.1)
  A₂_nonprojective : ¬ Projective (σ.obj A₂.1)
  x_nonprojective : ¬ Projective (σ.obj x.1)
  A₁_to_p : HasIrreducibleMorphism (σ.obj A₁.1) (σ.obj p.1)
  predecessor_A₁ : HasUniqueDeletedPredecessor σ K A₁ A₂
  predecessor_A₂ : HasExactlyTwoDeletedPredecessors σ K A₂ p x
  predecessor_x : HasUniqueDeletedPredecessor σ K x A₁
  tau_A₁ :
    (AR.arTranslation σ ⟨A₁.1, A₁_nonprojective⟩).1 = p.1
  tau_A₂ :
    (AR.arTranslation σ ⟨A₂.1, A₂_nonprojective⟩).1 = A₁.1
  tau_x_mem :
    (AR.arTranslation σ ⟨x.1, x_nonprojective⟩).1 ∈ K

noncomputable instance trianglePacketFinite (K : Set ι) :
    Finite (AR.TrianglePacket σ K) :=
  Finite.of_injective
    (fun T ↦ (T.p, T.A₁, T.A₂, T.x)) (by
      intro T₁ T₂ h
      ext
      · exact congrArg Subtype.val (congrArg (fun q ↦ q.1) h)
      · exact congrArg Subtype.val (congrArg (fun q ↦ q.2.1) h)
      · exact congrArg Subtype.val (congrArg (fun q ↦ q.2.2.1) h)
      · exact congrArg Subtype.val (congrArg (fun q ↦ q.2.2.2) h))

namespace TrianglePacket

variable {AR : σ.FiniteARTranslationData} {K : Set ι}
  (T : AR.TrianglePacket σ K)

/-- An actual row-`T` AR configuration supplies the numerical triangle
packet when retained irreducible multiplicities are one. -/
def killedTrianglePacket (U : AR.HasUnitDeletedMiddleMultiplicities σ K) :
    (AR.factorLadderData σ K).KilledTrianglePacket
      (deletedProjectiveSet σ K) where
  p := T.p
  A₁ := T.A₁
  A₂ := T.A₂
  x := T.x
  theta_x := by
    simpa using AR.factorLadderTheta_basis_eq_basis_of_uniquePredecessor
      σ K U T.predecessor_x
  theta_A₁ := by
    simpa using AR.factorLadderTheta_basis_eq_basis_of_uniquePredecessor
      σ K U T.predecessor_A₁
  theta_A₂ := by
    simpa using
      AR.factorLadderTheta_basis_eq_add_basis_of_exactlyTwoPredecessors
        σ K U T.predecessor_A₂
  tau_x := by
    rw [factorLadderData_tau]
    apply AR.factorLadderTau_basis_eq_zero_of_target_eq_none σ K T.x
    exact AR.factorLadderTauTarget_eq_none_of_translation_mem
      σ K T.x T.x_nonprojective T.tau_x_mem
  tau_A₁ := by
    rw [factorLadderData_tau]
    exact AR.factorLadderTau_basis_eq_basis_of_translation_eq
      σ K T.A₁ T.p T.A₂ T.A₁_nonprojective T.tau_A₁
        T.predecessor_A₁.1
  tau_A₂ := by
    rw [factorLadderData_tau]
    exact AR.factorLadderTau_basis_eq_basis_of_translation_eq
      σ K T.A₂ T.A₁ T.p T.A₂_nonprojective T.tau_A₂
        T.predecessor_A₂.2.1
  p_mem := T.p_projective
  A₁_not_mem := T.A₁_nonprojective
  A₂_not_mem := T.A₂_nonprojective
  x_not_mem := T.x_nonprojective

/-- Over an algebraically closed ground field, row `T` automatically gives
the terminating numerical triangle packet. -/
def killedTrianglePacketOfIsAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k]
    [Algebra k R] [FiniteDimensional k R] :
    (AR.factorLadderData σ K).KilledTrianglePacket
      (deletedProjectiveSet σ K) :=
  T.killedTrianglePacket σ
    (AR.hasUnitDeletedMiddleMultiplicities_of_isAlgClosed
      (k := k) (R := R) σ K)

/-- An actual row-`T` configuration cannot reach a retained projective in
the forward factor ladder. -/
theorem not_reachesBoundary_of_isAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k]
    [Algebra k R] [FiniteDimensional k R] :
    ¬ (AR.factorLadderData σ K).ReachesBoundary
      (deletedProjectiveSet σ K) T.x :=
  (T.killedTrianglePacketOfIsAlgClosed (k := k) σ).not_reachesBoundary

end TrianglePacket

end FiniteARTranslationData

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
