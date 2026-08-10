import OpConjecture.RepresentationTheory.SingleCrossRadicalNormalForm
import OpConjecture.RepresentationTheory.PeirceCotangentExtDimension

/-!
# A unique cross Ext arrow forces the single-cross radical normal form

Exact Peirce-cotangent--Ext dimensions turn a unique cross Ext--Gabriel arrow
into the sole nonzero cotangent corner.  The corresponding representative
then generates a one-dimensional square-zero Jacobson radical.  This is a
general categorical-to-ring bridge and uses no concrete algebra or module
classification.
-/

noncomputable section

namespace OpConjecture.QuotientSurvival.TwoCoordinateData

open OpConjecture.GabrielArrowBridge

universe u v

variable {K B : Type u} {kappa : Type v}
  [Field K] [Ring B] [Algebra K B]
  [IsArtinianRing B] [FiniteDimensional K B]
  [Small.{u} Bᵐᵒᵖ] [IsNoetherianRing Bᵐᵒᵖ]

variable (D : OpConjecture.QuotientSurvival.TwoCoordinateData
  (K := K) (B := B))
variable (tau : OpConjecture.IndecomposableSkeleton.{u, v, u}
  Bᵐᵒᵖ kappa)

omit [IsArtinianRing B] [FiniteDimensional K B] in
/-- Vanishing of all simple self-Ext spaces makes every multiplicity-bearing
Ext--Gabriel arrow a cross arrow. -/
theorem extGabrielArrow_source_ne_target_of_selfExt_subsingleton
    (hNoSelf : ∀ s : tau.SimpleIndex, Subsingleton (ExtOne tau s s))
    (a : ExtGabrielArrowIndex (K := K) tau) :
    ExtGabrielArrowIndex.source tau a ≠
      ExtGabrielArrowIndex.target tau a := by
  intro hst
  rcases a with ⟨s, t, n⟩
  change s = t at hst
  subst t
  letI : Subsingleton (ExtOne tau s s) := hNoSelf s
  have hzero : Module.finrank K (ExtOne tau s s) = 0 :=
    Module.finrank_zero_of_subsingleton
  have hpos : 0 < Module.finrank K (ExtOne tau s s) :=
    lt_of_le_of_lt (Nat.zero_le n.1) n.2
  omega

/-- A unique cross Ext--Gabriel arrow determines the sole nonzero Peirce
cotangent corner, the global cotangent bound, and an orientation-independent
single-cross radical normal form. -/
theorem uniqueCrossExtArrow_singleCrossRadicalData
    (a : ExtGabrielArrowIndex (K := K) tau)
    (hCard : Nat.card (ExtGabrielArrowIndex (K := K) tau) = 1)
    (hCross : ExtGabrielArrowIndex.source tau a ≠
      ExtGabrielArrowIndex.target tau a) :
    let E :=
      OpConjecture.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
        D tau
    let i := E.symm (ExtGabrielArrowIndex.source tau a)
    let j := E.symm (ExtGabrielArrowIndex.target tau a)
    i ≠ j ∧
      Module.finrank K (D.jacobsonCotangentCornerSubmodule i j) = 1 ∧
      (∀ p q : Fin 2, (p, q) ≠ (i, j) →
        Module.finrank K (D.jacobsonCotangentCornerSubmodule p q) = 0) ∧
      Module.finrank K
          (OpConjecture.QuotientSurvival.jacobsonCotangentSubmodule
            (K := K) (B := B)) ≤ 1 ∧
      ∃ c : B,
        c ∈ Ring.jacobson B ∧
        D.liftedCoordinate i * c = c ∧
        c * D.liftedCoordinate j = c ∧
        c ∉ (Ring.jacobson B) ^ 2 ∧
        OpConjecture.QuotientSurvival.JacobsonCotangentSpannedBy
          (K := K) (0 : B) c 0 ∧
        SingleCrossRadicalData (K := K) c := by
  classical
  let E :=
    OpConjecture.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
      D tau
  let i := E.symm (ExtGabrielArrowIndex.source tau a)
  let j := E.symm (ExtGabrielArrowIndex.target tau a)
  have hij : i ≠ j := by
    intro h
    apply hCross
    exact E.symm.injective h
  have hUnique := Nat.card_eq_one_iff_unique.mp hCard
  letI : Subsingleton (ExtGabrielArrowIndex (K := K) tau) := hUnique.1
  have hArrowDim :
      Module.finrank K
          (ExtOne tau
            (ExtGabrielArrowIndex.source tau a)
            (ExtGabrielArrowIndex.target tau a)) = 1 := by
    rcases a with ⟨s, t, n⟩
    change Module.finrank K (ExtOne tau s t) = 1
    have hpos : 0 < Module.finrank K (ExtOne tau s t) :=
      lt_of_le_of_lt (Nat.zero_le n.1) n.2
    have hle : Module.finrank K (ExtOne tau s t) ≤ 1 := by
      by_contra hnot
      have hone : 1 < Module.finrank K (ExtOne tau s t) := by omega
      let a0 : ExtGabrielArrowIndex (K := K) tau :=
        ⟨s, t, ⟨0, hpos⟩⟩
      let a1 : ExtGabrielArrowIndex (K := K) tau :=
        ⟨s, t, ⟨1, hone⟩⟩
      have heq : a0 = a1 := Subsingleton.elim _ _
      have hn := congrArg
        (fun x : ExtGabrielArrowIndex (K := K) tau ↦ (x.2.2 : Nat)) heq
      norm_num [a0, a1] at hn
    omega
  have hCornerOne :
      Module.finrank K (D.jacobsonCotangentCornerSubmodule i j) = 1 := by
    rw [D.finrank_jacobsonCotangentCornerSubmodule_eq_alignedExt tau i j]
    change Module.finrank K (ExtOne tau (E i) (E j)) = 1
    rw [show E i = ExtGabrielArrowIndex.source tau a from
        E.apply_symm_apply _,
      show E j = ExtGabrielArrowIndex.target tau a from
        E.apply_symm_apply _]
    exact hArrowDim
  have hCornerZero : ∀ p q : Fin 2, (p, q) ≠ (i, j) →
      Module.finrank K (D.jacobsonCotangentCornerSubmodule p q) = 0 := by
    intro p q hpq
    rw [D.finrank_jacobsonCotangentCornerSubmodule_eq_alignedExt tau p q]
    let s := E p
    let t := E q
    by_contra hne
    have hpos : 0 < Module.finrank K (ExtOne tau s t) :=
      Nat.pos_of_ne_zero hne
    let b : ExtGabrielArrowIndex (K := K) tau :=
      ⟨s, t, ⟨0, hpos⟩⟩
    have hba : b = a := Subsingleton.elim _ _
    apply hpq
    have hs := congrArg (ExtGabrielArrowIndex.source tau) hba
    have ht := congrArg (ExtGabrielArrowIndex.target tau) hba
    change E p = ExtGabrielArrowIndex.source tau a at hs
    change E q = ExtGabrielArrowIndex.target tau a at ht
    have hp : p = i := by
      calc
        p = E.symm (E p) := (E.symm_apply_apply p).symm
        _ = E.symm (ExtGabrielArrowIndex.source tau a) := by
          exact congrArg E.symm hs
        _ = i := rfl
    have hq : q = j := by
      calc
        q = E.symm (E q) := (E.symm_apply_apply q).symm
        _ = E.symm (ExtGabrielArrowIndex.target tau a) := by
          exact congrArg E.symm ht
        _ = j := rfl
    exact Prod.ext hp hq
  have hTotal :
      Module.finrank K
          (OpConjecture.QuotientSurvival.jacobsonCotangentSubmodule
            (K := K) (B := B)) ≤ 1 := by
    have hbound := D.finrank_jacobsonCotangentSubmodule_le_sum_corners
    have hsum :
        (∑ p : Fin 2, ∑ q : Fin 2,
          Module.finrank K (D.jacobsonCotangentCornerSubmodule p q)) = 1 := by
      calc
        (∑ p : Fin 2, ∑ q : Fin 2,
            Module.finrank K (D.jacobsonCotangentCornerSubmodule p q)) =
            ∑ q : Fin 2,
              Module.finrank K (D.jacobsonCotangentCornerSubmodule i q) := by
          apply Finset.sum_eq_single i
          · intro p _ hpi
            apply Finset.sum_eq_zero
            intro q _
            apply hCornerZero p q
            intro hpq
            exact hpi (congrArg Prod.fst hpq)
          · simp
        _ = Module.finrank K
              (D.jacobsonCotangentCornerSubmodule i j) := by
          apply Finset.sum_eq_single j
          · intro q _ hqj
            apply hCornerZero i q
            intro hpq
            exact hqj (congrArg Prod.snd hpq)
          · simp
        _ = 1 := hCornerOne
    calc
      Module.finrank K
          (OpConjecture.QuotientSurvival.jacobsonCotangentSubmodule
            (K := K) (B := B)) ≤
          (Module.finrank K (D.jacobsonCotangentCornerSubmodule 0 0) +
            Module.finrank K (D.jacobsonCotangentCornerSubmodule 0 1)) +
          (Module.finrank K (D.jacobsonCotangentCornerSubmodule 1 0) +
            Module.finrank K (D.jacobsonCotangentCornerSubmodule 1 1)) := hbound
      _ = 1 := by simpa [Fin.sum_univ_two] using hsum
  obtain ⟨c, hcJ, hcL, hcR, hc2⟩ :=
    OpConjecture.CoordinateGabrielRealization.exists_extArrow_bicorner_cotangent_representative
      D tau a
  have hspan :
      OpConjecture.QuotientSurvival.JacobsonCotangentSpannedBy
        (K := K) (0 : B) c 0 :=
    jacobsonCotangentSpannedBy_single_of_finrank_le_one
      hcJ hc2 hTotal
  have hnormal : SingleCrossRadicalData (K := K) c :=
    D.singleCrossRadicalData_of_cotangentSpanned_at hij hcL hcR hspan
  exact ⟨hij, hCornerOne, hCornerZero, hTotal,
    c, hcJ, hcL, hcR, hc2, hspan, hnormal⟩

end OpConjecture.QuotientSurvival.TwoCoordinateData
