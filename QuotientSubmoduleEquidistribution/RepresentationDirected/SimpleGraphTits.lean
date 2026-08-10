import QuotientSubmoduleEquidistribution.RepresentationDirected.SimpleGraphRootSignReduction
import Mathlib.Tactic.Abel

/-!
# The Tits root-sign theorem for a simple graph

This file proves the missing geometric input for the simply-laced Coxeter
group of an arbitrary finite simple graph.  No finite-type, definiteness, or
classification hypothesis is used.

The proof is a length induction specialized to Coxeter exponents two and
three.  Given a non-descent `i` of `w`, remove a right descent `t`.  If `i`
and `t` are nonadjacent, commutation transports the non-descent to the shorter
element.  If they are adjacent, either both shorter roots are positive or one
more descent is removed; the length-three braid relation then supplies the
remaining non-descent.  The corresponding root calculations are respectively
`s_t alpha_i = alpha_i`, `s_t alpha_i = alpha_i + alpha_t`, and
`s_i s_t alpha_i = alpha_t`.
-/

noncomputable section

namespace QuotientSubmoduleEquidistribution.RepresentationDirected.RootSignStrategy

open SimpleGraphCoxeter WordRootProcess

universe u

variable {L : Type u} [Fintype L]

omit [Fintype L] in
private theorem simple_comm_of_ne_of_not_adj
    (G : SimpleGraph L) {i t : L} (hne : i ≠ t) (hit : ¬ G.Adj i t) :
    (system G).simple i * (system G).simple t =
      (system G).simple t * (system G).simple i := by
  have h := (system G).wordProd_braidWord_eq i t
  simpa [CoxeterSystem.braidWord, CoxeterSystem.alternatingWord,
    matrix_apply_of_ne_of_not_adj G hne hit,
    matrix_apply_of_ne_of_not_adj G hne.symm
      ((G.adj_comm t i).not.mpr hit),
    (system G).wordProd_concat, (system G).wordProd_cons,
    (system G).wordProd_singleton] using h

omit [Fintype L] in
private theorem simple_braid_of_adj
    (G : SimpleGraph L) {i t : L} (hit : G.Adj i t) :
    (system G).simple i * (system G).simple t * (system G).simple i =
      (system G).simple t * (system G).simple i * (system G).simple t := by
  have h := (system G).wordProd_braidWord_eq i t
  simpa [CoxeterSystem.braidWord, CoxeterSystem.alternatingWord,
    matrix_apply_of_adj G hit, matrix_apply_of_adj G hit.symm,
    (system G).wordProd_concat, (system G).wordProd_cons,
    (system G).wordProd_singleton, mul_assoc] using h.symm

omit [Fintype L] in
private theorem isPositive_add
    {z z' : RootLattice L} (hz : IsPositive z) (hz' : IsPositive z') :
    IsPositive (z + z') := by
  refine ⟨fun i ↦ add_nonneg (hz.1 i) (hz'.1 i), ?_⟩
  intro hzero
  apply hz.2
  funext i
  have hi := congrFun hzero i
  change z i + z' i = 0 at hi
  refine le_antisymm ?_ (hz.1 i)
  calc
    z i = -z' i := eq_neg_of_add_eq_zero_left hi
    _ ≤ 0 := neg_nonpos.mpr (hz'.1 i)

/-- Tits' length/root-sign theorem in the direction used throughout the
paper: if `i` is not a right descent of `w`, then `w alpha_i` is a positive
root.  It holds for every finite simple graph, including affine and
indefinite graphs. -/
theorem positiveRoot_of_not_isRightDescent
    (G : SimpleGraph L) (w : Group G) (i : L)
    (hnot : ¬ (system G).IsRightDescent w i) :
    IsPositive (geometricRepresentation G w (simpleRoot i)) := by
  induction hw : (system G).length w using Nat.strong_induction_on generalizing w i with
  | h n ih =>
      by_cases hwOne : w = 1
      · subst w
        simpa using simpleRoot_isPositive i
      · obtain ⟨t, htDescent⟩ := (system G).exists_rightDescent_of_ne_one hwOne
        have htLength :
            (system G).length (w * (system G).simple t) + 1 =
              (system G).length w :=
          (system G).isRightDescent_iff.mp htDescent
        have hit : i ≠ t := by
          intro hit
          subst t
          exact hnot htDescent
        let v : Group G := w * (system G).simple t
        have hvLength : (system G).length v + 1 = n := by
          simpa only [v, hw] using htLength
        have hvLt : (system G).length v < n := by omega
        have hwEq : w = v * (system G).simple t := by
          dsimp only [v]
          symm
          exact (system G).simple_mul_simple_cancel_right t
        have htNotV : ¬ (system G).IsRightDescent v t := by
          exact ((system G).isRightDescent_iff_not_isRightDescent_mul).mp htDescent
        by_cases hadj : G.Adj i t
        · by_cases hiNotV : ¬ (system G).IsRightDescent v i
          · have hvi := ih _ hvLt v i hiNotV rfl
            have hvt := ih _ hvLt v t htNotV rfl
            rw [hwEq, map_mul, LinearEquiv.mul_apply,
              geometricRepresentation_simple,
              simpleReflectionEquiv_apply,
              simpleReflection_simpleRoot_of_adj G hadj.symm,
              map_add]
            exact isPositive_add hvi hvt
          · have hiDescentV : (system G).IsRightDescent v i :=
              not_not.mp hiNotV
            let u : Group G := v * (system G).simple i
            have huLength :
                (system G).length u + 1 = (system G).length v := by
              simpa only [u] using
                (system G).isRightDescent_iff.mp hiDescentV
            have huLt : (system G).length u < n := by omega
            have hvEq : v = u * (system G).simple i := by
              dsimp only [u]
              symm
              exact (system G).simple_mul_simple_cancel_right i
            have htNotU : ¬ (system G).IsRightDescent u t := by
              intro htDescentU
              let r : Group G := u * (system G).simple t
              have hrLength :
                  (system G).length r + 1 = (system G).length u := by
                simpa only [r] using
                  (system G).isRightDescent_iff.mp htDescentU
              have hwiLength :
                  (system G).length (w * (system G).simple i) =
                    (system G).length w + 1 :=
                (system G).not_isRightDescent_iff.mp hnot
              have hprod :
                  w * (system G).simple i =
                    r * (system G).simple i * (system G).simple t := by
                rw [hwEq, hvEq]
                dsimp only [r]
                calc
                  u * (system G).simple i * (system G).simple t *
                        (system G).simple i =
                      u * ((system G).simple i * (system G).simple t *
                        (system G).simple i) := by simp only [mul_assoc]
                  _ = u * ((system G).simple t * (system G).simple i *
                        (system G).simple t) := by
                      rw [simple_braid_of_adj G hadj]
                  _ = u * (system G).simple t * (system G).simple i *
                        (system G).simple t := by simp only [mul_assoc]
              rw [hprod] at hwiLength
              have hboundOne := (system G).length_mul_le r
                ((system G).simple i)
              have hboundTwo := (system G).length_mul_le
                (r * (system G).simple i) ((system G).simple t)
              have hiSimple := (system G).length_simple i
              have htSimple := (system G).length_simple t
              omega
            have hut := ih _ huLt u t htNotU rfl
            have hinner :
                simpleReflection G i
                    (simpleReflection G t (simpleRoot i)) = simpleRoot t := by
              rw [simpleReflection_simpleRoot_of_adj G hadj.symm,
                map_add, simpleReflection_simpleRoot_self,
                simpleReflection_simpleRoot_of_adj G hadj]
              abel
            rw [hwEq, hvEq]
            simp only [map_mul, LinearEquiv.mul_apply,
              geometricRepresentation_simple, simpleReflectionEquiv_apply,
              hinner]
            exact hut
        · have hiNotV : ¬ (system G).IsRightDescent v i := by
            intro hiDescentV
            have hviLength :
                (system G).length (v * (system G).simple i) + 1 =
                  (system G).length v :=
              (system G).isRightDescent_iff.mp hiDescentV
            have hwiLength :
                (system G).length (w * (system G).simple i) =
                  (system G).length w + 1 :=
              (system G).not_isRightDescent_iff.mp hnot
            have hprod :
                w * (system G).simple i =
                  (v * (system G).simple i) * (system G).simple t := by
              rw [hwEq]
              simp only [mul_assoc]
              rw [← simple_comm_of_ne_of_not_adj G hit hadj]
            rw [hprod] at hwiLength
            have hbound := (system G).length_mul_le
              (v * (system G).simple i) ((system G).simple t)
            have hsimple := (system G).length_simple t
            omega
          have hvi := ih _ hvLt v i hiNotV rfl
          rw [hwEq, map_mul, LinearEquiv.mul_apply,
            geometricRepresentation_simple, simpleReflectionEquiv_apply,
            simpleReflection_simpleRoot_of_ne_of_not_adj G hit.symm
              ((G.adj_comm t i).not.mpr hadj)]
          exact hvi

/-- Every reduced word has positive inversion roots in the integral Tits
representation of an arbitrary finite simple graph. -/
theorem reducedWordsHavePositiveInversionRoots
    (G : SimpleGraph L) : ReducedWordsHavePositiveInversionRoots G := by
  intro Q hred x
  apply positiveRoot_of_not_isRightDescent G
  exact (isReduced_iff_hasNoPrefixRightDescents G Q).mp hred x x.isLt

/-- The unconditional global root-sign/right-descent equivalence. -/
theorem globalRootSignCompatibility
    (G : SimpleGraph L) : HasGlobalRootSignCompatibility G :=
  (reducedWordsPositive_iff_globalCompatibility G).mp
    (reducedWordsHavePositiveInversionRoots G)

/-- Every real root of an arbitrary finite simple graph is either positive
or negative. -/
theorem realRootSignDichotomy
    (G : SimpleGraph L) : HasRealRootSignDichotomy G :=
  hasRealRootSignDichotomy_of_reducedWordsPositive G
    (reducedWordsHavePositiveInversionRoots G)

/-- The graph-word reducedness criterion in its final unconditional form. -/
theorem isReduced_iff_positiveInversionRoots
    (G : SimpleGraph L) (Q : List L) :
    IsReduced G Q ↔ HasPositiveInversionRoots G Q :=
  isReduced_iff_hasPositiveInversionRoots_of_rightDescentNegativity G Q
    (rightDescentImpliesNegativeRoot_of_reducedWordsPositive G
      (reducedWordsHavePositiveInversionRoots G))

end QuotientSubmoduleEquidistribution.RepresentationDirected.RootSignStrategy
