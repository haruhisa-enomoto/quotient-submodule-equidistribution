import Mathlib.Tactic
import QuotientSubmoduleEquidistribution.ConvexGeometry.Relabeling

/-!
# Componentwise products of finite set closures

This file supplies the abstract block-product step needed by the repaired
bottom-level recurrence.  It is independent of module theory.
-/

noncomputable section

open Polynomial Set

namespace QuotientSubmoduleEquidistribution.SetClosure.ComponentwiseProduct

universe u v

variable {E : Type u} {F : Type v}

/-- The left component of a subset of a disjoint sum. -/
def leftPart (S : Set (E ⊕ F)) : Set E :=
  Sum.inl ⁻¹' S

/-- The right component of a subset of a disjoint sum. -/
def rightPart (S : Set (E ⊕ F)) : Set F :=
  Sum.inr ⁻¹' S

/-- Assemble two component subsets inside their disjoint sum. -/
def assemble (A : Set E) (B : Set F) : Set (E ⊕ F) :=
  Sum.inl '' A ∪ Sum.inr '' B

@[simp]
theorem leftPart_assemble (A : Set E) (B : Set F) :
    leftPart (assemble A B) = A := by
  ext x
  simp [leftPart, assemble]

@[simp]
theorem rightPart_assemble (A : Set E) (B : Set F) :
    rightPart (assemble A B) = B := by
  ext x
  simp [rightPart, assemble]

@[simp]
theorem assemble_parts (S : Set (E ⊕ F)) :
    assemble (leftPart S) (rightPart S) = S := by
  ext x
  cases x <;> simp [assemble, leftPart, rightPart]

/-- The closure on `E ⊕ F` obtained by closing the two components
independently. -/
def productClosure
    (c : SetClosure E) (d : SetClosure F) : SetClosure (E ⊕ F) :=
  ClosureOperator.mk'
    (fun S ↦ assemble (c (leftPart S)) (d (rightPart S)))
    (by
      intro S T hST x hx
      rcases hx with hx | hx
      · exact Or.inl
          (Set.image_mono (c.monotone (Set.preimage_mono hST)) hx)
      · exact Or.inr
          (Set.image_mono (d.monotone (Set.preimage_mono hST)) hx))
    (by
      intro S x hx
      cases x with
      | inl x =>
          exact Set.mem_union_left _
            ⟨x, c.le_closure (leftPart S) hx, rfl⟩
      | inr x =>
          exact Set.mem_union_right _
            ⟨x, d.le_closure (rightPart S) hx, rfl⟩)
    (by
      intro S
      change
        assemble
            (c (leftPart (assemble (c (leftPart S)) (d (rightPart S)))))
            (d (rightPart (assemble (c (leftPart S)) (d (rightPart S))))) ⊆
          assemble (c (leftPart S)) (d (rightPart S))
      rw [leftPart_assemble, rightPart_assemble,
        c.idempotent, d.idempotent])

@[simp]
theorem productClosure_apply
    (c : SetClosure E) (d : SetClosure F) (S : Set (E ⊕ F)) :
    productClosure c d S =
      assemble (c (leftPart S)) (d (rightPart S)) :=
  rfl

/-- A subset is closed for the componentwise product exactly when each
component is closed. -/
theorem isClosed_productClosure_iff
    (c : SetClosure E) (d : SetClosure F) (S : Set (E ⊕ F)) :
    (productClosure c d).IsClosed S ↔
      c.IsClosed (leftPart S) ∧ d.IsClosed (rightPart S) := by
  rw [ClosureOperator.isClosed_iff, c.isClosed_iff, d.isClosed_iff]
  change
    assemble (c (leftPart S)) (d (rightPart S)) = S ↔
      c (leftPart S) = leftPart S ∧
        d (rightPart S) = rightPart S
  constructor
  · intro h
    constructor
    · simpa using congrArg leftPart h
    · simpa using congrArg rightPart h
  · rintro ⟨hc, hd⟩
    calc
      assemble (c (leftPart S)) (d (rightPart S)) =
          assemble (leftPart S) (rightPart S) :=
        congrArg₂ assemble hc hd
      _ = S := assemble_parts S

/-- Closed sets of a componentwise product are pairs of component closed
sets. -/
def closedEquiv (c : SetClosure E) (d : SetClosure F) :
    (productClosure c d).Closeds ≃ c.Closeds × d.Closeds where
  toFun C :=
    (⟨leftPart (C : Set (E ⊕ F)),
        (isClosed_productClosure_iff c d _).mp C.2 |>.1⟩,
      ⟨rightPart (C : Set (E ⊕ F)),
        (isClosed_productClosure_iff c d _).mp C.2 |>.2⟩)
  invFun pair :=
    ⟨assemble (pair.1 : Set E) (pair.2 : Set F),
      (isClosed_productClosure_iff c d _).mpr
        (by simpa using And.intro pair.1.2 pair.2.2)⟩
  left_inv C := by
    apply Subtype.ext
    exact assemble_parts (C : Set (E ⊕ F))
  right_inv pair := by
    apply Prod.ext
    · apply Subtype.ext
      exact leftPart_assemble (pair.1 : Set E) (pair.2 : Set F)
    · apply Subtype.ext
      exact rightPart_assemble (pair.1 : Set E) (pair.2 : Set F)

/-- Cardinalities add when two subsets are assembled in disjoint summands. -/
theorem ncard_assemble [Finite E] [Finite F]
    (A : Set E) (B : Set F) :
    (assemble A B).ncard = A.ncard + B.ncard := by
  rw [assemble,
    Set.ncard_union_eq Set.disjoint_image_inl_image_inr,
    Set.ncard_image_of_injective _ Sum.inl_injective,
    Set.ncard_image_of_injective _ Sum.inr_injective]

/-- The closed-set equivalence preserves size as the sum of component
sizes. -/
@[simp]
theorem closedEquiv_symm_ncard [Finite E] [Finite F]
    (c : SetClosure E) (d : SetClosure F)
    (pair : c.Closeds × d.Closeds) :
    ((((closedEquiv c d).symm pair : (productClosure c d).Closeds) :
        Set (E ⊕ F))).ncard =
      (pair.1 : Set E).ncard + (pair.2 : Set F).ncard := by
  exact ncard_assemble (pair.1 : Set E) (pair.2 : Set F)

/-- The level polynomial of a componentwise product is the product of the
two component level polynomials. -/
theorem productClosure_levelPolynomial [Finite E] [Finite F]
    (c : SetClosure E) (d : SetClosure F) :
    (productClosure c d).levelPolynomial =
      c.levelPolynomial * d.levelPolynomial := by
  classical
  letI := Fintype.ofFinite c.Closeds
  letI := Fintype.ofFinite d.Closeds
  letI := Fintype.ofFinite (productClosure c d).Closeds
  rw [levelPolynomial_eq_sum_stat
    (productClosure c d) (closedEquiv c d).symm
    (fun pair ↦ (pair.1 : Set E).ncard + (pair.2 : Set F).ncard)
    (closedEquiv_symm_ncard c d)]
  unfold levelPolynomial
  rw [Fintype.sum_prod_type]
  simp_rw [pow_add]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro C _
  rw [← Finset.mul_sum]

/-- Coefficients of the product closure are the explicit convolution of
the component level counts. -/
theorem productClosure_levelCount [Finite E] [Finite F]
    (c : SetClosure E) (d : SetClosure F) (n : ℕ) :
    (productClosure c d).levelCount n =
      ∑ pair ∈ Finset.antidiagonal n,
        c.levelCount pair.1 * d.levelCount pair.2 := by
  rw [← levelPolynomial_coeff,
    productClosure_levelPolynomial,
    Polynomial.coeff_mul]
  simp only [levelPolynomial_coeff]

/-- Componentwise agreement through level `n` implies agreement of the
product closures at level `n`. -/
theorem productClosure_levelCount_eq_of_component_eq
    [Finite E] [Finite F]
    (cQ cS : SetClosure E) (dQ dS : SetClosure F) (n : ℕ)
    (hleft : ∀ i ≤ n, cQ.levelCount i = cS.levelCount i)
    (hright : ∀ i ≤ n, dQ.levelCount i = dS.levelCount i) :
    (productClosure cQ dQ).levelCount n =
      (productClosure cS dS).levelCount n := by
  rw [productClosure_levelCount, productClosure_levelCount]
  apply Finset.sum_congr rfl
  intro pair hpair
  have hsum : pair.1 + pair.2 = n :=
    Finset.mem_antidiagonal.mp hpair
  rw [hleft pair.1 (by omega), hright pair.2 (by omega)]

/-- The simultaneous level-three/level-four block-product hook used by
`ThreeFourCoreRecurrenceData.disconnected`. -/
theorem productClosure_levelCount_three_and_four_eq
    [Finite E] [Finite F]
    (cQ cS : SetClosure E) (dQ dS : SetClosure F)
    (hleft : ∀ i ≤ 4, cQ.levelCount i = cS.levelCount i)
    (hright : ∀ i ≤ 4, dQ.levelCount i = dS.levelCount i) :
    (productClosure cQ dQ).levelCount 3 =
        (productClosure cS dS).levelCount 3 ∧
      (productClosure cQ dQ).levelCount 4 =
        (productClosure cS dS).levelCount 4 := by
  constructor
  · apply productClosure_levelCount_eq_of_component_eq cQ cS dQ dS 3
    · intro i hi
      exact hleft i (by omega)
    · intro i hi
      exact hright i (by omega)
  · apply productClosure_levelCount_eq_of_component_eq cQ cS dQ dS 4
    · exact hleft
    · exact hright

/-- A closure relabeling preserves every individual level count. -/
theorem levelCount_eq_of_relabeling
    {G H : Type*} [Finite G] [Finite H]
    {c : SetClosure G} {d : SetClosure H}
    (h : SetClosure.RelabelingEquiv c d) (n : ℕ) :
    c.levelCount n = d.levelCount n := by
  rw [← levelPolynomial_coeff, h.levelPolynomial_eq,
    levelPolynomial_coeff]

/-- Relabeled form of the simultaneous disconnected hook.

In a module-theoretic application, `hQ` and `hS` are precisely the two
component-decomposition adapters still required: they identify the ambient
quotient and submodule closures with the respective componentwise products.
-/
theorem relabeledProduct_levelCount_three_and_four_eq
    {G : Type*} [Finite E] [Finite F] [Finite G]
    (cQ cS : SetClosure E) (dQ dS : SetClosure F)
    (qClosure sClosure : SetClosure G)
    (hQ : SetClosure.RelabelingEquiv
      (productClosure cQ dQ) qClosure)
    (hS : SetClosure.RelabelingEquiv
      (productClosure cS dS) sClosure)
    (hleft : ∀ i ≤ 4, cQ.levelCount i = cS.levelCount i)
    (hright : ∀ i ≤ 4, dQ.levelCount i = dS.levelCount i) :
    qClosure.levelCount 3 = sClosure.levelCount 3 ∧
      qClosure.levelCount 4 = sClosure.levelCount 4 := by
  have hproduct := productClosure_levelCount_three_and_four_eq
    cQ cS dQ dS hleft hright
  constructor
  · calc
      qClosure.levelCount 3 =
          (productClosure cQ dQ).levelCount 3 :=
        (levelCount_eq_of_relabeling hQ 3).symm
      _ = (productClosure cS dS).levelCount 3 := hproduct.1
      _ = sClosure.levelCount 3 :=
        levelCount_eq_of_relabeling hS 3
  · calc
      qClosure.levelCount 4 =
          (productClosure cQ dQ).levelCount 4 :=
        (levelCount_eq_of_relabeling hQ 4).symm
      _ = (productClosure cS dS).levelCount 4 := hproduct.2
      _ = sClosure.levelCount 4 :=
        levelCount_eq_of_relabeling hS 4

end QuotientSubmoduleEquidistribution.SetClosure.ComponentwiseProduct
