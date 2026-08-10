import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Jacobson.Radical
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import QuotientSubmoduleEquidistribution.RepresentationTheory.AuslanderEquivalence

/-!
# Strong heredity-chain vocabulary

This file gives a literal Lean formulation of the ideal-theoretic side of
Tsukamoto's Theorem 3.22.  It also proves the elementary facts that an
idempotent `e` generates an idempotent two-sided ideal and that the principal
right module `eA` is finite projective.

No rejective-chain equivalence is postulated in this vocabulary file.
Downstream modules prove the required directions of Tsukamoto's
projectivity/rejectivity bridge (Proposition 3.16) and
cosemisimplicity/radical-sandwich bridge (Lemma 3.18).  The semantic
connection from strong heredity chains to the standard-module notion of
strongly quasi-hereditary algebra remains separate.
-/

noncomputable section

open CategoryTheory
open MulOpposite

namespace QuotientSubmoduleEquidistribution.Tsukamoto

universe u

variable {A : Type u} [Ring A]

/-- The principal two-sided ideal `AeA`. -/
def principalTwoSidedIdeal (e : A) : TwoSidedIdeal A :=
  TwoSidedIdeal.span {e}

/-- The principal right ideal `eA`, represented as a left ideal of the
opposite ring. -/
def principalRightIdeal (e : A) : Ideal Aᵐᵒᵖ :=
  Ideal.span {op e}

/-- Literal idempotence `H² = H` for a two-sided ideal.  Mathlib's ideal
multiplication is used through the canonical left-ideal view. -/
def IsIdempotentIdeal (H : TwoSidedIdeal A) : Prop :=
  H.asIdeal * H.asIdeal = H.asIdeal

/-- An idempotent element generates an idempotent two-sided ideal. -/
theorem principalTwoSidedIdeal_isIdempotent
    {e : A} (he : IsIdempotentElem e) :
    IsIdempotentIdeal (principalTwoSidedIdeal e) := by
  let H := principalTwoSidedIdeal e
  let P : Ideal A := H.asIdeal * H.asIdeal
  haveI : P.IsTwoSided := inferInstance
  apply le_antisymm
  · exact Ideal.mul_le_right
  · have heH : e ∈ H :=
      TwoSidedIdeal.subset_span (Set.mem_singleton e)
    have heP : e ∈ P := by
      rw [← he.eq]
      exact Ideal.mul_mem_mul heH heH
    have hHP : H ≤ P.toTwoSided := by
      apply TwoSidedIdeal.span_le.mpr
      rw [Set.singleton_subset_iff]
      exact (Ideal.mem_toTwoSided).2 heP
    intro x hx
    exact Ideal.mem_toTwoSided.mp (hHP hx)

/-- Projectivity of a two-sided ideal as a right `A`-module. -/
def IsRightProjectiveIdeal (H : TwoSidedIdeal A) : Prop :=
  Module.Projective Aᵐᵒᵖ H

/-- Projectivity of a two-sided ideal as a left `A`-module. -/
def IsLeftProjectiveIdeal (H : TwoSidedIdeal A) : Prop :=
  Module.Projective A H

/-- The image of `H` in the quotient ring `A/I`, denoted `H/I` when
`I ≤ H`. -/
def quotientImage (H I : TwoSidedIdeal A) :
    TwoSidedIdeal (A ⧸ I.asIdeal) :=
  TwoSidedIdeal.map (Ideal.Quotient.mk I.asIdeal) H

/-- The radical-sandwich condition
`(H/I) J(A/I) (H/I) = 0`. -/
def RadicalSandwichZero (H I : TwoSidedIdeal A) : Prop :=
  let Hbar := quotientImage H I
  Hbar.asIdeal *
      Ring.jacobson (A ⧸ I.asIdeal) *
      Hbar.asIdeal =
    (⊥ : Ideal (A ⧸ I.asIdeal))

/-- A strict finite chain of idempotent two-sided ideals
`A = H₀ > H₁ > ... > Hₙ = 0`. -/
structure IdempotentIdealChain (A : Type u) [Ring A] (n : ℕ) where
  ideal : Fin (n + 1) → TwoSidedIdeal A
  strictAnti : StrictAnti ideal
  top_eq : ideal 0 = ⊤
  bot_eq : ideal (Fin.last n) = ⊥
  idempotent : ∀ i, IsIdempotentIdeal (ideal i)

namespace IdempotentIdealChain

variable {n : ℕ} (H : IdempotentIdealChain A n)

/-- Tsukamoto's right-strong heredity-chain conditions: right projectivity
of the nonfinal terms and the radical-sandwich condition at every step. -/
def IsRightStrongHeredity : Prop :=
  (∀ i : Fin n, IsRightProjectiveIdeal (H.ideal i.castSucc)) ∧
    ∀ i : Fin n,
      RadicalSandwichZero
        (H.ideal i.castSucc) (H.ideal i.succ)

/-- The left-strong heredity-chain conditions. -/
def IsLeftStrongHeredity : Prop :=
  (∀ i : Fin n, IsLeftProjectiveIdeal (H.ideal i.castSucc)) ∧
    ∀ i : Fin n,
      RadicalSandwichZero
        (H.ideal i.castSucc) (H.ideal i.succ)

/-- A chain which is both right- and left-strong. -/
def IsStrongHeredity : Prop :=
  H.IsRightStrongHeredity ∧ H.IsLeftStrongHeredity

/-- Chosen idempotents presenting every term as `AeᵢA`. -/
structure IdempotentPresentation where
  generator : Fin (n + 1) → A
  isIdempotent : ∀ i, IsIdempotentElem (generator i)
  span_eq : ∀ i,
    principalTwoSidedIdeal (generator i) = H.ideal i

end IdempotentIdealChain

/-- Existence of an ideal-theoretic right-strong heredity chain.  This is
deliberately distinct from the standard-module definition of a
right-strongly quasi-hereditary algebra. -/
def HasRightStrongHeredityChain (A : Type u) [Ring A] : Prop :=
  ∃ (n : ℕ) (H : IdempotentIdealChain A n),
    H.IsRightStrongHeredity

/-- Existence of an ideal-theoretic left-strong heredity chain. -/
def HasLeftStrongHeredityChain (A : Type u) [Ring A] : Prop :=
  ∃ (n : ℕ) (H : IdempotentIdealChain A n),
    H.IsLeftStrongHeredity

/-- Elements of `eA` are fixed by right multiplication by `e`
(expressed in the opposite ring). -/
theorem mul_op_eq_self_of_mem_principalRightIdeal
    {e : A} (he : IsIdempotentElem e)
    {x : Aᵐᵒᵖ} (hx : x ∈ principalRightIdeal e) :
    x * op e = x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      rw [Set.mem_singleton_iff.mp hx]
      apply unop_injective
      simpa using he.eq
  | zero => simp
  | add x y _ _ hx hy =>
      rw [add_mul, hx, hy]
  | smul r x _ hx =>
      change (r * x) * op e = r * x
      rw [mul_assoc, hx]

/-- The regular right module projects onto `eA` by multiplication by
`e`. -/
def principalRightProjection (e : A) :
    Aᵐᵒᵖ →ₗ[Aᵐᵒᵖ] principalRightIdeal e :=
  (LinearMap.mulRight Aᵐᵒᵖ (op e)).codRestrict
    (principalRightIdeal e)
    (fun x ↦ by
      change x * op e ∈ principalRightIdeal e
      exact
        (principalRightIdeal e).mul_mem_left x
          (Ideal.subset_span (Set.mem_singleton (op e))))

/-- The inclusion followed by the principal projection is the identity
on `eA`. -/
theorem principalRightProjection_comp_subtype
    {e : A} (he : IsIdempotentElem e) :
    (principalRightProjection e).comp
        (Submodule.subtype (principalRightIdeal e)) =
      LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change x.1 * op e = x.1
  exact mul_op_eq_self_of_mem_principalRightIdeal he x.property

/-- For idempotent `e`, the right ideal `eA` is projective. -/
theorem principalRightIdeal_projective
    {e : A} (he : IsIdempotentElem e) :
    Module.Projective Aᵐᵒᵖ (principalRightIdeal e) :=
  Module.Projective.of_split
    (Submodule.subtype (principalRightIdeal e))
    (principalRightProjection e)
    (principalRightProjection_comp_subtype he)

/-- For idempotent `e`, the right ideal `eA` is finitely generated. -/
theorem principalRightIdeal_finite
    {e : A} (he : IsIdempotentElem e) :
    Module.Finite Aᵐᵒᵖ (principalRightIdeal e) :=
  Module.Finite.of_surjective
    (principalRightProjection e)
    (fun x ↦
      ⟨x.1, by
        apply Subtype.ext
        change x.1 * op e = x.1
        exact
          mul_op_eq_self_of_mem_principalRightIdeal he x.property⟩)

/-- The categorical right module represented by `eA`. -/
def principalRightModule (e : A) : ModuleCat.{u} Aᵐᵒᵖ :=
  ModuleCat.of Aᵐᵒᵖ (principalRightIdeal e)

/-- The literal additive closure `add(eA)`. -/
def addPrincipalRightModule (e : A) :
    ObjectProperty (ModuleCat.{u} Aᵐᵒᵖ) :=
  AuslanderEquivalence.finiteAddClosure (principalRightModule e)

/-- The principal module `eA` is an object of the existing finite
projective-module category. -/
theorem principalRightModule_mem_finiteProjectiveModules
    {e : A} (he : IsIdempotentElem e) :
    AuslanderEquivalence.finiteProjectiveModules Aᵐᵒᵖ
      (principalRightModule e) := by
  refine ⟨principalRightIdeal_finite he, ?_⟩
  exact
    (IsProjective.iff_projective
      (principalRightIdeal e)).mp
      (principalRightIdeal_projective he)

end QuotientSubmoduleEquidistribution.Tsukamoto
