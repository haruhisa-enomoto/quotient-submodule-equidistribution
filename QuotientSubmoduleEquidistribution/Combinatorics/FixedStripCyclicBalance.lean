import QuotientSubmoduleEquidistribution.Combinatorics.CyclicBinaryTransitions
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.Data.Set.Card.Arithmetic

/-!
# Fixed-strip balance from cyclic parametrizations

The fixed-strip argument groups quotient and reversed row-`F` packets into
finite cyclic binary systems.  Quotient packets are the false-to-true
transitions and reversed packets are the true-to-false transitions.  This
file packages precisely that reduction and derives an equivalence of the two
packet types from the elementary cyclic transition count.
-/

set_option autoImplicit false
noncomputable section

namespace QuotientSubmoduleEquidistribution.FixedStripCyclicBalance

universe u v w

/-- A false-to-true transition at `i` along the permutation `step`. -/
def IsRise {α : Type u} (step : α ≃ α) (bit : α → Bool)
    (i : α) : Prop :=
  bit (step.symm i) = false ∧ bit i = true

/-- A true-to-false transition after `i` along the permutation `step`. -/
def IsFall {α : Type u} (step : α ≃ α) (bit : α → Bool)
    (i : α) : Prop :=
  bit i = true ∧ bit (step i) = false

/-- Data identifying two packet families with rises and falls in a finite
family of cyclic binary systems. -/
structure Parametrization (QuotientPacket : Type u)
    (ReversePacket : Type v) where
  Context : FintypeCat.{w}
  Position : Context → FintypeCat.{w}
  step : ∀ c, Position c ≃ Position c
  bit : ∀ c, Position c → Bool
  quotientEquiv : QuotientPacket ≃
    Σ c : Context, {i : Position c // IsRise (step c) (bit c) i}
  reverseEquiv : ReversePacket ≃
    Σ c : Context, {i : Position c // IsFall (step c) (bit c) i}

/-- The rise and fall subtypes of one finite permutation have equal
cardinality. -/
theorem isRise_card_eq_isFall_card
    {α : Type u} [Fintype α]
    (step : α ≃ α) (bit : α → Bool) :
    Nat.card {i : α // IsRise step bit i} =
      Nat.card {i : α // IsFall step bit i} := by
  classical
  letI : Fintype {i : α // IsRise step bit i} := Fintype.ofFinite _
  letI : Fintype {i : α // IsFall step bit i} := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype, Fintype.card_subtype]
  simpa only [IsRise, IsFall, CyclicBinaryTransitions.rises,
    CyclicBinaryTransitions.falls] using
    (CyclicBinaryTransitions.rises_card_eq_falls_card step bit)

namespace Parametrization

variable {QuotientPacket : Type u} {ReversePacket : Type v}
  (P : Parametrization.{u, v, w} QuotientPacket ReversePacket)

/-- Choose the fiberwise rise-to-fall equivalences supplied by equal finite
cardinalities, and keep the context fixed. -/
def riseEquivFallAt (c : P.Context) :
    {i : P.Position c // IsRise (P.step c) (P.bit c) i} ≃
      {i : P.Position c // IsFall (P.step c) (P.bit c) i} := by
  classical
  letI : Fintype (P.Position c) := FintypeCat.fintype
  letI : Fintype
      {i : P.Position c // IsRise (P.step c) (P.bit c) i} :=
    Fintype.ofFinite _
  letI : Fintype
      {i : P.Position c // IsFall (P.step c) (P.bit c) i} :=
    Fintype.ofFinite _
  apply Fintype.equivOfCardEq
  simpa only [Nat.card_eq_fintype_card] using
    (isRise_card_eq_isFall_card (P.step c) (P.bit c))

/-- Choose the fiberwise rise-to-fall equivalences supplied by equal finite
cardinalities, and keep the context fixed. -/
def riseEquivFall :
    (Σ c : P.Context,
        {i : P.Position c // IsRise (P.step c) (P.bit c) i}) ≃
      (Σ c : P.Context,
        {i : P.Position c // IsFall (P.step c) (P.bit c) i}) where
  toFun z := ⟨z.1, P.riseEquivFallAt z.1 z.2⟩
  invFun z := ⟨z.1, (P.riseEquivFallAt z.1).symm z.2⟩
  left_inv z := by
    rcases z with ⟨c, i⟩
    change
      (⟨c, (P.riseEquivFallAt c).symm (P.riseEquivFallAt c i)⟩ :
        Σ c : P.Context,
          {i : P.Position c // IsRise (P.step c) (P.bit c) i}) =
        ⟨c, i⟩
    rw [(P.riseEquivFallAt c).symm_apply_apply]
  right_inv z := by
    rcases z with ⟨c, i⟩
    change
      (⟨c, P.riseEquivFallAt c ((P.riseEquivFallAt c).symm i)⟩ :
        Σ c : P.Context,
          {i : P.Position c // IsFall (P.step c) (P.bit c) i}) =
        ⟨c, i⟩
    rw [(P.riseEquivFallAt c).apply_symm_apply]

/-- A cyclic parametrization gives a canonical-up-to-finite-choice
equivalence between the quotient and reverse fixed-packet families. -/
def packetEquiv : QuotientPacket ≃ ReversePacket :=
  P.quotientEquiv.trans (P.riseEquivFall.trans P.reverseEquiv.symm)

include P in
/-- Consequently the two fixed-packet families have equal finite
cardinality. -/
theorem card_eq [Fintype QuotientPacket] [Fintype ReversePacket] :
    Fintype.card QuotientPacket = Fintype.card ReversePacket :=
  Fintype.card_congr (packetEquiv P)

end Parametrization

end QuotientSubmoduleEquidistribution.FixedStripCyclicBalance
