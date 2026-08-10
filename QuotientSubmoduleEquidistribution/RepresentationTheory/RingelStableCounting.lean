import QuotientSubmoduleEquidistribution.RepresentationTheory.StableIsomorphismReflection

/-!
# From Ringel's stable pairing to cardinality equality

This file isolates the exact object-level content of `D η` needed after
Ringel's Theorem 1.  It does not assume the desired cardinality equality.
-/

noncomputable section

open Set CategoryTheory

namespace QuotientSubmoduleEquidistribution.RingelStable

universe u v

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {iota : Type v}
  (sigma : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, v, u} R iota)

/-- The boundary of categorical projectives inside the chosen skeleton. -/
def projectiveSet : Set iota :=
  {i | Projective (sigma.obj i)}

/-- The boundary of categorical injectives inside the chosen skeleton. -/
def injectiveSet : Set iota :=
  {i | Injective (sigma.obj i)}

/-- Object-level data extracted from Ringel's stable equivalence after
composition with Artin duality.  The source inverse is only required modulo
projectives and the target inverse only modulo injectives, exactly as in
`L/P` and `K/Q`. -/
structure RingelStableAssignment (T C : Set iota) where
  forward :
    {i // i ∈ T \ projectiveSet sigma} →
      {i // i ∈ C \ injectiveSet sigma}
  backward :
    {i // i ∈ C \ injectiveSet sigma} →
      {i // i ∈ T \ projectiveSet sigma}
  source_inverse_stable :
    ∀ x,
      StableIso
        (sigma.obj ((backward (forward x)).1))
        (sigma.obj x.1)
  target_inverse_stable :
    ∀ y,
      InjectiveStableIso
        (sigma.obj ((forward (backward y)).1))
        (sigma.obj y.1)

namespace RingelStableAssignment

variable {sigma} {T C : Set iota}

/-- Ringel's stable inverse data gives an actual equivalence on the
nonprojective/noninjective indecomposable labels. -/
def nonboundaryEquiv
    (D : RingelStableAssignment sigma T C) :
    {i // i ∈ T \ projectiveSet sigma} ≃
      {i // i ∈ C \ injectiveSet sigma} where
  toFun := D.forward
  invFun := D.backward
  left_inv x := by
    apply Subtype.ext
    apply sigma.eq_of_iso
    exact
      nonempty_iso_of_stableIso
        (sigma.indecomposable ((D.backward (D.forward x)).1))
        (sigma.indecomposable x.1)
        (sigma.finiteLength ((D.backward (D.forward x)).1))
        (sigma.finiteLength x.1)
        (D.backward (D.forward x)).property.2
        x.property.2
        (D.source_inverse_stable x)
  right_inv y := by
    apply Subtype.ext
    apply sigma.eq_of_iso
    exact
      nonempty_iso_of_injectiveStableIso
        (sigma.indecomposable ((D.forward (D.backward y)).1))
        (sigma.indecomposable y.1)
        (sigma.finiteLength ((D.forward (D.backward y)).1))
        (sigma.finiteLength y.1)
        (D.forward (D.backward y)).property.2
        y.property.2
        (D.target_inverse_stable y)

/-- Consequently the two nonboundary parts have the same finite cardinality. -/
theorem ncard_nonboundary_eq
    (D : RingelStableAssignment sigma T C) :
    (T \ projectiveSet sigma).ncard =
      (C \ injectiveSet sigma).ncard :=
  Set.ncard_congr' D.nonboundaryEquiv

/-- Add the projective/injective boundary back.  This is the exact finite
counting deduction used in Ringel's Corollary 5. -/
theorem ncard_eq_of_boundary_ncard_eq
    [Finite iota]
    (D : RingelStableAssignment sigma T C)
    (hPT : projectiveSet sigma ⊆ T)
    (hIC : injectiveSet sigma ⊆ C)
    (hboundary :
      (projectiveSet sigma).ncard = (injectiveSet sigma).ncard) :
    T.ncard = C.ncard := by
  calc
    T.ncard =
        (T \ projectiveSet sigma).ncard +
          (projectiveSet sigma).ncard :=
      (Set.ncard_sdiff_add_ncard_of_subset hPT).symm
    _ =
        (C \ injectiveSet sigma).ncard +
          (injectiveSet sigma).ncard := by
      rw [D.ncard_nonboundary_eq, hboundary]
    _ = C.ncard :=
      Set.ncard_sdiff_add_ncard_of_subset hIC

end RingelStableAssignment

end QuotientSubmoduleEquidistribution.RingelStable
