import QuotientSubmoduleEquidistribution.RepresentationTheory.Conjecture

/-!
# Abstract endpoint for the representation-directed profile

This module isolates the last, purely enumerative step of
`thm:directed-main`.

The finite type `U` is intended to be the Bruhat interval
`{u // u ≤ w_A}`.  The difficult representation-theoretic and Coxeter
arguments are exposed as data: for every `u`, one supplies its length,
the lexicographically first and colexicographically last omitted position
sets, and the two resulting closed-set parametrizations.

From only those data, this file proves:

* both closed supports have size `|ind A| - length u`;
* both level polynomials are the reverse-length enumerator;
* quotient--submodule equidistribution;
* an explicit size-preserving equivalence between the two closed-set
  families; and
* equivalences between `U` and the ranges of the two sorted position-set
  maps.
-/

noncomputable section

namespace QuotientSubmoduleEquidistribution.RepresentationDirected

open Polynomial Set

universe uR uI uM uU

variable
    {R : Type uR} [Ring R] [IsNoetherianRing R]
    {ι : Type uI}
    (σ : IndecomposableSkeleton.{uR, uI, uM} R ι)
    (U : Type uU)

/-- The exact finite output needed from the directed sorting theorem.

`U` is the Bruhat interval.  The names `lexFirstOmitted` and
`colexLastOmitted` record the intended Coxeter meaning; proving that the
selected position sets really have those extremal properties belongs to
the upstream sorting theorem, not to this enumerative interface. -/
structure ProfileParametrization where
  length : U → ℕ
  lexFirstOmitted : U → Finset ι
  colexLastOmitted : U → Finset ι
  card_lexFirstOmitted :
    ∀ u : U, (lexFirstOmitted u).card = length u
  card_colexLastOmitted :
    ∀ u : U, (colexLastOmitted u).card = length u
  quotientClosedEquiv : U ≃ σ.qClosure.Closeds
  submoduleClosedEquiv : U ≃ σ.sClosure.Closeds
  support_quotientClosedEquiv :
    ∀ u : U,
      ((quotientClosedEquiv u : σ.qClosure.Closeds) : Set ι) =
        (↑(lexFirstOmitted u) : Set ι)ᶜ
  support_submoduleClosedEquiv :
    ∀ u : U,
      ((submoduleClosedEquiv u : σ.sClosure.Closeds) : Set ι) =
        (↑(colexLastOmitted u) : Set ι)ᶜ

namespace ProfileParametrization

variable
    {R : Type uR} [Ring R] [IsNoetherianRing R]
    {ι : Type uI}
    {σ : IndecomposableSkeleton.{uR, uI, uM} R ι}
    {U : Type uU}
    (p : ProfileParametrization σ U)

/-- The quotient-closed support indexed by `u` has kept size
`|ind A| - length u`. -/
theorem ncard_quotientClosedEquiv [Finite ι] (u : U) :
    (((p.quotientClosedEquiv u : σ.qClosure.Closeds) : Set ι).ncard) =
      Nat.card ι - p.length u := by
  rw [p.support_quotientClosedEquiv u, Set.ncard_compl,
    Set.ncard_coe_finset, p.card_lexFirstOmitted u]

/-- The submodule-closed support indexed by `u` has the same kept size. -/
theorem ncard_submoduleClosedEquiv [Finite ι] (u : U) :
    (((p.submoduleClosedEquiv u : σ.sClosure.Closeds) : Set ι).ncard) =
      Nat.card ι - p.length u := by
  rw [p.support_submoduleClosedEquiv u, Set.ncard_compl,
    Set.ncard_coe_finset, p.card_colexLastOmitted u]

/-- The quotient profile is the reverse-length enumerator of the finite
Bruhat interval. -/
theorem quotientLevelPolynomial_eq_reverseLength
    [Finite ι] [Fintype U] :
    σ.qClosure.levelPolynomial =
      ∑ u : U, X ^ (Nat.card ι - p.length u) := by
  exact
    QuotientSubmoduleEquidistribution.SetClosure.levelPolynomial_eq_sum_stat
      σ.qClosure p.quotientClosedEquiv
      (fun u : U ↦ Nat.card ι - p.length u)
      p.ncard_quotientClosedEquiv

/-- The submodule profile is the same reverse-length enumerator. -/
theorem submoduleLevelPolynomial_eq_reverseLength
    [Finite ι] [Fintype U] :
    σ.sClosure.levelPolynomial =
      ∑ u : U, X ^ (Nat.card ι - p.length u) := by
  exact
    QuotientSubmoduleEquidistribution.SetClosure.levelPolynomial_eq_sum_stat
      σ.sClosure p.submoduleClosedEquiv
      (fun u : U ↦ Nat.card ι - p.length u)
      p.ncard_submoduleClosedEquiv

include p in
/-- The final polynomial equality in the representation-directed theorem. -/
theorem quotientLevelPolynomial_eq_submoduleLevelPolynomial
    [Finite ι] [Fintype U] :
    σ.qClosure.levelPolynomial = σ.sClosure.levelPolynomial := by
  rw [quotientLevelPolynomial_eq_reverseLength p,
    submoduleLevelPolynomial_eq_reverseLength p]

include p in
/-- Paper-facing formulation of the strong quotient--submodule
equidistribution consequence. -/
theorem quotientSubmoduleEquidistribution
    [Finite ι] [Fintype U] :
    σ.HasQuotientSubmoduleEquidistribution :=
  quotientLevelPolynomial_eq_submoduleLevelPolynomial p

/-- Match quotient-closed and submodule-closed supports through their common
Bruhat-interval parameter. -/
def quotientSubmoduleClosedEquiv :
    σ.qClosure.Closeds ≃ σ.sClosure.Closeds :=
  p.quotientClosedEquiv.symm.trans p.submoduleClosedEquiv

/-- The matching through the common Bruhat parameter preserves kept size. -/
theorem quotientSubmoduleClosedEquiv_ncard
    [Finite ι]
    (C : σ.qClosure.Closeds) :
    (((p.quotientSubmoduleClosedEquiv C :
        σ.sClosure.Closeds) : Set ι).ncard) =
      (C : Set ι).ncard := by
  let u : U := p.quotientClosedEquiv.symm C
  have hq :
      (C : Set ι).ncard = Nat.card ι - p.length u := by
    change (C : Set ι).ncard =
      Nat.card ι - p.length (p.quotientClosedEquiv.symm C)
    simpa using p.ncard_quotientClosedEquiv
      (p.quotientClosedEquiv.symm C)
  have hs :
      (((p.quotientSubmoduleClosedEquiv C :
          σ.sClosure.Closeds) : Set ι).ncard) =
        Nat.card ι - p.length u := by
    change
      (((p.submoduleClosedEquiv
          (p.quotientClosedEquiv.symm C) :
          σ.sClosure.Closeds) : Set ι).ncard) =
        Nat.card ι - p.length
          (p.quotientClosedEquiv.symm C)
    simpa [quotientSubmoduleClosedEquiv] using
      p.ncard_submoduleClosedEquiv
        (p.quotientClosedEquiv.symm C)
  exact hs.trans hq.symm

/-- Distinct Bruhat parameters have distinct lex-first omitted supports.
This is forced already by the quotient closed-set parametrization. -/
theorem lexFirstOmitted_injective :
    Function.Injective p.lexFirstOmitted := by
  intro u v huv
  apply p.quotientClosedEquiv.injective
  apply Subtype.ext
  change
    ((p.quotientClosedEquiv u : σ.qClosure.Closeds) : Set ι) =
      ((p.quotientClosedEquiv v : σ.qClosure.Closeds) : Set ι)
  rw [p.support_quotientClosedEquiv u,
    p.support_quotientClosedEquiv v, huv]

/-- Distinct Bruhat parameters have distinct colex-last omitted supports. -/
theorem colexLastOmitted_injective :
    Function.Injective p.colexLastOmitted := by
  intro u v huv
  apply p.submoduleClosedEquiv.injective
  apply Subtype.ext
  change
    ((p.submoduleClosedEquiv u : σ.sClosure.Closeds) : Set ι) =
      ((p.submoduleClosedEquiv v : σ.sClosure.Closeds) : Set ι)
  rw [p.support_submoduleClosedEquiv u,
    p.support_submoduleClosedEquiv v, huv]

/-- The Bruhat interval is equivalent to the family of lex-first sorted
position sets which actually occurs. -/
def lexFirstSupportEquiv :
    U ≃ Set.range p.lexFirstOmitted :=
  Equiv.ofInjective p.lexFirstOmitted p.lexFirstOmitted_injective

/-- The Bruhat interval is equivalent to the family of colex-last sorted
position sets which actually occurs. -/
def colexLastSupportEquiv :
    U ≃ Set.range p.colexLastOmitted :=
  Equiv.ofInjective p.colexLastOmitted p.colexLastOmitted_injective

/-- Abstract lex-first/colex-last position-set matching through the common
Bruhat parameter. -/
def lexFirstColexLastSupportEquiv :
    Set.range p.lexFirstOmitted ≃ Set.range p.colexLastOmitted :=
  p.lexFirstSupportEquiv.symm.trans p.colexLastSupportEquiv

/-- Corresponding lex-first and colex-last omitted position sets have the
same cardinality. -/
theorem card_lexFirst_eq_card_colexLast (u : U) :
    (p.lexFirstOmitted u).card =
      (p.colexLastOmitted u).card := by
  rw [p.card_lexFirstOmitted u, p.card_colexLastOmitted u]

end ProfileParametrization

end QuotientSubmoduleEquidistribution.RepresentationDirected


