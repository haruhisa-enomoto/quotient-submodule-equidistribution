import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Finset.Sum
import OpConjecture.RadicalSquareZero.ClosureAdapter

/-!
# Top-coverage construction of radical-square-zero closure fibers

This module derives the `A`-side decorated-core
parametrization from a purely finite closedness criterion.

The ground type is the disjoint union `Nonsimple ⊕ Vertex`.  The input
specifies a finite nonsimple support for every common core and says
that a full set is closed exactly when:

* its nonsimple part is the support of one core; and
* its simple part contains that core's mandatory `topSupport`.

Injectivity of the nonsimple-support map makes the core unique.  The
remaining simple labels are exactly a finite subset of the complement
of `topSupport`, hence an `AChoice`.

No module, algebra, quiver, or separated-representation statement is
assumed here.
-/

namespace OpConjecture.RadicalSquareZeroCombinatorics

open Finset Polynomial Set
open scoped BigOperators

universe u v w w₁ w₂

variable {Core : Type u} {Vertex : Type v}
  [Fintype Core] [Fintype Vertex] [DecidableEq Vertex]

namespace CoreFamily
namespace TopCoverage

variable {Nonsimple : Type w} [Fintype Nonsimple]

/-- Split a set on `Nonsimple ⊕ Vertex` into its two finite parts. -/
noncomputable def setPartsEquiv :
    Set (Nonsimple ⊕ Vertex) ≃
      Finset Nonsimple × Finset Vertex :=
  Fintype.finsetEquivSet.symm.trans Finset.sumEquiv.toEquiv

/-- The nonsimple labels selected by a full set. -/
noncomputable def nonsimplePart
    (S : Set (Nonsimple ⊕ Vertex)) : Finset Nonsimple :=
  (setPartsEquiv S).1

/-- The simple labels selected by a full set. -/
noncomputable def simplePart
    (S : Set (Nonsimple ⊕ Vertex)) : Finset Vertex :=
  (setPartsEquiv S).2

omit [DecidableEq Vertex] in
@[simp]
theorem mem_nonsimplePart_iff
    (S : Set (Nonsimple ⊕ Vertex)) (y : Nonsimple) :
    y ∈ nonsimplePart S ↔ Sum.inl y ∈ S := by
  simp [nonsimplePart, setPartsEquiv]
  exact Set.ext_iff.mp
    (Fintype.finsetEquivSet.apply_symm_apply S) _

omit [DecidableEq Vertex] in
@[simp]
theorem mem_simplePart_iff
    (S : Set (Nonsimple ⊕ Vertex)) (v : Vertex) :
    v ∈ simplePart S ↔ Sum.inr v ∈ S := by
  simp [simplePart, setPartsEquiv]
  exact Set.ext_iff.mp
    (Fintype.finsetEquivSet.apply_symm_apply S) _

omit [DecidableEq Vertex] in
@[simp]
theorem setPartsEquiv_symm_parts
    (S₀ : Finset Nonsimple) (S₁ : Finset Vertex) :
    nonsimplePart (setPartsEquiv.symm (S₀, S₁)) = S₀ ∧
      simplePart (setPartsEquiv.symm (S₀, S₁)) = S₁ := by
  simp [nonsimplePart, simplePart]

omit [DecidableEq Vertex] in
/-- Cardinality is additive across the nonsimple/simple split. -/
theorem ncard_eq_card_parts
    (S : Set (Nonsimple ⊕ Vertex)) :
    S.ncard =
      (nonsimplePart S).card + (simplePart S).card := by
  classical
  let s : Finset (Nonsimple ⊕ Vertex) :=
    Fintype.finsetEquivSet.symm S
  have hcoe : (s : Set (Nonsimple ⊕ Vertex)) = S := by
    simp [s]
  rw [← hcoe, Set.ncard_coe_finset]
  simpa [nonsimplePart, simplePart, setPartsEquiv] using
    (Finset.card_toLeft_add_card_toRight (u := s)).symm

/-- Forget the proof that a chosen vertex lies outside the mandatory
support. -/
noncomputable def freeVertices
    (T : Finset Vertex) (s : Finset ↥Tᶜ) : Finset Vertex :=
  ((Equiv.finsetSubtypeComm
    (fun v : Vertex ↦ v ∈ Tᶜ)) s).1

/-- Every forgotten free vertex is outside the mandatory support. -/
theorem not_mem_of_mem_freeVertices
    (T : Finset Vertex) (s : Finset ↥Tᶜ)
    {v : Vertex} (hv : v ∈ freeVertices T s) :
    v ∉ T := by
  have hvcompl :=
    ((Equiv.finsetSubtypeComm
      (fun v : Vertex ↦ v ∈ Tᶜ)) s).property v hv
  simpa using hvcompl

/-- Forgetting subtype proofs is injective on finite choices. -/
theorem freeVertices_injective
    (T : Finset Vertex) :
    Function.Injective (freeVertices T) := by
  intro s t h
  apply
    (Equiv.finsetSubtypeComm
      (fun v : Vertex ↦ v ∈ Tᶜ)).injective
  exact Subtype.ext h

/-- Forgetting subtype proofs preserves the number of chosen
vertices. -/
theorem card_freeVertices
    (T : Finset Vertex) (s : Finset ↥Tᶜ) :
    (freeVertices T s).card = s.card := by
  classical
  simp [freeVertices, Equiv.finsetSubtypeComm]

/-- Purely combinatorial input for the top-coverage construction. -/
structure ATopCoverageData
    (F : CoreFamily Core Vertex)
    (cl : OpConjecture.SetClosure (Nonsimple ⊕ Vertex)) where
  /-- The nonsimple labels belonging to one common core. -/
  corePart : Core → Finset Nonsimple
  /-- A nonsimple support determines its core. -/
  corePart_injective : Function.Injective corePart
  /-- The stored core size is the actual support cardinality. -/
  coreSize_eq_card (x : Core) :
    F.coreSize x = (corePart x).card
  /-- Closedness is precisely core admissibility plus top coverage. -/
  isClosed_iff (S : Set (Nonsimple ⊕ Vertex)) :
    cl.IsClosed S ↔
      ∃ x : Core,
        nonsimplePart S = corePart x ∧
          F.topSupport x ⊆ simplePart S

namespace ATopCoverageData

variable {F : CoreFamily Core Vertex}
  {cl : OpConjecture.SetClosure (Nonsimple ⊕ Vertex)}
  (D : ATopCoverageData F cl)

/-- The full set represented by a core and its optional simple
labels. -/
noncomputable def decoratedSet
    (w : Σ x : Core, F.AChoice x) :
    Set (Nonsimple ⊕ Vertex) :=
  setPartsEquiv.symm
    (D.corePart w.1,
      F.topSupport w.1 ∪
        freeVertices (F.topSupport w.1) w.2)

omit [Fintype Core] in
/-- Every decorated set satisfies the top-coverage closedness
criterion. -/
theorem isClosed_decoratedSet
    (w : Σ x : Core, F.AChoice x) :
    cl.IsClosed (D.decoratedSet w) := by
  rw [D.isClosed_iff]
  refine ⟨w.1, ?_, ?_⟩
  · simp [decoratedSet, nonsimplePart]
  · simp [decoratedSet, simplePart]

/-- Regard a decoration as the corresponding closed set. -/
noncomputable def decoratedClosed
    (w : Σ x : Core, F.AChoice x) : cl.Closeds :=
  ⟨D.decoratedSet w, D.isClosed_decoratedSet w⟩

omit [Fintype Core] in
/-- Different decorations give different closed sets.  Uniqueness of
the core comes from its nonsimple support; after the core is fixed,
union with the mandatory support can be cancelled because every free
vertex lies in its complement. -/
theorem decoratedClosed_injective :
    Function.Injective D.decoratedClosed := by
  rintro ⟨x, s⟩ ⟨y, t⟩ h
  have hset :
      D.decoratedSet ⟨x, s⟩ =
        D.decoratedSet ⟨y, t⟩ :=
    congrArg Subtype.val h
  have hparts :=
    congrArg (setPartsEquiv
      (Nonsimple := Nonsimple) (Vertex := Vertex)) hset
  have hpair :
      (D.corePart x,
          F.topSupport x ∪
            freeVertices (F.topSupport x) s) =
        (D.corePart y,
          F.topSupport y ∪
            freeVertices (F.topSupport y) t) := by
    simpa [decoratedSet] using hparts
  have hxy : x = y :=
    D.corePart_injective (congrArg Prod.fst hpair)
  subst y
  have hunion :
      F.topSupport x ∪
          freeVertices (F.topSupport x) s =
        F.topSupport x ∪
          freeVertices (F.topSupport x) t :=
    congrArg Prod.snd hpair
  have hfree :
      freeVertices (F.topSupport x) s =
        freeVertices (F.topSupport x) t := by
    ext v
    by_cases hv : v ∈ F.topSupport x
    · have hvs :
          v ∉ freeVertices (F.topSupport x) s :=
        fun hmem ↦
          (not_mem_of_mem_freeVertices
            (F.topSupport x) s hmem) hv
      have hvt :
          v ∉ freeVertices (F.topSupport x) t :=
        fun hmem ↦
          (not_mem_of_mem_freeVertices
            (F.topSupport x) t hmem) hv
      simp [hvs, hvt]
    · have hm := Finset.ext_iff.mp hunion v
      simpa [hv] using hm
  have hst : s = t :=
    freeVertices_injective (F.topSupport x) hfree
  subst t
  rfl

omit [Fintype Core] in
/-- Every closed set is represented by a decoration.  Its optional
choice is its simple part with the mandatory top support removed. -/
theorem decoratedClosed_surjective :
    Function.Surjective D.decoratedClosed := by
  intro C
  obtain ⟨x, hcore, hcover⟩ :=
    (D.isClosed_iff (C : Set (Nonsimple ⊕ Vertex))).mp C.property
  let extras :
      {S : Finset Vertex //
        ∀ v ∈ S, v ∈ (F.topSupport x)ᶜ} :=
    ⟨simplePart (C : Set (Nonsimple ⊕ Vertex)) \
        F.topSupport x, by
      intro v hv
      simp only [Finset.mem_sdiff, Finset.mem_compl] at hv ⊢
      exact hv.2⟩
  let s : F.AChoice x :=
    (Equiv.finsetSubtypeComm
      (fun v : Vertex ↦
        v ∈ (F.topSupport x)ᶜ)).symm extras
  have hfree :
      freeVertices (F.topSupport x) s =
        simplePart (C : Set (Nonsimple ⊕ Vertex)) \
          F.topSupport x := by
    change
      ((Equiv.finsetSubtypeComm
          (fun v : Vertex ↦
            v ∈ (F.topSupport x)ᶜ)) s).1 =
        simplePart (C : Set (Nonsimple ⊕ Vertex)) \
          F.topSupport x
    have happly :=
      (Equiv.finsetSubtypeComm
        (fun v : Vertex ↦
          v ∈ (F.topSupport x)ᶜ)).apply_symm_apply extras
    exact congrArg Subtype.val happly
  refine ⟨⟨x, s⟩, ?_⟩
  apply Subtype.ext
  apply
    (setPartsEquiv
      (Nonsimple := Nonsimple)
      (Vertex := Vertex)).injective
  change
    setPartsEquiv (D.decoratedSet ⟨x, s⟩) =
      setPartsEquiv (C : Set (Nonsimple ⊕ Vertex))
  rw [decoratedSet, Equiv.apply_symm_apply]
  change
    (D.corePart x,
      F.topSupport x ∪
        freeVertices (F.topSupport x) s) =
      (nonsimplePart
          (C : Set (Nonsimple ⊕ Vertex)),
        simplePart
          (C : Set (Nonsimple ⊕ Vertex)))
  rw [hfree, Finset.union_sdiff_of_subset hcover]
  exact congrArg
    (fun S : Finset Nonsimple ↦
      (S, simplePart
        (C : Set (Nonsimple ⊕ Vertex)))) hcore.symm

/-- Decorations and closed sets are equivalent under the top-coverage
criterion. -/
noncomputable def decoratedClosedEquiv :
    (Σ x : Core, F.AChoice x) ≃ cl.Closeds :=
  Equiv.ofBijective D.decoratedClosed
    ⟨D.decoratedClosed_injective,
      D.decoratedClosed_surjective⟩

omit [Fintype Core] in
/-- The represented closed set has precisely its combinatorial
`aWeight`. -/
theorem ncard_decoratedClosed
    (w : Σ x : Core, F.AChoice x) :
    (((D.decoratedClosed w : cl.Closeds) :
        Set (Nonsimple ⊕ Vertex))).ncard =
      F.aWeight w.1 w.2 := by
  change (D.decoratedSet w).ncard =
    F.aWeight w.1 w.2
  rw [ncard_eq_card_parts]
  unfold decoratedSet
  have hparts :=
    setPartsEquiv_symm_parts
      (Nonsimple := Nonsimple)
      (Vertex := Vertex)
      (D.corePart w.1)
      (F.topSupport w.1 ∪
        freeVertices (F.topSupport w.1) w.2)
  rw [hparts.1, hparts.2]
  have hdisjoint :
      Disjoint (F.topSupport w.1)
        (freeVertices (F.topSupport w.1) w.2) := by
    rw [Finset.disjoint_left]
    intro v hvtop hvfree
    exact
      (not_mem_of_mem_freeVertices
        (F.topSupport w.1) w.2 hvfree) hvtop
  rw [Finset.card_union_of_disjoint hdisjoint,
    card_freeVertices, ← D.coreSize_eq_card]
  unfold aWeight baseWeight
  omega

/-- The generic top-coverage characterization constructs exactly the
`AClosedParametrization` expected by the polynomial adapter. -/
noncomputable def toAClosedParametrization :
    AClosedParametrization F cl where
  closedEquiv := D.decoratedClosedEquiv.symm
  ncard_closed C := by
    let w : Σ x : Core, F.AChoice x :=
      D.decoratedClosedEquiv.symm C
    have heq :
        D.decoratedClosedEquiv w = C :=
      D.decoratedClosedEquiv.apply_symm_apply C
    calc
      ((C : cl.Closeds) :
          Set (Nonsimple ⊕ Vertex)).ncard =
          (((D.decoratedClosedEquiv w : cl.Closeds) :
            Set (Nonsimple ⊕ Vertex))).ncard := by
        rw [heq]
      _ = F.aWeight w.1 w.2 :=
        D.ncard_decoratedClosed w
      _ = F.aWeight
          (D.decoratedClosedEquiv.symm C).1
          (D.decoratedClosedEquiv.symm C).2 := rfl

include D

/-- Polynomial consequence of the generic top-coverage
characterization. -/
theorem levelPolynomial_eq_aEnumerator :
    cl.levelPolynomial = F.aEnumerator :=
  AClosedParametrization.levelPolynomial_eq_aEnumerator
    (toAClosedParametrization D)

end ATopCoverageData

/-! ## Two-copy separated-side construction -/

/-- Split a set on `Nonsimple ⊕ (Vertex ⊕ Vertex)` into its nonsimple
part and its two simple copies. -/
noncomputable def tripleSetPartsEquiv :
    Set (Nonsimple ⊕ (Vertex ⊕ Vertex)) ≃
      Finset Nonsimple ×
        (Finset Vertex × Finset Vertex) :=
  (setPartsEquiv
      (Nonsimple := Nonsimple)
      (Vertex := Vertex ⊕ Vertex)).trans
    (Equiv.prodCongr (Equiv.refl _)
      Finset.sumEquiv.toEquiv)

/-- The nonsimple part of a separated-side full set. -/
noncomputable def bNonsimplePart
    (S : Set (Nonsimple ⊕ (Vertex ⊕ Vertex))) :
    Finset Nonsimple :=
  (tripleSetPartsEquiv S).1

/-- The simple copy in which `topSupport` is mandatory. -/
noncomputable def bCoveredSimplePart
    (S : Set (Nonsimple ⊕ (Vertex ⊕ Vertex))) :
    Finset Vertex :=
  (tripleSetPartsEquiv S).2.1

/-- The additional completely free simple copy. -/
noncomputable def bFreeSimplePart
    (S : Set (Nonsimple ⊕ (Vertex ⊕ Vertex))) :
    Finset Vertex :=
  (tripleSetPartsEquiv S).2.2

omit [DecidableEq Vertex] in
@[simp]
theorem mem_bNonsimplePart_iff
    (S : Set (Nonsimple ⊕ (Vertex ⊕ Vertex)))
    (y : Nonsimple) :
    y ∈ bNonsimplePart S ↔ Sum.inl y ∈ S := by
  simp [bNonsimplePart, tripleSetPartsEquiv, setPartsEquiv]
  exact Set.ext_iff.mp
    (Fintype.finsetEquivSet.apply_symm_apply S) _

omit [DecidableEq Vertex] in
@[simp]
theorem mem_bCoveredSimplePart_iff
    (S : Set (Nonsimple ⊕ (Vertex ⊕ Vertex)))
    (v : Vertex) :
    v ∈ bCoveredSimplePart S ↔
      Sum.inr (Sum.inl v) ∈ S := by
  simp [bCoveredSimplePart, tripleSetPartsEquiv, setPartsEquiv]
  exact Set.ext_iff.mp
    (Fintype.finsetEquivSet.apply_symm_apply S) _

omit [DecidableEq Vertex] in
@[simp]
theorem mem_bFreeSimplePart_iff
    (S : Set (Nonsimple ⊕ (Vertex ⊕ Vertex)))
    (v : Vertex) :
    v ∈ bFreeSimplePart S ↔
      Sum.inr (Sum.inr v) ∈ S := by
  simp [bFreeSimplePart, tripleSetPartsEquiv, setPartsEquiv]
  exact Set.ext_iff.mp
    (Fintype.finsetEquivSet.apply_symm_apply S) _

omit [DecidableEq Vertex] in
@[simp]
theorem tripleSetPartsEquiv_symm_parts
    (S₀ : Finset Nonsimple)
    (S₁ S₂ : Finset Vertex) :
    bNonsimplePart
        (tripleSetPartsEquiv.symm (S₀, (S₁, S₂))) =
      S₀ ∧
    bCoveredSimplePart
        (tripleSetPartsEquiv.symm (S₀, (S₁, S₂))) =
      S₁ ∧
    bFreeSimplePart
        (tripleSetPartsEquiv.symm (S₀, (S₁, S₂))) =
      S₂ := by
  simp [bNonsimplePart, bCoveredSimplePart,
    bFreeSimplePart]

omit [DecidableEq Vertex] in
/-- Cardinality is additive across all three separated-side parts. -/
theorem ncard_eq_card_tripleParts
    (S : Set (Nonsimple ⊕ (Vertex ⊕ Vertex))) :
    S.ncard =
      (bNonsimplePart S).card +
        (bCoveredSimplePart S).card +
          (bFreeSimplePart S).card := by
  classical
  let P : Finset Nonsimple × Finset (Vertex ⊕ Vertex) :=
    setPartsEquiv S
  have houter :=
    ncard_eq_card_parts
      (Nonsimple := Nonsimple)
      (Vertex := Vertex ⊕ Vertex) S
  have hinner :=
    Finset.card_toLeft_add_card_toRight (u := P.2)
  calc
    S.ncard = P.1.card + P.2.card := by
      simpa [P, nonsimplePart, simplePart] using houter
    _ = P.1.card +
        (P.2.toLeft.card + P.2.toRight.card) := by
      rw [hinner]
    _ = (bNonsimplePart S).card +
        (bCoveredSimplePart S).card +
          (bFreeSimplePart S).card := by
      simp [P, bNonsimplePart, bCoveredSimplePart,
        bFreeSimplePart, tripleSetPartsEquiv,
        Equiv.trans_apply, add_assoc]

/-- Purely combinatorial input for the separated-side top-coverage
construction.  The second simple copy is unrestricted by the iff. -/
structure BTopCoverageData
    (F : CoreFamily Core Vertex)
    (cl : OpConjecture.SetClosure
      (Nonsimple ⊕ (Vertex ⊕ Vertex))) where
  corePart : Core → Finset Nonsimple
  corePart_injective : Function.Injective corePart
  coreSize_eq_card (x : Core) :
    F.coreSize x = (corePart x).card
  isClosed_iff
      (S : Set (Nonsimple ⊕ (Vertex ⊕ Vertex))) :
    cl.IsClosed S ↔
      ∃ x : Core,
        bNonsimplePart S = corePart x ∧
          F.topSupport x ⊆ bCoveredSimplePart S

namespace BTopCoverageData

variable {F : CoreFamily Core Vertex}
  {cl : OpConjecture.SetClosure
    (Nonsimple ⊕ (Vertex ⊕ Vertex))}
  (D : BTopCoverageData F cl)

/-- The separated-side set represented by a common core, optional
vertices in the covered copy, and an arbitrary second-copy subset. -/
noncomputable def decoratedSet
    (w : Σ x : Core, F.BChoice x) :
    Set (Nonsimple ⊕ (Vertex ⊕ Vertex)) :=
  tripleSetPartsEquiv.symm
    (D.corePart w.1,
      (F.topSupport w.1 ∪
          freeVertices (F.topSupport w.1) w.2.1,
        w.2.2))

omit [Fintype Core] in
/-- Every separated-side decoration is closed by top coverage. -/
theorem isClosed_decoratedSet
    (w : Σ x : Core, F.BChoice x) :
    cl.IsClosed (D.decoratedSet w) := by
  rw [D.isClosed_iff]
  refine ⟨w.1, ?_, ?_⟩
  · simp [decoratedSet, bNonsimplePart]
  · simp [decoratedSet, bCoveredSimplePart]

/-- Regard a separated-side decoration as a closed set. -/
noncomputable def decoratedClosed
    (w : Σ x : Core, F.BChoice x) : cl.Closeds :=
  ⟨D.decoratedSet w, D.isClosed_decoratedSet w⟩

omit [Fintype Core] in
/-- Different separated-side decorations give different closed sets. -/
theorem decoratedClosed_injective :
    Function.Injective D.decoratedClosed := by
  rintro ⟨x, ⟨s, u⟩⟩ ⟨y, ⟨t, v⟩⟩ h
  have hset :
      D.decoratedSet ⟨x, (s, u)⟩ =
        D.decoratedSet ⟨y, (t, v)⟩ :=
    congrArg Subtype.val h
  have hparts :=
    congrArg (tripleSetPartsEquiv
      (Nonsimple := Nonsimple)
      (Vertex := Vertex)) hset
  have hpair :
      (D.corePart x,
          (F.topSupport x ∪
              freeVertices (F.topSupport x) s,
            u)) =
        (D.corePart y,
          (F.topSupport y ∪
              freeVertices (F.topSupport y) t,
            v)) := by
    simpa [decoratedSet] using hparts
  have hxy : x = y :=
    D.corePart_injective (congrArg Prod.fst hpair)
  subst y
  have hsimple :
      (F.topSupport x ∪
          freeVertices (F.topSupport x) s, u) =
        (F.topSupport x ∪
          freeVertices (F.topSupport x) t, v) :=
    congrArg Prod.snd hpair
  have hunion :
      F.topSupport x ∪
          freeVertices (F.topSupport x) s =
        F.topSupport x ∪
          freeVertices (F.topSupport x) t :=
    congrArg Prod.fst hsimple
  have hfree :
      freeVertices (F.topSupport x) s =
        freeVertices (F.topSupport x) t := by
    ext a
    by_cases ha : a ∈ F.topSupport x
    · have has :
          a ∉ freeVertices (F.topSupport x) s :=
        fun hmem ↦
          (not_mem_of_mem_freeVertices
            (F.topSupport x) s hmem) ha
      have hat :
          a ∉ freeVertices (F.topSupport x) t :=
        fun hmem ↦
          (not_mem_of_mem_freeVertices
            (F.topSupport x) t hmem) ha
      simp [has, hat]
    · have hm := Finset.ext_iff.mp hunion a
      simpa [ha] using hm
  have hst : s = t :=
    freeVertices_injective (F.topSupport x) hfree
  have huv : u = v :=
    congrArg Prod.snd hsimple
  subst t
  subst v
  rfl

omit [Fintype Core] in
/-- Every separated-side closed set is represented by a unique core,
the optional part of its covered copy, and its entire free copy. -/
theorem decoratedClosed_surjective :
    Function.Surjective D.decoratedClosed := by
  intro C
  obtain ⟨x, hcore, hcover⟩ :=
    (D.isClosed_iff
      (C : Set
        (Nonsimple ⊕ (Vertex ⊕ Vertex)))).mp C.property
  let extras :
      {S : Finset Vertex //
        ∀ a ∈ S, a ∈ (F.topSupport x)ᶜ} :=
    ⟨bCoveredSimplePart
          (C : Set
            (Nonsimple ⊕ (Vertex ⊕ Vertex))) \
        F.topSupport x, by
      intro a ha
      simp only [Finset.mem_sdiff, Finset.mem_compl] at ha ⊢
      exact ha.2⟩
  let s : F.AChoice x :=
    (Equiv.finsetSubtypeComm
      (fun a : Vertex ↦
        a ∈ (F.topSupport x)ᶜ)).symm extras
  let u : Finset Vertex :=
    bFreeSimplePart
      (C : Set
        (Nonsimple ⊕ (Vertex ⊕ Vertex)))
  have hfree :
      freeVertices (F.topSupport x) s =
        bCoveredSimplePart
            (C : Set
              (Nonsimple ⊕ (Vertex ⊕ Vertex))) \
          F.topSupport x := by
    change
      ((Equiv.finsetSubtypeComm
          (fun a : Vertex ↦
            a ∈ (F.topSupport x)ᶜ)) s).1 =
        bCoveredSimplePart
            (C : Set
              (Nonsimple ⊕ (Vertex ⊕ Vertex))) \
          F.topSupport x
    have happly :=
      (Equiv.finsetSubtypeComm
        (fun a : Vertex ↦
          a ∈ (F.topSupport x)ᶜ)).apply_symm_apply extras
    exact congrArg Subtype.val happly
  refine ⟨⟨x, (s, u)⟩, ?_⟩
  apply Subtype.ext
  apply
    (tripleSetPartsEquiv
      (Nonsimple := Nonsimple)
      (Vertex := Vertex)).injective
  change
    tripleSetPartsEquiv
        (D.decoratedSet ⟨x, (s, u)⟩) =
      tripleSetPartsEquiv
        (C : Set
          (Nonsimple ⊕ (Vertex ⊕ Vertex)))
  rw [decoratedSet, Equiv.apply_symm_apply]
  change
    (D.corePart x,
      (F.topSupport x ∪
          freeVertices (F.topSupport x) s,
        u)) =
      (bNonsimplePart
          (C : Set
            (Nonsimple ⊕ (Vertex ⊕ Vertex))),
        (bCoveredSimplePart
            (C : Set
              (Nonsimple ⊕ (Vertex ⊕ Vertex))),
          bFreeSimplePart
            (C : Set
              (Nonsimple ⊕ (Vertex ⊕ Vertex)))))
  rw [hfree, Finset.union_sdiff_of_subset hcover]
  exact congrArg
    (fun S : Finset Nonsimple ↦
      (S,
        (bCoveredSimplePart
            (C : Set
              (Nonsimple ⊕ (Vertex ⊕ Vertex))),
          bFreeSimplePart
            (C : Set
              (Nonsimple ⊕ (Vertex ⊕ Vertex)))))) hcore.symm

/-- Separated-side decorations and closed sets are equivalent. -/
noncomputable def decoratedClosedEquiv :
    (Σ x : Core, F.BChoice x) ≃ cl.Closeds :=
  Equiv.ofBijective D.decoratedClosed
    ⟨D.decoratedClosed_injective,
      D.decoratedClosed_surjective⟩

omit [Fintype Core] in
/-- The represented separated-side closed set has precisely its
combinatorial `bWeight`. -/
theorem ncard_decoratedClosed
    (w : Σ x : Core, F.BChoice x) :
    (((D.decoratedClosed w : cl.Closeds) :
        Set (Nonsimple ⊕ (Vertex ⊕ Vertex)))).ncard =
      F.bWeight w.1 w.2 := by
  change (D.decoratedSet w).ncard =
    F.bWeight w.1 w.2
  rw [ncard_eq_card_tripleParts]
  unfold decoratedSet
  have hparts :=
    tripleSetPartsEquiv_symm_parts
      (Nonsimple := Nonsimple)
      (Vertex := Vertex)
      (D.corePart w.1)
      (F.topSupport w.1 ∪
        freeVertices (F.topSupport w.1) w.2.1)
      w.2.2
  rw [hparts.1, hparts.2.1, hparts.2.2]
  have hdisjoint :
      Disjoint (F.topSupport w.1)
        (freeVertices (F.topSupport w.1) w.2.1) := by
    rw [Finset.disjoint_left]
    intro a hatop hafree
    exact
      (not_mem_of_mem_freeVertices
        (F.topSupport w.1) w.2.1 hafree) hatop
  rw [Finset.card_union_of_disjoint hdisjoint,
    card_freeVertices, ← D.coreSize_eq_card]
  unfold bWeight baseWeight
  omega

/-- The generic two-copy top-coverage characterization constructs the
`BClosedParametrization` expected by the polynomial adapter. -/
noncomputable def toBClosedParametrization :
    BClosedParametrization F cl where
  closedEquiv := D.decoratedClosedEquiv.symm
  ncard_closed C := by
    let w : Σ x : Core, F.BChoice x :=
      D.decoratedClosedEquiv.symm C
    have heq :
        D.decoratedClosedEquiv w = C :=
      D.decoratedClosedEquiv.apply_symm_apply C
    calc
      ((C : cl.Closeds) :
          Set
            (Nonsimple ⊕ (Vertex ⊕ Vertex))).ncard =
          (((D.decoratedClosedEquiv w : cl.Closeds) :
            Set
              (Nonsimple ⊕ (Vertex ⊕ Vertex)))).ncard := by
        rw [heq]
      _ = F.bWeight w.1 w.2 :=
        D.ncard_decoratedClosed w
      _ = F.bWeight
          (D.decoratedClosedEquiv.symm C).1
          (D.decoratedClosedEquiv.symm C).2 := rfl

include D

/-- Polynomial consequence of the generic two-copy top-coverage
characterization. -/
theorem levelPolynomial_eq_bEnumerator :
    cl.levelPolynomial = F.bEnumerator :=
  BClosedParametrization.levelPolynomial_eq_bEnumerator
    (toBClosedParametrization D)

end BTopCoverageData

/-- The full multiplication identity obtained from top-coverage
characterizations on two possibly different nonsimple ground types. -/
theorem levelPolynomial_B_eq_levelPolynomial_A_mul
    {NonsimpleA : Type w₁} {NonsimpleB : Type w₂}
    [Fintype NonsimpleA] [Fintype NonsimpleB]
    {F : CoreFamily Core Vertex}
    {clA : OpConjecture.SetClosure
      (NonsimpleA ⊕ Vertex)}
    {clB : OpConjecture.SetClosure
      (NonsimpleB ⊕ (Vertex ⊕ Vertex))}
    (DA : ATopCoverageData F clA)
    (DB : BTopCoverageData F clB) :
    clB.levelPolynomial =
      clA.levelPolynomial *
        (1 + X) ^ Fintype.card Vertex :=
  CoreFamily.levelPolynomial_B_eq_levelPolynomial_A_mul
    (ATopCoverageData.toAClosedParametrization DA)
    (BTopCoverageData.toBClosedParametrization DB)

end TopCoverage
end CoreFamily

end OpConjecture.RadicalSquareZeroCombinatorics
