import OpConjecture.RepresentationTheory.BottomTwoModules
import OpConjecture.ConvexGeometry.LevelPolynomial

/-!
# Conditional exact counts at closure level two

This file isolates the finite counting endpoint of the level-two
argument.  The representation-theoretic input is deliberately exposed as two
structures containing exact `iff` classifications.  No such classification is
asserted here.
-/

noncomputable section

open Set
open CategoryTheory CategoryTheory.Limits

namespace OpConjecture.IndecomposableSkeleton

universe u v w

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-! ## Finite parameter types -/

/-- Skeleton indices represented by indecomposables of composition length two. -/
def LengthTwoIndex :=
  {i : ι // σ.compositionLength i = 2}

/-- Unordered pairs of distinct simple skeleton indices. -/
def UnorderedSimplePair :=
  {P : Finset (σ.SimpleIndex) // P.card = 2}

/-- Quotient-closed supports at cardinality two. -/
def QClosedPair :=
  {C : σ.qClosure.Closeds // ((C : Set ι).ncard = 2)}

/-- Submodule-closed supports at cardinality two. -/
def SClosedPair :=
  {C : σ.sClosure.Closeds // ((C : Set ι).ncard = 2)}

/-- The embedding of simple skeleton indices into all skeleton indices. -/
def simpleIndexEmbedding : σ.SimpleIndex ↪ ι where
  toFun j := j.1
  inj' _ _ h := Subtype.ext h

/-- The underlying support of an unordered pair of simple indices. -/
def unorderedSimplePairSupport (P : σ.UnorderedSimplePair) : Set ι :=
  σ.simpleIndexEmbedding '' (P.1 : Set (σ.SimpleIndex))

@[simp]
theorem ncard_unorderedSimplePairSupport
    (P : σ.UnorderedSimplePair) :
    (σ.unorderedSimplePairSupport P).ncard = 2 := by
  rw [unorderedSimplePairSupport,
    Set.ncard_image_of_injective _ σ.simpleIndexEmbedding.injective,
    Set.ncard_coe_finset, P.2]

theorem simple_of_mem_unorderedSimplePairSupport
    (P : σ.UnorderedSimplePair) {i : ι}
    (hi : i ∈ σ.unorderedSimplePairSupport P) :
    Simple (σ.obj i) := by
  rcases hi with ⟨j, -, rfl⟩
  exact j.2

theorem unorderedSimplePairSupport_injective :
    Function.Injective σ.unorderedSimplePairSupport := by
  intro P Q hPQ
  apply Subtype.ext
  apply Finset.ext
  intro j
  have hmem :=
    Set.ext_iff.mp hPQ j.1
  constructor
  · intro hj
    have :
        σ.simpleIndexEmbedding j ∈
          σ.unorderedSimplePairSupport P := by
      exact ⟨j, hj, rfl⟩
    rw [hPQ] at this
    rcases this with ⟨k, hk, heq⟩
    have hkj : k = j :=
      σ.simpleIndexEmbedding.injective heq
    simpa [hkj] using hk
  · intro hj
    have :
        σ.simpleIndexEmbedding j ∈
          σ.unorderedSimplePairSupport Q := by
      exact ⟨j, hj, rfl⟩
    rw [← hPQ] at this
    rcases this with ⟨k, hk, heq⟩
    have hkj : k = j :=
      σ.simpleIndexEmbedding.injective heq
    simpa [hkj] using hk

/-- Every two-element support consisting of simple objects comes from a unique
unordered pair of simple skeleton indices. -/
theorem exists_unorderedSimplePair_of_ncard_of_forall_simple
    [Finite ι] (S : Set ι) (hcard : S.ncard = 2)
    (hsimple : ∀ i ∈ S, Simple (σ.obj i)) :
    ∃ P : σ.UnorderedSimplePair,
      σ.unorderedSimplePairSupport P = S := by
  classical
  letI := Fintype.ofFinite ι
  letI : Fintype (σ.SimpleIndex) := by
    unfold SimpleIndex
    infer_instance
  let P : Finset (σ.SimpleIndex) :=
    Finset.univ.filter fun j => j.1 ∈ S
  have hsupport :
      σ.simpleIndexEmbedding ''
          (P : Set (σ.SimpleIndex)) = S := by
    ext i
    constructor
    · rintro ⟨j, hj, rfl⟩
      change j.1 ∈ S
      simpa [P] using hj
    · intro hi
      refine ⟨⟨i, hsimple i hi⟩, ?_, rfl⟩
      simp [P, hi]
  have hPcard : P.card = 2 := by
    rw [← Set.ncard_coe_finset,
      ← Set.ncard_image_of_injective
        (P : Set (σ.SimpleIndex)) σ.simpleIndexEmbedding.injective,
      hsupport, hcard]
  exact ⟨⟨P, hPcard⟩, hsupport⟩

/-! ## Generic mixed-pair combinatorics -/

theorem lengthTwoIndex_not_simple (x : σ.LengthTwoIndex) :
    ¬ Simple (σ.obj x.1) := by
  intro hx
  have hone :=
    (σ.compositionLength_eq_one_iff_simple x.1).2 hx
  have htwo : σ.compositionLength x.1 = 2 := x.2
  omega

/-- A length-two index paired with a chosen simple index. -/
def lengthTwoPairSupport
    (partner : σ.LengthTwoIndex → σ.SimpleIndex)
    (x : σ.LengthTwoIndex) : Set ι :=
  {x.1, (partner x).1}

theorem lengthTwoIndex_ne_partner
    (partner : σ.LengthTwoIndex → σ.SimpleIndex)
    (x : σ.LengthTwoIndex) :
    x.1 ≠ (partner x).1 := by
  intro h
  apply σ.lengthTwoIndex_not_simple x
  simpa [h] using (partner x).2

@[simp]
theorem ncard_lengthTwoPairSupport
    (partner : σ.LengthTwoIndex → σ.SimpleIndex)
    (x : σ.LengthTwoIndex) :
    (σ.lengthTwoPairSupport partner x).ncard = 2 := by
  simp [lengthTwoPairSupport, σ.lengthTwoIndex_ne_partner partner x]

theorem lengthTwoPairSupport_injective
    (partner : σ.LengthTwoIndex → σ.SimpleIndex) :
    Function.Injective (σ.lengthTwoPairSupport partner) := by
  intro x y hxy
  apply Subtype.ext
  have hxmem :
      x.1 ∈ σ.lengthTwoPairSupport partner y := by
    rw [← hxy]
    simp [lengthTwoPairSupport]
  rcases (by
      simpa [lengthTwoPairSupport] using hxmem :
        x.1 = y.1 ∨ x.1 = (partner y).1) with h | h
  · exact h
  · exfalso
    apply σ.lengthTwoIndex_not_simple x
    simpa [h] using (partner y).2

/-- The support map from the disjoint parameter sum. -/
def twoPointParameterSupport
    (partner : σ.LengthTwoIndex → σ.SimpleIndex) :
    σ.UnorderedSimplePair ⊕ σ.LengthTwoIndex → Set ι
  | Sum.inl P => σ.unorderedSimplePairSupport P
  | Sum.inr x => σ.lengthTwoPairSupport partner x

theorem twoPointParameterSupport_injective
    (partner : σ.LengthTwoIndex → σ.SimpleIndex) :
    Function.Injective (σ.twoPointParameterSupport partner) := by
  intro a b hab
  cases a with
  | inl P =>
      cases b with
      | inl Q =>
          apply congrArg Sum.inl
          exact σ.unorderedSimplePairSupport_injective hab
      | inr y =>
          exfalso
          change σ.unorderedSimplePairSupport P =
            σ.lengthTwoPairSupport partner y at hab
          have hy :
              y.1 ∈ σ.unorderedSimplePairSupport P := by
            rw [hab]
            simp [lengthTwoPairSupport]
          exact σ.lengthTwoIndex_not_simple y
            (σ.simple_of_mem_unorderedSimplePairSupport P hy)
  | inr x =>
      cases b with
      | inl Q =>
          exfalso
          change σ.lengthTwoPairSupport partner x =
            σ.unorderedSimplePairSupport Q at hab
          have hx :
              x.1 ∈ σ.unorderedSimplePairSupport Q := by
            rw [← hab]
            simp [lengthTwoPairSupport]
          exact σ.lengthTwoIndex_not_simple x
            (σ.simple_of_mem_unorderedSimplePairSupport Q hx)
      | inr y =>
          apply congrArg Sum.inr
          exact σ.lengthTwoPairSupport_injective partner hab

/-! ## Exact classification hypotheses -/

/-- Exact input needed on the quotient side.  `top x` is a chosen simple
quotient of the length-two representative `x`; the reverse direction of
`isClosed_iff` includes the collective finite-sum closure assertion. -/
structure QLevelTwoClassification where
  top : ∀ x : σ.LengthTwoIndex, σ.SimpleQuotient x.1
  isClosed_iff (S : Set ι) (hcard : S.ncard = 2) :
    σ.qClosure.IsClosed S ↔
      (∀ i ∈ S, Simple (σ.obj i)) ∨
      ∃ x : σ.LengthTwoIndex,
        S = {x.1, (top x).index}

/-- Exact input needed on the submodule side.  `socle x` is a chosen simple
submodule of the length-two representative `x`; the reverse direction of
`isClosed_iff` includes the collective finite-sum closure assertion. -/
structure SLevelTwoClassification where
  socle : ∀ x : σ.LengthTwoIndex, σ.SimpleSubmodule x.1
  isClosed_iff (S : Set ι) (hcard : S.ncard = 2) :
    σ.sClosure.IsClosed S ↔
      (∀ i ∈ S, Simple (σ.obj i)) ∨
      ∃ x : σ.LengthTwoIndex,
        S = {x.1, (socle x).index}

def QLevelTwoClassification.topIndex
    (H : σ.QLevelTwoClassification)
    (x : σ.LengthTwoIndex) : σ.SimpleIndex :=
  ⟨(H.top x).index, (H.top x).simple⟩

def SLevelTwoClassification.socleIndex
    (H : σ.SLevelTwoClassification)
    (x : σ.LengthTwoIndex) : σ.SimpleIndex :=
  ⟨(H.socle x).index, (H.socle x).simple⟩

/-! ## Constructors from local representation-theoretic inputs -/

/--
Construct the exact quotient-side classification from its two local
representation-theoretic ingredients:

* every closed mixed pair has length-two nonsimple member;
* the nonsimple member paired with a chosen simple top is collectively
  quotient closed.
-/
def qLevelTwoClassification_of_local
    (top : ∀ x : σ.LengthTwoIndex,
      σ.SimpleQuotient x.1)
    (mixed_length_two :
      ∀ {x s : ι},
        σ.qClosure.IsClosed ({x, s} : Set ι) →
          ¬ Simple (σ.obj x) →
            Simple (σ.obj s) →
              σ.compositionLength x = 2)
    (pair_closed :
      ∀ x : σ.LengthTwoIndex,
        σ.qClosure.IsClosed
          ({x.1, (top x).index} : Set ι)) :
    σ.QLevelTwoClassification where
  top := top
  isClosed_iff S hcard := by
    constructor
    · intro hclosed
      rcases σ.qClosed_pair_classification hcard hclosed with
        hsimple | ⟨x, s, -, hS, hx, hunique⟩
      · exact Or.inl hsimple
      · have hpair :
            σ.qClosure.IsClosed ({x, s} : Set ι) := by
          rw [← hS]
          exact hclosed
        have hxLength :
            σ.compositionLength x = 2 :=
          mixed_length_two hpair hx hunique.1
        let x₂ : σ.LengthTwoIndex :=
          ⟨x, hxLength⟩
        have htop :
            (top x₂).index = s :=
          hunique.2 (top x₂)
        refine Or.inr ⟨x₂, ?_⟩
        simpa [x₂, htop] using hS
    · rintro (hsimple | ⟨x, hS⟩)
      · exact σ.qClosure_isClosed_of_forall_simple hsimple
      · rw [hS]
        exact pair_closed x

/--
Submodule-side companion to
`qLevelTwoClassification_of_local`.
-/
def sLevelTwoClassification_of_local
    (socle : ∀ x : σ.LengthTwoIndex,
      σ.SimpleSubmodule x.1)
    (mixed_length_two :
      ∀ {x s : ι},
        σ.sClosure.IsClosed ({x, s} : Set ι) →
          ¬ Simple (σ.obj x) →
            Simple (σ.obj s) →
              σ.compositionLength x = 2)
    (pair_closed :
      ∀ x : σ.LengthTwoIndex,
        σ.sClosure.IsClosed
          ({x.1, (socle x).index} : Set ι)) :
    σ.SLevelTwoClassification where
  socle := socle
  isClosed_iff S hcard := by
    constructor
    · intro hclosed
      rcases σ.sClosed_pair_classification hcard hclosed with
        hsimple | ⟨x, s, -, hS, hx, hunique⟩
      · exact Or.inl hsimple
      · have hpair :
            σ.sClosure.IsClosed ({x, s} : Set ι) := by
          rw [← hS]
          exact hclosed
        have hxLength :
            σ.compositionLength x = 2 :=
          mixed_length_two hpair hx hunique.1
        let x₂ : σ.LengthTwoIndex :=
          ⟨x, hxLength⟩
        have hsocle :
            (socle x₂).index = s :=
          hunique.2 (socle x₂)
        refine Or.inr ⟨x₂, ?_⟩
        simpa [x₂, hsocle] using hS
    · rintro (hsimple | ⟨x, hS⟩)
      · exact σ.sClosure_isClosed_of_forall_simple hsimple
      · rw [hS]
        exact pair_closed x

/-! ## Equivalences with the two closure levels -/

/-- Send either an unordered simple pair or a length-two representative to
its quotient-closed two-point support. -/
def qParameterToClosedPair
    (H : σ.QLevelTwoClassification) :
    σ.UnorderedSimplePair ⊕ σ.LengthTwoIndex → σ.QClosedPair
  | Sum.inl P =>
      ⟨⟨σ.unorderedSimplePairSupport P,
          σ.qClosure_isClosed_of_forall_simple
            (fun i hi =>
              σ.simple_of_mem_unorderedSimplePairSupport P hi)⟩,
        σ.ncard_unorderedSimplePairSupport P⟩
  | Sum.inr x =>
      ⟨⟨σ.lengthTwoPairSupport H.topIndex x,
          (H.isClosed_iff
            (σ.lengthTwoPairSupport H.topIndex x)
            (σ.ncard_lengthTwoPairSupport H.topIndex x)).2
              (Or.inr ⟨x, by
                rfl⟩)⟩,
        σ.ncard_lengthTwoPairSupport H.topIndex x⟩

/-- Send either an unordered simple pair or a length-two representative to
its submodule-closed two-point support. -/
def sParameterToClosedPair
    (H : σ.SLevelTwoClassification) :
    σ.UnorderedSimplePair ⊕ σ.LengthTwoIndex → σ.SClosedPair
  | Sum.inl P =>
      ⟨⟨σ.unorderedSimplePairSupport P,
          σ.sClosure_isClosed_of_forall_simple
            (fun i hi =>
              σ.simple_of_mem_unorderedSimplePairSupport P hi)⟩,
        σ.ncard_unorderedSimplePairSupport P⟩
  | Sum.inr x =>
      ⟨⟨σ.lengthTwoPairSupport H.socleIndex x,
          (H.isClosed_iff
            (σ.lengthTwoPairSupport H.socleIndex x)
            (σ.ncard_lengthTwoPairSupport H.socleIndex x)).2
              (Or.inr ⟨x, by
                rfl⟩)⟩,
        σ.ncard_lengthTwoPairSupport H.socleIndex x⟩

@[simp]
theorem coe_qParameterToClosedPair
    (H : σ.QLevelTwoClassification)
    (a : σ.UnorderedSimplePair ⊕ σ.LengthTwoIndex) :
    ((σ.qParameterToClosedPair H a).1 : Set ι) =
      σ.twoPointParameterSupport H.topIndex a := by
  cases a <;> rfl

@[simp]
theorem coe_sParameterToClosedPair
    (H : σ.SLevelTwoClassification)
    (a : σ.UnorderedSimplePair ⊕ σ.LengthTwoIndex) :
    ((σ.sParameterToClosedPair H a).1 : Set ι) =
      σ.twoPointParameterSupport H.socleIndex a := by
  cases a <;> rfl

theorem qParameterToClosedPair_injective
    (H : σ.QLevelTwoClassification) :
    Function.Injective (σ.qParameterToClosedPair H) := by
  intro a b hab
  apply σ.twoPointParameterSupport_injective H.topIndex
  have hsupport := congrArg
    (fun C : σ.QClosedPair => (C.1 : Set ι)) hab
  simpa using hsupport

theorem sParameterToClosedPair_injective
    (H : σ.SLevelTwoClassification) :
    Function.Injective (σ.sParameterToClosedPair H) := by
  intro a b hab
  apply σ.twoPointParameterSupport_injective H.socleIndex
  have hsupport := congrArg
    (fun C : σ.SClosedPair => (C.1 : Set ι)) hab
  simpa using hsupport

theorem qParameterToClosedPair_surjective
    [Finite ι] (H : σ.QLevelTwoClassification) :
    Function.Surjective (σ.qParameterToClosedPair H) := by
  intro C
  have hclass :=
    (H.isClosed_iff (C.1 : Set ι) C.2).1 C.1.2
  rcases hclass with hsimple | ⟨x, hx⟩
  · obtain ⟨P, hP⟩ :=
      σ.exists_unorderedSimplePair_of_ncard_of_forall_simple
        (C.1 : Set ι) C.2 hsimple
    refine ⟨Sum.inl P, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hP
  · refine ⟨Sum.inr x, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hx.symm

theorem sParameterToClosedPair_surjective
    [Finite ι] (H : σ.SLevelTwoClassification) :
    Function.Surjective (σ.sParameterToClosedPair H) := by
  intro C
  have hclass :=
    (H.isClosed_iff (C.1 : Set ι) C.2).1 C.1.2
  rcases hclass with hsimple | ⟨x, hx⟩
  · obtain ⟨P, hP⟩ :=
      σ.exists_unorderedSimplePair_of_ncard_of_forall_simple
        (C.1 : Set ι) C.2 hsimple
    refine ⟨Sum.inl P, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hP
  · refine ⟨Sum.inr x, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hx.symm

/-- Conditional exact enumeration of quotient-closed supports at level two. -/
def qLevelTwoEquiv [Finite ι]
    (H : σ.QLevelTwoClassification) :
    σ.UnorderedSimplePair ⊕ σ.LengthTwoIndex ≃ σ.QClosedPair :=
  Equiv.ofBijective (σ.qParameterToClosedPair H)
    ⟨σ.qParameterToClosedPair_injective H,
      σ.qParameterToClosedPair_surjective H⟩

/-- Conditional exact enumeration of submodule-closed supports at level two. -/
def sLevelTwoEquiv [Finite ι]
    (H : σ.SLevelTwoClassification) :
    σ.UnorderedSimplePair ⊕ σ.LengthTwoIndex ≃ σ.SClosedPair :=
  Equiv.ofBijective (σ.sParameterToClosedPair H)
    ⟨σ.sParameterToClosedPair_injective H,
      σ.sParameterToClosedPair_surjective H⟩

/-! ## Exact level-two formulas -/

theorem levelCount_two_eq_natCard_qClosedPair [Finite ι] :
    σ.qClosure.levelCount 2 = Nat.card σ.QClosedPair := by
  unfold OpConjecture.SetClosure.levelCount
  calc
    {C : σ.qClosure.Closeds | (C : Set ι).ncard = 2}.ncard =
        Nat.card {C : σ.qClosure.Closeds //
          (C : Set ι).ncard = 2} :=
      (Nat.card_coe_set_eq _).symm
    _ = Nat.card σ.QClosedPair := rfl

theorem levelCount_two_eq_natCard_sClosedPair [Finite ι] :
    σ.sClosure.levelCount 2 = Nat.card σ.SClosedPair := by
  unfold OpConjecture.SetClosure.levelCount
  calc
    {C : σ.sClosure.Closeds | (C : Set ι).ncard = 2}.ncard =
        Nat.card {C : σ.sClosure.Closeds //
          (C : Set ι).ncard = 2} :=
      (Nat.card_coe_set_eq _).symm
    _ = Nat.card σ.SClosedPair := rfl

theorem natCard_unorderedSimplePair [Finite ι] :
    Nat.card σ.UnorderedSimplePair =
      Nat.choose (Nat.card σ.SimpleIndex) 2 := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  letI : Fintype (σ.SimpleIndex) := by
    unfold SimpleIndex
    infer_instance
  letI : Fintype (σ.UnorderedSimplePair) := by
    unfold UnorderedSimplePair
    infer_instance
  rw [Nat.card_eq_fintype_card]
  change Fintype.card
      {P : Finset (σ.SimpleIndex) // P.card = 2} =
    Nat.choose (Nat.card σ.SimpleIndex) 2
  rw [Fintype.card_finset_len, Nat.card_eq_fintype_card]

/-- The quotient-side level-two formula, conditional only on the exact
classification packaged by `H`. -/
theorem qLevelCount_two_formula [Finite ι]
    (H : σ.QLevelTwoClassification) :
    σ.qClosure.levelCount 2 =
      Nat.choose (Nat.card σ.SimpleIndex) 2 +
        Nat.card σ.LengthTwoIndex := by
  rw [σ.levelCount_two_eq_natCard_qClosedPair,
    Nat.card_congr (σ.qLevelTwoEquiv H).symm]
  haveI : Finite σ.UnorderedSimplePair := by
    unfold UnorderedSimplePair SimpleIndex
    infer_instance
  haveI : Finite σ.LengthTwoIndex := by
    unfold LengthTwoIndex
    infer_instance
  rw [Nat.card_sum, σ.natCard_unorderedSimplePair]

/-- The submodule-side level-two formula, conditional only on the exact
classification packaged by `H`. -/
theorem sLevelCount_two_formula [Finite ι]
    (H : σ.SLevelTwoClassification) :
    σ.sClosure.levelCount 2 =
      Nat.choose (Nat.card σ.SimpleIndex) 2 +
        Nat.card σ.LengthTwoIndex := by
  rw [σ.levelCount_two_eq_natCard_sClosedPair,
    Nat.card_congr (σ.sLevelTwoEquiv H).symm]
  haveI : Finite σ.UnorderedSimplePair := by
    unfold UnorderedSimplePair SimpleIndex
    infer_instance
  haveI : Finite σ.LengthTwoIndex := by
    unfold LengthTwoIndex
    infer_instance
  rw [Nat.card_sum, σ.natCard_unorderedSimplePair]

/-- Once the quotient and submodule classifications use the same skeleton
length-two index type, their second closure levels agree. -/
theorem qLevelCount_two_eq_sLevelCount_two [Finite ι]
    (Hq : σ.QLevelTwoClassification)
    (Hs : σ.SLevelTwoClassification) :
    σ.qClosure.levelCount 2 = σ.sClosure.levelCount 2 := by
  rw [σ.qLevelCount_two_formula Hq,
    σ.sLevelCount_two_formula Hs]

end OpConjecture.IndecomposableSkeleton
