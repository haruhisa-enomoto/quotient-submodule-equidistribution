import OpConjecture.RepresentationTheory.ArtinFaithfulCore

/-!
# Abstract faithful triples over Artin factors

This file supplies the classification-free part of the direct bottom-three
argument.  A faithful closed triple can occur only when the common Ringel core
has size two or three.  In the size-three case the triple is uniquely the
core.  Exact-annihilator decomposition therefore splits the full third level
into core-three factors and faithful triples over core-two factors.

No concrete algebra or indecomposable-module classification is used.
-/

noncomputable section

open Set

namespace OpConjecture.IndecomposableSkeleton.FaithfulCore

universe u v vq w

open OpConjecture.AnnihilatorInflation
open OpConjecture.IndecomposableSkeleton
open OpConjecture.BottomLevels

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v}
  (σ : IndecomposableSkeleton.{u, v, u} R ι)

private theorem not_subsingleton_of_mem_skeleton
    {C : Set ι} {i : ι} (_hi : i ∈ C) :
    ¬ Subsingleton (σ.obj i) :=
  not_subsingleton_iff_nontrivial.mpr (σ.indecomposable i).nontrivial

private theorem core_ncard_ne_zero_of_faithful_triple
    {c : OpConjecture.SetClosure ι}
    (M : MinimalFaithfulCore.Data c (IsFaithfulSupport σ.obj))
    (C : c.Closeds)
    (hCfaithful : IsFaithfulSupport σ.obj (C : Set ι))
    (hCcard : (C : Set ι).ncard = 3) :
    (M.core : Set ι).ncard ≠ 0 := by
  classical
  have hCfinite : (C : Set ι).Finite :=
    Set.finite_of_ncard_ne_zero (by omega)
  have hsubset : (M.core : Set ι) ⊆ (C : Set ι) :=
    M.core_le C hCfaithful
  have hcoreFinite : (M.core : Set ι).Finite :=
    hCfinite.subset hsubset
  intro hzero
  have hcoreEmpty : (M.core : Set ι) = ∅ :=
    (Set.ncard_eq_zero hcoreFinite).mp hzero
  have htopbot : (⊤ : TwoSidedIdeal R) = ⊥ := by
    simpa [hcoreEmpty, IsFaithfulSupport] using M.core_faithful
  have hone : (1 : R) = 0 := by
    have honeMem : (1 : R) ∈ (⊥ : TwoSidedIdeal R) := by
      rw [← htopbot]
      exact Set.mem_univ 1
    simpa using honeMem
  obtain ⟨i, hi⟩ := Set.nonempty_of_ncard_ne_zero (by omega :
    (C : Set ι).ncard ≠ 0)
  apply not_subsingleton_of_mem_skeleton σ hi
  constructor
  intro x y
  have hx : x = 0 := by
    calc
      x = (1 : R) • x := (one_smul R x).symm
      _ = (0 : R) • x := by rw [hone]
      _ = 0 := zero_smul R x
  have hy : y = 0 := by
    calc
      y = (1 : R) • y := (one_smul R y).symm
      _ = (0 : R) • y := by rw [hone]
      _ = 0 := zero_smul R y
  exact hx.trans hy.symm

private theorem core_ncard_le_three_of_faithful_triple
    {c : OpConjecture.SetClosure ι}
    (M : MinimalFaithfulCore.Data c (IsFaithfulSupport σ.obj))
    (C : c.Closeds)
    (hCfaithful : IsFaithfulSupport σ.obj (C : Set ι))
    (hCcard : (C : Set ι).ncard = 3) :
    (M.core : Set ι).ncard ≤ 3 := by
  have hCfinite : (C : Set ι).Finite :=
    Set.finite_of_ncard_ne_zero (by omega)
  have hle := Set.ncard_le_ncard (M.core_le C hCfaithful) hCfinite
  simpa only [hCcard] using hle

private theorem faithful_triple_eq_core_of_core_ncard_eq_three
    {c : OpConjecture.SetClosure ι}
    (M : MinimalFaithfulCore.Data c (IsFaithfulSupport σ.obj))
    (C : c.Closeds)
    (hCfaithful : IsFaithfulSupport σ.obj (C : Set ι))
    (hCcard : (C : Set ι).ncard = 3)
    (hcore : (M.core : Set ι).ncard = 3) :
    (C : Set ι) = (M.core : Set ι) := by
  have hCfinite : (C : Set ι).Finite :=
    Set.finite_of_ncard_ne_zero (by omega)
  exact (Set.eq_of_subset_of_ncard_le (M.core_le C hCfaithful)
    (by omega) hCfinite).symm

/-- A faithful quotient-closed triple contains a core of size at most three. -/
theorem quotientCore_ncard_le_three_of_faithfulQTriple
    (normal : ClosedFaithfulNormalForm σ
      (IsFaithfulSupport σ.obj) (IsFaithfulSupport σ.obj))
    (C : σ.qClosure.Closeds)
    (hCfaithful : IsFaithfulSupport σ.obj (C : Set ι))
    (hCcard : (C : Set ι).ncard = 3) :
    (quotientCore σ : Set ι).ncard ≤ 3 := by
  let Q := quotientCoreData σ normal
  simpa only [Q, quotientCoreData_core] using
    core_ncard_le_three_of_faithful_triple σ Q C hCfaithful hCcard

/-- The same core-size bound on the submodule side. -/
theorem submoduleCore_ncard_le_three_of_faithfulSTriple
    (normal : ClosedFaithfulNormalForm σ
      (IsFaithfulSupport σ.obj) (IsFaithfulSupport σ.obj))
    (C : σ.sClosure.Closeds)
    (hCfaithful : IsFaithfulSupport σ.obj (C : Set ι))
    (hCcard : (C : Set ι).ncard = 3) :
    (submoduleCore σ : Set ι).ncard ≤ 3 := by
  let S := submoduleCoreData σ normal
  simpa only [S, submoduleCoreData_core] using
    core_ncard_le_three_of_faithful_triple σ S C hCfaithful hCcard

/-- At common core size three, the faithful quotient triple is the core. -/
theorem faithfulQTriple_eq_quotientCore
    (normal : ClosedFaithfulNormalForm σ
      (IsFaithfulSupport σ.obj) (IsFaithfulSupport σ.obj))
    (C : σ.qClosure.Closeds)
    (hCfaithful : IsFaithfulSupport σ.obj (C : Set ι))
    (hCcard : (C : Set ι).ncard = 3)
    (hcore : (quotientCore σ : Set ι).ncard = 3) :
    (C : Set ι) = (quotientCore σ : Set ι) := by
  let Q := quotientCoreData σ normal
  simpa only [Q, quotientCoreData_core] using
    faithful_triple_eq_core_of_core_ncard_eq_three
      σ Q C hCfaithful hCcard hcore

/-- At common core size three, the faithful submodule triple is the core. -/
theorem faithfulSTriple_eq_submoduleCore
    (normal : ClosedFaithfulNormalForm σ
      (IsFaithfulSupport σ.obj) (IsFaithfulSupport σ.obj))
    (C : σ.sClosure.Closeds)
    (hCfaithful : IsFaithfulSupport σ.obj (C : Set ι))
    (hCcard : (C : Set ι).ncard = 3)
    (hcore : (submoduleCore σ : Set ι).ncard = 3) :
    (C : Set ι) = (submoduleCore σ : Set ι) := by
  let S := submoduleCoreData σ normal
  simpa only [S, submoduleCoreData_core] using
    faithful_triple_eq_core_of_core_ncard_eq_three
      σ S C hCfaithful hCcard hcore

/-- A faithful quotient triple can occur only over a factor whose common
Ringel core has size two or three. -/
theorem quotientCore_ncard_eq_two_or_three_of_faithfulQTriple
    (normal : ClosedFaithfulNormalForm σ
      (IsFaithfulSupport σ.obj) (IsFaithfulSupport σ.obj))
    (e :
      {i // i ∈ (submoduleCore σ : Set ι)} ≃
        {i // i ∈ (quotientCore σ : Set ι)})
    (C : σ.qClosure.Closeds)
    (hCfaithful : IsFaithfulSupport σ.obj (C : Set ι))
    (hCcard : (C : Set ι).ncard = 3) :
    (quotientCore σ : Set ι).ncard = 2 ∨
      (quotientCore σ : Set ι).ncard = 3 := by
  let Q := quotientCoreData σ normal
  have hle : (quotientCore σ : Set ι).ncard ≤ 3 :=
    quotientCore_ncard_le_three_of_faithfulQTriple
      σ normal C hCfaithful hCcard
  have hnezero : (quotientCore σ : Set ι).ncard ≠ 0 := by
    simpa only [Q, quotientCoreData_core] using
      core_ncard_ne_zero_of_faithful_triple σ Q C hCfaithful hCcard
  have hneone : (quotientCore σ : Set ι).ncard ≠ 1 := by
    intro hone
    letI : Subsingleton ι :=
      subsingleton_of_quotientCore_ncard_eq_one σ e hone
    have hCle : (C : Set ι).ncard ≤ 1 :=
      Set.ncard_le_one_of_subsingleton (C : Set ι)
    omega
  omega

/-- A faithful submodule triple has the same two-or-three common-core
dichotomy.  The conclusion uses the quotient core, the convention for `d`. -/
theorem quotientCore_ncard_eq_two_or_three_of_faithfulSTriple
    (normal : ClosedFaithfulNormalForm σ
      (IsFaithfulSupport σ.obj) (IsFaithfulSupport σ.obj))
    (e :
      {i // i ∈ (submoduleCore σ : Set ι)} ≃
        {i // i ∈ (quotientCore σ : Set ι)})
    (C : σ.sClosure.Closeds)
    (hCfaithful : IsFaithfulSupport σ.obj (C : Set ι))
    (hCcard : (C : Set ι).ncard = 3) :
    (quotientCore σ : Set ι).ncard = 2 ∨
      (quotientCore σ : Set ι).ncard = 3 := by
  let S := submoduleCoreData σ normal
  have hsle : (submoduleCore σ : Set ι).ncard ≤ 3 :=
    submoduleCore_ncard_le_three_of_faithfulSTriple
      σ normal C hCfaithful hCcard
  have hsnezero : (submoduleCore σ : Set ι).ncard ≠ 0 := by
    simpa only [S, submoduleCoreData_core] using
      core_ncard_ne_zero_of_faithful_triple σ S C hCfaithful hCcard
  have hsneone : (submoduleCore σ : Set ι).ncard ≠ 1 := by
    intro hone
    letI : Subsingleton ι :=
      subsingleton_of_submoduleCore_ncard_eq_one σ hone
    have hCle : (C : Set ι).ncard ≤ 1 :=
      Set.ncard_le_one_of_subsingleton (C : Set ι)
    omega
  have hs : (submoduleCore σ : Set ι).ncard = 2 ∨
      (submoduleCore σ : Set ι).ncard = 3 := by
    omega
  rw [Set.ncard_congr' e] at hs
  exact hs

/-! ## Faithful triples on a skeleton with at most three labels -/

section AtMostThreeLabels

variable [Finite ι]

/-- Faithful quotient-closed triples on one fixed skeleton. -/
abbrev SkeletonFaithfulQTriple :=
  {C : σ.qClosure.Closeds //
    IsFaithfulSupport σ.obj (C : Set ι) ∧
      (C : Set ι).ncard = 3}

/-- Faithful submodule-closed triples on one fixed skeleton. -/
abbrev SkeletonFaithfulSTriple :=
  {C : σ.sClosure.Closeds //
    IsFaithfulSupport σ.obj (C : Set ι) ∧
      (C : Set ι).ncard = 3}

private theorem support_ncard_le_index_card
    (C : Set ι) : C.ncard ≤ Nat.card ι := by
  simpa [Set.ncard_univ] using
    Set.ncard_le_ncard (Set.subset_univ C)
      (Set.finite_univ : (Set.univ : Set ι).Finite)

private theorem index_card_eq_three_of_level_three
    {c : OpConjecture.SetClosure ι}
    (hle : Nat.card ι ≤ 3)
    (C : {C : c.Closeds // (C : Set ι).ncard = 3}) :
    Nat.card ι = 3 := by
  have hsupport := support_ncard_le_index_card (ι := ι) (C.1 : Set ι)
  rw [C.2] at hsupport
  omega

private theorem closed_level_three_eq_top
    {c : OpConjecture.SetClosure ι}
    (hle : Nat.card ι ≤ 3)
    (C : {C : c.Closeds // (C : Set ι).ncard = 3}) :
    C.1 = ⊤ := by
  apply Subtype.ext
  exact (Set.eq_univ_iff_ncard (C.1 : Set ι)).2
    (C.2.trans (index_card_eq_three_of_level_three hle C).symm)

/-- On a finite skeleton with at most three labels, a faithful
quotient-closed level-three fiber is a subsingleton: every support in it is
the whole skeleton. -/
theorem faithfulQLevel_three_subsingleton_of_natCard_le
    (hle : Nat.card ι ≤ 3) :
    Subsingleton (SkeletonFaithfulQTriple σ) := by
  constructor
  intro C D
  apply Subtype.ext
  exact (closed_level_three_eq_top hle ⟨C.1, C.2.2⟩).trans
    (closed_level_three_eq_top hle ⟨D.1, D.2.2⟩).symm

/-- The same uniqueness statement for faithful submodule-closed triples. -/
theorem faithfulSLevel_three_subsingleton_of_natCard_le
    (hle : Nat.card ι ≤ 3) :
    Subsingleton (SkeletonFaithfulSTriple σ) := by
  constructor
  intro C D
  apply Subtype.ext
  exact (closed_level_three_eq_top hle ⟨C.1, C.2.2⟩).trans
    (closed_level_three_eq_top hle ⟨D.1, D.2.2⟩).symm

variable
  (normal : ClosedFaithfulNormalForm σ
    (IsFaithfulSupport σ.obj) (IsFaithfulSupport σ.obj))

include normal

omit [Finite ι] in
private theorem univ_isFaithfulSupport :
    IsFaithfulSupport σ.obj (Set.univ : Set ι) := by
  let Q := quotientCoreData σ normal
  exact isFaithfulSupport_monotone σ.obj (Set.subset_univ _)
    (by simpa only [Q, quotientCoreData_core] using Q.core_faithful)

private def topFaithfulQLevelThree
    (hcard : Nat.card ι = 3) :
    SkeletonFaithfulQTriple σ := by
  refine ⟨⊤, ?_, ?_⟩
  · simpa using univ_isFaithfulSupport σ normal
  · simpa [Set.ncard_univ] using hcard

private def topFaithfulSLevelThree
    (hcard : Nat.card ι = 3) :
    SkeletonFaithfulSTriple σ := by
  refine ⟨⊤, ?_, ?_⟩
  · simpa using univ_isFaithfulSupport σ normal
  · simpa [Set.ncard_univ] using hcard

/-- On a finite skeleton with at most three labels, a faithful quotient
triple exists exactly when the complete indecomposable skeleton has three
labels. -/
theorem nonempty_faithfulQLevel_three_iff_natCard_eq
    (hle : Nat.card ι ≤ 3) :
    Nonempty (SkeletonFaithfulQTriple σ) ↔
      Nat.card ι = 3 := by
  constructor
  · rintro ⟨C⟩
    exact index_card_eq_three_of_level_three hle ⟨C.1, C.2.2⟩
  · intro hcard
    exact ⟨topFaithfulQLevelThree σ normal hcard⟩

/-- The identical existence criterion for faithful submodule triples. -/
theorem nonempty_faithfulSLevel_three_iff_natCard_eq
    (hle : Nat.card ι ≤ 3) :
    Nonempty (SkeletonFaithfulSTriple σ) ↔
      Nat.card ι = 3 := by
  constructor
  · rintro ⟨C⟩
    exact index_card_eq_three_of_level_three hle ⟨C.1, C.2.2⟩
  · intro hcard
    exact ⟨topFaithfulSLevelThree σ normal hcard⟩

end AtMostThreeLabels

/-! ## Global annihilator split at level three -/

/-- Quotient-closed triples on the ambient skeleton. -/
abbrev ArtinQTriple :=
  ArtinQLevel σ 3

/-- Submodule-closed triples on the ambient skeleton. -/
abbrev ArtinSTriple :=
  ArtinSLevel σ 3

section FactorwiseAssembly

variable {L : TwoSidedIdeal R → Type vq}
  [factorNoetherian :
    ∀ I : TwoSidedIdeal R,
      IsNoetherianRing (Quotient.Factor I)]
  (τ : ∀ I : TwoSidedIdeal R,
    IndecomposableSkeleton.{u, vq, u} (Quotient.Factor I) (L I))
  (D : ∀ I : TwoSidedIdeal R,
    Skeleton.InflationData σ I (τ I))
  (normal : ∀ I : TwoSidedIdeal R,
    ClosedFaithfulNormalForm (τ I)
      (IsFaithfulSupport (τ I).obj)
      (IsFaithfulSupport (τ I).obj))
  (coreEquiv : ∀ I : TwoSidedIdeal R,
    {i // i ∈ (submoduleCore (τ I) : Set (L I))} ≃
      {i // i ∈ (quotientCore (τ I) : Set (L I))})

/-- Ideals whose factor has common Ringel core size three. -/
abbrev CoreThreeIdeal :=
  {I : TwoSidedIdeal R //
    (quotientCore (τ I) : Set (L I)).ncard = 3}

/-- The level-three quotient side as faithful triples over all factors. -/
abbrev FactorFaithfulQTriples :=
  Σ I : TwoSidedIdeal R,
    Skeleton.InflationData.FaithfulQLevel I (τ I) 3

/-- The level-three submodule side as faithful triples over all factors. -/
abbrev FactorFaithfulSTriples :=
  Σ I : TwoSidedIdeal R,
    Skeleton.InflationData.FaithfulSLevel I (τ I) 3

/-- Faithful quotient triples over precisely the core-two factors. -/
abbrev CoreTwoFaithfulQTriples :=
  Σ I : CoreTwoIdeal τ,
    Skeleton.InflationData.FaithfulQLevel I.1 (τ I.1) 3

/-- Faithful submodule triples over precisely the core-two factors. -/
abbrev CoreTwoFaithfulSTriples :=
  Σ I : CoreTwoIdeal τ,
    Skeleton.InflationData.FaithfulSLevel I.1 (τ I.1) 3

private def quotientCoreFaithfulTriple
    (I : CoreThreeIdeal τ) :
    Skeleton.InflationData.FaithfulQLevel I.1 (τ I.1) 3 := by
  let Q := quotientCoreData (τ I.1) (normal I.1)
  exact ⟨quotientCore (τ I.1),
    by simpa only [Q, quotientCoreData_core] using Q.core_faithful,
    I.2⟩

private def submoduleCoreFaithfulTriple
    (I : CoreThreeIdeal τ) :
    Skeleton.InflationData.FaithfulSLevel I.1 (τ I.1) 3 := by
  let S := submoduleCoreData (τ I.1) (normal I.1)
  have hcard : (submoduleCore (τ I.1) : Set (L I.1)).ncard = 3 := by
    rw [Set.ncard_congr' (coreEquiv I.1)]
    exact I.2
  exact ⟨submoduleCore (τ I.1),
    by simpa only [S, submoduleCoreData_core] using S.core_faithful,
    hcard⟩

/-- In the core-three stratum, forgetting the unique faithful quotient
triple loses no information. -/
def qCoreThreePartEquiv :
    {X : FactorFaithfulQTriples τ //
      (quotientCore (τ X.1) : Set (L X.1)).ncard = 3} ≃
        CoreThreeIdeal τ where
  toFun X := ⟨X.1.1, X.2⟩
  invFun I := ⟨⟨I.1, quotientCoreFaithfulTriple τ normal I⟩, I.2⟩
  left_inv X := by
    rcases X with ⟨⟨I, C⟩, hcore⟩
    apply Subtype.ext
    refine Sigma.ext rfl (heq_of_eq ?_)
    apply Subtype.ext
    apply Subtype.ext
    change (quotientCore (τ I) : Set (L I)) = (C.1 : Set (L I))
    exact (faithfulQTriple_eq_quotientCore (τ I) (normal I)
      C.1 C.2.1 C.2.2 hcore).symm
  right_inv I := by
    apply Subtype.ext
    rfl

/-- The same uniqueness on the submodule side. -/
def sCoreThreePartEquiv :
    {X : FactorFaithfulSTriples τ //
      (quotientCore (τ X.1) : Set (L X.1)).ncard = 3} ≃
        CoreThreeIdeal τ where
  toFun X := ⟨X.1.1, X.2⟩
  invFun I := ⟨⟨I.1,
    submoduleCoreFaithfulTriple τ normal coreEquiv I⟩, I.2⟩
  left_inv X := by
    rcases X with ⟨⟨I, C⟩, hcore⟩
    apply Subtype.ext
    refine Sigma.ext rfl (heq_of_eq ?_)
    apply Subtype.ext
    apply Subtype.ext
    change (submoduleCore (τ I) : Set (L I)) = (C.1 : Set (L I))
    have hsubcore :
        (submoduleCore (τ I) : Set (L I)).ncard = 3 := by
      rw [Set.ncard_congr' (coreEquiv I)]
      exact hcore
    exact (faithfulSTriple_eq_submoduleCore (τ I) (normal I)
      C.1 C.2.1 C.2.2 hsubcore).symm
  right_inv I := by
    apply Subtype.ext
    rfl

/-- The complementary quotient-side stratum is exactly a faithful triple
over a core-two factor. -/
def qNotCoreThreePartEquiv :
    {X : FactorFaithfulQTriples τ //
      ¬ (quotientCore (τ X.1) : Set (L X.1)).ncard = 3} ≃
        CoreTwoFaithfulQTriples τ where
  toFun X := by
    rcases X with ⟨⟨I, C⟩, hnotthree⟩
    have hcases :=
      quotientCore_ncard_eq_two_or_three_of_faithfulQTriple
        (τ I) (normal I) (coreEquiv I) C.1 C.2.1 C.2.2
    have htwo : (quotientCore (τ I) : Set (L I)).ncard = 2 :=
      hcases.resolve_right hnotthree
    exact ⟨⟨I, htwo⟩, C⟩
  invFun X := by
    rcases X with ⟨⟨I, htwo⟩, C⟩
    have hnotthree :
        ¬ (quotientCore (τ I) : Set (L I)).ncard = 3 := by
      intro hthree
      omega
    exact ⟨⟨I, C⟩, hnotthree⟩
  left_inv X := by
    rcases X with ⟨⟨I, C⟩, hnotthree⟩
    apply Subtype.ext
    rfl
  right_inv X := by
    rcases X with ⟨I, C⟩
    refine Sigma.ext ?_ (heq_of_eq rfl)
    apply Subtype.ext
    rfl

/-- The analogous complementary submodule stratum. -/
def sNotCoreThreePartEquiv :
    {X : FactorFaithfulSTriples τ //
      ¬ (quotientCore (τ X.1) : Set (L X.1)).ncard = 3} ≃
        CoreTwoFaithfulSTriples τ where
  toFun X := by
    rcases X with ⟨⟨I, C⟩, hnotthree⟩
    have hcases :=
      quotientCore_ncard_eq_two_or_three_of_faithfulSTriple
        (τ I) (normal I) (coreEquiv I) C.1 C.2.1 C.2.2
    have htwo : (quotientCore (τ I) : Set (L I)).ncard = 2 :=
      hcases.resolve_right hnotthree
    exact ⟨⟨I, htwo⟩, C⟩
  invFun X := by
    rcases X with ⟨⟨I, htwo⟩, C⟩
    have hnotthree :
        ¬ (quotientCore (τ I) : Set (L I)).ncard = 3 := by
      intro hthree
      omega
    exact ⟨⟨I, C⟩, hnotthree⟩
  left_inv X := by
    rcases X with ⟨⟨I, C⟩, hnotthree⟩
    apply Subtype.ext
    rfl
  right_inv X := by
    rcases X with ⟨I, C⟩
    refine Sigma.ext ?_ (heq_of_eq rfl)
    apply Subtype.ext
    rfl

/-- Every quotient-closed triple is either the unique core of a core-three
factor or a faithful triple over a core-two factor. -/
def qTripleCoreSplitEquiv :
    ArtinQTriple σ ≃
      CoreThreeIdeal τ ⊕
        CoreTwoFaithfulQTriples τ :=
  (qLevelFactorFaithfulEquiv σ τ D 3).trans <|
    (Equiv.sumCompl (fun X : FactorFaithfulQTriples τ ↦
      (quotientCore (τ X.1) : Set (L X.1)).ncard = 3)).symm |>.trans
        (Equiv.sumCongr
          (qCoreThreePartEquiv τ normal)
          (qNotCoreThreePartEquiv τ normal coreEquiv))

/-- The identical global split on the submodule side. -/
def sTripleCoreSplitEquiv :
    ArtinSTriple σ ≃
      CoreThreeIdeal τ ⊕
        CoreTwoFaithfulSTriples τ :=
  (sLevelFactorFaithfulEquiv σ τ D 3).trans <|
    (Equiv.sumCompl (fun X : FactorFaithfulSTriples τ ↦
      (quotientCore (τ X.1) : Set (L X.1)).ncard = 3)).symm |>.trans
        (Equiv.sumCongr
          (sCoreThreePartEquiv τ normal coreEquiv)
          (sNotCoreThreePartEquiv τ normal coreEquiv))

include D normal coreEquiv in
/-- A finite ambient skeleton forces the subtype of contributing core-three
ideals to be finite, even when the whole ideal type is not. -/
theorem finite_coreThreeIdeal [Finite ι] :
    Finite (CoreThreeIdeal τ) := by
  letI : Finite (ArtinQTriple σ) := by
    unfold ArtinQTriple ArtinQLevel
    infer_instance
  letI : Finite
      (CoreThreeIdeal τ ⊕ CoreTwoFaithfulQTriples τ) :=
    (qTripleCoreSplitEquiv σ τ D normal coreEquiv).finite_iff.mp
      inferInstance
  exact Finite.of_injective
    (fun I : CoreThreeIdeal τ ↦
      (Sum.inl I : CoreThreeIdeal τ ⊕ CoreTwoFaithfulQTriples τ))
    Sum.inl_injective

include D normal coreEquiv in
/-- The residual quotient-side core-two faithful-triple family is likewise
finite. -/
theorem finite_coreTwoFaithfulQTriples [Finite ι] :
    Finite (CoreTwoFaithfulQTriples τ) := by
  letI : Finite (ArtinQTriple σ) := by
    unfold ArtinQTriple ArtinQLevel
    infer_instance
  letI : Finite
      (CoreThreeIdeal τ ⊕ CoreTwoFaithfulQTriples τ) :=
    (qTripleCoreSplitEquiv σ τ D normal coreEquiv).finite_iff.mp
      inferInstance
  exact Finite.of_injective
    (fun C : CoreTwoFaithfulQTriples τ ↦
      (Sum.inr C : CoreThreeIdeal τ ⊕ CoreTwoFaithfulQTriples τ))
    Sum.inr_injective

include D normal coreEquiv in
/-- The residual submodule-side family is finite for the same reason. -/
theorem finite_coreTwoFaithfulSTriples [Finite ι] :
    Finite (CoreTwoFaithfulSTriples τ) := by
  letI : Finite (ArtinSTriple σ) := by
    unfold ArtinSTriple ArtinSLevel
    infer_instance
  letI : Finite
      (CoreThreeIdeal τ ⊕ CoreTwoFaithfulSTriples τ) :=
    (sTripleCoreSplitEquiv σ τ D normal coreEquiv).finite_iff.mp
      inferInstance
  exact Finite.of_injective
    (fun C : CoreTwoFaithfulSTriples τ ↦
      (Sum.inr C : CoreThreeIdeal τ ⊕ CoreTwoFaithfulSTriples τ))
    Sum.inr_injective

include D normal coreEquiv in
/-- Exact quotient-side third-level count before the core-two factors are
classified. -/
theorem qTriple_natCard_split [Finite ι] :
    Nat.card (ArtinQTriple σ) =
      Nat.card (CoreThreeIdeal τ) +
        Nat.card (CoreTwoFaithfulQTriples τ) := by
  letI : Finite (CoreThreeIdeal τ) :=
    finite_coreThreeIdeal σ τ D normal coreEquiv
  letI : Finite (CoreTwoFaithfulQTriples τ) :=
    finite_coreTwoFaithfulQTriples σ τ D normal coreEquiv
  rw [Nat.card_congr (qTripleCoreSplitEquiv σ τ D normal coreEquiv),
    Nat.card_sum]

include D normal coreEquiv in
/-- Exact submodule-side third-level count before the core-two factors are
classified. -/
theorem sTriple_natCard_split [Finite ι] :
    Nat.card (ArtinSTriple σ) =
      Nat.card (CoreThreeIdeal τ) +
        Nat.card (CoreTwoFaithfulSTriples τ) := by
  letI : Finite (CoreThreeIdeal τ) :=
    finite_coreThreeIdeal σ τ D normal coreEquiv
  letI : Finite (CoreTwoFaithfulSTriples τ) :=
    finite_coreTwoFaithfulSTriples σ τ D normal coreEquiv
  rw [Nat.card_congr (sTripleCoreSplitEquiv σ τ D normal coreEquiv),
    Nat.card_sum]

/-- A parametrization of the remaining core-two quotient triples by a type
`P` upgrades the abstract split to the paper-shaped two-summand
parametrization.  Eventually `P` will be the subtype of Morita-`kA₂` factor
ideals. -/
def qTripleIdealEquivOfCoreTwoParametrization
    {P : Type w} (small : CoreTwoFaithfulQTriples τ ≃ P) :
    ArtinQTriple σ ≃ CoreThreeIdeal τ ⊕ P :=
  (qTripleCoreSplitEquiv σ τ D normal coreEquiv).trans
    (Equiv.sumCongr (Equiv.refl _) small)

/-- The corresponding submodule-side parametrization. -/
def sTripleIdealEquivOfCoreTwoParametrization
    {P : Type w} (small : CoreTwoFaithfulSTriples τ ≃ P) :
    ArtinSTriple σ ≃ CoreThreeIdeal τ ⊕ P :=
  (sTripleCoreSplitEquiv σ τ D normal coreEquiv).trans
    (Equiv.sumCongr (Equiv.refl _) small)

/-- Common parametrizations of the two core-two residual strata give the
abstract bottom-three equivalence. -/
def tripleEquivOfCoreTwoParametrizations
    {P : Type w}
    (qSmall : CoreTwoFaithfulQTriples τ ≃ P)
    (sSmall : CoreTwoFaithfulSTriples τ ≃ P) :
    ArtinQTriple σ ≃ ArtinSTriple σ :=
  (qTripleIdealEquivOfCoreTwoParametrization
      σ τ D normal coreEquiv qSmall).trans
    (sTripleIdealEquivOfCoreTwoParametrization
      σ τ D normal coreEquiv sSmall).symm

include D normal coreEquiv in
/-- Numerical third-level equality is an immediate consequence of the same
residual parametrizations. -/
theorem triple_natCard_eq_of_coreTwoParametrizations
    {P : Type w}
    (qSmall : CoreTwoFaithfulQTriples τ ≃ P)
    (sSmall : CoreTwoFaithfulSTriples τ ≃ P) :
    Nat.card (ArtinQTriple σ) = Nat.card (ArtinSTriple σ) :=
  Nat.card_congr
    (tripleEquivOfCoreTwoParametrizations
      σ τ D normal coreEquiv qSmall sSmall)

end FactorwiseAssembly

end OpConjecture.IndecomposableSkeleton.FaithfulCore
