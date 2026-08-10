import QuotientSubmoduleEquidistribution.Nakayama.ChainClosure
import QuotientSubmoduleEquidistribution.RepresentationTheory.Approximation
import QuotientSubmoduleEquidistribution.RepresentationTheory.ConormalModules
import QuotientSubmoduleEquidistribution.RepresentationTheory.LengthThreeUniserialSubmodule

/-!
# Fixed-top and fixed-socle chain adapters

This file isolates the collective-closure step in the Nakayama
argument.  Once the indecomposables are labeled by their fixed-top or
fixed-socle chains and the one-object epi/mono relation is known, finite
direct sums add no further closure relations.
-/

noncomputable section

open Set CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.NakayamaModuleChains

open NakayamaCombinatorics

universe u v w x y

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v}
  (σ : IndecomposableSkeleton.{u, v, w} R ι)

/-! ## Counting the same indecomposables by top and by socle -/

/-- Chain indices whose capacity reaches the specified positive length. -/
abbrev CapacityAtLeastIndex
    {κ : Type x} (c : κ → ℕ) (n : ℕ) :=
  {i : κ // n ≤ c i}

/-- Points in the product of chains lying at the specified positive
composition length.  Coordinate zero corresponds to length one. -/
abbrev ChainLengthLayer
    {κ : Type x} (c : κ → ℕ) (n : ℕ) :=
  {p : ChainPoint c // (p.2 : ℕ) + 1 = n}

/-- For positive `n`, a chain reaches length `n` exactly when it contains
its unique point in layer `n`. -/
def capacityAtLeastIndexEquivChainLengthLayer
    {κ : Type x} {c : κ → ℕ} {n : ℕ} (hn : 0 < n) :
    CapacityAtLeastIndex c n ≃ ChainLengthLayer c n where
  toFun i :=
    ⟨⟨i.1, ⟨n - 1, by omega⟩⟩, by
      change n - 1 + 1 = n
      omega⟩
  invFun p :=
    ⟨p.1.1, by
      have hp := p.1.2.isLt
      have hpLength := p.2
      omega⟩
  left_inv i := by
    apply Subtype.ext
    rfl
  right_inv p := by
    apply Subtype.ext
    refine Sigma.ext rfl (heq_of_eq ?_)
    apply Fin.ext
    ·
      dsimp
      have hpLength := p.2
      omega

/-- The multiset definition of the number of chains reaching `n` is the
cardinality of the corresponding subtype of chain indices. -/
theorem capacityAtLeastCount_eq_natCard_index
    {κ : Type x} [Fintype κ] (c : κ → ℕ) (n : ℕ) :
    capacityAtLeastCount c n =
      Nat.card (CapacityAtLeastIndex c n) := by
  classical
  rw [capacityAtLeastCount, capacityMultiset,
    Multiset.countP_map, Nat.card_eq_fintype_card]
  symm
  change
    Fintype.card {i : κ // n ≤ c i} =
      (Finset.univ.filter fun i : κ ↦ n ≤ c i).card
  exact Fintype.card_subtype (fun i : κ ↦ n ≤ c i)

/-- At positive length, `capacityAtLeastCount` is the cardinality of the
corresponding layer of actual chain points. -/
theorem capacityAtLeastCount_eq_natCard_lengthLayer
    {κ : Type x} [Fintype κ] (c : κ → ℕ) {n : ℕ} (hn : 0 < n) :
    capacityAtLeastCount c n =
      Nat.card (ChainLengthLayer c n) := by
  rw [capacityAtLeastCount_eq_natCard_index]
  exact Nat.card_congr
    (capacityAtLeastIndexEquivChainLengthLayer hn)

/-- A chain labeling which records the length coordinate identifies its
`n`-th layer with the fiber of the actual label-length function. -/
def chainLengthLayerEquivLabelLengthFiber
    {κ : Type x} {c : κ → ℕ}
    (e : ChainPoint c ≃ ι) (length : ι → ℕ)
    (hlength : ∀ p, length (e p) = (p.2 : ℕ) + 1)
    (n : ℕ) :
    ChainLengthLayer c n ≃ {i : ι // length i = n} where
  toFun p := ⟨e p.1, (hlength p.1).trans p.2⟩
  invFun i :=
    ⟨e.symm i.1, by
      rw [← hlength (e.symm i.1), e.apply_symm_apply]
      exact i.2⟩
  left_inv p := by
    apply Subtype.ext
    exact e.symm_apply_apply p.1
  right_inv i := by
    apply Subtype.ext
    exact e.apply_symm_apply i.1

/-- If two chain labelings enumerate the same actual labels with the same
positive length statistic, and their chain-index types are equivalent,
then their capacity-at-least counts agree in every degree.  This is the
formal content of counting Nakayama indecomposables first by top and then
by socle. -/
theorem capacityAtLeastCount_eq_of_labelLength
    {κ : Type x} {κ₂ : Type y} [Fintype κ] [Fintype κ₂]
    {c : κ → ℕ} {d : κ₂ → ℕ}
    (e : ChainPoint c ≃ ι) (e₂ : ChainPoint d ≃ ι)
    (indexEquiv : κ ≃ κ₂)
    (length : ι → ℕ)
    (hlength : ∀ p, length (e p) = (p.2 : ℕ) + 1)
    (hlength₂ : ∀ p, length (e₂ p) = (p.2 : ℕ) + 1) :
    ∀ n, capacityAtLeastCount c n =
      capacityAtLeastCount d n := by
  intro n
  rcases n with _ | n
  · calc
      capacityAtLeastCount c 0 = Nat.card κ := by
        simp [capacityAtLeastCount, capacityMultiset]
      _ = Nat.card κ₂ := Nat.card_congr indexEquiv
      _ = capacityAtLeastCount d 0 := by
        simp [capacityAtLeastCount, capacityMultiset]
  · rw [capacityAtLeastCount_eq_natCard_lengthLayer c (Nat.succ_pos n),
      capacityAtLeastCount_eq_natCard_lengthLayer d (Nat.succ_pos n)]
    calc
      Nat.card (ChainLengthLayer c (n + 1)) =
          Nat.card {i : ι // length i = n + 1} :=
        Nat.card_congr
          (chainLengthLayerEquivLabelLengthFiber
            e length hlength (n + 1))
      _ = Nat.card (ChainLengthLayer d (n + 1)) :=
        (Nat.card_congr
          (chainLengthLayerEquivLabelLengthFiber
            e₂ length hlength₂ (n + 1))).symm

/-- Exact module data for a decomposition into fixed-top quotient chains.

The relation field is stated using the canonical singleton chain closure:
there is an epimorphism from `i` to `j` exactly when `j` occurs below `i`
in the same chain. -/
structure FixedTopChainData
    {κ : Type x} [Fintype κ] (c : κ → ℕ) where
  labelEquiv : ChainPoint c ≃ ι
  uniserial : ∀ i : ι, IsUniserialModule R (σ.obj i)
  epi_iff (i j : ι) :
    (∃ f : σ.obj i ⟶ σ.obj j, Epi f) ↔
      labelEquiv.symm j ∈
        chainClosure c ({labelEquiv.symm i} : Set (ChainPoint c))

/-- Exact module data for a decomposition into fixed-socle submodule
chains.  There is a monomorphism from `i` to `j` exactly when `i` occurs
below `j` in the same chain. -/
structure FixedSocleChainData
    {κ : Type x} [Fintype κ] (c : κ → ℕ) where
  labelEquiv : ChainPoint c ≃ ι
  uniserial : ∀ i : ι, IsUniserialModule R (σ.obj i)
  mono_iff (i j : ι) :
    (∃ f : σ.obj i ⟶ σ.obj j, Mono f) ↔
      labelEquiv.symm i ∈
        chainClosure c ({labelEquiv.symm j} : Set (ChainPoint c))

namespace FixedTopChainData

variable {κ : Type x} [Fintype κ] {c : κ → ℕ}

/-- Fixed-top chain data conjugate canonical downward chain closure to the
actual quotient closure. -/
def relabeling (D : FixedTopChainData σ c) :
    SetClosure.RelabelingEquiv (chainClosure c) σ.qClosure where
  equiv := D.labelEquiv
  map_closure S := by
    ext j
    constructor
    · rintro ⟨q, hq, rfl⟩
      change
        σ.InFac (D.labelEquiv '' S)
          (σ.obj (D.labelEquiv q))
      obtain ⟨k, hkS, hqk⟩ := hq
      let p : ChainPoint c := ⟨q.1, k⟩
      have hpS : p ∈ S := hkS
      have hqp :
          q ∈ chainClosure c ({p} : Set (ChainPoint c)) := by
        exact ⟨k, by simp [p], hqk⟩
      obtain ⟨f, hf⟩ :=
        (D.epi_iff (D.labelEquiv p) (D.labelEquiv q)).2
          (by simpa using hqp)
      letI : Epi f := hf
      have hsource :
          σ.InFac (D.labelEquiv '' S)
            (σ.obj (D.labelEquiv p)) :=
        σ.subset_qSet (D.labelEquiv '' S) ⟨p, hpS, rfl⟩
      exact σ.inFac_of_epi hsource f
    · intro hj
      change σ.InFac (D.labelEquiv '' S) (σ.obj j) at hj
      obtain ⟨P⟩ := hj
      letI : Epi P.map := P.epi
      obtain ⟨t, ht⟩ :=
        σ.exists_epi_biproduct_component_of_simple_top
          P.index P.label
          (σ.moduleTop_isSimple_of_isUniserial (D.uniserial j))
          P.map
      let f :
          σ.obj (P.label t) ⟶ σ.obj j :=
        biproduct.ι
          (fun b : P.index ↦ σ.obj (P.label b)) t ≫ P.map
      have hf : Epi f := ht
      have hrel :
          D.labelEquiv.symm j ∈
            chainClosure c
              ({D.labelEquiv.symm (P.label t)} :
                Set (ChainPoint c)) :=
        (D.epi_iff (P.label t) j).1 ⟨f, hf⟩
      have hselected : D.labelEquiv.symm (P.label t) ∈ S := by
        rcases P.mem t with ⟨p, hp, hpe⟩
        rw [← hpe, D.labelEquiv.symm_apply_apply]
        exact hp
      have hq :
          D.labelEquiv.symm j ∈ chainClosure c S :=
        (chainClosure c).monotone
          (Set.singleton_subset_iff.mpr hselected) hrel
      exact
        ⟨D.labelEquiv.symm j, hq,
          D.labelEquiv.apply_symm_apply j⟩

/-- The actual quotient level polynomial is the product-of-chains
polynomial determined by the fixed-top capacities. -/
theorem quotient_levelPolynomial_eq_capacityPolynomial
    [Finite ι]
    (D : FixedTopChainData σ c) :
    σ.qClosure.levelPolynomial =
      NakayamaCombinatorics.capacityPolynomial c := by
  calc
    σ.qClosure.levelPolynomial =
        (chainClosure c).levelPolynomial :=
      D.relabeling.levelPolynomial_eq.symm
    _ = ∏ i, NakayamaCombinatorics.chainPolynomial (c i) :=
      NakayamaCombinatorics.chainClosure_levelPolynomial c
    _ = NakayamaCombinatorics.capacityPolynomial c :=
      (NakayamaCombinatorics.capacityPolynomial_eq_prod_chainPolynomial
        c).symm

end FixedTopChainData

namespace FixedSocleChainData

variable {κ : Type x} [Fintype κ] {c : κ → ℕ}

/-- Fixed-socle chain data conjugate canonical downward chain closure to
the actual submodule closure. -/
def relabeling (D : FixedSocleChainData σ c) :
    SetClosure.RelabelingEquiv (chainClosure c) σ.sClosure where
  equiv := D.labelEquiv
  map_closure S := by
    ext j
    constructor
    · rintro ⟨q, hq, rfl⟩
      change
        σ.InSub (D.labelEquiv '' S)
          (σ.obj (D.labelEquiv q))
      obtain ⟨k, hkS, hqk⟩ := hq
      let p : ChainPoint c := ⟨q.1, k⟩
      have hpS : p ∈ S := hkS
      have hqp :
          q ∈ chainClosure c ({p} : Set (ChainPoint c)) := by
        exact ⟨k, by simp [p], hqk⟩
      obtain ⟨f, hf⟩ :=
        (D.mono_iff (D.labelEquiv q) (D.labelEquiv p)).2
          (by simpa using hqp)
      letI : Mono f := hf
      have htarget :
          σ.InSub (D.labelEquiv '' S)
            (σ.obj (D.labelEquiv p)) :=
        σ.subset_sSet (D.labelEquiv '' S) ⟨p, hpS, rfl⟩
      exact σ.inSub_of_mono htarget f
    · intro hj
      change σ.InSub (D.labelEquiv '' S) (σ.obj j) at hj
      obtain ⟨P⟩ := hj
      letI : Mono P.map := P.mono
      obtain ⟨t, ht⟩ :=
        σ.exists_mono_biproduct_component_of_isUniserial
          (D.uniserial j) P.index P.label P.map
      let f :
          σ.obj j ⟶ σ.obj (P.label t) :=
        P.map ≫
          biproduct.π
            (fun b : P.index ↦ σ.obj (P.label b)) t
      have hf : Mono f := ht
      have hrel :
          D.labelEquiv.symm j ∈
            chainClosure c
              ({D.labelEquiv.symm (P.label t)} :
                Set (ChainPoint c)) :=
        (D.mono_iff j (P.label t)).1 ⟨f, hf⟩
      have hselected : D.labelEquiv.symm (P.label t) ∈ S := by
        rcases P.mem t with ⟨p, hp, hpe⟩
        rw [← hpe, D.labelEquiv.symm_apply_apply]
        exact hp
      have hq :
          D.labelEquiv.symm j ∈ chainClosure c S :=
        (chainClosure c).monotone
          (Set.singleton_subset_iff.mpr hselected) hrel
      exact
        ⟨D.labelEquiv.symm j, hq,
          D.labelEquiv.apply_symm_apply j⟩

/-- The actual submodule level polynomial is the product-of-chains
polynomial determined by the fixed-socle capacities. -/
theorem submodule_levelPolynomial_eq_capacityPolynomial
    [Finite ι]
    (D : FixedSocleChainData σ c) :
    σ.sClosure.levelPolynomial =
      NakayamaCombinatorics.capacityPolynomial c := by
  calc
    σ.sClosure.levelPolynomial =
        (chainClosure c).levelPolynomial :=
      D.relabeling.levelPolynomial_eq.symm
    _ = ∏ i, NakayamaCombinatorics.chainPolynomial (c i) :=
      NakayamaCombinatorics.chainClosure_levelPolynomial c
    _ = NakayamaCombinatorics.capacityPolynomial c :=
      (NakayamaCombinatorics.capacityPolynomial_eq_prod_chainPolynomial
        c).symm

end FixedSocleChainData

/-- The exact final Nakayama comparison: equality of the numbers of
fixed-top and fixed-socle chains reaching every length forces equality of
the actual quotient and submodule level polynomials. -/
theorem quotient_levelPolynomial_eq_submodule_of_atLeastCount_eq
    [Finite ι]
    {κ : Type x} {κ₂ : Type y} [Fintype κ] [Fintype κ₂]
    {topCapacity : κ → ℕ} {socleCapacity : κ₂ → ℕ}
    (Q : FixedTopChainData σ topCapacity)
    (S : FixedSocleChainData σ socleCapacity)
    (hcount :
      ∀ n,
        NakayamaCombinatorics.capacityAtLeastCount topCapacity n =
          NakayamaCombinatorics.capacityAtLeastCount socleCapacity n) :
    σ.qClosure.levelPolynomial = σ.sClosure.levelPolynomial := by
  rw [Q.quotient_levelPolynomial_eq_capacityPolynomial,
    S.submodule_levelPolynomial_eq_capacityPolynomial]
  exact
    NakayamaCombinatorics.capacityPolynomial_eq_of_atLeastCount_eq
      topCapacity socleCapacity hcount

/-- Source-facing Nakayama endpoint.  Fixed-top and fixed-socle chain
classifications which both identify the chain coordinate with composition
length automatically have the same capacity multiset, hence the same
actual quotient and submodule level polynomial. -/
theorem quotient_levelPolynomial_eq_submodule_of_fixedChains
    [Finite ι]
    {κ : Type x} {κ₂ : Type y} [Fintype κ] [Fintype κ₂]
    {topCapacity : κ → ℕ} {socleCapacity : κ₂ → ℕ}
    (Q : FixedTopChainData σ topCapacity)
    (S : FixedSocleChainData σ socleCapacity)
    (indexEquiv : κ ≃ κ₂)
    (hTopLength :
      ∀ p,
        σ.compositionLength (Q.labelEquiv p) =
          (p.2 : ℕ) + 1)
    (hSocleLength :
      ∀ p,
        σ.compositionLength (S.labelEquiv p) =
          (p.2 : ℕ) + 1) :
    σ.qClosure.levelPolynomial = σ.sClosure.levelPolynomial :=
  quotient_levelPolynomial_eq_submodule_of_atLeastCount_eq σ Q S
    (capacityAtLeastCount_eq_of_labelLength
      Q.labelEquiv S.labelEquiv indexEquiv
      σ.compositionLength hTopLength hSocleLength)

/-- The exact source-facing classification package needed for the
Nakayama polynomial theorem.  Both families are indexed by the same
simple-label type; their capacities may differ before the length-fiber
argument identifies their multisets. -/
structure FixedTopSocleChainClassification where
  ChainIndex : Type v
  [chainIndexFintype : Fintype ChainIndex]
  topCapacity : ChainIndex → ℕ
  socleCapacity : ChainIndex → ℕ
  top : FixedTopChainData σ topCapacity
  socle : FixedSocleChainData σ socleCapacity
  top_compositionLength :
    ∀ p,
      σ.compositionLength (top.labelEquiv p) =
        (p.2 : ℕ) + 1
  socle_compositionLength :
    ∀ p,
      σ.compositionLength (socle.labelEquiv p) =
        (p.2 : ℕ) + 1

namespace FixedTopSocleChainClassification

/-- A complete fixed-top/fixed-socle classification proves the actual
Nakayama quotient--submodule level-polynomial equality. -/
theorem levelPolynomial_eq
    [Finite ι]
    (D : FixedTopSocleChainClassification σ) :
    σ.qClosure.levelPolynomial = σ.sClosure.levelPolynomial := by
  letI : Fintype D.ChainIndex := D.chainIndexFintype
  exact
    quotient_levelPolynomial_eq_submodule_of_fixedChains σ
      D.top D.socle (Equiv.refl D.ChainIndex)
      D.top_compositionLength D.socle_compositionLength

end FixedTopSocleChainClassification

end QuotientSubmoduleEquidistribution.NakayamaModuleChains
