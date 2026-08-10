import QuotientSubmoduleEquidistribution.RepresentationTheory.ConnectedSmallCoreAssembly
import QuotientSubmoduleEquidistribution.RepresentationTheory.FiniteDimensionalNoParallelExt
import QuotientSubmoduleEquidistribution.RepresentationTheory.HereditaryNoSelfExt
import QuotientSubmoduleEquidistribution.RepresentationTheory.SerialBoundaryTheorem
import QuotientSubmoduleEquidistribution.RepresentationTheory.ExtDualTransport
import QuotientSubmoduleEquidistribution.RepresentationTheory.TwoVertexArrowSupport
import QuotientSubmoduleEquidistribution.RepresentationTheory.NakayamaFixedTopChains
import QuotientSubmoduleEquidistribution.RepresentationTheory.ContragredientDuality

/-!
# The categorical hereditary boundary with two simple modules

This file proves the counting part of the core-size-two boundary without a
quiver presentation or a classification of modules over a concrete algebra.
Finite left heredity kills simple self-extensions.  With two simple labels,
the no-parallel Ext theorem then makes both endpoint maps of the Ext quiver
injective.  Contragredient duality and the abstract two-sided serial theorem
make every indecomposable uniserial.  Finally, projective radicals show that
the two fixed-top chains contain at most three labels in total.
-/

noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.HereditaryTwoSimpleBoundary

universe u v

open QuotientSubmoduleEquidistribution.GabrielArrowBridge
open QuotientSubmoduleEquidistribution.IndecomposableSkeleton
open QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore
open QuotientSubmoduleEquidistribution.IndecomposableSkeleton.ProjectiveSimpleRank
open QuotientSubmoduleEquidistribution.NakayamaFixedTopChains

section AlignedEquivalence

variable {R S : Type u}
  [Ring R] [IsNoetherianRing R]
  [Ring S] [IsNoetherianRing S]
  {iota kappa : Type v}
  (sigma : IndecomposableSkeleton.{u, v, u} R iota)
  (tau : IndecomposableSkeleton.{u, v, u} S kappa)

/-- An aligned equivalence restricts its label equivalence to the simple
representatives. -/
def simpleIndexEquiv
    (E : IndecomposableSkeleton.AlignedEquivalence sigma tau) :
    sigma.SimpleIndex ≃ tau.SimpleIndex where
  toFun i := ⟨E.labelEquiv i.1, by
    letI : Simple (sigma.obj i.1) := i.2
    have hmap : Simple (E.categoryEquiv.functor.obj (sigma.obj i.1)) :=
      CategoryTheory.simple_obj E.categoryEquiv.functor (sigma.obj i.1)
    exact (Simple.iff_of_iso (E.objIso i.1)).mp hmap⟩
  invFun j := ⟨E.labelEquiv.symm j.1, by
    letI : Simple (tau.obj j.1) := j.2
    let i := E.labelEquiv.symm j.1
    have htarget : Simple (tau.obj (E.labelEquiv i)) := by
      simpa [i] using j.2
    have hmap : Simple (E.categoryEquiv.functor.obj (sigma.obj i)) :=
      (Simple.iff_of_iso (E.objIso i)).mpr htarget
    exact
      (CategoryTheory.simple_obj_iff
        E.categoryEquiv.functor (sigma.obj i)).mp hmap⟩
  left_inv i := by
    apply Subtype.ext
    simp
  right_inv j := by
    apply Subtype.ext
    simp

end AlignedEquivalence

variable {K R : Type u}
  [Field K] [IsAlgClosed K]
  [Ring R] [Small.{u} R] [Algebra K R]
  [FiniteDimensional K R] [IsNoetherianRing R]
  {iota : Type v} [Finite iota]
  (sigma : IndecomposableSkeleton.{u, v, u} R iota)

/-- A finite complete skeleton over a finite-dimensional algebra over an
algebraically closed field has no parallel degree-one Ext arrows.  This is
the left-module form of the existing finite-isomorphism-class argument. -/
theorem noParallelExtSupport_of_finiteDimensional :
    NoParallelExtSupport (K := K) sigma :=
  QuotientSubmoduleEquidistribution.FiniteDimensionalNoParallelExt.noParallelExtSupport sigma

/-- Relabel the multiplicity-bearing Ext support by its two simple
vertices. -/
def twoVertexExtSupport
    (e : sigma.SimpleIndex ≃ Fin 2)
    (hNoParallel : NoParallelExtSupport (K := K) sigma) :
    QuotientSubmoduleEquidistribution.TwoVertexArrowSupport.Data
      (ExtGabrielArrowIndex (K := K) sigma) where
  source a := e (ExtGabrielArrowIndex.source sigma a)
  target a := e (ExtGabrielArrowIndex.target sigma a)
  pair_injective := by
    intro a b hab
    apply ExtGabrielArrowIndex.source_target_injective sigma hNoParallel
    apply Prod.ext
    · apply e.injective
      exact congrArg Prod.fst hab
    · apply e.injective
      exact congrArg Prod.snd hab

omit [IsAlgClosed K] [FiniteDimensional K R] [Finite iota] in
/-- Pointwise vanishing of simple self-Ext makes the two-vertex Ext support
loop-free. -/
theorem twoVertexExtSupport_noLoops
    (e : sigma.SimpleIndex ≃ Fin 2)
    (hNoParallel : NoParallelExtSupport (K := K) sigma)
    (hNoSelf : ∀ s : sigma.SimpleIndex,
      Subsingleton (ExtOne sigma s s)) :
    (twoVertexExtSupport sigma e hNoParallel).NoLoops := by
  intro i
  rintro ⟨a, hsource, htarget⟩
  have hst : ExtGabrielArrowIndex.source sigma a =
      ExtGabrielArrowIndex.target sigma a := by
    apply e.injective
    exact hsource.trans htarget.symm
  rcases a with ⟨s, t, k⟩
  change s = t at hst
  subst t
  letI : Subsingleton (ExtOne sigma s s) := hNoSelf s
  have hzero : Module.finrank K (ExtOne sigma s s) = 0 :=
    Module.finrank_zero_of_subsingleton
  haveI : IsEmpty (Fin (Module.finrank K (ExtOne sigma s s))) := by
    rw [hzero]
    infer_instance
  exact isEmptyElim k

omit [IsAlgClosed K] [FiniteDimensional K R] [Finite iota] in
/-- On two loop-free vertices, pair-injectivity of the Ext support makes
both source and target injective. -/
theorem extSourceTarget_injective_of_twoVertex_of_noSelfExt
    (e : sigma.SimpleIndex ≃ Fin 2)
    (hNoParallel : NoParallelExtSupport (K := K) sigma)
    (hNoSelf : ∀ s : sigma.SimpleIndex,
      Subsingleton (ExtOne sigma s s)) :
    Function.Injective (ExtGabrielArrowIndex.source (K := K) sigma) ∧
      Function.Injective (ExtGabrielArrowIndex.target (K := K) sigma) := by
  let V := twoVertexExtSupport sigma e hNoParallel
  have hVNoLoops : V.NoLoops :=
    twoVertexExtSupport_noLoops sigma e hNoParallel hNoSelf
  constructor
  · intro a b hab
    apply V.source_injective_of_noLoops hVNoLoops
    exact congrArg e hab
  · intro a b hab
    apply V.target_injective_of_noLoops hVNoLoops
    exact congrArg e hab

/-- A finite-left-hereditary finite-dimensional algebra with two simple
modules is Nakayama at the level of its complete finite skeleton.  The proof
is categorical: no concrete algebra or module classification is used. -/
theorem isNakayamaSkeleton_of_twoSimples_of_finitelyGeneratedLeftHereditary
    {S : Type u}
    [Ring S] [Small.{u} S] [Algebra K S]
    [FiniteDimensional K S] [IsNoetherianRing S]
    [IsNoetherianRing Rᵐᵒᵖ]
    {kappa : Type v} [Finite kappa]
    (tau : IndecomposableSkeleton.{u, v, u} S kappa)
    (D : IndecomposableSkeleton.AlignedAntiEquivalence sigma tau)
    (hHereditary : FinitelyGeneratedLeftHereditary R)
    (hTwo : Nat.card sigma.SimpleIndex = 2) :
    QuotientSubmoduleEquidistribution.LocalNakayamaBranch.IsNakayamaSkeleton sigma := by
  letI : IsArtinianRing R := IsArtinianRing.of_finite K R
  letI : IsArtinianRing S := IsArtinianRing.of_finite K S
  letI : Finite sigma.SimpleIndex :=
    Finite.of_injective Subtype.val Subtype.val_injective
  let e : sigma.SimpleIndex ≃ Fin 2 :=
    Finite.equivFinOfCardEq hTwo
  let hNoParallel : NoParallelExtSupport (K := K) sigma :=
    noParallelExtSupport_of_finiteDimensional sigma
  let hDualNoParallel : NoParallelExtSupport (K := K) tau :=
    noParallelExtSupport_of_finiteDimensional tau
  have hNoSelf : ∀ s : sigma.SimpleIndex,
      Subsingleton (ExtOne sigma s s) :=
    fun s ↦
      QuotientSubmoduleEquidistribution.HereditaryNoSelfExt.selfExtOne_subsingleton_of_finitelyGeneratedLeftHereditary
        (K := K) sigma hHereditary s
  have hEndpoints :=
    extSourceTarget_injective_of_twoVertex_of_noSelfExt
      sigma e hNoParallel hNoSelf
  let hFinite :
      QuotientSubmoduleEquidistribution.ExtDegreeNakayamaReduction.FiniteExtOneSupport
        (K := K) sigma :=
    fun s t ↦ (hNoParallel s t).1
  let hDualFinite :
      QuotientSubmoduleEquidistribution.ExtDegreeNakayamaReduction.FiniteExtOneSupport
        (K := K) tau :=
    fun s t ↦ (hDualNoParallel s t).1
  have hProjective :
      QuotientSubmoduleEquidistribution.LocalNakayamaBranch.IsProjectiveNakayamaSkeleton sigma :=
    QuotientSubmoduleEquidistribution.SerialRingBridge.projectiveNakayamaSkeleton_of_extSource_injective
      sigma hFinite hEndpoints.1
  have hDualSource :
      Function.Injective
        (ExtGabrielArrowIndex.source (K := K) tau) :=
    QuotientSubmoduleEquidistribution.ExtDualTransport.AlignedAntiEquivalence.dualExtSource_injective_of_extTarget_injective
      sigma tau D hNoParallel hDualNoParallel hEndpoints.2
  have hDualProjective :
      QuotientSubmoduleEquidistribution.LocalNakayamaBranch.IsProjectiveNakayamaSkeleton tau :=
    QuotientSubmoduleEquidistribution.SerialRingBridge.projectiveNakayamaSkeleton_of_extSource_injective
      tau hDualFinite hDualSource
  have hInjective :
      QuotientSubmoduleEquidistribution.SerialRingBridge.IsInjectiveNakayamaSkeleton sigma :=
    QuotientSubmoduleEquidistribution.SerialRingBridge.injectiveNakayamaSkeleton_of_dual_projectiveNakayama
      sigma tau D hDualProjective
  exact
    QuotientSubmoduleEquidistribution.SerialEndpointReduction.isNakayamaSkeleton_of_projective_and_injective_boundaries
      (K := K) sigma hProjective hInjective

section Capacity

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {iota : Type v} [Finite iota]
  (sigma : IndecomposableSkeleton.{u, v, u} R iota)

/-- Positive weights on a two-point type which are closed under taking a
predecessor have total weight at most three. -/
theorem sum_le_three_of_card_eq_two_of_exists_pred
    {alpha : Type*} [Fintype alpha] (c : alpha → ℕ)
    (hcard : Nat.card alpha = 2)
    (hpos : ∀ a, 0 < c a)
    (hpred : ∀ a, 1 < c a → ∃ b, c b + 1 = c a) :
    ∑ a, c a ≤ 3 := by
  classical
  obtain ⟨a, b, hab, hpairs⟩ := Nat.card_eq_two_iff.mp hcard
  have hcases (x : alpha) : x = a ∨ x = b := by
    have hx : x ∈ ({a, b} : Set alpha) := by
      rw [hpairs]
      trivial
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hx
  have hone : c a = 1 ∨ c b = 1 := by
    by_contra hnot
    have haNe : c a ≠ 1 := fun ha ↦ hnot (Or.inl ha)
    have hbNe : c b ≠ 1 := fun hb ↦ hnot (Or.inr hb)
    have haPos : 0 < c a := hpos a
    have hbPos : 0 < c b := hpos b
    have haOneLt : 1 < c a := by omega
    have hbOneLt : 1 < c b := by omega
    obtain ⟨x, hx⟩ := hpred a haOneLt
    obtain ⟨y, hy⟩ := hpred b hbOneLt
    rcases hcases x with rfl | rfl
    · omega
    · rcases hcases y with rfl | rfl <;> omega
  have hsum : ∑ x, c x = c a + c b := by
    have huniv : (Finset.univ : Finset alpha) = {a, b} := by
      ext x
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
        true_iff]
      exact hcases x
    rw [huniv]
    simp [hab]
  rw [hsum]
  rcases hone with ha | hb
  · have hbLe : c b ≤ 2 := by
      by_cases hbSmall : c b ≤ 1
      · omega
      · obtain ⟨x, hx⟩ := hpred b (by omega)
        rcases hcases x with rfl | rfl <;> omega
    omega
  · have haLe : c a ≤ 2 := by
      by_cases haSmall : c a ≤ 1
      · omega
      · obtain ⟨x, hx⟩ := hpred a (by omega)
        rcases hcases x with rfl | rfl <;> omega
    omega

omit [Finite iota] in
/-- Under finite left heredity, the nonzero radical of a chosen uniserial
projective is another chosen projective, with capacity one smaller. -/
theorem exists_capacity_predecessor
    (hNakayama : QuotientSubmoduleEquidistribution.LocalNakayamaBranch.IsNakayamaSkeleton sigma)
    (hHereditary : FinitelyGeneratedLeftHereditary R)
    (j : sigma.SimpleIndex)
    (hj : 1 < fixedTopCapacity sigma j) :
    ∃ k : sigma.SimpleIndex,
      fixedTopCapacity sigma k + 1 = fixedTopCapacity sigma j := by
  let p : iota := projectiveLabelOfSimple sigma j
  let J : Submodule R (sigma.obj p) := sigma.moduleRadical p
  have hpProjective : Projective (sigma.obj p) :=
    projective_projectiveLabelOfSimple sigma j
  have hJProjectiveModule : Module.Projective R J :=
    hHereditary (sigma.obj p) hpProjective J
  have hJProjective : Projective (FGModuleCat.of R J) :=
    QuotientSubmoduleEquidistribution.RingelStable.fgProjective_of_moduleProjective
      (FGModuleCat.of R J) hJProjectiveModule
  letI : IsArtinian R (sigma.obj p) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (sigma.finiteLength p)).2
  have htopSimple : IsSimpleModule R ((sigma.obj p) ⧸ J) := by
    change IsSimpleModule R (sigma.moduleTop p)
    exact sigma.moduleTop_isSimple_of_isUniserial (hNakayama p)
  have htopLength : Module.length R ((sigma.obj p) ⧸ J) = 1 :=
    Module.length_eq_one_iff.mpr htopSimple
  have hlengthAdd :
      Module.length R (sigma.obj p) =
        Module.length R J + Module.length R ((sigma.obj p) ⧸ J) :=
    Module.length_eq_add_of_exact J.subtype J.mkQ
      J.subtype_injective J.mkQ_surjective
      (LinearMap.exact_subtype_mkQ J)
  have hJLength : Module.length R J =
      (fixedTopCapacity sigma j - 1 : ℕ) := by
    change Module.length R J =
      ((sigma.compositionLength p - 1 : ℕ) : ℕ∞)
    rw [htopLength] at hlengthAdd
    have hpos : 0 < sigma.compositionLength p :=
      sigma.compositionLength_pos p
    apply WithTop.add_right_cancel ENat.one_ne_top
    calc
      Module.length R J + 1 = Module.length R (sigma.obj p) :=
        hlengthAdd.symm
      _ = (sigma.compositionLength p : ℕ∞) :=
        (sigma.coe_compositionLength p).symm
      _ = ((sigma.compositionLength p - 1 : ℕ) : ℕ∞) + 1 := by
        norm_cast
        omega
  have hJpos : (0 : ℕ∞) < Module.length R J := by
    rw [hJLength]
    exact_mod_cast (show 0 < fixedTopCapacity sigma j - 1 by omega)
  letI : Nontrivial J := Module.length_pos_iff.mp hJpos
  have hJuniserial : IsUniserialModule R J :=
    (hNakayama p).submodule J
  have hJIndec : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R (FGModuleCat.of R J) :=
    hJuniserial.isIndecomposableModule
  obtain ⟨i, ⟨e⟩⟩ := sigma.complete (FGModuleCat.of R J) hJIndec
  have hiProjective : Projective (sigma.obj i) :=
    Projective.of_iso e hJProjective
  let q : ProjectiveIndex sigma := ⟨i, hiProjective⟩
  let k : sigma.SimpleIndex := projectiveIndexEquivSimpleIndex sigma q
  refine ⟨k, ?_⟩
  have hkLabel : projectiveLabelOfSimple sigma k = i := by
    change ((projectiveIndexEquivSimpleIndex sigma).symm
      ((projectiveIndexEquivSimpleIndex sigma) q)).1 = i
    rw [(projectiveIndexEquivSimpleIndex sigma).symm_apply_apply]
  have hiLength : sigma.compositionLength i =
      fixedTopCapacity sigma j - 1 := by
    rw [← ENat.coe_inj, sigma.coe_compositionLength, ← hJLength]
    exact (FGModuleCat.isoToLinearEquiv e).length_eq.symm
  change sigma.compositionLength (projectiveLabelOfSimple sigma k) + 1 =
    sigma.compositionLength p
  rw [hkLabel, hiLength]
  change fixedTopCapacity sigma j - 1 + 1 = fixedTopCapacity sigma j
  omega

/-- A complete finite uniserial skeleton with two simple labels and finite
left heredity contains at most three indecomposable labels. -/
theorem natCard_le_three_of_twoSimples_of_finitelyGeneratedLeftHereditary
    (hNakayama : QuotientSubmoduleEquidistribution.LocalNakayamaBranch.IsNakayamaSkeleton sigma)
    (hHereditary : FinitelyGeneratedLeftHereditary R)
    (hTwo : Nat.card sigma.SimpleIndex = 2) :
    Nat.card iota ≤ 3 := by
  classical
  letI : Finite sigma.SimpleIndex :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype sigma.SimpleIndex := Fintype.ofFinite sigma.SimpleIndex
  have hcapacityPos : ∀ j : sigma.SimpleIndex,
      0 < fixedTopCapacity sigma j := by
    intro j
    exact sigma.compositionLength_pos (projectiveLabelOfSimple sigma j)
  have hcapacityPred : ∀ j : sigma.SimpleIndex,
      1 < fixedTopCapacity sigma j →
        ∃ k : sigma.SimpleIndex,
          fixedTopCapacity sigma k + 1 = fixedTopCapacity sigma j := by
    intro j hj
    exact exists_capacity_predecessor sigma hNakayama hHereditary j hj
  have hsum :
      (∑ j : sigma.SimpleIndex, fixedTopCapacity sigma j) ≤ 3 :=
    sum_le_three_of_card_eq_two_of_exists_pred
      (fixedTopCapacity sigma) hTwo hcapacityPos hcapacityPred
  calc
    Nat.card iota =
        Nat.card
          (QuotientSubmoduleEquidistribution.NakayamaCombinatorics.ChainPoint
            (fixedTopCapacity sigma)) :=
      Nat.card_congr (fixedTopLabelEquiv sigma hNakayama).symm
    _ = ∑ j : sigma.SimpleIndex, fixedTopCapacity sigma j := by
      rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
      simp
    _ ≤ 3 := hsum

end Capacity

namespace AlgebraNode

open QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence

variable (K : Type u) [Field K] [IsAlgClosed K]

/-- Node-level categorical boundary: finite left heredity and exactly two
simple labels force at most three indecomposable labels. -/
theorem indexCard_le_three_of_twoSimples_of_finitelyGeneratedLeftHereditary
    (B : AlgebraNode K)
    (hHereditary : FinitelyGeneratedLeftHereditary B.Carrier)
    (hTwo : Nat.card B.skeleton.SimpleIndex = 2) :
    Nat.card B.Index ≤ 3 := by
  letI : IsArtinianRing B.Carrier :=
    IsArtinianRing.of_finite K B.Carrier
  let tau :=
    QuotientSubmoduleEquidistribution.rightIndecomposableSkeleton.{u, u, u} K B.Carrier
  let D :=
    QuotientSubmoduleEquidistribution.Contragredient.alignedBiduality
      K B.Carrier B.skeleton tau
  letI : Finite
      (QuotientSubmoduleEquidistribution.CanonicalIndecomposableIndex.{u, u}
        B.Carrierᵐᵒᵖ) :=
    D.forward.labelEquiv.finite_iff.mp inferInstance
  have hNakayama :
      QuotientSubmoduleEquidistribution.LocalNakayamaBranch.IsNakayamaSkeleton B.skeleton :=
    isNakayamaSkeleton_of_twoSimples_of_finitelyGeneratedLeftHereditary
      (K := K) (R := B.Carrier) (S := B.Carrierᵐᵒᵖ)
      B.skeleton tau D.forward hHereditary hTwo
  exact
    natCard_le_three_of_twoSimples_of_finitelyGeneratedLeftHereditary
      B.skeleton hNakayama hHereditary hTwo

/-- The Ringel-core equality branch automatically supplies the finite
heredity premise in the preceding theorem. -/
theorem indexCard_le_three_of_twoSimples_of_projectiveCount_eq_coreSize
    (B : AlgebraNode K)
    (hTwo : Nat.card B.skeleton.SimpleIndex = 2)
    (hvd : projectiveCount K B = coreSize K B) :
    Nat.card B.Index ≤ 3 := by
  exact
    indexCard_le_three_of_twoSimples_of_finitelyGeneratedLeftHereditary
      K B
      (finitelyGeneratedLeftHereditary_of_projectiveCount_eq_coreSize
        K B hvd)
      hTwo

end AlgebraNode

end QuotientSubmoduleEquidistribution.HereditaryTwoSimpleBoundary
