import QuotientSubmoduleEquidistribution.RepresentationTheory.HereditaryTwoSimpleBoundary

/-!
# The exact projective shape at the hereditary two-simple cardinality-three boundary

The categorical two-simple hereditary theorem bounds a finite complete
skeleton by three labels.  At equality, the fixed-top chain classification
forces the two indecomposable projective capacities to be one and two.  Finite
left heredity then identifies the radical of the length-two projective with
the length-one projective.

These are intrinsic statements for an arbitrary algebra and complete
skeleton.  No quiver presentation or concrete module classification occurs.
-/

noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.HereditaryTwoSimpleCardThreeShape

universe u v

open QuotientSubmoduleEquidistribution.IndecomposableSkeleton
open QuotientSubmoduleEquidistribution.IndecomposableSkeleton.ProjectiveSimpleRank
open QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore
open QuotientSubmoduleEquidistribution.NakayamaFixedTopChains

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {iota : Type v} [Finite iota]
  (sigma : IndecomposableSkeleton.{u, v, u} R iota)

/-- In a finite complete uniserial skeleton with exactly two simple labels
and three indecomposable labels, the two fixed-top capacities are one and
two, in some order. -/
theorem exists_short_long_simple
    (hNakayama :
      QuotientSubmoduleEquidistribution.LocalNakayamaBranch.IsNakayamaSkeleton sigma)
    (hTwo : Nat.card sigma.SimpleIndex = 2)
    (hThree : Nat.card iota = 3) :
    ∃ short long : sigma.SimpleIndex,
      short ≠ long ∧
        fixedTopCapacity sigma short = 1 ∧
        fixedTopCapacity sigma long = 2 := by
  classical
  letI : Finite sigma.SimpleIndex :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype sigma.SimpleIndex := Fintype.ofFinite sigma.SimpleIndex
  have hsum :
      ∑ j : sigma.SimpleIndex, fixedTopCapacity sigma j = 3 := by
    calc
      ∑ j : sigma.SimpleIndex, fixedTopCapacity sigma j =
          Nat.card
            (QuotientSubmoduleEquidistribution.NakayamaCombinatorics.ChainPoint
              (fixedTopCapacity sigma)) := by
        rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
        simp
      _ = Nat.card iota :=
        Nat.card_congr (fixedTopLabelEquiv sigma hNakayama)
      _ = 3 := hThree
  obtain ⟨a, b, hab, hpairs⟩ := Nat.card_eq_two_iff.mp hTwo
  have hcases (x : sigma.SimpleIndex) : x = a ∨ x = b := by
    have hx : x ∈ ({a, b} : Set sigma.SimpleIndex) := by
      rw [hpairs]
      trivial
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hx
  have huniv : (Finset.univ : Finset sigma.SimpleIndex) = {a, b} := by
    ext x
    simp only [Finset.mem_univ, Finset.mem_insert,
      Finset.mem_singleton, true_iff]
    exact hcases x
  have habSum :
      fixedTopCapacity sigma a + fixedTopCapacity sigma b = 3 := by
    rw [huniv] at hsum
    simpa [hab] using hsum
  have haPos : 0 < fixedTopCapacity sigma a :=
    sigma.compositionLength_pos (projectiveLabelOfSimple sigma a)
  have hbPos : 0 < fixedTopCapacity sigma b :=
    sigma.compositionLength_pos (projectiveLabelOfSimple sigma b)
  rcases show
      (fixedTopCapacity sigma a = 1 ∧
          fixedTopCapacity sigma b = 2) ∨
        (fixedTopCapacity sigma b = 1 ∧
          fixedTopCapacity sigma a = 2) by omega with h | h
  · exact ⟨a, b, hab, h.1, h.2⟩
  · exact ⟨b, a, hab.symm, h.1, h.2⟩

omit [Finite iota] in
/-- If a projective fixed-top chain has capacity two, finite left heredity
makes its radical the indecomposable projective of capacity one. -/
theorem exists_radical_iso_short_projective
    (hNakayama :
      QuotientSubmoduleEquidistribution.LocalNakayamaBranch.IsNakayamaSkeleton sigma)
    (hHereditary : FinitelyGeneratedLeftHereditary R)
    (long : sigma.SimpleIndex)
    (hlong : fixedTopCapacity sigma long = 2) :
    ∃ short : sigma.SimpleIndex,
      fixedTopCapacity sigma short = 1 ∧
        Nonempty
          (sigma.obj (projectiveLabelOfSimple sigma short) ≅
            FGModuleCat.of R
              (sigma.moduleRadical
                (projectiveLabelOfSimple sigma long))) := by
  let p : iota := projectiveLabelOfSimple sigma long
  let J : Submodule R (sigma.obj p) := sigma.moduleRadical p
  have hpProjective : Projective (sigma.obj p) :=
    projective_projectiveLabelOfSimple sigma long
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
  have hJLength : Module.length R J = 1 := by
    rw [htopLength] at hlengthAdd
    apply WithTop.add_right_cancel ENat.one_ne_top
    calc
      Module.length R J + 1 = Module.length R (sigma.obj p) :=
        hlengthAdd.symm
      _ = (sigma.compositionLength p : ℕ∞) :=
        (sigma.coe_compositionLength p).symm
      _ = 2 := by
        have hlong' : sigma.compositionLength p = 2 := by
          simpa [p, fixedTopCapacity] using hlong
        exact_mod_cast hlong'
      _ = (1 : ℕ∞) + 1 := by norm_num
  have hJpos : (0 : ℕ∞) < Module.length R J := by
    rw [hJLength]
    norm_num
  letI : Nontrivial J := Module.length_pos_iff.mp hJpos
  have hJuniserial : IsUniserialModule R J :=
    (hNakayama p).submodule J
  have hJIndec : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R (FGModuleCat.of R J) :=
    hJuniserial.isIndecomposableModule
  obtain ⟨i, ⟨e⟩⟩ := sigma.complete (FGModuleCat.of R J) hJIndec
  have hiProjective : Projective (sigma.obj i) :=
    Projective.of_iso e hJProjective
  let q : ProjectiveIndex sigma := ⟨i, hiProjective⟩
  let short : sigma.SimpleIndex := projectiveIndexEquivSimpleIndex sigma q
  have hshortLabel : projectiveLabelOfSimple sigma short = i := by
    change ((projectiveIndexEquivSimpleIndex sigma).symm
      ((projectiveIndexEquivSimpleIndex sigma) q)).1 = i
    rw [(projectiveIndexEquivSimpleIndex sigma).symm_apply_apply]
  have hiLength : sigma.compositionLength i = 1 := by
    rw [← ENat.coe_inj, sigma.coe_compositionLength]
    exact (FGModuleCat.isoToLinearEquiv e).length_eq.symm.trans hJLength
  refine ⟨short, ?_, ?_⟩
  · change sigma.compositionLength
      (projectiveLabelOfSimple sigma short) = 1
    rw [hshortLabel, hiLength]
  · exact ⟨by simpa only [hshortLabel, J, p] using e.symm⟩

/-- Exact intrinsic projective shape at the cardinality-three boundary:
there are distinct short and long simple tops of capacities one and two, and
the radical of the long projective is isomorphic to the short projective. -/
theorem exists_projective_shape
    (hNakayama :
      QuotientSubmoduleEquidistribution.LocalNakayamaBranch.IsNakayamaSkeleton sigma)
    (hHereditary : FinitelyGeneratedLeftHereditary R)
    (hTwo : Nat.card sigma.SimpleIndex = 2)
    (hThree : Nat.card iota = 3) :
    ∃ short long : sigma.SimpleIndex,
      short ≠ long ∧
        fixedTopCapacity sigma short = 1 ∧
        fixedTopCapacity sigma long = 2 ∧
        Nonempty
          (sigma.obj (projectiveLabelOfSimple sigma short) ≅
            FGModuleCat.of R
              (sigma.moduleRadical
                (projectiveLabelOfSimple sigma long))) := by
  obtain ⟨_short, long, _hne, _hshort, hlong⟩ :=
    exists_short_long_simple sigma hNakayama hTwo hThree
  obtain ⟨short, hshort, hIso⟩ :=
    exists_radical_iso_short_projective
      sigma hNakayama hHereditary long hlong
  have hne : short ≠ long := by
    intro hEq
    subst long
    omega
  exact ⟨short, long, hne, hshort, hlong, hIso⟩

/-- At the same boundary there is exactly one indecomposable object of
composition length two.  This is a direct consequence of the fixed-top
chain parametrization and does not classify modules over any model algebra. -/
theorem natCard_lengthTwoIndex_eq_one
    (hNakayama :
      QuotientSubmoduleEquidistribution.LocalNakayamaBranch.IsNakayamaSkeleton sigma)
    (hTwo : Nat.card sigma.SimpleIndex = 2)
    (hThree : Nat.card iota = 3) :
    Nat.card sigma.LengthTwoIndex = 1 := by
  classical
  obtain ⟨short, long, hne, hshort, hlong⟩ :=
    exists_short_long_simple sigma hNakayama hTwo hThree
  letI : Finite sigma.SimpleIndex :=
    Finite.of_injective Subtype.val Subtype.val_injective
  let hcases (s : sigma.SimpleIndex) : s = short ∨ s = long := by
    obtain ⟨a, b, hab, hpairs⟩ := Nat.card_eq_two_iff.mp hTwo
    have hshortCase : short = a ∨ short = b := by
      have hs : short ∈ ({a, b} : Set sigma.SimpleIndex) := by
        rw [hpairs]
        trivial
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hs
    have hlongCase : long = a ∨ long = b := by
      have hl : long ∈ ({a, b} : Set sigma.SimpleIndex) := by
        rw [hpairs]
        trivial
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hl
    have hs : s = a ∨ s = b := by
      have hs' : s ∈ ({a, b} : Set sigma.SimpleIndex) := by
        rw [hpairs]
        trivial
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hs'
    rcases hshortCase with hsa | hsb <;>
      rcases hlongCase with hla | hlb <;>
        rcases hs with ha | hb
    · exact False.elim (hne (hsa.trans hla.symm))
    · exact False.elim (hne (hsa.trans hla.symm))
    · exact Or.inl (ha.trans hsa.symm)
    · exact Or.inr (hb.trans hlb.symm)
    · exact Or.inr (ha.trans hla.symm)
    · exact Or.inl (hb.trans hsb.symm)
    · exact False.elim (hne (hsb.trans hlb.symm))
    · exact False.elim (hne (hsb.trans hlb.symm))
  let q : QuotientSubmoduleEquidistribution.NakayamaCombinatorics.ChainPoint
      (fixedTopCapacity sigma) :=
    ⟨long, ⟨1, by rw [hlong]; omega⟩⟩
  let x0 : sigma.LengthTwoIndex :=
    ⟨fixedTopLabelEquiv sigma hNakayama q, by
      change sigma.compositionLength
        (fixedTopLabel sigma hNakayama q) = 2
      rw [fixedTopLabel_compositionLength]⟩
  have heqDefault (x : sigma.LengthTwoIndex) : x = x0 := by
    let p := (fixedTopLabelEquiv sigma hNakayama).symm x.1
    have hpLength :=
      fixedTopLabelEquiv_symm_compositionLength sigma hNakayama x.1
    have hpVal : (p.2 : ℕ) = 1 := by
      change sigma.compositionLength x.1 = (p.2 : ℕ) + 1 at hpLength
      rw [x.2] at hpLength
      omega
    have hpFirst : p.1 = long := by
      rcases hcases p.1 with hpShort | hpLong
      · have hpCapacity : fixedTopCapacity sigma p.1 = 1 :=
          (congrArg (fixedTopCapacity sigma) hpShort).trans hshort
        have hpLt : (p.2 : ℕ) < 1 := p.2.isLt.trans_eq hpCapacity
        rw [hpVal] at hpLt
        omega
      · exact hpLong
    have hpq : p = q := by
      cases hpFirst
      refine Sigma.ext rfl (heq_of_eq ?_)
      apply Fin.ext
      exact hpVal
    apply Subtype.ext
    change x.1 = fixedTopLabelEquiv sigma hNakayama q
    calc
      x.1 = fixedTopLabelEquiv sigma hNakayama p :=
        ((fixedTopLabelEquiv sigma hNakayama).apply_symm_apply x.1).symm
      _ = fixedTopLabelEquiv sigma hNakayama q :=
        congrArg (fixedTopLabelEquiv sigma hNakayama) hpq
  letI : Subsingleton sigma.LengthTwoIndex :=
    ⟨fun x y ↦ (heqDefault x).trans (heqDefault y).symm⟩
  letI : Nonempty sigma.LengthTwoIndex := ⟨x0⟩
  exact Nat.card_unique

section ExtArrow

variable {K : Type u} [Field K]
  [Small.{u} R] [IsArtinianRing R] [Algebra K R]

/-- With the maintained no-parallel theorem, the preceding unique
length-two object is equivalently the unique multiplicity-bearing
Ext--Gabriel arrow. -/
theorem natCard_extGabrielArrowIndex_eq_one
    (hNakayama :
      QuotientSubmoduleEquidistribution.LocalNakayamaBranch.IsNakayamaSkeleton sigma)
    (hTwo : Nat.card sigma.SimpleIndex = 2)
    (hThree : Nat.card iota = 3)
    (hNoParallel :
      QuotientSubmoduleEquidistribution.GabrielArrowBridge.NoParallelExtSupport
        (K := K) sigma) :
    Nat.card
        (QuotientSubmoduleEquidistribution.GabrielArrowBridge.ExtGabrielArrowIndex
          (K := K) sigma) = 1 := by
  rw [← QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.natCard_lengthTwoIndex_eq_extGabrielArrowIndex
    sigma hNoParallel]
  exact natCard_lengthTwoIndex_eq_one sigma hNakayama hTwo hThree

end ExtArrow

namespace AlgebraNode

open QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence

variable (K : Type u) [Field K] [IsAlgClosed K]

/-- Core equality and two simple labels imply the intrinsic Nakayama
condition on the complete node skeleton. -/
theorem isNakayamaSkeleton_of_twoSimples_of_projectiveCount_eq_coreSize
    (B : AlgebraNode K)
    (hTwo : Nat.card B.skeleton.SimpleIndex = 2)
    (hvd : projectiveCount K B = coreSize K B) :
    QuotientSubmoduleEquidistribution.LocalNakayamaBranch.IsNakayamaSkeleton B.skeleton := by
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
  have hHereditary : FinitelyGeneratedLeftHereditary B.Carrier :=
    QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence.finitelyGeneratedLeftHereditary_of_projectiveCount_eq_coreSize
      K B hvd
  exact
    QuotientSubmoduleEquidistribution.HereditaryTwoSimpleBoundary.isNakayamaSkeleton_of_twoSimples_of_finitelyGeneratedLeftHereditary
      (K := K) (R := B.Carrier) (S := B.Carrierᵐᵒᵖ)
      B.skeleton tau D.forward hHereditary hTwo

/-- Node-level form used by the residual level-three recognition problem.
Core equality supplies finite left heredity, and the existing two-simple
categorical theorem supplies uniseriality before the exact projective shape
is extracted. -/
theorem exists_projective_shape_of_twoSimples_of_cardThree_of_projectiveCount_eq_coreSize
    (B : AlgebraNode K)
    (hTwo : Nat.card B.skeleton.SimpleIndex = 2)
    (hThree : Nat.card B.Index = 3)
    (hvd : projectiveCount K B = coreSize K B) :
    ∃ short long : B.skeleton.SimpleIndex,
      short ≠ long ∧
        fixedTopCapacity B.skeleton short = 1 ∧
        fixedTopCapacity B.skeleton long = 2 ∧
        Nonempty
          (B.skeleton.obj
              (projectiveLabelOfSimple B.skeleton short) ≅
            FGModuleCat.of B.Carrier
              (B.skeleton.moduleRadical
                (projectiveLabelOfSimple B.skeleton long))) := by
  have hHereditary : FinitelyGeneratedLeftHereditary B.Carrier :=
    QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence.finitelyGeneratedLeftHereditary_of_projectiveCount_eq_coreSize
      K B hvd
  have hNakayama :
      QuotientSubmoduleEquidistribution.LocalNakayamaBranch.IsNakayamaSkeleton B.skeleton :=
    isNakayamaSkeleton_of_twoSimples_of_projectiveCount_eq_coreSize
      K B hTwo hvd
  exact exists_projective_shape
    B.skeleton hNakayama hHereditary hTwo hThree

/-- The corresponding node has exactly one multiplicity-bearing
Ext--Gabriel arrow. -/
theorem extGabrielArrowCard_eq_one_of_twoSimples_of_cardThree_of_projectiveCount_eq_coreSize
    (B : AlgebraNode K)
    (hTwo : Nat.card B.skeleton.SimpleIndex = 2)
    (hThree : Nat.card B.Index = 3)
    (hvd : projectiveCount K B = coreSize K B) :
    Nat.card
        (QuotientSubmoduleEquidistribution.GabrielArrowBridge.ExtGabrielArrowIndex
          (K := K) B.skeleton) = 1 := by
  letI : IsArtinianRing B.Carrier :=
    IsArtinianRing.of_finite K B.Carrier
  have hNakayama :
      QuotientSubmoduleEquidistribution.LocalNakayamaBranch.IsNakayamaSkeleton B.skeleton :=
    isNakayamaSkeleton_of_twoSimples_of_projectiveCount_eq_coreSize
      K B hTwo hvd
  have hNoParallel :
      QuotientSubmoduleEquidistribution.GabrielArrowBridge.NoParallelExtSupport
        (K := K) B.skeleton :=
    QuotientSubmoduleEquidistribution.HereditaryTwoSimpleBoundary.noParallelExtSupport_of_finiteDimensional
      B.skeleton
  exact natCard_extGabrielArrowIndex_eq_one
    B.skeleton hNakayama hTwo hThree hNoParallel

end AlgebraNode

end QuotientSubmoduleEquidistribution.HereditaryTwoSimpleCardThreeShape
