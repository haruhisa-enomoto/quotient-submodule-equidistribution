import OpConjecture.RepresentationTheory.A2SeparatedClassification
import OpConjecture.RepresentationTheory.ConnectedSmallCoreRank
import OpConjecture.RepresentationTheory.ProjectiveSimpleRank
import OpConjecture.RepresentationTheory.RingelEtaCoreCardinality

/-!
# The faithful core of the one-arrow triangular algebra

The top endpoint simple has no nonzero map to a finite projective module.
Consequently it is absent from the torsionless core.  Together with the
two-simple projective-rank theorem and Ringel's core-cardinality theorem,
this computes the fixed `A₂` quotient core as having cardinality two.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Set

namespace OpConjecture.A2Separated

open OpConjecture.IndecomposableSkeleton
open OpConjecture.IndecomposableSkeleton.FaithfulCore
open SeparatedTriangularAlgebra

universe u

variable (K : Type u) [Field K]

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- The top endpoint simple has no nonzero map to the left regular module.
The diagonal top idempotent first kills the radical coordinates of the
image, and the square-zero arrow then kills its remaining top coordinate. -/
theorem top_hom_regular_eq_zero
    (f : candidateFG K 1 ⟶
      (regularFGModule (R := Triangular K))) : f = 0 := by
  let x : Realized (topData K) := (1, PUnit.unit)
  let a : Triangular K := f.hom.hom x
  let eTop : Triangular K := TrivSqZeroExt.inl ((0, 1) : K × K)
  have hTop := f.hom.hom.map_smul eTop x
  have hxTop : eTop • x = x := by
    dsimp only [eTop]
    rw [inl_smul_realized]
    apply Prod.ext
    · simp [x]
    · exact Subsingleton.elim _ _
  have hTop' : f.hom.hom x = eTop • f.hom.hom x := by
    calc
      f.hom.hom x = f.hom.hom (eTop • x) := congrArg f.hom.hom hxTop.symm
      _ = eTop • f.hom.hom x := hTop
  change a = eTop * a at hTop'
  have haRad := congrArg (fun z : Triangular K ↦ z.fst.1) hTop'
  have haArrow := congrArg (fun z : Triangular K ↦ z.snd.val) hTop'
  have hRadZero : a.fst.1 = 0 := by
    simpa [eTop] using haRad
  have hArrowZero : a.snd.val = 0 := by
    simpa [eTop] using haArrow
  let arrow : Triangular K :=
    TrivSqZeroExt.inr (⟨1⟩ : SeparatedTriangularAlgebra.SeparatedIdeal K K)
  have hArrow := f.hom.hom.map_smul arrow x
  have hxArrow : arrow • x = 0 := by
    dsimp only [arrow]
    rw [inr_smul_realized]
    apply Prod.ext
    · rfl
    · exact Subsingleton.elim _ _
  have hArrow' : f.hom.hom (0 : Realized (topData K)) =
      arrow • f.hom.hom x := by
    calc
      f.hom.hom (0 : Realized (topData K)) =
          f.hom.hom (arrow • x) := congrArg f.hom.hom hxArrow.symm
      _ = arrow • f.hom.hom x := hArrow
  change f.hom.hom (0 : Realized (topData K)) = arrow * a at hArrow'
  have hArrow'' : (0 : Triangular K) = arrow * a := by
    calc
      0 = f.hom.hom (0 : Realized (topData K)) :=
        (map_zero f.hom.hom).symm
      _ = arrow * a := hArrow'
  have haTop := congrArg (fun z : Triangular K ↦ z.snd.val) hArrow''
  have hTopZero : a.fst.2 = 0 := by
    simpa [arrow] using haTop.symm
  have ha : a = 0 := by
    apply TrivSqZeroExt.ext
    · apply Prod.ext
      · exact hRadZero
      · exact hTopZero
    · apply SeparatedTriangularAlgebra.SeparatedIdeal.ext
      exact hArrowZero
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  change f.hom.hom y = 0
  rcases y with ⟨t, d⟩
  change K at t
  change PUnit at d
  have hy : ((t, d) : Realized (topData K)) =
      (algebraMap K (Triangular K) t) • x := by
    apply Prod.ext
    · change t = t * (1 : K)
      simp
    · exact Subsingleton.elim _ _
  calc
    f.hom.hom (t, d) =
        f.hom.hom ((algebraMap K (Triangular K) t) • x) :=
      congrArg f.hom.hom hy
    _ = (algebraMap K (Triangular K) t) • f.hom.hom x :=
      f.hom.hom.map_smul _ _
    _ = 0 := by rw [show f.hom.hom x = a from rfl, ha, smul_zero]

/-- Hence the top endpoint simple has no nonzero map to any finite
categorical projective. -/
theorem top_hom_projective_eq_zero
    (P : FGModuleCat.{u} (Triangular K)) (hP : Projective P)
    (f : candidateFG K 1 ⟶ P) : f = 0 := by
  obtain ⟨L, p, hp⟩ := regularFGModule_generates (R := Triangular K) P
  letI : Epi p := hp
  letI : Projective P := hP
  let s : P ⟶ ⨁ fun _ : L ↦ regularFGModule (R := Triangular K) :=
    Projective.factorThru (𝟙 P) p
  have hs : s ≫ p = 𝟙 P := Projective.factorThru_comp (𝟙 P) p
  have hfs : f ≫ s = 0 := by
    apply biproduct.hom_ext
    intro l
    simpa only [Category.assoc, zero_comp] using
      top_hom_regular_eq_zero K
        (f ≫ s ≫ biproduct.π
          (fun _ : L ↦ regularFGModule (R := Triangular K)) l)
  calc
    f = f ≫ 𝟙 P := by simp
    _ = (f ≫ s) ≫ p := by rw [Category.assoc, hs]
    _ = 0 := by rw [hfs]; simp

/-- The top endpoint label selected in the canonical skeleton is not in the
submodule closure of the projective labels. -/
theorem candidateIndex_one_not_mem_submoduleCore :
    candidateIndex K 1 ∉
      (submoduleCore (sigma K) :
        Set (CanonicalIndecomposableIndex.{u, u} (Triangular K))) := by
  intro hmem
  obtain ⟨L, m, hm⟩ :=
    (mem_submoduleCore_iff_inSubOfModule (sigma K)
      (candidateIndex K 1)).1 hmem
  let sourceMap : candidateFG K 1 ⟶ (sigma K).obj (candidateIndex K 1) :=
    (candidateIndexIso K 1).hom
  let g : candidateFG K 1 ⟶
      ⨁ fun _ : L ↦ projectiveGenerator (sigma K) := sourceMap ≫ m
  have hgzero : g = 0 := by
    apply biproduct.hom_ext
    intro l
    simpa only [zero_comp] using
      top_hom_projective_eq_zero K (projectiveGenerator (sigma K))
        (projective_projectiveGenerator (sigma K))
        (g ≫ biproduct.π (fun _ : L ↦ projectiveGenerator (sigma K)) l)
  haveI : Mono g := by
    dsimp only [g]
    letI : Mono m := hm
    infer_instance
  letI : Simple (candidateFG K 1) :=
    (candidateFG_simple_iff K 1).2 (Or.inl rfl)
  apply CategoryTheory.id_nonzero (candidateFG K 1)
  apply (cancel_mono g).1
  rw [hgzero]
  simp

/-- The torsionless core of the fixed one-arrow algebra has cardinality
two. -/
theorem submoduleCore_ncard_eq_two :
    (submoduleCore (sigma K) :
      Set (CanonicalIndecomposableIndex.{u, u} (Triangular K))).ncard = 2 := by
  have hProjective :
      (projectiveLabels (sigma K) :
        Set (CanonicalIndecomposableIndex.{u, u} (Triangular K))).ncard = 2 := by
    calc
      (projectiveLabels (sigma K) :
          Set (CanonicalIndecomposableIndex.{u, u} (Triangular K))).ncard =
          Nat.card (sigma K).SimpleIndex :=
        OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.ncard_projectiveLabels_eq_natCard_simpleIndex
          (sigma K)
      _ = 2 := natCard_simpleIndex_eq_two K
  have hLower : 2 ≤
      (submoduleCore (sigma K) :
        Set (CanonicalIndecomposableIndex.{u, u} (Triangular K))).ncard := by
    rw [← hProjective]
    exact Set.ncard_le_ncard
      (OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.projectiveLabels_subset_submoduleCore
        (sigma K)) (Set.toFinite _)
  have hProper :
      (submoduleCore (sigma K) :
        Set (CanonicalIndecomposableIndex.{u, u} (Triangular K))) ⊂ Set.univ := by
    refine ⟨Set.subset_univ _, ?_⟩
    intro hreverse
    exact candidateIndex_one_not_mem_submoduleCore K
      (hreverse (Set.mem_univ _))
  have hUpper :
      (submoduleCore (sigma K) :
        Set (CanonicalIndecomposableIndex.{u, u} (Triangular K))).ncard < 3 := by
    calc
      (submoduleCore (sigma K) :
          Set (CanonicalIndecomposableIndex.{u, u} (Triangular K))).ncard <
          (Set.univ : Set
            (CanonicalIndecomposableIndex.{u, u} (Triangular K))).ncard :=
        Set.ncard_lt_ncard hProper (Set.toFinite _)
      _ = Nat.card
          (CanonicalIndecomposableIndex.{u, u} (Triangular K)) := by
        simp
      _ = 3 := natCard_canonicalIndex_eq_three K
  omega

/-- Ringel's stable equivalence transports the preceding computation to
the quotient-side faithful core. -/
theorem quotientCore_ncard_eq_two :
    (quotientCore (sigma K) :
      Set (CanonicalIndecomposableIndex.{u, u} (Triangular K))).ncard = 2 := by
  have hRingel : RingelCoreCardinality (sigma K) :=
    OpConjecture.RingelStable.FaithfulCoreAdapter.ringelCoreCardinality_of_ringelEtaStableEquivalence
      (sigma K) K
  calc
    (quotientCore (sigma K) :
        Set (CanonicalIndecomposableIndex.{u, u} (Triangular K))).ncard =
        (submoduleCore (sigma K) :
          Set (CanonicalIndecomposableIndex.{u, u} (Triangular K))).ncard :=
      hRingel
    _ = 2 := submoduleCore_ncard_eq_two K

end OpConjecture.A2Separated
