import QuotientSubmoduleEquidistribution.Combinatorics.BoundaryTranslationProducts
import QuotientSubmoduleEquidistribution.RepresentationTheory.FourVertexArrowOrbits

/-!
# Global square shift on pairs of labelled AR arrows

Rather than choosing two mesh-rotation orbits and rectangular coordinates,
the simultaneous `(f,e) ↦ (f+2,e+2)` move can be performed on the finite
type of all pairs of labelled irreducible-arrow occurrences.  The enlarged
source and target predicates are exactly the first-two and last-two layers
of every chain component; periodic components have neither boundary.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open CategoryTheory

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton.ARMeshRotationData

universe u v w

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} [Fintype ι] [DecidableEq ι]
  (σ : IndecomposableSkeleton.{u, v, w} R ι)
  (M : σ.ARMeshRotationData)

/-- Simultaneous two-step mesh rotation on all pairs of labelled arrow
occurrences. -/
def arrowPairTwoStepData :=
  let A := M.arrowOrbitData σ
  A.twoStepProd A

/-- The labelled arrow occurrences left after deleting the outermost
projective-target and injective-source occurrence of every chain orbit. -/
abbrev InteriorArrow := (M.arrowOrbitData σ).Interior

/-- Mesh rotation restricted to the interior arrow occurrences. -/
def arrowInteriorOrbitData := (M.arrowOrbitData σ).interior

/-- Simultaneous two-step rotation on pairs of interior arrow
occurrences.  Its boundary is the shifted rectangle used in the signed
strip argument. -/
def arrowInteriorPairTwoStepData :=
  let A := M.arrowInteriorOrbitData σ
  A.twoStepProd A

noncomputable instance arrowPairTwoStepSourceFintype :
    Fintype {p : σ.IrreduciblePair × σ.IrreduciblePair //
      (M.arrowOrbitData σ).TwoSource p.1 ∨
        (M.arrowOrbitData σ).TwoSource p.2} := Fintype.ofFinite _

noncomputable instance arrowPairTwoStepTargetFintype :
    Fintype {p : σ.IrreduciblePair × σ.IrreduciblePair //
      (M.arrowOrbitData σ).TwoTarget p.1 ∨
        (M.arrowOrbitData σ).TwoTarget p.2} := Fintype.ofFinite _

noncomputable instance interiorArrowFintype :
    Fintype (M.InteriorArrow σ) := Fintype.ofFinite _

noncomputable instance arrowInteriorPairTwoStepSourceFintype :
    Fintype {p : M.InteriorArrow σ × M.InteriorArrow σ //
      (M.arrowInteriorOrbitData σ).TwoSource p.1 ∨
        (M.arrowInteriorOrbitData σ).TwoSource p.2} :=
  Fintype.ofFinite _

noncomputable instance arrowInteriorPairTwoStepTargetFintype :
    Fintype {p : M.InteriorArrow σ × M.InteriorArrow σ //
      (M.arrowInteriorOrbitData σ).TwoTarget p.1 ∨
        (M.arrowInteriorOrbitData σ).TwoTarget p.2} :=
  Fintype.ofFinite _

omit [Fintype ι] [DecidableEq ι] in
/-- On an interior arrow, the shifted source predicate says exactly that
the original arrow starts at a projective. -/
theorem arrowInterior_source_iff (a : M.InteriorArrow σ) :
    (M.arrowOrbitData σ).InteriorSource a ↔
      Projective (σ.obj a.1.1.1) := by
  have hrotate := M.arrowOrbitData_tau_val σ
    ⟨a.1, a.2.1⟩
  change Projective
      (σ.obj ((M.arrowOrbitData σ).tau ⟨a.1, a.2.1⟩).1.1.2) ↔
    Projective (σ.obj a.1.1.1)
  rw [congrArg Prod.snd hrotate]

omit [Fintype ι] [DecidableEq ι] in
/-- On an interior arrow, the shifted target predicate says exactly that
the original arrow ends at an injective. -/
theorem arrowInterior_target_iff (a : M.InteriorArrow σ) :
    (M.arrowOrbitData σ).InteriorTarget a ↔
      Injective (σ.obj a.1.1.2) := by
  have hrotate := M.arrowOrbitData_tau_symm_val σ
    ⟨a.1, a.2.2⟩
  change Injective
      (σ.obj ((M.arrowOrbitData σ).tau.symm
        ⟨a.1, a.2.2⟩).1.1.1) ↔
    Injective (σ.obj a.1.1.2)
  rw [congrArg Prod.fst hrotate]

omit [Fintype ι] [DecidableEq ι] in
/-- For arrow mesh rotation, the enlarged source boundary consists exactly
of arrows incident with a projective at either endpoint. -/
theorem arrowOrbit_twoSource_iff (a : σ.IrreduciblePair) :
    (M.arrowOrbitData σ).TwoSource a ↔
      Projective (σ.obj a.1.2) ∨ Projective (σ.obj a.1.1) := by
  let O := M.arrowOrbitData σ
  constructor
  · intro h
    rcases h with ht | hnext
    · exact Or.inl ht
    · by_cases ht : Projective (σ.obj a.1.2)
      · exact Or.inl ht
      · right
        have hp := hnext ht
        have hval := M.arrowOrbitData_tau_val σ ⟨a, ht⟩
        have htarget := congrArg Prod.snd hval
        simpa only [htarget] using hp
  · intro h
    rcases h with ht | hs
    · exact Or.inl ht
    · right
      intro ht
      have hval := M.arrowOrbitData_tau_val σ ⟨a, ht⟩
      have htarget := congrArg Prod.snd hval
      simpa only [htarget] using hs

omit [Fintype ι] [DecidableEq ι] in
/-- Dually, the enlarged target boundary consists exactly of arrows
incident with an injective at either endpoint. -/
theorem arrowOrbit_twoTarget_iff (a : σ.IrreduciblePair) :
    (M.arrowOrbitData σ).TwoTarget a ↔
      Injective (σ.obj a.1.1) ∨ Injective (σ.obj a.1.2) := by
  let O := M.arrowOrbitData σ
  constructor
  · intro h
    rcases h with hs | hprev
    · exact Or.inl hs
    · by_cases hs : Injective (σ.obj a.1.1)
      · exact Or.inl hs
      · right
        have hi := hprev hs
        have hval := M.arrowOrbitData_tau_symm_val σ ⟨a, hs⟩
        have hsource := congrArg Prod.fst hval
        simpa only [hsource] using hi
  · intro h
    rcases h with hs | ht
    · exact Or.inl hs
    · right
      intro hs
      have hval := M.arrowOrbitData_tau_symm_val σ ⟨a, hs⟩
      have hsource := congrArg Prod.fst hval
      simpa only [hsource] using ht

omit [Fintype ι] [DecidableEq ι] in
/-- Two successor steps are possible only when the original arrow target is
noninjective. -/
theorem target_noninjective_of_not_twoTarget
    (a : σ.IrreduciblePair)
    (ha : ¬ (M.arrowOrbitData σ).TwoTarget a) :
    ¬ Injective (σ.obj a.1.2) := by
  let O := M.arrowOrbitData σ
  have ha₀ : ¬ Injective (σ.obj a.1.1) :=
    O.not_twoTarget_first ha
  have ha₁ := O.not_twoTarget_second ha
  have hfirst := M.arrowOrbitData_tau_symm_val σ ⟨a, ha₀⟩
  have hsource := congrArg Prod.fst hfirst
  rw [hsource] at ha₁
  exact ha₁

omit [Fintype ι] [DecidableEq ι] in
/-- Advancing an arrow occurrence twice applies inverse AR translation to
its target vertex. -/
theorem two_successor_target_eq_inverse
    (a : σ.IrreduciblePair)
    (ha : ¬ (M.arrowOrbitData σ).TwoTarget a) :
    let O := M.arrowOrbitData σ
    (O.successor (O.successor a)).1.2 =
      (M.tau.symm ⟨a.1.2,
        M.target_noninjective_of_not_twoTarget σ a ha⟩).1 := by
  let O := M.arrowOrbitData σ
  have ha₀ : ¬ Injective (σ.obj a.1.1) :=
    O.not_twoTarget_first ha
  let s := O.successor a
  have hs_eq : s = O.tau.symm ⟨a, ha₀⟩ := by
    simp [s, QuotientSubmoduleEquidistribution.BoundaryTranslationChains.Data.successor, ha₀]
  have hsNI : ¬ Injective (σ.obj s.1.1) := by
    have h := O.not_twoTarget_second ha
    simpa only [hs_eq] using h
  have hfirst := M.arrowOrbitData_tau_symm_val σ ⟨a, ha₀⟩
  have hsSource : s.1.1 = a.1.2 := by
    rw [hs_eq]
    exact congrArg Prod.fst hfirst
  have hsecond := M.arrowOrbitData_tau_symm_val σ ⟨s, hsNI⟩
  calc
    (O.successor (O.successor a)).1.2 = (O.successor s).1.2 := rfl
    _ = (O.tau.symm ⟨s, hsNI⟩).1.1.2 := by
      simp [QuotientSubmoduleEquidistribution.BoundaryTranslationChains.Data.successor, hsNI]
    _ = (M.tau.symm ⟨s.1.1, hsNI⟩).1 :=
      congrArg Prod.snd hsecond
    _ = (M.tau.symm ⟨a.1.2,
        M.target_noninjective_of_not_twoTarget σ a ha⟩).1 := by
      congr 2
      apply Subtype.ext
      exact hsSource

omit [Fintype ι] [DecidableEq ι] in
/-- Equality of two arrow targets is invariant under simultaneous
two-successor advancement. -/
theorem two_successor_target_eq_iff
    (a b : σ.IrreduciblePair)
    (ha : ¬ (M.arrowOrbitData σ).TwoTarget a)
    (hb : ¬ (M.arrowOrbitData σ).TwoTarget b) :
    let O := M.arrowOrbitData σ
    (O.successor (O.successor a)).1.2 =
        (O.successor (O.successor b)).1.2 ↔
      a.1.2 = b.1.2 := by
  let O := M.arrowOrbitData σ
  change (O.successor (O.successor a)).1.2 =
      (O.successor (O.successor b)).1.2 ↔ a.1.2 = b.1.2
  have hA := M.two_successor_target_eq_inverse σ a ha
  have hB := M.two_successor_target_eq_inverse σ b hb
  change (O.successor (O.successor a)).1.2 =
      (M.tau.symm ⟨a.1.2,
        M.target_noninjective_of_not_twoTarget σ a ha⟩).1 at hA
  change (O.successor (O.successor b)).1.2 =
      (M.tau.symm ⟨b.1.2,
        M.target_noninjective_of_not_twoTarget σ b hb⟩).1 at hB
  rw [hA, hB]
  constructor
  · intro h
    have hsub : M.tau.symm
          ⟨a.1.2, M.target_noninjective_of_not_twoTarget σ a ha⟩ =
        M.tau.symm
          ⟨b.1.2, M.target_noninjective_of_not_twoTarget σ b hb⟩ := by
      apply Subtype.ext
      exact h
    exact congrArg Subtype.val (M.tau.symm.injective hsub)
  · intro h
    congr 2
    apply Subtype.ext
    exact h

omit [Fintype ι] [DecidableEq ι] in
/-- Advancing an arrow occurrence twice applies inverse AR translation to
its source vertex. -/
theorem two_successor_source_eq_inverse
    (a : σ.IrreduciblePair)
    (ha : ¬ (M.arrowOrbitData σ).TwoTarget a) :
    let O := M.arrowOrbitData σ
    (O.successor (O.successor a)).1.1 =
      (M.tau.symm ⟨a.1.1, O.not_twoTarget_first ha⟩).1 := by
  let O := M.arrowOrbitData σ
  have ha₀ : ¬ Injective (σ.obj a.1.1) :=
    O.not_twoTarget_first ha
  let s := O.successor a
  have hs_eq : s = O.tau.symm ⟨a, ha₀⟩ := by
    simp [s, QuotientSubmoduleEquidistribution.BoundaryTranslationChains.Data.successor, ha₀]
  have hsNI : ¬ Injective (σ.obj s.1.1) := by
    have h := O.not_twoTarget_second ha
    simpa only [hs_eq] using h
  have hfirst := M.arrowOrbitData_tau_symm_val σ ⟨a, ha₀⟩
  have hsecond := M.arrowOrbitData_tau_symm_val σ ⟨s, hsNI⟩
  calc
    (O.successor (O.successor a)).1.1 = (O.successor s).1.1 := rfl
    _ = (O.tau.symm ⟨s, hsNI⟩).1.1.1 := by
      simp [QuotientSubmoduleEquidistribution.BoundaryTranslationChains.Data.successor, hsNI]
    _ = s.1.2 := congrArg Prod.fst hsecond
    _ = (O.tau.symm ⟨a, ha₀⟩).1.1.2 := by rw [hs_eq]
    _ = (M.tau.symm ⟨a.1.1, ha₀⟩).1 :=
      congrArg Prod.snd hfirst

omit [Fintype ι] [DecidableEq ι] in
/-- Equality of two arrow sources is invariant under simultaneous
two-successor advancement. -/
theorem two_successor_source_eq_iff
    (a b : σ.IrreduciblePair)
    (ha : ¬ (M.arrowOrbitData σ).TwoTarget a)
    (hb : ¬ (M.arrowOrbitData σ).TwoTarget b) :
    let O := M.arrowOrbitData σ
    (O.successor (O.successor a)).1.1 =
        (O.successor (O.successor b)).1.1 ↔
      a.1.1 = b.1.1 := by
  let O := M.arrowOrbitData σ
  change (O.successor (O.successor a)).1.1 =
      (O.successor (O.successor b)).1.1 ↔ a.1.1 = b.1.1
  have hA := M.two_successor_source_eq_inverse σ a ha
  have hB := M.two_successor_source_eq_inverse σ b hb
  change (O.successor (O.successor a)).1.1 =
      (M.tau.symm ⟨a.1.1, O.not_twoTarget_first ha⟩).1 at hA
  change (O.successor (O.successor b)).1.1 =
      (M.tau.symm ⟨b.1.1, O.not_twoTarget_first hb⟩).1 at hB
  rw [hA, hB]
  constructor
  · intro h
    have hsub : M.tau.symm
          ⟨a.1.1, O.not_twoTarget_first ha⟩ =
        M.tau.symm
          ⟨b.1.1, O.not_twoTarget_first hb⟩ := by
      apply Subtype.ext
      exact h
    exact congrArg Subtype.val (M.tau.symm.injective hsub)
  · intro h
    congr 2
    exact Subtype.ext h

omit [Fintype ι] [DecidableEq ι] in
/-- If an interior arrow lies before the last two interior layers, then its
underlying original occurrence lies before the last two original layers. -/
theorem original_not_twoTarget_of_interior_not_twoTarget
    (a : M.InteriorArrow σ)
    (ha : ¬ (M.arrowInteriorOrbitData σ).TwoTarget a) :
    ¬ (M.arrowOrbitData σ).TwoTarget a.1 := by
  let U := M.arrowInteriorOrbitData σ
  have ht : ¬ Injective (σ.obj a.1.1.2) := by
    intro hi
    exact U.not_twoTarget_first ha
      ((M.arrowInterior_target_iff σ a).2 hi)
  rw [M.arrowOrbit_twoTarget_iff σ]
  exact not_or_intro a.2.2 ht

omit [Fintype ι] [DecidableEq ι] in
/-- Equality of the underlying arrow targets is invariant under two
successor steps in the trimmed arrow orbit. -/
theorem interior_two_successor_target_eq_iff
    (a b : M.InteriorArrow σ)
    (ha : ¬ (M.arrowInteriorOrbitData σ).TwoTarget a)
    (hb : ¬ (M.arrowInteriorOrbitData σ).TwoTarget b) :
    let U := M.arrowInteriorOrbitData σ
    (U.successor (U.successor a)).1.1.2 =
        (U.successor (U.successor b)).1.1.2 ↔
      a.1.1.2 = b.1.1.2 := by
  let O := M.arrowOrbitData σ
  let U := M.arrowInteriorOrbitData σ
  change (U.successor (U.successor a)).1.1.2 =
      (U.successor (U.successor b)).1.1.2 ↔
    a.1.1.2 = b.1.1.2
  have haVal := O.interior_two_successor_val a ha
  have hbVal := O.interior_two_successor_val b hb
  have haTarget :
      (U.successor (U.successor a)).1.1.2 =
        (O.successor (O.successor a.1)).1.2 := by
    simpa only [U, O, arrowInteriorOrbitData] using congrArg
      (fun q : σ.IrreduciblePair ↦ q.1.2) haVal
  have hbTarget :
      (U.successor (U.successor b)).1.1.2 =
        (O.successor (O.successor b.1)).1.2 := by
    simpa only [U, O, arrowInteriorOrbitData] using congrArg
      (fun q : σ.IrreduciblePair ↦ q.1.2) hbVal
  rw [haTarget, hbTarget]
  exact M.two_successor_target_eq_iff σ a.1 b.1
    (M.original_not_twoTarget_of_interior_not_twoTarget σ a ha)
    (M.original_not_twoTarget_of_interior_not_twoTarget σ b hb)

omit [Fintype ι] [DecidableEq ι] in
/-- Equality of the underlying arrow sources is invariant under two
successor steps in the trimmed arrow orbit. -/
theorem interior_two_successor_source_eq_iff
    (a b : M.InteriorArrow σ)
    (ha : ¬ (M.arrowInteriorOrbitData σ).TwoTarget a)
    (hb : ¬ (M.arrowInteriorOrbitData σ).TwoTarget b) :
    let U := M.arrowInteriorOrbitData σ
    (U.successor (U.successor a)).1.1.1 =
        (U.successor (U.successor b)).1.1.1 ↔
      a.1.1.1 = b.1.1.1 := by
  let O := M.arrowOrbitData σ
  let U := M.arrowInteriorOrbitData σ
  change (U.successor (U.successor a)).1.1.1 =
      (U.successor (U.successor b)).1.1.1 ↔
    a.1.1.1 = b.1.1.1
  have haVal := O.interior_two_successor_val a ha
  have hbVal := O.interior_two_successor_val b hb
  have haSource :
      (U.successor (U.successor a)).1.1.1 =
        (O.successor (O.successor a.1)).1.1 := by
    simpa only [U, O, arrowInteriorOrbitData] using congrArg
      (fun q : σ.IrreduciblePair ↦ q.1.1) haVal
  have hbSource :
      (U.successor (U.successor b)).1.1.1 =
        (O.successor (O.successor b.1)).1.1 := by
    simpa only [U, O, arrowInteriorOrbitData] using congrArg
      (fun q : σ.IrreduciblePair ↦ q.1.1) hbVal
  rw [haSource, hbSource]
  exact M.two_successor_source_eq_iff σ a.1 b.1
    (M.original_not_twoTarget_of_interior_not_twoTarget σ a ha)
    (M.original_not_twoTarget_of_interior_not_twoTarget σ b hb)

omit [DecidableEq ι] in
/-- Global weighted square-shift conservation on pairs of actual labelled
AR-arrow occurrences. -/
theorem arrowPairTwoStep_weighted_balance
    {A : Type*} [AddCommMonoid A]
    (weight : σ.IrreduciblePair × σ.IrreduciblePair → A)
    (hshift : ∀ p
      (_hp : ¬ ((M.arrowOrbitData σ).TwoTarget p.1 ∨
        (M.arrowOrbitData σ).TwoTarget p.2)),
      weight
          ((M.arrowOrbitData σ).successor
            ((M.arrowOrbitData σ).successor p.1),
           (M.arrowOrbitData σ).successor
            ((M.arrowOrbitData σ).successor p.2)) =
        weight p) :
    (∑ p : {p : σ.IrreduciblePair × σ.IrreduciblePair //
        (M.arrowOrbitData σ).TwoSource p.1 ∨
          (M.arrowOrbitData σ).TwoSource p.2},
      weight p.1) =
    ∑ p : {p : σ.IrreduciblePair × σ.IrreduciblePair //
        (M.arrowOrbitData σ).TwoTarget p.1 ∨
          (M.arrowOrbitData σ).TwoTarget p.2},
      weight p.1 := by
  let O := M.arrowOrbitData σ
  let B := O.twoStepProd O
  apply B.sum_source_eq_sum_target_of_successor_invariant weight
  intro p hp
  rw [O.twoStepProd_successor_eq O p hp]
  exact hshift p hp

/-- Global raw square-shift identity for the equality indicators of arrow
targets.  It simultaneously sums over all chain and periodic arrow-orbit
components, while retaining the labelled arrow occurrences. -/
theorem arrowPairTwoStep_targetEquality_balance :
    (∑ p : {p : σ.IrreduciblePair × σ.IrreduciblePair //
        (M.arrowOrbitData σ).TwoSource p.1 ∨
          (M.arrowOrbitData σ).TwoSource p.2},
      if p.1.1.1.2 = p.1.2.1.2 then 1 else 0) =
    ∑ p : {p : σ.IrreduciblePair × σ.IrreduciblePair //
        (M.arrowOrbitData σ).TwoTarget p.1 ∨
          (M.arrowOrbitData σ).TwoTarget p.2},
      if p.1.1.1.2 = p.1.2.1.2 then 1 else 0 := by
  classical
  apply M.arrowPairTwoStep_weighted_balance σ
    (weight := fun p ↦ if p.1.1.2 = p.2.1.2 then 1 else 0)
  intro p hp
  have h₁ : ¬ (M.arrowOrbitData σ).TwoTarget p.1 :=
    fun h ↦ hp (Or.inl h)
  have h₂ : ¬ (M.arrowOrbitData σ).TwoTarget p.2 :=
    fun h ↦ hp (Or.inr h)
  apply if_congr
  · exact M.two_successor_target_eq_iff σ p.1 p.2 h₁ h₂
  · rfl
  · rfl

/-- The source-equality version of the full global square-shift identity.
This is the form obtained from target equality after reversing every arrow. -/
theorem arrowPairTwoStep_sourceEquality_balance :
    (∑ p : {p : σ.IrreduciblePair × σ.IrreduciblePair //
        (M.arrowOrbitData σ).TwoSource p.1 ∨
          (M.arrowOrbitData σ).TwoSource p.2},
      if p.1.1.1.1 = p.1.2.1.1 then 1 else 0) =
    ∑ p : {p : σ.IrreduciblePair × σ.IrreduciblePair //
        (M.arrowOrbitData σ).TwoTarget p.1 ∨
          (M.arrowOrbitData σ).TwoTarget p.2},
      if p.1.1.1.1 = p.1.2.1.1 then 1 else 0 := by
  classical
  apply M.arrowPairTwoStep_weighted_balance σ
    (weight := fun p ↦ if p.1.1.1 = p.2.1.1 then 1 else 0)
  intro p hp
  have h₁ : ¬ (M.arrowOrbitData σ).TwoTarget p.1 :=
    fun h ↦ hp (Or.inl h)
  have h₂ : ¬ (M.arrowOrbitData σ).TwoTarget p.2 :=
    fun h ↦ hp (Or.inr h)
  apply if_congr
  · exact M.two_successor_source_eq_iff σ p.1 p.2 h₁ h₂
  · rfl
  · rfl

omit [DecidableEq ι] in
/-- Global weighted square-shift conservation after deleting the outermost
occurrence of every chain orbit. -/
theorem arrowInteriorPairTwoStep_weighted_balance
    {A : Type*} [AddCommMonoid A]
    (weight : M.InteriorArrow σ × M.InteriorArrow σ → A)
    (hshift : ∀ p
      (_hp : ¬ ((M.arrowInteriorOrbitData σ).TwoTarget p.1 ∨
        (M.arrowInteriorOrbitData σ).TwoTarget p.2)),
      weight
          ((M.arrowInteriorOrbitData σ).successor
            ((M.arrowInteriorOrbitData σ).successor p.1),
           (M.arrowInteriorOrbitData σ).successor
            ((M.arrowInteriorOrbitData σ).successor p.2)) =
        weight p) :
    (∑ p : {p : M.InteriorArrow σ × M.InteriorArrow σ //
        (M.arrowInteriorOrbitData σ).TwoSource p.1 ∨
          (M.arrowInteriorOrbitData σ).TwoSource p.2},
      weight p.1) =
    ∑ p : {p : M.InteriorArrow σ × M.InteriorArrow σ //
        (M.arrowInteriorOrbitData σ).TwoTarget p.1 ∨
          (M.arrowInteriorOrbitData σ).TwoTarget p.2},
      weight p.1 := by
  let U := M.arrowInteriorOrbitData σ
  let B := U.twoStepProd U
  apply B.sum_source_eq_sum_target_of_successor_invariant weight
  intro p hp
  rw [U.twoStepProd_successor_eq U p hp]
  exact hshift p hp

/-- The manuscript's raw shifted rectangle identity, globally summed over
all chain and cyclic components after deleting their outer occurrences. -/
theorem arrowInteriorPairTwoStep_targetEquality_balance :
    (∑ p : {p : M.InteriorArrow σ × M.InteriorArrow σ //
        (M.arrowInteriorOrbitData σ).TwoSource p.1 ∨
          (M.arrowInteriorOrbitData σ).TwoSource p.2},
      if p.1.1.1.1.2 = p.1.2.1.1.2 then 1 else 0) =
    ∑ p : {p : M.InteriorArrow σ × M.InteriorArrow σ //
        (M.arrowInteriorOrbitData σ).TwoTarget p.1 ∨
          (M.arrowInteriorOrbitData σ).TwoTarget p.2},
      if p.1.1.1.1.2 = p.1.2.1.1.2 then 1 else 0 := by
  classical
  apply M.arrowInteriorPairTwoStep_weighted_balance σ
    (weight := fun p ↦ if p.1.1.1.2 = p.2.1.1.2 then 1 else 0)
  intro p hp
  have h₁ : ¬ (M.arrowInteriorOrbitData σ).TwoTarget p.1 :=
    fun h ↦ hp (Or.inl h)
  have h₂ : ¬ (M.arrowInteriorOrbitData σ).TwoTarget p.2 :=
    fun h ↦ hp (Or.inr h)
  apply if_congr
  · exact M.interior_two_successor_target_eq_iff σ p.1 p.2 h₁ h₂
  · rfl
  · rfl

/-- The source-equality version of the global trimmed square-shift
identity.  This is the form obtained from target equality after reversing
all arrows by aligned duality. -/
theorem arrowInteriorPairTwoStep_sourceEquality_balance :
    (∑ p : {p : M.InteriorArrow σ × M.InteriorArrow σ //
        (M.arrowInteriorOrbitData σ).TwoSource p.1 ∨
          (M.arrowInteriorOrbitData σ).TwoSource p.2},
      if p.1.1.1.1.1 = p.1.2.1.1.1 then 1 else 0) =
    ∑ p : {p : M.InteriorArrow σ × M.InteriorArrow σ //
        (M.arrowInteriorOrbitData σ).TwoTarget p.1 ∨
          (M.arrowInteriorOrbitData σ).TwoTarget p.2},
      if p.1.1.1.1.1 = p.1.2.1.1.1 then 1 else 0 := by
  classical
  apply M.arrowInteriorPairTwoStep_weighted_balance σ
    (weight := fun p ↦ if p.1.1.1.1 = p.2.1.1.1 then 1 else 0)
  intro p hp
  have h₁ : ¬ (M.arrowInteriorOrbitData σ).TwoTarget p.1 :=
    fun h ↦ hp (Or.inl h)
  have h₂ : ¬ (M.arrowInteriorOrbitData σ).TwoTarget p.2 :=
    fun h ↦ hp (Or.inr h)
  apply if_congr
  · exact M.interior_two_successor_source_eq_iff σ p.1 p.2 h₁ h₂
  · rfl
  · rfl

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton.ARMeshRotationData
