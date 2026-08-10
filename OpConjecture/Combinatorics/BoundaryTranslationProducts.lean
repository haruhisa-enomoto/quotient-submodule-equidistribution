import OpConjecture.Combinatorics.BoundaryTranslationWeightedBalance

/-!
# Two-step and product boundary translations

The signed strip moves both of two orbit coordinates forward by two.  This
file constructs that operation globally, without choosing orbit
representatives: first enlarge each boundary to its first or last two
layers, then take the product of two partial translations.
-/

set_option autoImplicit false
noncomputable section

namespace OpConjecture.BoundaryTranslationChains.Data

universe u v

variable {Vertex : Type u} {P I : Vertex → Prop}
  (T : OpConjecture.BoundaryTranslationChains.Data Vertex P I)

/-- The first two layers at the source end of every partial-translation
chain. -/
def TwoSource (x : Vertex) : Prop :=
  P x ∨ ∀ hx : ¬ P x, P (T.tau ⟨x, hx⟩).1

/-- The last two layers at the target end of every partial-translation
chain. -/
def TwoTarget (x : Vertex) : Prop :=
  I x ∨ ∀ hx : ¬ I x, I (T.tau.symm ⟨x, hx⟩).1

/-- Vertices remaining after deleting the two outer boundary layers of a
partial-translation component.  On a chain these are precisely the
non-source, non-target positions; a cyclic component is unchanged. -/
abbrev Interior (_T :
    OpConjecture.BoundaryTranslationChains.Data Vertex P I) :=
  {x : Vertex // ¬ P x ∧ ¬ I x}

/-- The new source boundary after deleting the old source and target
positions: an interior vertex is new-source exactly when its predecessor
was an old source. -/
def InteriorSource (x : T.Interior) : Prop :=
  P (T.tau ⟨x.1, x.2.1⟩).1

/-- The new target boundary after deleting the old source and target
positions: an interior vertex is new-target exactly when its successor was
an old target. -/
def InteriorTarget (x : T.Interior) : Prop :=
  I (T.tau.symm ⟨x.1, x.2.2⟩).1

/-- Restrict a finite partial translation to the interior obtained by
deleting the original source and target positions of every chain. -/
def interior :
    OpConjecture.BoundaryTranslationChains.Data T.Interior
      T.InteriorSource T.InteriorTarget where
  tau :=
    { toFun := fun x ↦ by
        let y := T.tau ⟨x.1.1, x.1.2.1⟩
        have hyP : ¬ P y.1 := by
          intro hy
          exact x.2 hy
        let yInterior : T.Interior := ⟨y.1, hyP, y.2⟩
        refine ⟨yInterior, ?_⟩
        intro hyTarget
        apply x.1.2.2
        change I (T.tau.symm ⟨y.1, y.2⟩).1 at hyTarget
        have hback : T.tau.symm ⟨y.1, y.2⟩ =
            ⟨x.1.1, x.1.2.1⟩ :=
          T.tau.symm_apply_apply ⟨x.1.1, x.1.2.1⟩
        simpa only [hback] using hyTarget
      invFun := fun z ↦ by
        let x := T.tau.symm ⟨z.1.1, z.1.2.2⟩
        have hxI : ¬ I x.1 := by
          intro hx
          exact z.2 hx
        let xInterior : T.Interior := ⟨x.1, x.2, hxI⟩
        refine ⟨xInterior, ?_⟩
        intro hxSource
        apply z.1.2.1
        change P (T.tau ⟨x.1, x.2⟩).1 at hxSource
        have hforward : T.tau ⟨x.1, x.2⟩ =
            ⟨z.1.1, z.1.2.2⟩ :=
          T.tau.apply_symm_apply ⟨z.1.1, z.1.2.2⟩
        simpa only [hforward] using hxSource
      left_inv := by
        intro x
        apply Subtype.ext
        apply Subtype.ext
        change (T.tau.symm
          (T.tau ⟨x.1.1, x.1.2.1⟩)).1 = x.1.1
        exact congrArg Subtype.val
          (T.tau.symm_apply_apply ⟨x.1.1, x.1.2.1⟩)
      right_inv := by
        intro z
        apply Subtype.ext
        apply Subtype.ext
        change (T.tau
          (T.tau.symm ⟨z.1.1, z.1.2.2⟩)).1 = z.1.1
        exact congrArg Subtype.val
          (T.tau.apply_symm_apply ⟨z.1.1, z.1.2.2⟩) }

/-- Away from the new target boundary, interior successor has the same
underlying vertex as the original successor. -/
theorem interior_successor_val
    (x : T.Interior) (hx : ¬ T.InteriorTarget x) :
    (T.interior.successor x).1 = T.successor x.1 := by
  classical
  simp [OpConjecture.BoundaryTranslationChains.Data.successor,
    interior, hx, x.2.2]

/-- The target boundary of the restricted interior translation is detected
by whether the next original successor is on the old target boundary. -/
theorem interiorTarget_iff_target_successor (x : T.Interior) :
    T.InteriorTarget x ↔ I (T.successor x.1) := by
  classical
  simp [InteriorTarget,
    OpConjecture.BoundaryTranslationChains.Data.successor, x.2.2]

/-- As long as the original successor trajectory has not reached the old
target boundary, iteration in the restricted interior translation has the
same underlying vertices as iteration in the original translation. -/
theorem interior_iterate_successor_val
    (x : T.Interior) (n : ℕ)
    (h : ∀ i < n, ¬ I ((T.successor^[i + 1]) x.1)) :
    ((T.interior.successor^[n]) x).1 = (T.successor^[n]) x.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hprefix : ∀ i < n, ¬ I ((T.successor^[i + 1]) x.1) := by
        intro i hi
        exact h i (by omega)
      have hval := ih hprefix
      let y := (T.interior.successor^[n]) x
      have hyTarget : ¬ T.InteriorTarget y := by
        rw [T.interiorTarget_iff_target_successor y]
        rw [show T.successor y.1 =
            (T.successor^[n + 1]) x.1 by
          rw [hval]
          simp only [Function.iterate_succ_apply']]
        exact h n (by omega)
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      calc
        (T.interior.successor y).1 = T.successor y.1 :=
          T.interior_successor_val y hyTarget
        _ = T.successor ((T.successor^[n]) x.1) :=
          congrArg T.successor hval

/-- Equivalent trajectory form: if the restricted successor iterates have
not yet reached their new target boundary, their values follow the original
successor trajectory. -/
theorem interior_iterate_successor_val_of_not_interiorTarget
    (x : T.Interior) (n : ℕ)
    (h : ∀ i < n,
      ¬ T.InteriorTarget ((T.interior.successor^[i]) x)) :
    ((T.interior.successor^[n]) x).1 = (T.successor^[n]) x.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hprefix : ∀ i < n,
          ¬ T.InteriorTarget ((T.interior.successor^[i]) x) := by
        intro i hi
        exact h i (by omega)
      have hval := ih hprefix
      let y := (T.interior.successor^[n]) x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      calc
        (T.interior.successor y).1 = T.successor y.1 :=
          T.interior_successor_val y (h n (by omega))
        _ = T.successor ((T.successor^[n]) x.1) :=
          congrArg T.successor hval

/-- Two interior vertices which meet under the restricted successor also
belong to the same component of the original partial translation. -/
theorem sameSuccessorOrbit_val_of_interior
    (x y : T.Interior)
    (hxy : T.interior.SameSuccessorOrbit x y) :
    T.SameSuccessorOrbit x.1 y.1 := by
  let U := T.interior
  have hstep : ∀ z : T.Interior,
      T.SameSuccessorOrbit z.1 (U.successor z).1 := by
    intro z
    by_cases hz : T.InteriorTarget z
    · rw [U.successor_eq_self_of_mem_target hz]
      exact T.sameSuccessorOrbit_refl z.1
    · rw [T.interior_successor_val z hz]
      exact ⟨1, 0, rfl⟩
  have hiterate : ∀ (n : ℕ) (z : T.Interior),
      T.SameSuccessorOrbit z.1 ((U.successor^[n]) z).1 := by
    intro n z
    induction n generalizing z with
    | zero => exact T.sameSuccessorOrbit_refl z.1
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact T.sameSuccessorOrbit_trans (ih z)
          (hstep ((U.successor^[n]) z))
  rcases hxy with ⟨m, n, hmeet⟩
  have hmeetVal : ((U.successor^[m]) x).1 =
      ((U.successor^[n]) y).1 := by
    simpa only [U] using congrArg Subtype.val hmeet
  have hmiddle : T.SameSuccessorOrbit
      ((U.successor^[m]) x).1 ((U.successor^[n]) y).1 :=
    ⟨0, 0, by simpa only [Function.iterate_zero, id_eq] using hmeetVal⟩
  exact T.sameSuccessorOrbit_trans (hiterate m x) <|
    T.sameSuccessorOrbit_trans hmiddle
      (T.sameSuccessorOrbit_symm (hiterate n y))

/-- If an interior vertex is the first vertex after an original source,
then restricting away the two old endpoints does not change its component
relation with any other interior vertex. -/
theorem interior_sameSuccessorOrbit_iff_of_mem_source
    [Fintype Vertex]
    (source_not_target : ∀ z, P z → ¬ I z)
    (x y : T.Interior) (hx : T.InteriorSource x) :
    T.interior.SameSuccessorOrbit x y ↔
      T.SameSuccessorOrbit x.1 y.1 := by
  let U := T.interior
  constructor
  · exact T.sameSuccessorOrbit_val_of_interior x y
  · intro hxy
    let s := T.tau ⟨x.1, x.2.1⟩
    have hsSource : P s.1 := hx
    have hsNotTarget : ¬ I s.1 := source_not_target s.1 hsSource
    have hsSuccessor : T.successor s.1 = x.1 := by
      rw [show T.successor s.1 =
          (T.tau.symm ⟨s.1, hsNotTarget⟩).1 by
        simp [OpConjecture.BoundaryTranslationChains.Data.successor,
          hsNotTarget]]
      exact congrArg Subtype.val
        (T.tau.symm_apply_apply ⟨x.1, x.2.1⟩)
    have hsx : T.SameSuccessorOrbit s.1 x.1 := by
      exact ⟨1, 0, by simpa only [Function.iterate_one,
        Function.iterate_zero, id_eq] using hsSuccessor⟩
    have hsy := T.sameSuccessorOrbit_trans hsx hxy
    obtain ⟨r, hr⟩ :=
      T.exists_iterate_eq_of_mem_source_of_sameSuccessorOrbit
        hsSource hsy
    have hrPos : 0 < r := by
      by_contra hnot
      have hrZero : r = 0 := by omega
      apply y.2.1
      rw [← hr, hrZero]
      exact hsSource
    obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
    have hpath : (T.successor^[t]) x.1 = y.1 := by
      calc
        (T.successor^[t]) x.1 =
            (T.successor^[t]) (T.successor s.1) :=
          congrArg (T.successor^[t]) hsSuccessor.symm
        _ = (T.successor^[t + 1]) s.1 := by
          exact (Function.iterate_succ_apply T.successor t s.1).symm
        _ = y.1 := hr
    have havoid : ∀ i < t,
        ¬ I ((T.successor^[i + 1]) x.1) := by
      intro i hi htarget
      let d := t - (i + 1)
      have heqTarget : (T.successor^[t]) x.1 =
          (T.successor^[i + 1]) x.1 := by
        calc
        (T.successor^[t]) x.1 =
            (T.successor^[d + (i + 1)]) x.1 := by
          congr 1
          dsimp only [d]
          omega
        _ = (T.successor^[d])
            ((T.successor^[i + 1]) x.1) :=
          Function.iterate_add_apply T.successor d (i + 1) x.1
        _ = (T.successor^[i + 1]) x.1 :=
          T.iterate_eq_self_of_mem_target _ htarget d
      apply y.2.2
      rw [← hpath, heqTarget]
      exact htarget
    have hval := T.interior_iterate_successor_val x t havoid
    refine ⟨t, 0, ?_⟩
    apply Subtype.ext
    simpa only [Function.iterate_zero, id_eq, hval] using hpath

theorem not_twoSource_first {x : Vertex} (hx : ¬ T.TwoSource x) :
    ¬ P x := by
  intro hp
  exact hx (Or.inl hp)

theorem not_twoSource_second {x : Vertex} (hx : ¬ T.TwoSource x) :
    ¬ P (T.tau ⟨x, T.not_twoSource_first hx⟩).1 := by
  intro hp
  apply hx
  right
  intro hx'
  simpa only [Subsingleton.elim hx' (T.not_twoSource_first hx)] using hp

theorem not_twoSource_of
    {x : Vertex} (hx : ¬ P x)
    (hnext : ¬ P (T.tau ⟨x, hx⟩).1) :
    ¬ T.TwoSource x := by
  intro h
  rcases h with hp | hp
  · exact hx hp
  · exact hnext (hp hx)

theorem not_twoTarget_first {x : Vertex} (hx : ¬ T.TwoTarget x) :
    ¬ I x := by
  intro hi
  exact hx (Or.inl hi)

theorem not_twoTarget_second {x : Vertex} (hx : ¬ T.TwoTarget x) :
    ¬ I (T.tau.symm ⟨x, T.not_twoTarget_first hx⟩).1 := by
  intro hi
  apply hx
  right
  intro hx'
  simpa only [Subsingleton.elim hx' (T.not_twoTarget_first hx)] using hi

theorem not_twoTarget_of
    {x : Vertex} (hx : ¬ I x)
    (hprev : ¬ I (T.tau.symm ⟨x, hx⟩).1) :
    ¬ T.TwoTarget x := by
  intro h
  rcases h with hi | hi
  · exact hx hi
  · exact hprev (hi hx)

/-- Away from the last two interior layers, two interior successor steps
have the same underlying vertex as two original successor steps. -/
theorem interior_two_successor_val
    (x : T.Interior) (hx : ¬ T.interior.TwoTarget x) :
    (T.interior.successor (T.interior.successor x)).1 =
      T.successor (T.successor x.1) := by
  let U := T.interior
  have hx₀ : ¬ T.InteriorTarget x := U.not_twoTarget_first hx
  have hfirst := T.interior_successor_val x hx₀
  have hx₁raw := U.not_twoTarget_second hx
  have hx₁ : ¬ T.InteriorTarget (U.successor x) := by
    have hsuccessor : U.successor x =
        U.tau.symm ⟨x, hx₀⟩ := by
      simp [OpConjecture.BoundaryTranslationChains.Data.successor, hx₀]
    simpa only [hsuccessor] using hx₁raw
  calc
    (U.successor (U.successor x)).1 =
        T.successor (U.successor x).1 :=
      T.interior_successor_val (U.successor x) hx₁
    _ = T.successor (T.successor x.1) := by rw [hfirst]

/-- Apply the original partial translation twice.  Its source and target
boundaries are respectively the first and last two layers. -/
def twoStep :
    OpConjecture.BoundaryTranslationChains.Data Vertex
      T.TwoSource T.TwoTarget where
  tau :=
    { toFun := fun x ↦ by
        let hx₀ : ¬ P x.1 := T.not_twoSource_first x.2
        let y := T.tau ⟨x.1, hx₀⟩
        let hy₀ : ¬ P y.1 := T.not_twoSource_second x.2
        let z := T.tau ⟨y.1, hy₀⟩
        refine ⟨z.1, T.not_twoTarget_of z.2 ?_⟩
        have hback : T.tau.symm ⟨z.1, z.2⟩ = ⟨y.1, hy₀⟩ := by
          exact T.tau.symm_apply_apply ⟨y.1, hy₀⟩
        simpa only [hback] using y.2
      invFun := fun z ↦ by
        let hz₀ : ¬ I z.1 := T.not_twoTarget_first z.2
        let y := T.tau.symm ⟨z.1, hz₀⟩
        let hy₀ : ¬ I y.1 := T.not_twoTarget_second z.2
        let x := T.tau.symm ⟨y.1, hy₀⟩
        refine ⟨x.1, T.not_twoSource_of x.2 ?_⟩
        have hforward : T.tau ⟨x.1, x.2⟩ = ⟨y.1, hy₀⟩ := by
          exact T.tau.apply_symm_apply ⟨y.1, hy₀⟩
        simpa only [hforward] using y.2
      left_inv := by
        intro x
        apply Subtype.ext
        simp
      right_inv := by
        intro z
        apply Subtype.ext
        simp }

/-- Away from the last two layers, the successor for `twoStep` is the
square of the original successor. -/
theorem twoStep_successor_eq
    (x : Vertex) (hx : ¬ T.TwoTarget x) :
    T.twoStep.successor x = T.successor (T.successor x) := by
  classical
  have hx₀ := T.not_twoTarget_first hx
  have hx₁ := T.not_twoTarget_second hx
  simp [OpConjecture.BoundaryTranslationChains.Data.successor,
    twoStep, hx, hx₀, hx₁]

section Product

variable {Vertex₂ : Type v} {P₂ I₂ : Vertex₂ → Prop}
  (U : OpConjecture.BoundaryTranslationChains.Data Vertex₂ P₂ I₂)

/-- Product partial translation.  A pair is on a boundary when either of
its coordinates is on the corresponding boundary. -/
def prod :
    OpConjecture.BoundaryTranslationChains.Data (Vertex × Vertex₂)
      (fun p ↦ P p.1 ∨ P₂ p.2) (fun p ↦ I p.1 ∨ I₂ p.2) where
  tau :=
    { toFun := fun p ↦ by
        let x := T.tau ⟨p.1.1, fun hp ↦ p.2 (Or.inl hp)⟩
        let y := U.tau ⟨p.1.2, fun hp ↦ p.2 (Or.inr hp)⟩
        exact ⟨(x.1, y.1), by
          rintro (hx | hy)
          · exact x.2 hx
          · exact y.2 hy⟩
      invFun := fun p ↦ by
        let x := T.tau.symm ⟨p.1.1, fun hi ↦ p.2 (Or.inl hi)⟩
        let y := U.tau.symm ⟨p.1.2, fun hi ↦ p.2 (Or.inr hi)⟩
        exact ⟨(x.1, y.1), by
          rintro (hx | hy)
          · exact x.2 hx
          · exact y.2 hy⟩
      left_inv := by
        intro p
        apply Subtype.ext
        apply Prod.ext
        · exact congrArg Subtype.val
            (T.tau.symm_apply_apply
              ⟨p.1.1, fun hp ↦ p.2 (Or.inl hp)⟩)
        · exact congrArg Subtype.val
            (U.tau.symm_apply_apply
              ⟨p.1.2, fun hp ↦ p.2 (Or.inr hp)⟩)
      right_inv := by
        intro p
        apply Subtype.ext
        apply Prod.ext
        · exact congrArg Subtype.val
            (T.tau.apply_symm_apply
              ⟨p.1.1, fun hi ↦ p.2 (Or.inl hi)⟩)
        · exact congrArg Subtype.val
            (U.tau.apply_symm_apply
              ⟨p.1.2, fun hi ↦ p.2 (Or.inr hi)⟩) }

/-- Away from the product target boundary, successor acts coordinatewise. -/
theorem prod_successor_eq
    (p : Vertex × Vertex₂) (hp : ¬ (I p.1 ∨ I₂ p.2)) :
    (T.prod U).successor p = (T.successor p.1, U.successor p.2) := by
  classical
  have hx : ¬ I p.1 := fun hi ↦ hp (Or.inl hi)
  have hy : ¬ I₂ p.2 := fun hi ↦ hp (Or.inr hi)
  simp [OpConjecture.BoundaryTranslationChains.Data.successor,
    prod, hx, hy]

/-- The global simultaneous two-step translation on a pair of partial
translation components. -/
def twoStepProd := prod T.twoStep U.twoStep

/-- Away from the enlarged target boundary, the product successor is
literal simultaneous advancement by two original successor steps. -/
theorem twoStepProd_successor_eq
    (p : Vertex × Vertex₂)
    (hp : ¬ (T.TwoTarget p.1 ∨ U.TwoTarget p.2)) :
    (T.twoStepProd U).successor p =
      (T.successor (T.successor p.1),
        U.successor (U.successor p.2)) := by
  change (T.twoStep.prod U.twoStep).successor p = _
  rw [prod_successor_eq T.twoStep U.twoStep p hp]
  apply Prod.ext
  · exact T.twoStep_successor_eq p.1 (fun h ↦ hp (Or.inl h))
  · exact U.twoStep_successor_eq p.2 (fun h ↦ hp (Or.inr h))

/-- Before the first product target is reached, `n` product steps are
exactly `2 * n` original successor steps in each coordinate. -/
theorem twoStepProd_iterate_successor_eq
    [Fintype Vertex] [Fintype Vertex₂]
    (p : Vertex × Vertex₂)
    (hp : T.TwoSource p.1 ∨ U.TwoSource p.2)
    {n : ℕ}
    (hn : n ≤ (T.twoStepProd U).firstTargetIndex p hp) :
    ((T.twoStepProd U).successor^[n]) p =
      ((T.successor^[2 * n]) p.1,
        (U.successor^[2 * n]) p.2) := by
  let B := T.twoStepProd U
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      have hnlt : n < (T.twoStepProd U).firstTargetIndex p hp := by omega
      rw [T.twoStepProd_successor_eq U _
        ((T.twoStepProd U).not_mem_target_before_firstTargetIndex
          p hp hnlt)]
      rw [ih (by omega)]
      apply Prod.ext
      · change T.successor (T.successor ((T.successor^[2 * n]) p.1)) =
          (T.successor^[2 * (n + 1)]) p.1
        rw [show 2 * (n + 1) = 2 + 2 * n by omega,
          Function.iterate_add_apply]
        rfl
      · change U.successor (U.successor ((U.successor^[2 * n]) p.2)) =
          (U.successor^[2 * (n + 1)]) p.2
        rw [show 2 * (n + 1) = 2 + 2 * n by omega,
          Function.iterate_add_apply]
        rfl

/-- The endpoint of a simultaneous two-step product chain has the
elementwise orbit-coordinate formula used by the signed strip. -/
theorem twoStepProd_targetEndpoint_eq
    [Fintype Vertex] [Fintype Vertex₂]
    (p : Vertex × Vertex₂)
    (hp : T.TwoSource p.1 ∨ U.TwoSource p.2) :
    let n := (T.twoStepProd U).firstTargetIndex p hp
    (T.twoStepProd U).targetEndpoint p hp =
      ((T.successor^[2 * n]) p.1,
        (U.successor^[2 * n]) p.2) := by
  exact T.twoStepProd_iterate_successor_eq U p hp le_rfl

end Product

end OpConjecture.BoundaryTranslationChains.Data
