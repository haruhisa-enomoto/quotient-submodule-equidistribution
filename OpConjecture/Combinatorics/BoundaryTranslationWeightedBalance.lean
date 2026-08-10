import OpConjecture.Combinatorics.BoundaryTranslationChains
import Mathlib.Data.Fintype.BigOperators

/-!
# Weighted conservation on finite partial-translation chains

A finite partial translation decomposes into chains from its source boundary
to its target boundary and boundary-free cycles.  Any weight which is
preserved by successor therefore has the same total on the two boundaries.
This is the abstract finite-diagonal conservation principle used by the
four-vertex strip argument.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace OpConjecture.BoundaryTranslationChains.Data

universe u v

variable {Vertex : Type u} {P I : Vertex → Prop}
  (T : OpConjecture.BoundaryTranslationChains.Data Vertex P I)

/-- Two vertices lie in the same successor component when some forward
iterate of each is the same.  On a partial-translation chain this is the
intrinsic, representative-free version of belonging to the same labelled
orbit; it also works on periodic components. -/
def SameSuccessorOrbit (x y : Vertex) : Prop :=
  ∃ m n : ℕ, (T.successor^[m]) x = (T.successor^[n]) y

/-- Advancing both entries once preserves and reflects membership in the
same successor component. -/
theorem sameSuccessorOrbit_successor_iff (x y : Vertex) :
    T.SameSuccessorOrbit (T.successor x) (T.successor y) ↔
      T.SameSuccessorOrbit x y := by
  constructor
  · rintro ⟨m, n, h⟩
    refine ⟨m + 1, n + 1, ?_⟩
    simpa only [Function.iterate_succ_apply] using h
  · rintro ⟨m, n, h⟩
    refine ⟨m, n, ?_⟩
    have h' := congrArg T.successor h
    calc
      (T.successor^[m]) (T.successor x) =
          T.successor ((T.successor^[m]) x) :=
        (Function.Commute.iterate_self T.successor m) x
      _ = T.successor ((T.successor^[n]) y) := h'
      _ = (T.successor^[n]) (T.successor y) :=
        ((Function.Commute.iterate_self T.successor n) y).symm

/-- Simultaneously advancing both entries by any number of steps preserves
and reflects their successor component. -/
theorem sameSuccessorOrbit_iterate_iff
    (x y : Vertex) (r : ℕ) :
    T.SameSuccessorOrbit ((T.successor^[r]) x) ((T.successor^[r]) y) ↔
      T.SameSuccessorOrbit x y := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        T.sameSuccessorOrbit_successor_iff, ih]

/-- The future-meeting relation is reflexive. -/
theorem sameSuccessorOrbit_refl (x : Vertex) :
    T.SameSuccessorOrbit x x :=
  ⟨0, 0, rfl⟩

/-- The future-meeting relation is symmetric. -/
theorem sameSuccessorOrbit_symm {x y : Vertex}
    (h : T.SameSuccessorOrbit x y) :
    T.SameSuccessorOrbit y x := by
  rcases h with ⟨m, n, h⟩
  exact ⟨n, m, h.symm⟩

/-- The future-meeting relation is transitive. -/
theorem sameSuccessorOrbit_trans {x y z : Vertex}
    (hxy : T.SameSuccessorOrbit x y)
    (hyz : T.SameSuccessorOrbit y z) :
    T.SameSuccessorOrbit x z := by
  rcases hxy with ⟨m, n, hxy⟩
  rcases hyz with ⟨r, s, hyz⟩
  rcases le_total n r with hnr | hrn
  · let d := r - n
    refine ⟨d + m, s, ?_⟩
    calc
      (T.successor^[d + m]) x =
          (T.successor^[d]) ((T.successor^[m]) x) :=
        Function.iterate_add_apply T.successor d m x
      _ = (T.successor^[d]) ((T.successor^[n]) y) :=
        congrArg (T.successor^[d]) hxy
      _ = (T.successor^[d + n]) y :=
        (Function.iterate_add_apply T.successor d n y).symm
      _ = (T.successor^[r]) y := by
        congr 1
        dsimp only [d]
        omega
      _ = (T.successor^[s]) z := hyz
  · let d := n - r
    refine ⟨m, d + s, ?_⟩
    calc
      (T.successor^[m]) x = (T.successor^[n]) y := hxy
      _ = (T.successor^[d + r]) y := by
        congr 1
        dsimp only [d]
        omega
      _ = (T.successor^[d]) ((T.successor^[r]) y) :=
        Function.iterate_add_apply T.successor d r y
      _ = (T.successor^[d]) ((T.successor^[s]) z) :=
        congrArg (T.successor^[d]) hyz
      _ = (T.successor^[d + s]) z :=
        (Function.iterate_add_apply T.successor d s z).symm

/-- In a finite chain component, the source-boundary point is the canonical
first representative: every point in its successor component is one of its
forward iterates.  Boundary-free periodic components are excluded by the
source hypothesis. -/
theorem exists_iterate_eq_of_mem_source_of_sameSuccessorOrbit
    [Fintype Vertex] {x y : Vertex} (hx : P x)
    (hxy : T.SameSuccessorOrbit x y) :
    ∃ r : ℕ, (T.successor^[r]) x = y := by
  classical
  obtain ⟨m, n, hmeet⟩ := hxy
  let L := T.firstTargetIndex x hx
  let z := T.targetEndpoint x hx
  have hzTarget : I z := T.targetEndpoint_mem_target x hx
  have hyEndpoint : (T.successor^[L + n]) y = z := by
    calc
      (T.successor^[L + n]) y =
          (T.successor^[L]) ((T.successor^[n]) y) :=
        Function.iterate_add_apply T.successor L n y
      _ = (T.successor^[L]) ((T.successor^[m]) x) :=
        congrArg (T.successor^[L]) hmeet.symm
      _ = (T.successor^[m]) ((T.successor^[L]) x) :=
        by
          rw [← Function.iterate_add_apply,
            ← Function.iterate_add_apply]
          congr 1
          omega
      _ = (T.successor^[m]) z := rfl
      _ = z := T.iterate_eq_self_of_mem_target z hzTarget m
  have hyReaches : ∃ r : ℕ, I ((T.successor^[r]) y) :=
    ⟨L + n, hyEndpoint ▸ hzTarget⟩
  let s := Nat.find hyReaches
  have hsTarget : I ((T.successor^[s]) y) := Nat.find_spec hyReaches
  have hsLe : s ≤ L + n :=
    Nat.find_min' hyReaches (hyEndpoint ▸ hzTarget)
  have hsEndpoint : (T.successor^[s]) y = z := by
    have hlate : (T.successor^[L + n]) y =
        (T.successor^[L + n - s]) ((T.successor^[s]) y) := by
      calc
        (T.successor^[L + n]) y =
            (T.successor^[(L + n - s) + s]) y := by
          rw [Nat.sub_add_cancel hsLe]
        _ = (T.successor^[L + n - s]) ((T.successor^[s]) y) :=
          Function.iterate_add_apply T.successor (L + n - s) s y
    calc
      (T.successor^[s]) y =
          (T.successor^[L + n - s]) ((T.successor^[s]) y) :=
        (T.iterate_eq_self_of_mem_target
          ((T.successor^[s]) y) hsTarget (L + n - s)).symm
      _ = (T.successor^[L + n]) y := hlate.symm
      _ = z := hyEndpoint
  have havoidY : ∀ i < s, ¬ I ((T.successor^[i]) y) := by
    intro i hi
    exact Nat.find_min hyReaches hi
  have hyReverse : (T.reverse.successor^[s]) z = y := by
    rw [← hsEndpoint]
    exact T.reverse_iterate_iterate_eq_of_not_mem_target_before y s havoidY
  have hsL : s ≤ L := by
    by_contra hnot
    have hLs : L < s := by omega
    have hxReverse : (T.reverse.successor^[L]) z = x := by
      simpa [z, L] using
        T.reverse_iterate_targetEndpoint_eq x hx (n := L) le_rfl
    have hyx : y = x := by
      calc
        y = (T.reverse.successor^[s]) z := hyReverse.symm
        _ = (T.reverse.successor^[s - L])
              ((T.reverse.successor^[L]) z) := by
          rw [← Function.iterate_add_apply]
          congr 2
          omega
        _ = (T.reverse.successor^[s - L]) x :=
          congrArg (T.reverse.successor^[s - L]) hxReverse
        _ = x := T.reverse.iterate_eq_self_of_mem_target x hx (s - L)
    have hbefore : ¬ I ((T.successor^[L]) y) :=
      Nat.find_min hyReaches hLs
    apply hbefore
    rw [hyx]
    exact T.firstTargetIndex_spec x hx
  refine ⟨L - s, ?_⟩
  have hback := T.reverse_iterate_targetEndpoint_eq x hx hsL
  exact hback.symm.trans hyReverse

/-- A component whose source representative is already on the target
boundary is a singleton. -/
theorem eq_of_mem_source_of_mem_target_of_sameSuccessorOrbit
    [Fintype Vertex] {x y : Vertex} (hxSource : P x) (hxTarget : I x)
    (hxy : T.SameSuccessorOrbit x y) :
    y = x := by
  obtain ⟨r, hr⟩ :=
    T.exists_iterate_eq_of_mem_source_of_sameSuccessorOrbit hxSource hxy
  rw [T.iterate_eq_self_of_mem_target x hxTarget r] at hr
  exact hr.symm

/-- Replacing either endpoint by another occurrence in the same component
does not change the component-comparison predicate. -/
theorem sameSuccessorOrbit_congr_of_related
    {x x' y y' : Vertex}
    (hx : T.SameSuccessorOrbit x x')
    (hy : T.SameSuccessorOrbit y y') :
    T.SameSuccessorOrbit x y ↔ T.SameSuccessorOrbit x' y' := by
  constructor
  · intro h
    exact T.sameSuccessorOrbit_trans (T.sameSuccessorOrbit_symm hx) <|
      T.sameSuccessorOrbit_trans h hy
  · intro h
    exact T.sameSuccessorOrbit_trans hx <|
      T.sameSuccessorOrbit_trans h (T.sameSuccessorOrbit_symm hy)

/-- Advancing only the first occurrence preserves and reflects whether two
occurrences lie in the same component. -/
theorem sameSuccessorOrbit_successor_left_iff (x y : Vertex) :
    T.SameSuccessorOrbit (T.successor x) y ↔
      T.SameSuccessorOrbit x y := by
  exact (T.sameSuccessorOrbit_congr_of_related
    (show T.SameSuccessorOrbit x (T.successor x) from ⟨1, 0, rfl⟩)
    (T.sameSuccessorOrbit_refl y)).symm

/-- Advancing only the second occurrence likewise preserves and reflects
the component predicate. -/
theorem sameSuccessorOrbit_successor_right_iff (x y : Vertex) :
    T.SameSuccessorOrbit x (T.successor y) ↔
      T.SameSuccessorOrbit x y := by
  exact (T.sameSuccessorOrbit_congr_of_related
    (T.sameSuccessorOrbit_refl x)
    (show T.SameSuccessorOrbit y (T.successor y) from ⟨1, 0, rfl⟩)).symm

/-- Future meeting is exactly undirected connectedness generated by one
successor step.  This formulation is useful when the orientation of a
partial translation is reversed. -/
theorem sameSuccessorOrbit_iff_eqvGen_successor (x y : Vertex) :
    T.SameSuccessorOrbit x y ↔
      Relation.EqvGen (fun a b ↦ T.successor a = b) x y := by
  let R : Vertex → Vertex → Prop := fun a b ↦ T.successor a = b
  have hpath : ∀ (a : Vertex) (n : ℕ),
      Relation.EqvGen R a ((T.successor^[n]) a) := by
    intro a n
    induction n with
    | zero => exact Relation.EqvGen.refl a
    | succ n ih =>
        apply Relation.EqvGen.trans a ((T.successor^[n]) a)
          ((T.successor^[n + 1]) a) ih
        apply Relation.EqvGen.rel
        simp [R, Function.iterate_succ_apply']
  constructor
  · rintro ⟨m, n, h⟩
    apply Relation.EqvGen.trans x ((T.successor^[m]) x) y
      (hpath x m)
    rw [h]
    exact Relation.EqvGen.symm y ((T.successor^[n]) y) (hpath y n)
  · intro h
    induction h with
    | rel a b hab =>
        refine ⟨1, 0, ?_⟩
        simpa only [Function.iterate_one, Function.iterate_zero,
          id_eq] using hab
    | refl a => exact T.sameSuccessorOrbit_refl a
    | symm a b _ ih => exact T.sameSuccessorOrbit_symm ih
    | trans a b c _ _ hab hbc =>
        exact T.sameSuccessorOrbit_trans hab hbc

/-- Reversing a partial translation does not change its undirected
successor components. -/
theorem reverse_sameSuccessorOrbit_iff (x y : Vertex) :
    T.reverse.SameSuccessorOrbit x y ↔ T.SameSuccessorOrbit x y := by
  let R : Vertex → Vertex → Prop := fun a b ↦ T.successor a = b
  let S : Vertex → Vertex → Prop :=
    fun a b ↦ T.reverse.successor a = b
  have hRS : ∀ {a b : Vertex}, R a b → Relation.EqvGen S a b := by
    intro a b hab
    by_cases ha : I a
    · have hab' : a = b := by
        exact (T.successor_eq_self_of_mem_target ha).symm.trans hab
      simpa only [hab'] using (Relation.EqvGen.refl a :
        Relation.EqvGen S a a)
    · have hback : T.reverse.successor b = a := by
        rw [← hab]
        exact T.reverse_successor_successor_of_not_mem_target ha
      exact Relation.EqvGen.symm b a (Relation.EqvGen.rel b a hback)
  have hSR : ∀ {a b : Vertex}, S a b → Relation.EqvGen R a b := by
    intro a b hab
    by_cases ha : P a
    · have hab' : a = b := by
        exact (T.reverse.successor_eq_self_of_mem_target ha).symm.trans hab
      simpa only [hab'] using (Relation.EqvGen.refl a :
        Relation.EqvGen R a a)
    · have hback : T.successor b = a := by
        rw [← hab]
        exact T.reverse.reverse_successor_successor_of_not_mem_target ha
      exact Relation.EqvGen.symm b a (Relation.EqvGen.rel b a hback)
  rw [T.reverse.sameSuccessorOrbit_iff_eqvGen_successor,
    T.sameSuccessorOrbit_iff_eqvGen_successor]
  constructor
  · exact Relation.EqvGen.eqvGen_le hSR
  · exact Relation.EqvGen.eqvGen_le hRS

section Conjugacy

variable {Vertex₂ : Type v} {P₂ I₂ : Vertex₂ → Prop}
  (U : OpConjecture.BoundaryTranslationChains.Data Vertex₂ P₂ I₂)

/-- An equivalence conjugating successor maps preserves and reflects the
intrinsic successor-component relation. -/
theorem sameSuccessorOrbit_congr
    (E : Vertex ≃ Vertex₂)
    (hsuccessor : ∀ x, E (T.successor x) = U.successor (E x))
    (x y : Vertex) :
    T.SameSuccessorOrbit x y ↔
      U.SameSuccessorOrbit (E x) (E y) := by
  have hiterate : ∀ (n : ℕ) (x : Vertex),
      E ((T.successor^[n]) x) = (U.successor^[n]) (E x) := by
    intro n x
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
          hsuccessor, ih]
  constructor
  · rintro ⟨m, n, h⟩
    refine ⟨m, n, ?_⟩
    rw [← hiterate m x, ← hiterate n y, h]
  · rintro ⟨m, n, h⟩
    refine ⟨m, n, ?_⟩
    apply E.injective
    rw [hiterate m x, hiterate n y]
    exact h

end Conjugacy

/-- A successor-invariant weight is constant up to every position of a
source-to-target chain. -/
theorem weight_iterate_eq_of_le_firstTargetIndex
    [Fintype Vertex]
    {A : Type v} [AddCommMonoid A]
    (weight : Vertex → A)
    (hsuccessor : ∀ x, ¬ I x → weight (T.successor x) = weight x)
    (p : Vertex) (hp : P p) {n : ℕ}
    (hn : n ≤ T.firstTargetIndex p hp) :
    weight (T.successor^[n] p) = weight p := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      have hnlt : n < T.firstTargetIndex p hp := by omega
      rw [hsuccessor _
        (T.not_mem_target_before_firstTargetIndex p hp hnlt)]
      exact ih (by omega)

/-- A successor-invariant weight has equal values at the two endpoints of
every source-to-target chain. -/
theorem weight_targetEndpoint_eq
    [Fintype Vertex]
    {A : Type v} [AddCommMonoid A]
    (weight : Vertex → A)
    (hsuccessor : ∀ x, ¬ I x → weight (T.successor x) = weight x)
    (p : Vertex) (hp : P p) :
    weight (T.targetEndpoint p hp) = weight p := by
  exact T.weight_iterate_eq_of_le_firstTargetIndex
    weight hsuccessor p hp le_rfl

/-- A successor-invariant predicate has the same truth value at both
endpoints of every source-to-target chain. -/
theorem predicate_targetEndpoint_iff
    [Fintype Vertex]
    (Q : Vertex → Prop)
    (hsuccessor : ∀ x, ¬ I x → (Q (T.successor x) ↔ Q x))
    (p : Vertex) (hp : P p) :
    Q (T.targetEndpoint p hp) ↔ Q p := by
  classical
  let weight : Vertex → ℕ := fun x ↦ if Q x then 1 else 0
  have hweight : ∀ x, ¬ I x →
      weight (T.successor x) = weight x := by
    intro x hx
    apply if_congr
    · exact hsuccessor x hx
    · rfl
    · rfl
  have h := T.weight_targetEndpoint_eq weight hweight p hp
  change (if Q (T.targetEndpoint p hp) then 1 else 0) =
      (if Q p then 1 else 0) at h
  constructor
  · intro hQ
    by_contra hnQ
    simp [hQ, hnQ] at h
  · intro hQ
    by_contra hnQ
    simp [hQ, hnQ] at h

/-- The boundary endpoint equivalence restricts to any
successor-invariant predicate. -/
def boundaryPredicateEquiv
    [Fintype Vertex]
    (Q : Vertex → Prop)
    (hsuccessor : ∀ x, ¬ I x → (Q (T.successor x) ↔ Q x)) :
    {p : {x // P x} // Q p.1} ≃
      {i : {x // I x} // Q i.1} := by
  apply T.boundaryEndpointEquiv.subtypeEquiv
  intro p
  simpa only [T.boundaryEndpointEquiv_apply] using
    (T.predicate_targetEndpoint_iff Q hsuccessor p.1 p.2).symm

/-- Weighted boundary conservation: the sum over the source boundary equals
the sum over the target boundary. -/
theorem sum_source_eq_sum_target_of_successor_invariant
    [Fintype Vertex]
    [Fintype {x // P x}] [Fintype {x // I x}]
    {A : Type v} [AddCommMonoid A]
    (weight : Vertex → A)
    (hsuccessor : ∀ x, ¬ I x → weight (T.successor x) = weight x) :
    (∑ p : {x // P x}, weight p.1) =
      ∑ i : {x // I x}, weight i.1 := by
  classical
  apply Fintype.sum_equiv T.boundaryEndpointEquiv
  intro p
  symm
  simpa only [T.boundaryEndpointEquiv_apply] using
    T.weight_targetEndpoint_eq weight hsuccessor p.1 p.2

end OpConjecture.BoundaryTranslationChains.Data
