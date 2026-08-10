import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin

/-!
# Finite chains for a partial boundary translation

An equivalence from the complement of a source boundary to the complement
of a target boundary decomposes a finite set into boundary-to-boundary
chains and boundary-free cycles.  This file proves the endpoint-existence
fact needed for Auslander--Reiten translation chains without imposing a
global acyclicity hypothesis.
-/

set_option autoImplicit false
noncomputable section

namespace QuotientSubmoduleEquidistribution.BoundaryTranslationChains

universe u

/-- A partial translation which is bijective away from its two
boundaries. -/
structure Data (Vertex : Type u) (P I : Vertex → Prop) where
  tau : {x // ¬ P x} ≃ {x // ¬ I x}

namespace Data

variable {Vertex : Type u} {P I : Vertex → Prop}
  (T : Data Vertex P I)

/-- Reverse a partial translation, interchanging its source and target
boundaries. -/
def reverse : Data Vertex I P where
  tau := T.tau.symm

/-- Move one step from the source boundary toward the target boundary,
and stay fixed after the target boundary is reached. -/
def successor (x : Vertex) : Vertex := by
  classical
  by_cases hx : I x
  · exact x
  · exact (T.tau.symm ⟨x, hx⟩).1

theorem successor_eq_self_of_mem_target {x : Vertex} (hx : I x) :
    T.successor x = x := by
  simp [successor, hx]

theorem successor_not_mem_source_of_not_mem_target
    {x : Vertex} (hx : ¬ I x) :
    ¬ P (T.successor x) := by
  have h := (T.tau.symm ⟨x, hx⟩).2
  simpa [successor, hx] using h

theorem tau_successor_of_not_mem_target
    {x : Vertex} (hx : ¬ I x) :
    T.tau ⟨T.successor x,
      T.successor_not_mem_source_of_not_mem_target hx⟩ = ⟨x, hx⟩ := by
  simp [successor, hx]

/-- Away from the target boundary, one successor step can be cancelled. -/
theorem successor_left_injective
    {x y : Vertex} (hx : ¬ I x) (hy : ¬ I y)
    (h : T.successor x = T.successor y) : x = y := by
  have hs : T.tau.symm ⟨x, hx⟩ = T.tau.symm ⟨y, hy⟩ := by
    apply Subtype.ext
    simpa [successor, hx, hy] using h
  have hxy : (⟨x, hx⟩ : {q // ¬ I q}) = ⟨y, hy⟩ :=
    T.tau.symm.injective hs
  exact congrArg Subtype.val hxy

/-- Cancelling equal iterates before the target boundary produces a
positive return time to the initial vertex. -/
theorem exists_positive_return_of_iterate_eq
    (p : Vertex) {i j : ℕ} (hij : i < j)
    (heq : T.successor^[i] p = T.successor^[j] p)
    (havoid : ∀ n, n < j → ¬ I (T.successor^[n] p)) :
    ∃ k, 0 < k ∧ k ≤ j ∧ p = T.successor^[k] p := by
  induction i generalizing j with
  | zero =>
      exact ⟨j, Nat.zero_lt_of_lt hij, le_rfl, heq⟩
  | succ i ih =>
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
      have hij' : i < j := by omega
      have heq' : T.successor^[i] p = T.successor^[j] p := by
        apply T.successor_left_injective
          (havoid i (by omega)) (havoid j (by omega))
        simpa only [Function.iterate_succ_apply'] using heq
      obtain ⟨k, hkpos, hkle, hk⟩ := ih hij' heq'
        (fun n hn ↦ havoid n (by omega))
      exact ⟨k, hkpos, by omega, hk⟩

/-- Starting at the source boundary of a finite partial-translation
component, one reaches the target boundary within at most `card Vertex`
steps.  Boundary-free cycles may exist elsewhere. -/
theorem exists_iterate_mem_target [Fintype Vertex]
    (p : Vertex) (hp : P p) :
    ∃ n ≤ Fintype.card Vertex, I (T.successor^[n] p) := by
  classical
  by_contra hnone
  push Not at hnone
  let N := Fintype.card Vertex
  let f : Fin (N + 1) → Vertex := fun n ↦ T.successor^[n.1] p
  have hnotinj : ¬ Function.Injective f := by
    intro hinj
    have hcard := Fintype.card_le_of_injective f hinj
    have : N + 1 ≤ N := by simpa [N] using hcard
    omega
  obtain ⟨i, j, hijEq, hijNe⟩ := Function.not_injective_iff.mp hnotinj
  have hijVal : i.1 ≠ j.1 := by
    intro h
    exact hijNe (Fin.ext h)
  have impossible : ∀ {i j : Fin (N + 1)}, i.1 < j.1 →
      f i = f j → False := by
    intro i j hij hijEq
    have havoid : ∀ n, n < j.1 →
        ¬ I (T.successor^[n] p) := by
      intro n hn
      exact hnone n (by
        exact le_trans (Nat.le_of_lt hn) (Nat.le_of_lt_succ j.2))
    obtain ⟨k, hkpos, hkle, hk⟩ :=
      T.exists_positive_return_of_iterate_eq p hij hijEq havoid
    obtain ⟨m, hkm⟩ := Nat.exists_eq_add_of_le hkpos
    subst k
    have hmj : m < j.1 := by omega
    have hnotI : ¬ I (T.successor^[m] p) := havoid m hmj
    have hnotP : ¬ P (T.successor^[1 + m] p) := by
      rw [show 1 + m = m + 1 by omega, Function.iterate_succ_apply']
      exact T.successor_not_mem_source_of_not_mem_target hnotI
    have hp' : P (T.successor^[1 + m] p) := by
      rw [← hk]
      exact hp
    exact hnotP hp'
  rcases lt_or_gt_of_ne hijVal with hij | hji
  · exact impossible hij hijEq
  · exact impossible hji hijEq.symm

/-- Unbounded form of target-boundary existence. -/
theorem exists_iterate_mem_target_unbounded [Fintype Vertex]
    (p : Vertex) (hp : P p) :
    ∃ n, I (T.successor^[n] p) := by
  obtain ⟨n, _, hn⟩ := T.exists_iterate_mem_target p hp
  exact ⟨n, hn⟩

/-- The first index at which the successor chain from a source-boundary
vertex reaches the target boundary. -/
def firstTargetIndex [Fintype Vertex]
    (p : Vertex) (hp : P p) : ℕ := by
  classical
  exact Nat.find (exists_iterate_mem_target_unbounded T p hp)

/-- The terminal target-boundary vertex of the successor chain. -/
def targetEndpoint [Fintype Vertex]
    (p : Vertex) (hp : P p) : Vertex :=
  T.successor^[firstTargetIndex T p hp] p

theorem firstTargetIndex_spec [Fintype Vertex]
    (p : Vertex) (hp : P p) :
    I (T.successor^[firstTargetIndex T p hp] p) := by
  classical
  exact Nat.find_spec (exists_iterate_mem_target_unbounded T p hp)

/-- A source-boundary point already lying on the target boundary reaches
that boundary at index zero. -/
theorem firstTargetIndex_eq_zero_of_mem_target [Fintype Vertex]
    (p : Vertex) (hp : P p) (hi : I p) :
    firstTargetIndex T p hp = 0 := by
  classical
  rw [firstTargetIndex, Nat.find_eq_zero]
  simpa using hi

/-- The endpoint of a source-boundary point already on the target boundary
is the point itself. -/
theorem targetEndpoint_eq_self_of_mem_target [Fintype Vertex]
    (p : Vertex) (hp : P p) (hi : I p) :
    targetEndpoint T p hp = p := by
  rw [targetEndpoint, T.firstTargetIndex_eq_zero_of_mem_target p hp hi]
  rfl

theorem firstTargetIndex_le_card [Fintype Vertex]
    (p : Vertex) (hp : P p) :
    firstTargetIndex T p hp ≤ Fintype.card Vertex := by
  classical
  obtain ⟨n, hncard, hn⟩ := exists_iterate_mem_target T p hp
  exact le_trans
    (Nat.find_min' (exists_iterate_mem_target_unbounded T p hp) hn)
    hncard

theorem not_mem_target_before_firstTargetIndex [Fintype Vertex]
    (p : Vertex) (hp : P p) {n : ℕ}
    (hn : n < firstTargetIndex T p hp) :
    ¬ I (T.successor^[n] p) := by
  classical
  exact Nat.find_min (exists_iterate_mem_target_unbounded T p hp) hn

/-- Positions in a boundary-to-boundary successor chain do not repeat before
the first target endpoint. -/
theorem iterate_ne_of_lt_le_firstTargetIndex [Fintype Vertex]
    (p : Vertex) (hp : P p) {i j : ℕ}
    (hij : i < j) (hj : j ≤ firstTargetIndex T p hp) :
    T.successor^[i] p ≠ T.successor^[j] p := by
  intro heq
  have havoid : ∀ n, n < j → ¬ I (T.successor^[n] p) := by
    intro n hn
    apply not_mem_target_before_firstTargetIndex T p hp
    exact lt_of_lt_of_le hn hj
  obtain ⟨k, hkpos, hkle, hk⟩ :=
    T.exists_positive_return_of_iterate_eq p hij heq havoid
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkpos
  have hmj : m < j := by omega
  have hmfirst : m < firstTargetIndex T p hp :=
    lt_of_lt_of_le hmj hj
  have hmnotI : ¬ I (T.successor^[m] p) :=
    not_mem_target_before_firstTargetIndex T p hp hmfirst
  have hnextNotP : ¬ P (T.successor^[m + 1] p) := by
    rw [Function.iterate_succ_apply']
    exact T.successor_not_mem_source_of_not_mem_target hmnotI
  apply hnextNotP
  rw [show m + 1 = 1 + m by omega, ← hk]
  exact hp

theorem targetEndpoint_mem_target [Fintype Vertex]
    (p : Vertex) (hp : P p) :
    I (targetEndpoint T p hp) :=
  firstTargetIndex_spec T p hp

/-- One reversed successor cancels one forward successor before the target
boundary. -/
theorem reverse_successor_successor_of_not_mem_target
    {x : Vertex} (hx : ¬ I x) :
    T.reverse.successor (T.successor x) = x := by
  classical
  have hnotP : ¬ P (T.successor x) :=
    T.successor_not_mem_source_of_not_mem_target hx
  have htau := T.tau_successor_of_not_mem_target hx
  change (if hp : P (T.successor x) then T.successor x
    else (T.tau ⟨T.successor x, hp⟩).1) = x
  rw [dif_neg hnotP]
  exact congrArg Subtype.val htau

/-- If the first `n` points of a successor trajectory avoid the target
boundary, reversing its first `n` steps returns to the starting point. -/
theorem reverse_iterate_iterate_eq_of_not_mem_target_before
    (p : Vertex) (n : ℕ)
    (havoid : ∀ i < n, ¬ I ((T.successor^[i]) p)) :
    (T.reverse.successor^[n]) ((T.successor^[n]) p) = p := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply,
        Function.iterate_succ_apply']
      rw [T.reverse_successor_successor_of_not_mem_target
        (havoid n (by omega))]
      exact ih (fun i hi ↦ havoid i (by omega))

/-- Every strictly positive position up to the first target endpoint lies
outside the source boundary. -/
theorem iterate_not_mem_source_of_pos_le_firstTargetIndex [Fintype Vertex]
    (p : Vertex) (hp : P p) {n : ℕ}
    (hnpos : 0 < n) (hn : n ≤ firstTargetIndex T p hp) :
    ¬ P (T.successor^[n] p) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [Function.iterate_succ_apply']
  apply T.successor_not_mem_source_of_not_mem_target
  apply T.not_mem_target_before_firstTargetIndex p hp
  omega

/-- Reversing `n` steps from the `m`th forward position removes those
steps, as long as the forward path has not passed its first target. -/
theorem reverse_iterate_iterate_eq [Fintype Vertex]
    (p : Vertex) (hp : P p) {n m : ℕ}
    (hnm : n ≤ m) (hm : m ≤ firstTargetIndex T p hp) :
    (T.reverse.successor^[n]) (T.successor^[m] p) =
      T.successor^[m - n] p := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
      rw [Function.iterate_succ_apply,
        Function.iterate_succ_apply']
      have hnotI : ¬ I (T.successor^[m] p) := by
        apply T.not_mem_target_before_firstTargetIndex p hp
        omega
      rw [T.reverse_successor_successor_of_not_mem_target hnotI]
      have hcancel := ih (m := m) (by omega) (by omega)
      simpa only [Nat.succ_sub_succ_eq_sub] using hcancel

/-- Reversing from the terminal endpoint retraces the original chain at
complementary positions. -/
theorem reverse_iterate_targetEndpoint_eq [Fintype Vertex]
    (p : Vertex) (hp : P p) {n : ℕ}
    (hn : n ≤ T.firstTargetIndex p hp) :
    (T.reverse.successor^[n]) (T.targetEndpoint p hp) =
      T.successor^[T.firstTargetIndex p hp - n] p := by
  exact T.reverse_iterate_iterate_eq p hp hn le_rfl

/-- The reversed chain from a terminal endpoint has exactly the same
length as the original boundary-to-boundary chain. -/
theorem reverse_firstTargetIndex_targetEndpoint [Fintype Vertex]
    (p : Vertex) (hp : P p) :
    T.reverse.firstTargetIndex (T.targetEndpoint p hp)
        (T.targetEndpoint_mem_target p hp) =
      T.firstTargetIndex p hp := by
  classical
  let q := T.targetEndpoint p hp
  let hq : I q := T.targetEndpoint_mem_target p hp
  let L := T.firstTargetIndex p hp
  change T.reverse.firstTargetIndex q hq = L
  apply Nat.le_antisymm
  · have hreach : P (T.reverse.successor^[L] q) := by
      change P
        (T.reverse.successor^[L] (T.targetEndpoint p hp))
      rw [T.reverse_iterate_targetEndpoint_eq p hp (n := L) le_rfl]
      simpa [L] using hp
    exact Nat.find_min'
      (T.reverse.exists_iterate_mem_target_unbounded q hq) hreach
  · by_contra hnot
    have hrlt : T.reverse.firstTargetIndex q hq < L := by omega
    have hspec := T.reverse.firstTargetIndex_spec q hq
    have hback := T.reverse_iterate_targetEndpoint_eq p hp
      (n := T.reverse.firstTargetIndex q hq) (Nat.le_of_lt hrlt)
    have hpositive : 0 < L - T.reverse.firstTargetIndex q hq :=
      Nat.sub_pos_of_lt hrlt
    have hnotP : ¬ P
        (T.successor^[L - T.reverse.firstTargetIndex q hq] p) :=
      T.iterate_not_mem_source_of_pos_le_firstTargetIndex p hp
        hpositive (Nat.sub_le L _)
    exact hnotP (hback ▸ hspec)

/-- Distinct source-boundary vertices have distinct first target endpoints. -/
theorem targetEndpoint_injective [Fintype Vertex] :
    Function.Injective
      (fun p : {x // P x} ↦
        (⟨T.targetEndpoint p.1 p.2,
          T.targetEndpoint_mem_target p.1 p.2⟩ : {x // I x})) := by
  intro p q hpq
  apply Subtype.ext
  have compare_of_le : ∀ (a b : {x // P x}),
      T.successor^[T.firstTargetIndex a.1 a.2] a.1 =
          T.successor^[T.firstTargetIndex b.1 b.2] b.1 →
        T.firstTargetIndex a.1 a.2 ≤
          T.firstTargetIndex b.1 b.2 →
        a.1 = b.1 := by
    intro a b hend hle
    let la := T.firstTargetIndex a.1 a.2
    let lb := T.firstTargetIndex b.1 b.2
    have hback := congrArg (T.reverse.successor^[la]) hend
    have hpback :
        (T.reverse.successor^[la]) (T.successor^[la] a.1) = a.1 := by
      simpa [la] using T.reverse_iterate_iterate_eq a.1 a.2
        (n := la) (m := la) le_rfl le_rfl
    have hqback :
        (T.reverse.successor^[la]) (T.successor^[lb] b.1) =
          T.successor^[lb - la] b.1 := by
      exact T.reverse_iterate_iterate_eq b.1 b.2 hle le_rfl
    rw [hpback, hqback] at hback
    by_cases heq : la = lb
    · simpa [heq] using hback
    · have hpos : 0 < lb - la := Nat.sub_pos_of_lt (lt_of_le_of_ne hle heq)
      have hnotP : ¬ P (T.successor^[lb - la] b.1) :=
        T.iterate_not_mem_source_of_pos_le_firstTargetIndex b.1 b.2
          hpos (Nat.sub_le lb la)
      exact (hnotP (hback ▸ a.2)).elim
  have hend :
      T.successor^[T.firstTargetIndex p.1 p.2] p.1 =
        T.successor^[T.firstTargetIndex q.1 q.2] q.1 :=
    congrArg Subtype.val hpq
  rcases le_total (T.firstTargetIndex p.1 p.2)
      (T.firstTargetIndex q.1 q.2) with hle | hle
  · exact compare_of_le p q hend hle
  · exact (compare_of_le q p hend.symm hle).symm

/-- The partial translation canonically matches its source-boundary and
target-boundary vertices by following each finite chain to its first target
endpoint. -/
def boundaryEndpointEquiv [Fintype Vertex] :
    {x // P x} ≃ {x // I x} := by
  classical
  let f : {x // P x} → {x // I x} := fun p ↦
    ⟨T.targetEndpoint p.1 p.2,
      T.targetEndpoint_mem_target p.1 p.2⟩
  have hcompl : Fintype.card {x // ¬ P x} =
      Fintype.card {x // ¬ I x} := Fintype.card_congr T.tau
  have hPcompl := Fintype.card_subtype_compl P
  have hIcompl := Fintype.card_subtype_compl I
  have hPle := Fintype.card_subtype_le P
  have hIle := Fintype.card_subtype_le I
  have hcard : Fintype.card {x // P x} = Fintype.card {x // I x} := by
    omega
  exact Equiv.ofBijective f
    ((Fintype.bijective_iff_injective_and_card f).2
      ⟨T.targetEndpoint_injective, hcard⟩)

@[simp]
theorem boundaryEndpointEquiv_apply [Fintype Vertex]
    (p : {x // P x}) :
    (T.boundaryEndpointEquiv p).1 = T.targetEndpoint p.1 p.2 := by
  classical
  rfl

/-- The boundary endpoint equivalence fixes every point in the intersection
of the source and target boundaries. -/
theorem boundaryEndpointEquiv_apply_of_mem_target [Fintype Vertex]
    (p : {x // P x}) (hi : I p.1) :
    T.boundaryEndpointEquiv p = ⟨p.1, hi⟩ := by
  apply Subtype.ext
  rw [T.boundaryEndpointEquiv_apply]
  exact T.targetEndpoint_eq_self_of_mem_target p.1 p.2 hi

/-- A vertex remains fixed under every successor iterate after it reaches
the target boundary. -/
theorem iterate_eq_self_of_mem_target
    (x : Vertex) (hx : I x) (n : ℕ) :
    T.successor^[n] x = x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      exact T.successor_eq_self_of_mem_target hx

/-- The boundary-free periodic part of a finite partial translation. -/
def PeriodicInterior [Fintype Vertex] :=
  {x : Vertex //
    ¬ P x ∧ ¬ I x ∧ ∃ n, 0 < n ∧ T.successor^[n] x = x}

noncomputable instance periodicInteriorFintype [Fintype Vertex] :
    Fintype T.PeriodicInterior := by
  letI : Finite T.PeriodicInterior :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

/-- Successor preserves the boundary-free periodic part. -/
def periodicInteriorSuccessor [Fintype Vertex]
    (x : T.PeriodicInterior) : T.PeriodicInterior := by
  classical
  refine ⟨T.successor x.1,
    T.successor_not_mem_source_of_not_mem_target x.2.2.1, ?_, ?_⟩
  · intro htarget
    obtain ⟨n, hnpos, hnreturn⟩ := x.2.2.2
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    have hfixed := T.iterate_eq_self_of_mem_target
      (T.successor x.1) htarget m
    have hreturn' : T.successor^[m] (T.successor x.1) = x.1 := by
      simpa only [Function.iterate_succ_apply] using hnreturn
    have hsx : T.successor x.1 = x.1 := hfixed.symm.trans hreturn'
    apply x.2.2.1
    simpa only [hsx] using htarget
  · obtain ⟨n, hnpos, hnreturn⟩ := x.2.2.2
    refine ⟨n, hnpos, ?_⟩
    calc
      T.successor^[n] (T.successor x.1) =
          T.successor (T.successor^[n] x.1) :=
        (Function.iterate_succ_apply T.successor n x.1).symm.trans
          (Function.iterate_succ_apply' T.successor n x.1)
      _ = T.successor x.1 := congrArg T.successor hnreturn

/-- Successor is a permutation of the boundary-free periodic part. -/
def periodicInteriorSuccessorEquiv [Fintype Vertex] :
    T.PeriodicInterior ≃ T.PeriodicInterior := by
  classical
  let f : T.PeriodicInterior → T.PeriodicInterior :=
    T.periodicInteriorSuccessor
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply T.successor_left_injective x.2.2.1 y.2.2.1
    exact congrArg Subtype.val hxy
  exact Equiv.ofBijective f
    ((Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, rfl⟩)

@[simp]
theorem periodicInteriorSuccessorEquiv_apply [Fintype Vertex]
    (x : T.PeriodicInterior) :
    (T.periodicInteriorSuccessorEquiv x).1 = T.successor x.1 := by
  classical
  rfl

end Data

end QuotientSubmoduleEquidistribution.BoundaryTranslationChains
