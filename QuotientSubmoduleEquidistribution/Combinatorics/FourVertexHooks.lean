import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Relation
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Hook overlap on a four-vertex rooted translation quiver

This file isolates the last paragraph of the manuscript's four-support
classification.  A hook is an oriented length-two path whose two targets
have unique predecessors and whose last vertex translates to the first.
On a rooted support with at most four vertices, two distinct hooks must
overlap consecutively, and three distinct hooks cannot occur.

The statement is purely finite and combinatorial.  No algebra presentation
or module classification enters.
-/

set_option autoImplicit false
noncomputable section

namespace QuotientSubmoduleEquidistribution.FourVertexHooks

universe u

/-- The finite translation-quiver data used by the hook-overlap argument. -/
structure Data (Vertex : Type u) where
  edge : Vertex → Vertex → Prop
  boundary : Set Vertex
  tau : Vertex → Option Vertex
  edge_irrefl : ∀ x, ¬ edge x x
  tau_injective : ∀ {x y a}, tau x = some a → tau y = some a → x = y
  rooted : ∀ x, ∃ p, p ∈ boundary ∧ Relation.ReflTransGen edge p x

namespace Data

variable {Vertex : Type u} (G : Data Vertex)

/-- An admissible hook `(a,u,b)` in the selected translation quiver. -/
@[ext]
structure Hook where
  a : Vertex
  u : Vertex
  b : Vertex
  edge_a_u : G.edge a u
  edge_u_b : G.edge u b
  u_not_boundary : u ∉ G.boundary
  b_not_boundary : b ∉ G.boundary
  predecessor_u : ∀ x, G.edge x u ↔ x = a
  predecessor_b : ∀ x, G.edge x b ↔ x = u
  tau_b : G.tau b = some a

namespace Hook

variable {G} (H : G.Hook)

theorem a_ne_u : H.a ≠ H.u := by
  intro h
  exact G.edge_irrefl H.u (h ▸ H.edge_a_u)

theorem u_ne_b : H.u ≠ H.b := by
  intro h
  exact G.edge_irrefl H.b (h ▸ H.edge_u_b)

/-- A hook is determined by its middle vertex. -/
theorem ext_u {H₁ H₂ : G.Hook} (h : H₁.u = H₂.u) : H₁ = H₂ := by
  have ha : H₁.a = H₂.a := by
    have hedge : G.edge H₁.a H₂.u := h ▸ H₁.edge_a_u
    exact (H₂.predecessor_u H₁.a).1 hedge
  have hb : H₁.b = H₂.b :=
    G.tau_injective H₁.tau_b (ha ▸ H₂.tau_b)
  ext <;> assumption

/-- A hook is also determined by its last vertex. -/
theorem ext_b {H₁ H₂ : G.Hook} (h : H₁.b = H₂.b) : H₁ = H₂ := by
  have hu : H₁.u = H₂.u := by
    have hedge : G.edge H₁.u H₂.b := h ▸ H₁.edge_u_b
    exact (H₂.predecessor_b H₁.u).1 hedge
  exact ext_u hu

end Hook

/-- The backwards endpoint of a predecessor-closed set remains in the set
along every directed path ending in the set. -/
theorem mem_of_reflTransGen_of_predecessorClosed
    {S : Set Vertex} {p x : Vertex}
    (hclosed : ∀ {y z}, G.edge y z → z ∈ S → y ∈ S)
    (hx : x ∈ S) (hpx : Relation.ReflTransGen G.edge p x) : p ∈ S := by
  induction hpx using Relation.ReflTransGen.head_induction_on with
  | refl => exact hx
  | @head y z hyz _ ih => exact hclosed hyz ih

/-- A rooted quiver has no nonempty predecessor-closed set disjoint from
the boundary. -/
theorem not_predecessorClosed_away_boundary
    {S : Set Vertex} {x : Vertex} (hx : x ∈ S)
    (hclosed : ∀ {y z}, G.edge y z → z ∈ S → y ∈ S)
    (haway : ∀ y, y ∈ S → y ∉ G.boundary) : False := by
  obtain ⟨p, hpBoundary, hpx⟩ := G.rooted x
  have hpS := G.mem_of_reflTransGen_of_predecessorClosed
    hclosed hx hpx
  exact haway p hpS hpBoundary

/-- The source and last vertex of a hook are distinct.  If they agreed,
the source and middle vertex would form a nonempty predecessor-closed set
disjoint from the boundary, contradicting rootedness. -/
theorem Hook.a_ne_b (H : G.Hook) : H.a ≠ H.b := by
  intro hab
  let S : Set Vertex := {H.a, H.u}
  have hclosed : ∀ {y z}, G.edge y z → z ∈ S → y ∈ S := by
    intro y z hyz hz
    rcases hz with (rfl | rfl)
    · have hy : y = H.u := by
        apply (H.predecessor_b y).1
        simpa [hab] using hyz
      rw [hy]
      simp [S]
    · have hy : y = H.a := (H.predecessor_u y).1 hyz
      rw [hy]
      simp [S]
  exact G.not_predecessorClosed_away_boundary
    (S := S) (x := H.a) (by simp [S]) hclosed (by
      intro y hy
      rcases hy with (rfl | rfl)
      · simpa [hab] using H.b_not_boundary
      · exact H.u_not_boundary)

/-- On a support of cardinality at most four, two distinct hooks must share
the last vertex of one with the middle vertex of the other. -/
theorem Hook.overlap_of_ne [Finite Vertex]
    (hcard : Nat.card Vertex ≤ 4)
    {H₁ H₂ : G.Hook} (hne : H₁ ≠ H₂) :
    H₁.b = H₂.u ∨ H₂.b = H₁.u := by
  classical
  by_contra hcross
  rw [not_or] at hcross
  have hu : H₁.u ≠ H₂.u := fun h ↦ hne (Hook.ext_u h)
  have hb : H₁.b ≠ H₂.b := fun h ↦ hne (Hook.ext_b h)
  obtain ⟨p, hpBoundary, _⟩ := G.rooted H₁.u
  have hpu₁ : p ≠ H₁.u := by
    intro h
    exact H₁.u_not_boundary (h ▸ hpBoundary)
  have hpb₁ : p ≠ H₁.b := by
    intro h
    exact H₁.b_not_boundary (h ▸ hpBoundary)
  have hpu₂ : p ≠ H₂.u := by
    intro h
    exact H₂.u_not_boundary (h ▸ hpBoundary)
  have hpb₂ : p ≠ H₂.b := by
    intro h
    exact H₂.b_not_boundary (h ▸ hpBoundary)
  have hu₁b₂ : H₁.u ≠ H₂.b := fun h ↦ hcross.2 h.symm
  letI : Fintype Vertex := Fintype.ofFinite Vertex
  let S : Finset Vertex := {p, H₁.u, H₁.b, H₂.u, H₂.b}
  have hnotp : p ∉ ({H₁.u, H₁.b, H₂.u, H₂.b} : Finset Vertex) := by
    simp [hpu₁, hpb₁, hpu₂, hpb₂]
  have hnotu₁ :
      H₁.u ∉ ({H₁.b, H₂.u, H₂.b} : Finset Vertex) := by
    simp [H₁.u_ne_b, hu, hu₁b₂]
  have hnotb₁ : H₁.b ∉ ({H₂.u, H₂.b} : Finset Vertex) := by
    simp [hcross.1, hb]
  have hnotu₂ : H₂.u ∉ ({H₂.b} : Finset Vertex) := by
    simp [H₂.u_ne_b]
  have hS : S.card = 5 := by
    dsimp only [S]
    rw [Finset.card_insert_of_notMem hnotp,
      Finset.card_insert_of_notMem hnotu₁,
      Finset.card_insert_of_notMem hnotb₁,
      Finset.card_insert_of_notMem hnotu₂]
    simp
  have hSle : S.card ≤ Fintype.card Vertex :=
    Finset.card_le_card (Finset.subset_univ S)
  have hfive : 5 ≤ Nat.card Vertex := by
    rw [hS] at hSle
    simpa only [Nat.card_eq_fintype_card] using hSle
  omega

/-- Two overlapping hooks have the source required by the consecutive
double-hook picture. -/
theorem Hook.source_eq_of_consecutive
    {H₁ H₂ : G.Hook} (h : H₁.b = H₂.u) :
    H₂.a = H₁.u := by
  have hedge : G.edge H₁.u H₂.u := h ▸ H₁.edge_u_b
  exact ((H₂.predecessor_u H₁.u).1 hedge).symm

/-- In a consecutive pair of hooks on at most four rooted vertices, the
first source is a boundary vertex.  Thus the abstract overlap is exactly
the manuscript's `P → u₁ → u₂ → u₃` double hook. -/
theorem Hook.first_mem_boundary_of_consecutive [Finite Vertex]
    (hcard : Nat.card Vertex ≤ 4)
    {H₁ H₂ : G.Hook} (h₁₂ : H₁.b = H₂.u) :
    H₁.a ∈ G.boundary := by
  classical
  by_contra haBoundary
  have hab : H₁.a ≠ H₁.b := by
    intro hab
    let S : Set Vertex := {H₁.a, H₁.u}
    have hclosed : ∀ {y z}, G.edge y z → z ∈ S → y ∈ S := by
      intro y z hyz hz
      rcases hz with (rfl | rfl)
      · have hy : y = H₁.u := by
          apply (H₁.predecessor_b y).1
          simpa [hab] using hyz
        rw [hy]
        simp [S]
      · have hy : y = H₁.a := (H₁.predecessor_u y).1 hyz
        rw [hy]
        simp [S]
    exact G.not_predecessorClosed_away_boundary
      (S := S) (x := H₁.a) (by simp [S]) hclosed (by
        intro y hy
        rcases hy with (rfl | rfl)
        · exact haBoundary
        · exact H₁.u_not_boundary)
  have hab₂ : H₁.a ≠ H₂.b := by
    intro hab₂
    let S : Set Vertex := {H₁.a, H₁.u, H₁.b}
    have hclosed : ∀ {y z}, G.edge y z → z ∈ S → y ∈ S := by
      intro y z hyz hz
      rcases hz with (rfl | rfl | rfl)
      · have hy : y = H₂.u := by
          apply (H₂.predecessor_b y).1
          simpa [hab₂] using hyz
        rw [hy, ← h₁₂]
        simp [S]
      · have hy : y = H₁.a := (H₁.predecessor_u y).1 hyz
        rw [hy]
        simp [S]
      · have hy : y = H₁.u := (H₁.predecessor_b y).1 hyz
        rw [hy]
        simp [S]
    exact G.not_predecessorClosed_away_boundary
      (S := S) (x := H₁.a) (by simp [S]) hclosed (by
        intro y hy
        rcases hy with (rfl | rfl | rfl)
        · exact haBoundary
        · exact H₁.u_not_boundary
        · exact H₁.b_not_boundary)
  have hu₁b₂ : H₁.u ≠ H₂.b := by
    intro hu₁b₂
    have hedge : G.edge H₁.a H₂.b := by
      simpa [hu₁b₂] using H₁.edge_a_u
    have haeq : H₁.a = H₂.u :=
      (H₂.predecessor_b H₁.a).1 hedge
    exact hab (haeq.trans h₁₂.symm)
  have hb₁b₂ : H₁.b ≠ H₂.b := by
    intro hb
    exact H₂.u_ne_b (h₁₂.symm.trans hb)
  obtain ⟨p, hpBoundary, _⟩ := G.rooted H₁.a
  have hpa : p ≠ H₁.a := by
    intro h
    exact haBoundary (h ▸ hpBoundary)
  have hpu : p ≠ H₁.u := by
    intro h
    exact H₁.u_not_boundary (h ▸ hpBoundary)
  have hpb : p ≠ H₁.b := by
    intro h
    exact H₁.b_not_boundary (h ▸ hpBoundary)
  have hpb₂ : p ≠ H₂.b := by
    intro h
    exact H₂.b_not_boundary (h ▸ hpBoundary)
  letI : Fintype Vertex := Fintype.ofFinite Vertex
  let S : Finset Vertex := {p, H₁.a, H₁.u, H₁.b, H₂.b}
  have hnotp :
      p ∉ ({H₁.a, H₁.u, H₁.b, H₂.b} : Finset Vertex) := by
    simp [hpa, hpu, hpb, hpb₂]
  have hnota :
      H₁.a ∉ ({H₁.u, H₁.b, H₂.b} : Finset Vertex) := by
    simp [H₁.a_ne_u, hab, hab₂]
  have hnotu : H₁.u ∉ ({H₁.b, H₂.b} : Finset Vertex) := by
    simp [H₁.u_ne_b, hu₁b₂]
  have hnotb : H₁.b ∉ ({H₂.b} : Finset Vertex) := by
    simp [hb₁b₂]
  have hS : S.card = 5 := by
    dsimp only [S]
    rw [Finset.card_insert_of_notMem hnotp,
      Finset.card_insert_of_notMem hnota,
      Finset.card_insert_of_notMem hnotu,
      Finset.card_insert_of_notMem hnotb]
    simp
  have hSle : S.card ≤ Fintype.card Vertex :=
    Finset.card_le_card (Finset.subset_univ S)
  have hfive : 5 ≤ Nat.card Vertex := by
    rw [hS] at hSle
    simpa only [Nat.card_eq_fintype_card] using hSle
  omega

/-- A directed three-cycle of consecutive hooks is incompatible with
rootedness: its middle vertices form a nonboundary predecessor-closed set. -/
theorem Hook.not_three_cycle
    {H₁ H₂ H₃ : G.Hook}
    (h₁₂ : H₁.b = H₂.u) (h₂₃ : H₂.b = H₃.u)
    (h₃₁ : H₃.b = H₁.u) : False := by
  have ha₁ : H₁.a = H₃.u :=
    Hook.source_eq_of_consecutive (G := G) h₃₁
  have ha₂ : H₂.a = H₁.u :=
    Hook.source_eq_of_consecutive (G := G) h₁₂
  have ha₃ : H₃.a = H₂.u :=
    Hook.source_eq_of_consecutive (G := G) h₂₃
  let S : Set Vertex := {H₁.u, H₂.u, H₃.u}
  have hclosed : ∀ {y z}, G.edge y z → z ∈ S → y ∈ S := by
    intro y z hyz hz
    rcases hz with (rfl | rfl | rfl)
    · have hy : y = H₁.a := (H₁.predecessor_u y).1 hyz
      rw [hy, ha₁]
      simp [S]
    · have hy : y = H₂.a := (H₂.predecessor_u y).1 hyz
      rw [hy, ha₂]
      simp [S]
    · have hy : y = H₃.a := (H₃.predecessor_u y).1 hyz
      rw [hy, ha₃]
      simp [S]
  obtain ⟨p, hpBoundary, hp⟩ := G.rooted H₁.u
  have hpS : p ∈ S :=
    G.mem_of_reflTransGen_of_predecessorClosed hclosed (by simp [S]) hp
  rcases hpS with (hp₁ | hp₂ | hp₃)
  · exact H₁.u_not_boundary (hp₁ ▸ hpBoundary)
  · exact H₂.u_not_boundary (hp₂ ▸ hpBoundary)
  · exact H₃.u_not_boundary (hp₃ ▸ hpBoundary)

/-- Three pairwise distinct hooks cannot occur on a rooted support of at
most four vertices. -/
theorem Hook.not_three_pairwise_ne [Finite Vertex]
    (hcard : Nat.card Vertex ≤ 4)
    (H₁ H₂ H₃ : G.Hook)
    (h₁₂ : H₁ ≠ H₂) (h₁₃ : H₁ ≠ H₃)
    (h₂₃ : H₂ ≠ H₃) : False := by
  rcases Hook.overlap_of_ne (G := G) hcard h₁₂ with h12 | h21
  · rcases Hook.overlap_of_ne (G := G) hcard h₁₃ with h13 | h31
    · apply h₂₃
      exact Hook.ext_u (h12.symm.trans h13)
    · rcases Hook.overlap_of_ne (G := G) hcard h₂₃ with h23 | h32
      · exact Hook.not_three_cycle (G := G) h12 h23 h31
      · apply h₁₂
        exact Hook.ext_u (h31.symm.trans h32)
  · rcases Hook.overlap_of_ne (G := G) hcard h₁₃ with h13 | h31
    · rcases Hook.overlap_of_ne (G := G) hcard h₂₃ with h23 | h32
      · apply h₁₃
        exact Hook.ext_u (h21.symm.trans h23)
      · exact Hook.not_three_cycle (G := G) h21 h13 h32
    · apply h₂₃
      exact Hook.ext_b (h21.trans h31.symm)

instance Hook.instFinite [Finite Vertex] : Finite G.Hook :=
  Finite.of_injective
    (fun H : G.Hook ↦ (H.a, H.u, H.b)) (by
      intro H₁ H₂ h
      exact Hook.ext_u (congrArg (fun q ↦ q.2.1) h))

/-- The manuscript bound `|H(D)| ≤ 2`. -/
theorem hook_card_le_two [Finite Vertex]
    (hcard : Nat.card Vertex ≤ 4) : Nat.card G.Hook ≤ 2 := by
  classical
  letI : Fintype G.Hook := Fintype.ofFinite G.Hook
  rw [Nat.card_eq_fintype_card]
  by_contra hle
  have hlt : 2 < Fintype.card G.Hook := by omega
  obtain ⟨H₁, H₂, H₃, h₁₂, h₁₃, h₂₃⟩ :=
    Fintype.two_lt_card_iff.mp hlt
  exact Hook.not_three_pairwise_ne (G := G) hcard H₁ H₂ H₃
    h₁₂ h₁₃ h₂₃

/-- An oriented pair of consecutive hooks, corresponding to the
double-hook packet in the manuscript. -/
structure DoubleHook where
  first : G.Hook
  second : G.Hook
  ne : first ≠ second
  consecutive : first.b = second.u

/-- Any two distinct hooks admit the unique possible consecutive
orientation. -/
theorem exists_doubleHook_of_ne [Finite Vertex]
    (hcard : Nat.card Vertex ≤ 4)
    {H₁ H₂ : G.Hook} (hne : H₁ ≠ H₂) :
    ∃ Q : G.DoubleHook,
      (Q.first = H₁ ∧ Q.second = H₂) ∨
        (Q.first = H₂ ∧ Q.second = H₁) := by
  rcases Hook.overlap_of_ne (G := G) hcard hne with h12 | h21
  · exact ⟨⟨H₁, H₂, hne, h12⟩, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨⟨H₂, H₁, hne.symm, h21⟩, Or.inr ⟨rfl, rfl⟩⟩

end Data

end QuotientSubmoduleEquidistribution.FourVertexHooks
