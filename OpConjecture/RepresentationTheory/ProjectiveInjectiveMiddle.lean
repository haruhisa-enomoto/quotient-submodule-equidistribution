import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Logic.Equiv.Fintype
import OpConjecture.ConvexGeometry.LevelPolynomial

/-!
# Projective-injective mesh middles

The pure finite translation-system core of the projective-injective-middle
corollary.  When every genuine mesh middle is supported on both boundary
walls, quotient and reverse-subobject hitting conditions are related by a
cardinality-preserving permutation of the vertices.
-/

set_option autoImplicit false
noncomputable section

open Polynomial Set

namespace OpConjecture.ProjectiveInjectiveMiddle

universe u

/-- A finite partial translation together with the support of each genuine
mesh middle.  The two boundary sets are the complements of the domain and
image of `tau`. -/
structure Data (V : Type u) where
  projective : Set V
  injective : Set V
  tau : {x : V // x ∉ projective} ≃ {z : V // z ∉ injective}
  middle : {x : V // x ∉ projective} → Set V
  middle_subset_projective_injective :
    ∀ x, middle x ⊆ projective ∩ injective

namespace Data

variable {V : Type u} [Fintype V] (A : Data V)

/-- Deleted sets satisfying every forward first-mesh hitting clause. -/
def QGood (D : Set V) : Prop :=
  ∀ x : {x : V // x ∉ A.projective},
    x.1 ∈ D → (D ∩ A.middle x).Nonempty

/-- Deleted sets satisfying every reverse first-mesh hitting clause. -/
def SGood (D : Set V) : Prop :=
  ∀ x : {x : V // x ∉ A.projective},
    (A.tau x).1 ∈ D → (D ∩ A.middle x).Nonempty

/-- The partial source on which the desired permutation is already fixed:
nonprojective vertices together with projective-injective vertices. -/
abbrev PermutationSource :=
  {x : V // x ∉ A.projective} ⊕
    {c : V // c ∈ A.projective ∩ A.injective}

/-- Inclusion of the prescribed source pieces into the vertex set. -/
def sourcePoint : A.PermutationSource → V
  | Sum.inl x => x.1
  | Sum.inr c => c.1

/-- The desired image: translate the nonprojectives and fix the common
boundary. -/
def targetPoint : A.PermutationSource → V
  | Sum.inl x => (A.tau x).1
  | Sum.inr c => c.1

noncomputable instance permutationSourceFinite :
    Finite A.PermutationSource := by
  classical
  letI : Finite {x : V // x ∉ A.projective} :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Finite {c : V // c ∈ A.projective ∩ A.injective} :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype {x : V // x ∉ A.projective} := Fintype.ofFinite _
  letI : Fintype {c : V // c ∈ A.projective ∩ A.injective} :=
    Fintype.ofFinite _
  exact Fintype.finite (inferInstance : Fintype A.PermutationSource)

omit [Fintype V] in
theorem sourcePoint_injective : Function.Injective A.sourcePoint := by
  intro a b hab
  cases a with
  | inl x =>
      cases b with
      | inl y =>
          apply congrArg Sum.inl
          apply Subtype.ext
          exact hab
      | inr c =>
          exfalso
          change x.1 = c.1 at hab
          apply x.2
          rw [hab]
          exact c.2.1
  | inr c =>
      cases b with
      | inl x =>
          exfalso
          change c.1 = x.1 at hab
          apply x.2
          rw [← hab]
          exact c.2.1
      | inr d =>
          apply congrArg Sum.inr
          apply Subtype.ext
          exact hab

omit [Fintype V] in
theorem targetPoint_injective : Function.Injective A.targetPoint := by
  intro a b hab
  cases a with
  | inl x =>
      cases b with
      | inl y =>
          apply congrArg Sum.inl
          apply A.tau.injective
          apply Subtype.ext
          exact hab
      | inr c =>
          exfalso
          change (A.tau x).1 = c.1 at hab
          apply (A.tau x).2
          rw [hab]
          exact c.2.2
  | inr c =>
      cases b with
      | inl x =>
          exfalso
          change c.1 = (A.tau x).1 at hab
          apply (A.tau x).2
          rw [← hab]
          exact c.2.2
      | inr d =>
          apply congrArg Sum.inr
          apply Subtype.ext
          exact hab

/-- A vertex permutation extending translation off the projective wall and
the identity on the projective-injective wall. -/
def vertexPerm : Equiv.Perm V :=
  Classical.choose
    (Equiv.Perm.exists_extending_pair A.sourcePoint A.targetPoint
      A.sourcePoint_injective A.targetPoint_injective)

theorem vertexPerm_spec (a : A.PermutationSource) :
    A.vertexPerm (A.sourcePoint a) = A.targetPoint a :=
  Classical.choose_spec
    (Equiv.Perm.exists_extending_pair A.sourcePoint A.targetPoint
      A.sourcePoint_injective A.targetPoint_injective) a

@[simp]
theorem vertexPerm_nonprojective
    (x : {x : V // x ∉ A.projective}) :
    A.vertexPerm x.1 = (A.tau x).1 :=
  A.vertexPerm_spec (Sum.inl x)

@[simp]
theorem vertexPerm_projective_injective
    (c : {c : V // c ∈ A.projective ∩ A.injective}) :
    A.vertexPerm c.1 = c.1 :=
  A.vertexPerm_spec (Sum.inr c)

theorem tau_mem_vertexPerm_image_iff
    (D : Set V) (x : {x : V // x ∉ A.projective}) :
    (A.tau x).1 ∈ A.vertexPerm '' D ↔ x.1 ∈ D := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    have heq : A.vertexPerm y = A.vertexPerm x.1 := by
      simpa using hxy
    exact (A.vertexPerm.injective heq) ▸ hy
  · intro hx
    exact ⟨x.1, hx, A.vertexPerm_nonprojective x⟩

theorem projectiveInjective_mem_vertexPerm_image_iff
    (D : Set V) (c : V) (hc : c ∈ A.projective ∩ A.injective) :
    c ∈ A.vertexPerm '' D ↔ c ∈ D := by
  let c' : {c : V // c ∈ A.projective ∩ A.injective} := ⟨c, hc⟩
  constructor
  · rintro ⟨y, hy, hxy⟩
    have heq : A.vertexPerm y = A.vertexPerm c := by
      calc
        A.vertexPerm y = c := hxy
        _ = A.vertexPerm c :=
          (A.vertexPerm_projective_injective c').symm
    exact (A.vertexPerm.injective heq) ▸ hy
  · intro hcD
    exact ⟨c, hcD, A.vertexPerm_projective_injective c'⟩

/-- The extended translation permutation carries the forward hitting
clauses exactly to the reverse hitting clauses. -/
theorem qGood_iff_sGood_image (D : Set V) :
    A.QGood D ↔ A.SGood (A.vertexPerm '' D) := by
  constructor
  · intro hQ x hx
    have hxD : x.1 ∈ D :=
      (A.tau_mem_vertexPerm_image_iff D x).1 hx
    obtain ⟨c, hcD, hcM⟩ := hQ x hxD
    have hcPI : c ∈ A.projective ∩ A.injective :=
      A.middle_subset_projective_injective x hcM
    exact ⟨c,
      (A.projectiveInjective_mem_vertexPerm_image_iff D c hcPI).2 hcD,
      hcM⟩
  · intro hS x hx
    have htau : (A.tau x).1 ∈ A.vertexPerm '' D :=
      (A.tau_mem_vertexPerm_image_iff D x).2 hx
    obtain ⟨c, hcD, hcM⟩ := hS x htau
    have hcPI : c ∈ A.projective ∩ A.injective :=
      A.middle_subset_projective_injective x hcM
    exact ⟨c,
      (A.projectiveInjective_mem_vertexPerm_image_iff D c hcPI).1 hcD,
      hcM⟩

/-- The forward-good and reverse-good deleted sets are equivalent. -/
def qGoodEquivSGood :
    {D : Set V // A.QGood D} ≃ {D : Set V // A.SGood D} where
  toFun D := ⟨A.vertexPerm '' D.1,
    (A.qGood_iff_sGood_image D.1).1 D.2⟩
  invFun E := ⟨A.vertexPerm.symm '' E.1, by
    apply (A.qGood_iff_sGood_image _).2
    simpa using E.2⟩
  left_inv D := by
    apply Subtype.ext
    exact A.vertexPerm.symm_image_image D.1
  right_inv E := by
    apply Subtype.ext
    exact A.vertexPerm.image_symm_image E.1

/-- The equivalence preserves the number of deleted vertices. -/
theorem ncard_qGoodEquivSGood (D : {D : Set V // A.QGood D}) :
    ((A.qGoodEquivSGood D).1).ncard = D.1.ncard :=
  Set.ncard_image_of_injective D.1 A.vertexPerm.injective

/-- Size-generating polynomial of a finite family of vertex subsets. -/
def sizePolynomial (Good : Set V → Prop) : Polynomial ℤ := by
  letI : Fintype {D : Set V // Good D} := Fintype.ofFinite _
  exact ∑ D : {D : Set V // Good D}, X ^ D.1.ncard

/-- Projective-injective mesh middles force equality of the forward and
reverse deleted-set size polynomials. -/
theorem qGood_sizePolynomial_eq_sGood :
    sizePolynomial A.QGood = sizePolynomial A.SGood := by
  classical
  letI : Fintype {D : Set V // A.QGood D} := Fintype.ofFinite _
  letI : Fintype {D : Set V // A.SGood D} := Fintype.ofFinite _
  unfold sizePolynomial
  apply Fintype.sum_equiv A.qGoodEquivSGood
  intro D
  rw [A.ncard_qGoodEquivSGood D]

end Data

end OpConjecture.ProjectiveInjectiveMiddle
