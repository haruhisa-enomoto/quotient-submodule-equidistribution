import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Jacobson.Radical
import Mathlib.RingTheory.Length
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import QuotientSubmoduleEquidistribution.RepresentationTheory.LengthTwoGabrielBridge

/-!
# The one-arrow rank core of the isotypic Loewy-two argument

This file proves the elementary linear-algebra step behind the
no-parallel-`Ext¹` argument.  A representation of one arrow is a linear map
`f : V → W`.  If its only commuting idempotent pairs are zero and one, then
both vertex spaces have dimension at most one.
-/

noncomputable section

open Set

namespace QuotientSubmoduleEquidistribution.LoewyTwoRankCore

universe u v w

variable {K : Type u} [Field K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]

/--
The idempotent formulation of indecomposability for a representation of the
quiver with one arrow.

In an idempotent-complete additive category this is equivalent to the usual
condition that the object is nonzero and is not a nontrivial direct sum.
-/
def IsIdempotentIndecomposable (f : V →ₗ[K] W) : Prop :=
  ∀ (p : V →ₗ[K] V) (q : W →ₗ[K] W),
    p.comp p = p →
    q.comp q = q →
    q.comp f = f.comp p →
    (p = 0 ∧ q = 0) ∨
      (p = LinearMap.id ∧ q = LinearMap.id)

private theorem exists_rankOne_idempotent
    [FiniteDimensional K V]
    (hV : 2 ≤ Module.finrank K V) :
    ∃ (v : V) (φ : V →ₗ[K] K) (p : V →ₗ[K] V),
      v ≠ 0 ∧ φ v = 1 ∧
      p = LinearMap.smulRight φ v ∧
      p.comp p = p ∧ p ≠ 0 ∧ p ≠ LinearMap.id := by
  have hpos : 0 < Module.finrank K V := lt_of_lt_of_le (by omega) hV
  letI : Nontrivial V := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hli : LinearIndependent K (fun _ : Unit ↦ v) :=
    LinearIndependent.of_subsingleton () hv
  obtain ⟨φ, hφ⟩ :=
    Module.exists_dual_forall_apply_eq_one
      (s := Set.univ) (hli.linearIndepOn Set.univ)
  have hφv : φ v = 1 := hφ () (Set.mem_univ ())
  let p : V →ₗ[K] V := LinearMap.smulRight φ v
  refine ⟨v, φ, p, hv, hφv, rfl, ?_, ?_, ?_⟩
  · ext x
    simp [p, LinearMap.comp_apply, hφv]
  · intro hp
    have hpv := LinearMap.congr_fun hp v
    apply hv
    simpa [p, hφv] using hpv
  · intro hp
    have hspan :
        ∀ x : V, ∃ c : K, c • v = x := by
      intro x
      refine ⟨φ x, ?_⟩
      have hx := LinearMap.congr_fun hp x
      simpa [p] using hx
    have hfinrank :
        Module.finrank K V ≤ 1 :=
      finrank_le_one v hspan
    omega

/--
If a finite-dimensional one-arrow representation has no nontrivial
idempotent endomorphism, then its source has dimension at most one.
-/
theorem source_finrank_le_one
    [FiniteDimensional K V] [FiniteDimensional K W]
    {f : V →ₗ[K] W}
    (hf : IsIdempotentIndecomposable f) :
    Module.finrank K V ≤ 1 := by
  by_contra hle
  have hV : 2 ≤ Module.finrank K V := by omega
  obtain ⟨v, φ, p, hv, hφv, rfl, hp_idem, hp_ne_zero, hp_ne_id⟩ :=
    exists_rankOne_idempotent (K := K) hV
  by_cases hfv : f v = 0
  · have hcomm :
        (0 : W →ₗ[K] W).comp f =
          f.comp (LinearMap.smulRight φ v) := by
      ext x
      simp [LinearMap.comp_apply, hfv]
    rcases hf (LinearMap.smulRight φ v) 0 hp_idem (by ext; simp)
        hcomm with hzero | hone
    · exact hp_ne_zero hzero.1
    · exact hp_ne_id hone.1
  · have hli : LinearIndependent K (fun _ : Unit ↦ f v) :=
      LinearIndependent.of_subsingleton () hfv
    obtain ⟨ψ, hψ⟩ :=
      Module.exists_dual_forall_apply_eq_one
        (s := Set.univ) (hli.linearIndepOn Set.univ)
    have hψfv : ψ (f v) = 1 :=
      hψ () (Set.mem_univ ())
    let q : W →ₗ[K] W :=
      LinearMap.smulRight ψ (f v)
    have hq_idem : q.comp q = q := by
      ext y
      simp [q, LinearMap.comp_apply, hψfv]
    have hq_ne_zero : q ≠ 0 := by
      intro hq
      have := LinearMap.congr_fun hq (f v)
      apply hfv
      simpa [q, hψfv] using this
    have hcomm :
        q.comp f =
          f.comp (LinearMap.smulRight (ψ.comp f) v) := by
      ext x
      simp [q, LinearMap.comp_apply]
    let p' : V →ₗ[K] V :=
      LinearMap.smulRight (ψ.comp f) v
    have hp'_idem : p'.comp p' = p' := by
      ext x
      simp [p', LinearMap.comp_apply, hψfv]
    have hp'_ne_zero : p' ≠ 0 := by
      intro hp'
      have := LinearMap.congr_fun hp' v
      apply hv
      simpa [p', hψfv] using this
    have hp'_ne_id : p' ≠ LinearMap.id := by
      intro hp'
      have hspan :
          ∀ x : V, ∃ c : K, c • v = x := by
        intro x
        refine ⟨ψ (f x), ?_⟩
        have hx := LinearMap.congr_fun hp' x
        simpa [p'] using hx
      have hfinrank :
          Module.finrank K V ≤ 1 :=
        finrank_le_one v hspan
      omega
    rcases hf p' q hp'_idem hq_idem (by simpa [p'] using hcomm) with
      hzero | hone
    · exact hp'_ne_zero hzero.1
    · exact hp'_ne_id hone.1

/--
The symmetric vertex bound: a finite-dimensional indecomposable one-arrow
representation also has target dimension at most one.
-/
theorem target_finrank_le_one
    [FiniteDimensional K V] [FiniteDimensional K W]
    {f : V →ₗ[K] W}
    (hf : IsIdempotentIndecomposable f) :
    Module.finrank K W ≤ 1 := by
  by_contra hle
  have hW : 2 ≤ Module.finrank K W := by omega
  by_cases hfzero : f = 0
  · obtain ⟨w, ψ, q, hw, hψw, rfl, hq_idem, hq_ne_zero, hq_ne_id⟩ :=
      exists_rankOne_idempotent (K := K) (V := W) hW
    rcases hf 0 (LinearMap.smulRight ψ w) (by ext; simp) hq_idem
        (by simp [hfzero]) with hzero | hone
    · exact hq_ne_zero hzero.2
    · exact hq_ne_id hone.2
  · obtain ⟨v, hfv⟩ := DFunLike.ne_iff.mp hfzero
    have hli : LinearIndependent K (fun _ : Unit ↦ f v) :=
      LinearIndependent.of_subsingleton () hfv
    obtain ⟨ψ, hψ⟩ :=
      Module.exists_dual_forall_apply_eq_one
        (s := Set.univ) (hli.linearIndepOn Set.univ)
    have hψfv : ψ (f v) = 1 :=
      hψ () (Set.mem_univ ())
    let p : V →ₗ[K] V :=
      LinearMap.smulRight (ψ.comp f) v
    let q : W →ₗ[K] W :=
      LinearMap.smulRight ψ (f v)
    have hp_idem : p.comp p = p := by
      ext x
      simp [p, LinearMap.comp_apply, hψfv]
    have hq_idem : q.comp q = q := by
      ext y
      simp [q, LinearMap.comp_apply, hψfv]
    have hq_ne_zero : q ≠ 0 := by
      intro hq
      have := LinearMap.congr_fun hq (f v)
      apply hfv
      simpa [q, hψfv] using this
    have hq_ne_id : q ≠ LinearMap.id := by
      intro hq
      have hspan :
          ∀ y : W, ∃ c : K, c • f v = y := by
        intro y
        refine ⟨ψ y, ?_⟩
        have hy := LinearMap.congr_fun hq y
        simpa [q] using hy
      have hfinrank :
          Module.finrank K W ≤ 1 :=
        finrank_le_one (f v) hspan
      omega
    have hcomm : q.comp f = f.comp p := by
      ext x
      simp [p, q, LinearMap.comp_apply]
    rcases hf p q hp_idem hq_idem hcomm with hzero | hone
    · exact hq_ne_zero hzero.2
    · exact hq_ne_id hone.2

/--
Paper-facing consequence of a one-arrow model for a module top.

The equality says that the source space of the one-arrow representation is
the multiplicity space of the semisimple top.  Thus the source bound above
forces the top to have composition length one.
-/
theorem moduleTop_isSimple_of_oneArrowModel
    {A : Type*} [Ring A]
    {M : Type*} [AddCommGroup M] [Module A M]
    [Nontrivial M] [Module.Finite A M] [IsArtinian A M]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (f : V →ₗ[K] W)
    (hf : IsIdempotentIndecomposable f)
    (hsourceLength :
      (Module.finrank K V : ℕ∞) =
        Module.length A
          (M ⧸ Module.jacobson A M)) :
    IsSimpleModule A
      (M ⧸ Module.jacobson A M) := by
  let J : Submodule A M := Module.jacobson A M
  have hJneTop : J ≠ ⊤ :=
    (Module.jacobson_lt_top A M).ne
  letI : Nontrivial (M ⧸ J) := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    exact hJneTop
      (Submodule.Quotient.subsingleton_iff.mp hsub)
  have hlengthPos :
      0 < Module.length A (M ⧸ J) :=
    Module.length_pos_iff.mpr inferInstance
  have hsource :
      Module.finrank K V ≤ 1 :=
    source_finrank_le_one hf
  have hlengthLe :
      Module.length A (M ⧸ J) ≤ 1 := by
    rw [← hsourceLength]
    exact ENat.coe_le_coe.mpr hsource
  have hlength :
      Module.length A (M ⧸ J) = 1 :=
    le_antisymm hlengthLe
      (Order.one_le_iff_ne_zero.mpr hlengthPos.ne')
  exact Module.length_eq_one_iff.mp hlength

/-! ## Multiplicity of a finite isotypic semisimple module -/

variable {R : Type u} [Ring R]
  {M : Type v} [AddCommGroup M] [Module R M]
  {S : Type w} [AddCommGroup S] [Module R S]

/--
A finite semisimple module isotypic of a simple module `S` is a finite power
of `S`, and its composition length is exactly that multiplicity.
-/
theorem exists_isotypicMultiplicity
    [IsSemisimpleModule R M] [Module.Finite R M]
    [IsSimpleModule R S]
    (h : IsIsotypicOfType R M S) :
    ∃ (n : ℕ) (_ : M ≃ₗ[R] Fin n → S),
      (n : ℕ∞) = Module.length R M := by
  obtain ⟨n, ⟨e⟩⟩ :=
    h.linearEquiv_fun
  refine ⟨n, e, ?_⟩
  rw [e.length_eq, Module.length_pi_of_fintype]
  simp

/-! ## Linear `Ext` decomposition over finite biproducts -/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

variable {C : Type v} [Category.{w} C] [Abelian C]
  [Linear K C] [HasExt C]

/--
Mathlib's additive equivalence expressing contravariant additivity of `Ext`
over a finite biproduct, upgraded to a linear equivalence.
-/
noncomputable def extBiproductLinearEquiv
    {J : Type*} [Fintype J]
    {X : J → C} {c : Bicone X}
    (hc : c.IsBilimit) (Y : C) (n : ℕ) :
    Ext c.pt Y n ≃ₗ[K]
      ∀ i, Ext (X i) Y n where
  toAddEquiv :=
    Ext.biproductAddEquiv hc Y n
  map_smul' r e := by
    ext i
    simp [Ext.biproductAddEquiv]

/--
Mathlib's additive equivalence expressing covariant additivity of `Ext` over
a finite biproduct, upgraded to a linear equivalence.
-/
noncomputable def extLinearEquivBiproduct
    (X : C) {J : Type*} [Fintype J]
    {Y : J → C} {c : Bicone Y}
    (hc : c.IsBilimit) (n : ℕ) :
    Ext X c.pt n ≃ₗ[K]
      ∀ i, Ext X (Y i) n where
  toAddEquiv :=
    Ext.addEquivBiproduct X hc n
  map_smul' r e := by
    ext i
    simp [Ext.addEquivBiproduct]

/--
An extension between two finite biproducts is linearly equivalent to a
matrix of extensions between their components.
-/
noncomputable def extBiproductBiproductLinearEquiv
    {I J : Type*} [Fintype I] [Fintype J]
    {X : I → C} {c : Bicone X}
    {Y : J → C} {d : Bicone Y}
    (hc : c.IsBilimit) (hd : d.IsBilimit) (n : ℕ) :
    Ext c.pt d.pt n ≃ₗ[K]
      ∀ i, ∀ j, Ext (X i) (Y j) n :=
  (extBiproductLinearEquiv hc d.pt n).trans
    (LinearEquiv.piCongrRight fun i ↦
      extLinearEquivBiproduct (X i) hd n)

/-! ## Exact interface to the categorical `Ext¹` reduction -/

universe x y

variable {A : Type x} [Ring A]
  {ι : Type y} [IsNoetherianRing Aᵐᵒᵖ]
  (σ :
    _root_.QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{x, y, x}
      Aᵐᵒᵖ ι)

/--
The exact numerical no-parallel-arrow hypothesis on the simple objects in a
chosen skeleton.

The finite-dimensionality conjunct cannot be omitted: Mathlib defines the
finrank of an infinite-dimensional space to be zero.
-/
def NoParallelExtOne
    (K : Type x) [Field K] [Algebra K A]
    [FiniteDimensional K A] : Prop :=
  ∀ {s t : ι},
    Simple (σ.obj s) →
    Simple (σ.obj t) →
    FiniteDimensional K
        (Ext (σ.obj s).obj (σ.obj t).obj 1) ∧
      Module.finrank K
        (Ext (σ.obj s).obj (σ.obj t).obj 1) ≤ 1

/--
The concrete output needed from the missing `Ext¹`-matrix construction for
one indecomposable module.

`V` is the multiplicity space of the top, witnessed by the equality of its
dimension with the composition length of the actual semisimple top.  The
linear map `f : V → W` is the single extension matrix.  Its idempotent
indecomposability is the precise property consumed by the rank core above.
-/
def HasOneArrowModel
    (K : Type x) [Field K]
    (j : ι) : Prop :=
  ∃ (V W : Type x)
    (_ : AddCommGroup V) (_ : Module K V)
    (_ : AddCommGroup W) (_ : Module K W)
    (_ : FiniteDimensional K V)
    (_ : FiniteDimensional K W)
    (f : V →ₗ[K] W),
      IsIdempotentIndecomposable f ∧
        (Module.finrank K V : ℕ∞) =
          Module.length Aᵐᵒᵖ (σ.moduleTop j)

/--
The sole unresolved construction after Mathlib's `Ext` biproduct additivity
and the rank core: no-parallel `Ext¹` must turn every isotypic Loewy-two
indecomposable into a one-arrow model.
-/
def NoParallelExtOneArrowReduction
    (K : Type x) [Field K] [IsAlgClosed K]
    [Algebra K A] [FiniteDimensional K A] : Prop :=
  NoParallelExtOne σ K →
    ∀ {j s t : ι},
      Simple (σ.obj s) →
      Simple (σ.obj t) →
      IsIsotypicOfType Aᵐᵒᵖ
        (σ.moduleTop j) (σ.obj s) →
      IsSemisimpleModule Aᵐᵒᵖ
        (σ.moduleRadical j) →
      IsIsotypicOfType Aᵐᵒᵖ
        (σ.moduleRadical j) (σ.obj t) →
      HasOneArrowModel σ K j

/--
Once the categorical `Ext¹`-matrix reduction is supplied, the outstanding
classification interface in `LengthTwoGabrielBridge` follows with no further
representation-theoretic input.
-/
theorem isotypicLoewyTwoClassification_of_noParallelExtOneArrowReduction
    (K : Type x) [Field K] [IsAlgClosed K]
    [Algebra K A] [FiniteDimensional K A]
    (hnoParallel : NoParallelExtOne σ K)
    (hreduction :
      NoParallelExtOneArrowReduction σ K) :
    QuotientSubmoduleEquidistribution.LengthTwoGabrielBridge.IndecomposableSkeleton.IsotypicLoewyTwoIndecomposablesHaveSimpleTop
      σ := by
  intro j s t hs ht htop hradSemisimple hradIsotypic
  obtain ⟨V, W, hVadd, hVmodule, hWadd, hWmodule,
      hVfinite, hWfinite, f, hf, hsourceLength⟩ :=
    hreduction hnoParallel hs ht htop hradSemisimple
      hradIsotypic
  letI : AddCommGroup V := hVadd
  letI : Module K V := hVmodule
  letI : AddCommGroup W := hWadd
  letI : Module K W := hWmodule
  letI : FiniteDimensional K V := hVfinite
  letI : FiniteDimensional K W := hWfinite
  letI : Nontrivial (σ.obj j) :=
    (σ.indecomposable j).nontrivial
  letI : IsArtinian Aᵐᵒᵖ (σ.obj j) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (σ.finiteLength j)).2
  exact
    moduleTop_isSimple_of_oneArrowModel
      f hf hsourceLength

end QuotientSubmoduleEquidistribution.LoewyTwoRankCore
