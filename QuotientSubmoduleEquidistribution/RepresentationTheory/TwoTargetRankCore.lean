import QuotientSubmoduleEquidistribution.RepresentationTheory.LoewyTwoRankCore

/-!
# The one-source, two-target rank core

This is the linear dual of the elementary two-source rank argument.  If the
common source is one-dimensional and a two-target representation has no
nontrivial commuting idempotent triple, each target is at most
one-dimensional.
-/

noncomputable section

namespace QuotientSubmoduleEquidistribution.LoewyTwoRankCore

universe u v w z

variable {K : Type u} [Field K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {Z : Type z} [AddCommGroup Z] [Module K Z]

/-- The condition that a pair of arrows with common source has only the
all-zero and all-identity commuting idempotent triples. -/
def IsTwoTargetIdempotentIndecomposable
    (f : V →ₗ[K] W) (g : V →ₗ[K] Z) : Prop :=
  ∀ (p : V →ₗ[K] V) (q : W →ₗ[K] W) (r : Z →ₗ[K] Z),
    p.comp p = p →
    q.comp q = q →
    r.comp r = r →
    q.comp f = f.comp p →
    r.comp g = g.comp p →
    (p = 0 ∧ q = 0 ∧ r = 0) ∨
      (p = LinearMap.id ∧ q = LinearMap.id ∧ r = LinearMap.id)

private theorem target_finrank_le_one_aux
    [FiniteDimensional K V] [FiniteDimensional K W]
    [FiniteDimensional K Z]
    {f : V →ₗ[K] W} {g : V →ₗ[K] Z}
    (hV : Module.finrank K V = 1)
    (hfg : IsTwoTargetIdempotentIndecomposable f g) :
    Module.finrank K W ≤ 1 := by
  by_contra hWle
  have hW : 2 ≤ Module.finrank K W := by omega
  have hrange :
      Module.finrank K f.range ≤ 1 := by
    calc
      Module.finrank K f.range ≤ Module.finrank K V :=
        LinearMap.finrank_range_le f
      _ = 1 := hV
  have hrangeLt : f.range < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro hrangeTop
    have hfinrank : Module.finrank K f.range = Module.finrank K W := by
      rw [hrangeTop]
      simp
    omega
  obtain ⟨w, -, hw⟩ := SetLike.exists_of_lt hrangeLt
  have hwQuot : f.range.mkQ w ≠ 0 := by
    simpa using hw
  have hli :
      LinearIndependent K (fun _ : Unit ↦ f.range.mkQ w) :=
    LinearIndependent.of_subsingleton () hwQuot
  obtain ⟨ψ, hψ⟩ :=
    Module.exists_dual_forall_apply_eq_one
      (s := Set.univ) (hli.linearIndepOn Set.univ)
  have hψw : ψ (f.range.mkQ w) = 1 :=
    hψ () (Set.mem_univ ())
  let φ : W →ₗ[K] K := ψ.comp f.range.mkQ
  have hφw : φ w = 1 := by
    simpa [φ, LinearMap.comp_apply] using hψw
  let q : W →ₗ[K] W := LinearMap.smulRight φ w
  have hqIdem : q.comp q = q := by
    ext x
    simp [q, LinearMap.comp_apply, hφw]
  have hqNe : q ≠ 0 := by
    intro hqZero
    have hqw := LinearMap.congr_fun hqZero w
    have hqwEq : q w = w := by
      simp [q, hφw]
    have hwZero : w = 0 := by
      rw [hqwEq] at hqw
      exact hqw
    exact hw (by simp [hwZero])
  have hfComm : q.comp f = f.comp (0 : V →ₗ[K] V) := by
    ext x
    have hmk : f.range.mkQ (f x) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact LinearMap.mem_range_self f x
    simp [q, φ, LinearMap.comp_apply, hmk]
  have hgComm :
      (0 : Z →ₗ[K] Z).comp g =
        g.comp (0 : V →ₗ[K] V) := by
    ext
    simp
  rcases hfg 0 q 0 (by ext; simp) hqIdem (by ext; simp)
      hfComm hgComm with hzero | hone
  · exact hqNe hzero.2.1
  · haveI : Nontrivial V :=
      Module.nontrivial_of_finrank_pos (R := K) (M := V) (by omega)
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have hp := LinearMap.congr_fun hone.1 v
    exact hv (by simpa using hp.symm)

/-- The first target of an idempotent-indecomposable two-target
representation with one-dimensional common source has dimension at most one. -/
theorem twoTarget_firstTarget_finrank_le_one
    [FiniteDimensional K V] [FiniteDimensional K W]
    [FiniteDimensional K Z]
    {f : V →ₗ[K] W} {g : V →ₗ[K] Z}
    (hV : Module.finrank K V = 1)
    (hfg : IsTwoTargetIdempotentIndecomposable f g) :
    Module.finrank K W ≤ 1 :=
  target_finrank_le_one_aux hV hfg

/-- The second target satisfies the symmetric bound. -/
theorem twoTarget_secondTarget_finrank_le_one
    [FiniteDimensional K V] [FiniteDimensional K W]
    [FiniteDimensional K Z]
    {f : V →ₗ[K] W} {g : V →ₗ[K] Z}
    (hV : Module.finrank K V = 1)
    (hfg : IsTwoTargetIdempotentIndecomposable f g) :
    Module.finrank K Z ≤ 1 := by
  exact
    target_finrank_le_one_aux
      (W := Z) (Z := W) (f := g) (g := f) hV
      (by
        intro p r q hp hr hq hrg hrf
        rcases hfg p q r hp hq hr hrf hrg with hzero | hone
        · exact Or.inl ⟨hzero.1, hzero.2.2, hzero.2.1⟩
        · exact Or.inr ⟨hone.1, hone.2.2, hone.2.1⟩)

/-- Both targets of an idempotent-indecomposable two-target
representation with one-dimensional common source have dimension at most
one. -/
theorem twoTarget_target_finrank_le_one
    [FiniteDimensional K V] [FiniteDimensional K W]
    [FiniteDimensional K Z]
    {f : V →ₗ[K] W} {g : V →ₗ[K] Z}
    (hV : Module.finrank K V = 1)
    (hfg : IsTwoTargetIdempotentIndecomposable f g) :
    Module.finrank K W ≤ 1 ∧ Module.finrank K Z ≤ 1 :=
  ⟨twoTarget_firstTarget_finrank_le_one hV hfg,
    twoTarget_secondTarget_finrank_le_one hV hfg⟩

end QuotientSubmoduleEquidistribution.LoewyTwoRankCore
