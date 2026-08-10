import QuotientSubmoduleEquidistribution.RepresentationTheory.LoewyTwoRankCore

/-!
# The two-source, one-target rank core

This is the elementary linear algebra needed for the branched
Loewy-length-two family at level three. If the target space is
one-dimensional and a two-source representation has no nontrivial
commuting idempotent triple, each source space is at most
one-dimensional.
-/

noncomputable section

namespace QuotientSubmoduleEquidistribution.LoewyTwoRankCore

universe u v w z

variable {K : Type u} [Field K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {Z : Type z} [AddCommGroup Z] [Module K Z]

/-- The condition that a pair of arrows with common target has only the
all-zero and all-identity commuting idempotent triples. -/
def IsTwoSourceIdempotentIndecomposable
    (f : V →ₗ[K] Z) (g : W →ₗ[K] Z) : Prop :=
  ∀ (p : V →ₗ[K] V) (q : W →ₗ[K] W) (r : Z →ₗ[K] Z),
    p.comp p = p →
    q.comp q = q →
    r.comp r = r →
    r.comp f = f.comp p →
    r.comp g = g.comp q →
    (p = 0 ∧ q = 0 ∧ r = 0) ∨
      (p = LinearMap.id ∧ q = LinearMap.id ∧ r = LinearMap.id)

private theorem source_finrank_le_one_aux
    [FiniteDimensional K V] [FiniteDimensional K W]
    [FiniteDimensional K Z]
    {f : V →ₗ[K] Z} {g : W →ₗ[K] Z}
    (hZ : Module.finrank K Z = 1)
    (hfg : IsTwoSourceIdempotentIndecomposable f g) :
    Module.finrank K V ≤ 1 := by
  by_contra hVle
  have hV : 2 ≤ Module.finrank K V := by omega
  have hrange :
      Module.finrank K f.range ≤ 1 := by
    simpa [hZ] using f.range.finrank_le
  have hsum :=
    LinearMap.finrank_range_add_finrank_ker f
  have hkerPos :
      0 < Module.finrank K f.ker := by
    omega
  letI : Nontrivial f.ker :=
    Module.nontrivial_of_finrank_pos hkerPos
  obtain ⟨v, hv⟩ := exists_ne (0 : f.ker)
  have hvval : v.1 ≠ 0 := by
    intro hzero
    apply hv
    apply Subtype.ext
    exact hzero
  have hli : LinearIndependent K (fun _ : Unit ↦ v.1) :=
    LinearIndependent.of_subsingleton () hvval
  obtain ⟨φ, hφ⟩ :=
    Module.exists_dual_forall_apply_eq_one
      (s := Set.univ) (hli.linearIndepOn Set.univ)
  have hφv : φ v.1 = 1 :=
    hφ () (Set.mem_univ ())
  let p : V →ₗ[K] V :=
    LinearMap.smulRight φ v.1
  have hpIdem : p.comp p = p := by
    ext x
    simp [p, LinearMap.comp_apply, hφv]
  have hpNe : p ≠ 0 := by
    intro hp
    have hpv := LinearMap.congr_fun hp v.1
    apply hvval
    simpa [p, hφv] using hpv
  have hfPv : f v.1 = 0 := v.2
  have hfComm :
      (0 : Z →ₗ[K] Z).comp f = f.comp p := by
    ext x
    simp [p, LinearMap.comp_apply, hfPv]
  have hgComm :
      (0 : Z →ₗ[K] Z).comp g =
        g.comp (0 : W →ₗ[K] W) := by
    ext
    simp
  rcases hfg p 0 0 hpIdem (by ext; simp) (by ext; simp)
      hfComm hgComm with hzero | hone
  · exact hpNe hzero.1
  · haveI : Nontrivial Z :=
      Module.nontrivial_of_finrank_pos (R := K) (M := Z) (by omega)
    obtain ⟨z, hz⟩ := exists_ne (0 : Z)
    have hr := LinearMap.congr_fun hone.2.2 z
    exact hz (by simpa using hr.symm)

/-- The first source of an idempotent-indecomposable two-source
representation with
one-dimensional target has dimension at most one. -/
theorem twoSource_firstSource_finrank_le_one
    [FiniteDimensional K V] [FiniteDimensional K W]
    [FiniteDimensional K Z]
    {f : V →ₗ[K] Z} {g : W →ₗ[K] Z}
    (hZ : Module.finrank K Z = 1)
    (hfg : IsTwoSourceIdempotentIndecomposable f g) :
    Module.finrank K V ≤ 1 :=
  source_finrank_le_one_aux hZ hfg

/-- The second source satisfies the symmetric bound. -/
theorem twoSource_secondSource_finrank_le_one
    [FiniteDimensional K V] [FiniteDimensional K W]
    [FiniteDimensional K Z]
    {f : V →ₗ[K] Z} {g : W →ₗ[K] Z}
    (hZ : Module.finrank K Z = 1)
    (hfg : IsTwoSourceIdempotentIndecomposable f g) :
    Module.finrank K W ≤ 1 := by
  exact
    source_finrank_le_one_aux
      (V := W) (W := V) (f := g) (g := f) hZ
      (by
        intro q p r hq hp hr hrg hrf
        rcases hfg p q r hp hq hr hrf hrg with hzero | hone
        · exact Or.inl ⟨hzero.2.1, hzero.1, hzero.2.2⟩
        · exact Or.inr ⟨hone.2.1, hone.1, hone.2.2⟩)

/-- Both sources of an idempotent-indecomposable two-source
representation with one-dimensional target have dimension at most one. -/
theorem twoSource_source_finrank_le_one
    [FiniteDimensional K V] [FiniteDimensional K W]
    [FiniteDimensional K Z]
    {f : V →ₗ[K] Z} {g : W →ₗ[K] Z}
    (hZ : Module.finrank K Z = 1)
    (hfg : IsTwoSourceIdempotentIndecomposable f g) :
    Module.finrank K V ≤ 1 ∧ Module.finrank K W ≤ 1 :=
  ⟨twoSource_firstSource_finrank_le_one hZ hfg,
    twoSource_secondSource_finrank_le_one hZ hfg⟩

end QuotientSubmoduleEquidistribution.LoewyTwoRankCore
