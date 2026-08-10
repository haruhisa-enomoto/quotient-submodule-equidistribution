import OpConjecture.RepresentationTheory.TwoTargetRankCore

/-!
# The missing source bound for a one-source, two-target representation
-/

noncomputable section

open Set

namespace OpConjecture.LoewyTwoRankCore

universe u v w z

variable {K : Type u} [Field K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {Z : Type z} [AddCommGroup Z] [Module K Z]

private theorem zero_ne_linearMap_id
    {M : Type*} [AddCommGroup M] [Module K M] [Nontrivial M] :
    (0 : M →ₗ[K] M) ≠ LinearMap.id := by
  intro h
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  have hmapped := LinearMap.congr_fun h m
  exact hm (by simpa using hmapped.symm)

/-- The common source of an idempotent-indecomposable fork has dimension at
most one.  Together with the existing conditional target bounds this is the
linear-algebra classification needed for the family-3 `A₃` fork. -/
theorem twoTarget_source_finrank_le_one
    [FiniteDimensional K V] [FiniteDimensional K W]
    [FiniteDimensional K Z]
    {f : V →ₗ[K] W} {g : V →ₗ[K] Z}
    (hfg : IsTwoTargetIdempotentIndecomposable f g) :
    Module.finrank K V ≤ 1 := by
  by_cases hW : Subsingleton W
  · letI : Subsingleton W := hW
    have hg : IsIdempotentIndecomposable g := by
      intro p r hp hr hcomm
      have hfcomm :
          (0 : W →ₗ[K] W).comp f = f.comp p :=
        Subsingleton.elim _ _
      rcases hfg p 0 r hp (by ext; simp) hr hfcomm hcomm with
        hzero | hone
      · exact Or.inl ⟨hzero.1, hzero.2.2⟩
      · exact Or.inr ⟨hone.1, hone.2.2⟩
    exact source_finrank_le_one hg
  · letI : Nontrivial W := not_subsingleton_iff_nontrivial.mp hW
    by_contra hVle
    have hV : 2 ≤ Module.finrank K V := by omega
    letI : Nontrivial V :=
      Module.nontrivial_of_finrank_pos (R := K) (M := V) (by omega)
    have hzeroIdW : (0 : W →ₗ[K] W) ≠ LinearMap.id :=
      zero_ne_linearMap_id (K := K)
    have hzeroIdV : (0 : V →ₗ[K] V) ≠ LinearMap.id :=
      zero_ne_linearMap_id (K := K)
    by_cases hfinj : Function.Injective f
    · by_cases hfsurj : Function.Surjective f
      · let ef : V ≃ₗ[K] W :=
          LinearEquiv.ofBijective f ⟨hfinj, hfsurj⟩
        let a : W →ₗ[K] Z := g.comp ef.symm.toLinearMap
        have ha : IsIdempotentIndecomposable a := by
          intro q r hq hr hcomm
          let p : V →ₗ[K] V :=
            ef.symm.toLinearMap.comp (q.comp ef.toLinearMap)
          have hp : p.comp p = p := by
            ext x
            have hqx := LinearMap.congr_fun hq (ef x)
            simpa [p, LinearMap.comp_apply] using
              congrArg ef.symm hqx
          have hqf : q.comp f = f.comp p := by
            ext x
            simp [p, LinearMap.comp_apply, ef]
          have hrg : r.comp g = g.comp p := by
            ext x
            have hx := LinearMap.congr_fun hcomm (ef x)
            simpa [a, p, LinearMap.comp_apply] using hx
          rcases hfg p q r hp hq hr hqf hrg with hzero | hone
          · exact Or.inl ⟨hzero.2.1, hzero.2.2⟩
          · exact Or.inr ⟨hone.2.1, hone.2.2⟩
        have hWle : Module.finrank K W ≤ 1 :=
          source_finrank_le_one ha
        have heq : Module.finrank K V = Module.finrank K W :=
          ef.finrank_eq
        omega
      · have hrangeLt : f.range < ⊤ := by
          rw [lt_top_iff_ne_top]
          exact fun htop ↦ hfsurj (LinearMap.range_eq_top.mp htop)
        obtain ⟨w, -, hw⟩ := SetLike.exists_of_lt hrangeLt
        have hwQuot : f.range.mkQ w ≠ 0 := by
          simpa using hw
        have hli :
            LinearIndependent K (fun _ : Unit ↦ f.range.mkQ w) :=
          LinearIndependent.of_subsingleton () hwQuot
        obtain ⟨psi, hpsi⟩ :=
          Module.exists_dual_forall_apply_eq_one
            (s := Set.univ) (hli.linearIndepOn Set.univ)
        have hpsiw : psi (f.range.mkQ w) = 1 :=
          hpsi () (Set.mem_univ ())
        let phi : W →ₗ[K] K := psi.comp f.range.mkQ
        have hphiw : phi w = 1 := by
          simpa [phi, LinearMap.comp_apply] using hpsiw
        let q : W →ₗ[K] W := LinearMap.smulRight phi w
        have hq : q.comp q = q := by
          ext y
          simp [q, LinearMap.comp_apply, hphiw]
        have hqne : q ≠ 0 := by
          intro hqzero
          have hqw := LinearMap.congr_fun hqzero w
          have hqw' : q w = w := by simp [q, hphiw]
          have hwzero : w = 0 := by rw [hqw'] at hqw; exact hqw
          exact hw (by simp [hwzero])
        have hqf : q.comp f = f.comp (0 : V →ₗ[K] V) := by
          ext x
          have hmk : f.range.mkQ (f x) = 0 := by
            rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
            exact LinearMap.mem_range_self f x
          simp [q, phi, LinearMap.comp_apply, hmk]
        have hzg :
            (0 : Z →ₗ[K] Z).comp g =
              g.comp (0 : V →ₗ[K] V) := by ext; simp
        rcases hfg 0 q 0 (by ext; simp) hq (by ext; simp)
            hqf hzg with hzero | hone
        · exact hqne hzero.2.1
        · exact hzeroIdV hone.1
    · have hker : f.ker ≠ ⊥ := by
        intro hbot
        exact hfinj (LinearMap.ker_eq_bot.mp hbot)
      let uMap : f.ker →ₗ[K] Z := g.comp f.ker.subtype
      by_cases hu : Function.Injective uMap
      · obtain ⟨l, hl⟩ :=
          uMap.exists_leftInverse_of_injective
            (LinearMap.ker_eq_bot.mpr hu)
        let p : V →ₗ[K] V :=
          f.ker.subtype.comp (l.comp g)
        let r : Z →ₗ[K] Z := uMap.comp l
        have hp : p.comp p = p := by
          ext x
          have hx := LinearMap.congr_fun hl (l (g x))
          simpa [p, uMap, LinearMap.comp_apply] using
            congrArg Subtype.val hx
        have hr : r.comp r = r := by
          ext z
          have hz := LinearMap.congr_fun hl (l z)
          simpa [r, uMap, LinearMap.comp_apply] using
            congrArg uMap hz
        have hfp : (0 : W →ₗ[K] W).comp f = f.comp p := by
          ext x
          exact (l (g x)).2.symm
        have hrg : r.comp g = g.comp p := by
          ext x
          rfl
        letI : Nontrivial f.ker :=
          (Submodule.nontrivial_iff_ne_bot).mpr hker
        obtain ⟨k, hk⟩ := exists_ne (0 : f.ker)
        have hkval : k.1 ≠ 0 := by
          intro hkzero
          apply hk
          apply Subtype.ext
          exact hkzero
        have hpne : p ≠ 0 := by
          intro hpzero
          have hpk := LinearMap.congr_fun hpzero k.1
          have hlk := LinearMap.congr_fun hl k
          apply hkval
          have hpfix : p k.1 = k.1 := by
            simpa [p, uMap, LinearMap.comp_apply] using congrArg Subtype.val hlk
          calc
            k.1 = p k.1 := hpfix.symm
            _ = 0 := by simpa using hpk
        rcases hfg p 0 r hp (by ext; simp) hr hfp hrg with
          hzero | hone
        · exact hpne hzero.1
        · exact hzeroIdW hone.2.1
      · have hkerU : uMap.ker ≠ ⊥ := by
          intro hbot
          exact hu (LinearMap.ker_eq_bot.mp hbot)
        letI : Nontrivial uMap.ker :=
          (Submodule.nontrivial_iff_ne_bot).mpr hkerU
        obtain ⟨k, hk⟩ := exists_ne (0 : uMap.ker)
        let v : V := k.1.1
        have hv : v ≠ 0 := by
          intro hvzero
          apply hk
          apply Subtype.ext
          apply Subtype.ext
          exact hvzero
        have hli : LinearIndependent K (fun _ : Unit ↦ v) :=
          LinearIndependent.of_subsingleton () hv
        obtain ⟨phi, hphi⟩ :=
          Module.exists_dual_forall_apply_eq_one
            (s := Set.univ) (hli.linearIndepOn Set.univ)
        have hphiv : phi v = 1 := hphi () (Set.mem_univ ())
        let p : V →ₗ[K] V := LinearMap.smulRight phi v
        have hp : p.comp p = p := by
          ext x
          simp [p, LinearMap.comp_apply, hphiv]
        have hpne : p ≠ 0 := by
          intro hpzero
          have hpv := LinearMap.congr_fun hpzero v
          apply hv
          simpa [p, hphiv] using hpv
        have hfv : f v = 0 := k.1.2
        have hgv : g v = 0 := k.2
        have hfp : (0 : W →ₗ[K] W).comp f = f.comp p := by
          ext x
          simp [p, LinearMap.comp_apply, hfv]
        have hgp : (0 : Z →ₗ[K] Z).comp g = g.comp p := by
          ext x
          simp [p, LinearMap.comp_apply, hgv]
        rcases hfg p 0 0 hp (by ext; simp) (by ext; simp)
            hfp hgp with hzero | hone
        · exact hpne hzero.1
        · exact hzeroIdW hone.2.1

end OpConjecture.LoewyTwoRankCore
