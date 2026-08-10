import QuotientSubmoduleEquidistribution.RepresentationTheory.LengthThreeUniserial
import QuotientSubmoduleEquidistribution.RepresentationTheory.LoewyTwoGabrielClassification

/-!
# Collective generation by a length-three uniserial source

This file develops radical-layer reductions for the remaining
collective-closure step.
-/

noncomputable section

open Set
open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution

universe u v w

/-- The map induced on module radicals by a linear map. -/
def radicalRestriction
    {R : Type u} [Ring R]
    {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    Module.jacobson R M →ₗ[R] Module.jacobson R N :=
  (f.domRestrict (Module.jacobson R M)).codRestrict
    (Module.jacobson R N) (fun z ↦ by
      apply Module.map_jacobson_le f
      exact ⟨z.1, z.2, rfl⟩)

/-- A surjection out of an Artinian module is surjective on radicals. -/
theorem radicalRestriction_surjective
    {R : Type u} [Ring R]
    {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [IsArtinian R M]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    Function.Surjective (radicalRestriction f) := by
  intro y
  have hy :
      y.1 ∈ Submodule.map f (Module.jacobson R M) := by
    rw [QuotientSubmoduleEquidistribution.LengthTwoGabrielBridge.map_jacobson_of_surjective_of_isArtinian
      f hf]
    exact y.2
  obtain ⟨z, hz, hzy⟩ := hy
  refine ⟨⟨z, hz⟩, ?_⟩
  apply Subtype.ext
  exact hzy

/-- Radical restriction can be iterated: a surjection out of an Artinian
module is also surjective on the radicals of the first radicals. -/
theorem secondRadicalRestriction_surjective
    {R : Type u} [Ring R]
    {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [IsArtinian R M]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    Function.Surjective
      (radicalRestriction (radicalRestriction f)) := by
  apply radicalRestriction_surjective
  exact radicalRestriction_surjective f hf

/-- For a finite product, the module radical is exactly the product of
the component radicals.  Mathlib provides the forward inclusion for an
arbitrary product; finiteness gives the reverse inclusion by summing the
coordinate inclusions. -/
theorem jacobson_finite_pi
    {R : Type u} [Ring R]
    {J : Type*} [Fintype J]
    (M : J → Type v)
    [∀ t, AddCommGroup (M t)] [∀ t, Module R (M t)] :
    Module.jacobson R (∀ t, M t) =
      Submodule.pi Set.univ (fun t ↦ Module.jacobson R (M t)) := by
  classical
  apply le_antisymm
  · exact Module.jacobson_pi_le R M
  · intro x hx
    have hsum : x = ∑ t, Pi.single t (x t) := by
      ext t
      simp
    rw [hsum]
    apply Submodule.sum_mem
    intro t ht
    apply Module.map_jacobson_le (LinearMap.single R M t)
    refine ⟨x t, ?_, ?_⟩
    · exact hx t (Set.mem_univ t)
    · rfl

/-- The submodule consisting pointwise of elements of `N t` is linearly
equivalent to the dependent product of the submodules. -/
def submodulePiLinearEquiv
    {R : Type u} [Ring R]
    {J : Type*}
    (M : J → Type v)
    [∀ t, AddCommGroup (M t)] [∀ t, Module R (M t)]
    (N : ∀ t, Submodule R (M t)) :
    Submodule.pi Set.univ N ≃ₗ[R] (∀ t, N t) where
  toFun x t := ⟨x.1 t, x.2 t (Set.mem_univ t)⟩
  invFun x := ⟨fun t ↦ (x t).1, fun t _ ↦ (x t).2⟩
  left_inv x := by rfl
  right_inv x := by rfl
  map_add' x y := by rfl
  map_smul' r x := by rfl

/-- A linear equivalence restricts to a linear equivalence of module
radicals. -/
noncomputable def radicalRestrictionEquiv
    {R : Type u} [Ring R]
    {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) :
    Module.jacobson R M ≃ₗ[R] Module.jacobson R N :=
  LinearEquiv.ofBijective (radicalRestriction e.toLinearMap) ⟨
    (fun x y hxy ↦ by
      apply Subtype.ext
      apply e.injective
      exact congrArg Subtype.val hxy),
    (fun y ↦ by
      have hy :
          y.1 ∈ Submodule.map e.toLinearMap (Module.jacobson R M) := by
        rw [Module.map_jacobson_of_bijective e.bijective]
        exact y.2
      obtain ⟨x, hx, hxy⟩ := hy
      refine ⟨⟨x, hx⟩, ?_⟩
      apply Subtype.ext
      exact hxy)⟩

/-- The radical of a finite product is linearly equivalent to the
product of the component radicals. -/
noncomputable def radicalFinitePiEquiv
    {R : Type u} [Ring R]
    {J : Type*} [Fintype J]
    (M : J → Type v)
    [∀ t, AddCommGroup (M t)] [∀ t, Module R (M t)] :
    Module.jacobson R (∀ t, M t) ≃ₗ[R]
      (∀ t, Module.jacobson R (M t)) :=
  (LinearEquiv.ofEq _ _ (jacobson_finite_pi M)).trans
    (submodulePiLinearEquiv M (fun t ↦ Module.jacobson R (M t)))

/-- A product modulo the pointwise product of submodules is the product
of the quotients.  This `Ring`-level version avoids the unnecessary
commutativity assumption on Mathlib's current `Submodule.quotientPi`. -/
noncomputable def quotientPiLinearEquiv
    {R : Type u} [Ring R]
    {J : Type*}
    (M : J → Type v)
    [∀ t, AddCommGroup (M t)] [∀ t, Module R (M t)]
    (N : ∀ t, Submodule R (M t)) :
    ((∀ t, M t) ⧸ Submodule.pi Set.univ N) ≃ₗ[R]
      (∀ t, M t ⧸ N t) := by
  let g : (∀ t, M t) →ₗ[R] (∀ t, M t ⧸ N t) :=
    LinearMap.pi fun t ↦
      (N t).mkQ.comp (LinearMap.proj t)
  have hgSurjective : Function.Surjective g := by
    intro y
    choose x hx using fun t ↦ (N t).mkQ_surjective (y t)
    refine ⟨fun t ↦ x t, ?_⟩
    funext t
    exact hx t
  have hker : LinearMap.ker g = Submodule.pi Set.univ N := by
    ext x
    constructor
    · intro hx t _
      have hcoord : (N t).mkQ (x t) = 0 := by
        have hgzero : g x = 0 := (LinearMap.mem_ker.mp hx)
        exact congrFun hgzero t
      exact (Submodule.Quotient.mk_eq_zero (N t)).mp hcoord
    · intro hx
      apply LinearMap.mem_ker.mpr
      funext t
      exact (Submodule.Quotient.mk_eq_zero (N t)).mpr
        (hx t (Set.mem_univ t))
  exact
    (Submodule.quotEquivOfEq
      (Submodule.pi Set.univ N) (LinearMap.ker g) hker.symm).trans
      (g.quotKerEquivOfSurjective hgSurjective)

/-- Linear equivalences identify the semisimple tops obtained by
quotienting by the module Jacobson radicals. -/
noncomputable def moduleTopLinearEquiv
    {R : Type u} [Ring R]
    {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) :
    (M ⧸ Module.jacobson R M) ≃ₗ[R]
      (N ⧸ Module.jacobson R N) :=
  Submodule.Quotient.equiv
    (Module.jacobson R M) (Module.jacobson R N) e
    (Module.map_jacobson_of_bijective e.bijective)

/-- The top of a finite product is the product of the component tops. -/
noncomputable def moduleTopFinitePiEquiv
    {R : Type u} [Ring R]
    {J : Type*} [Fintype J]
    (M : J → Type v)
    [∀ t, AddCommGroup (M t)] [∀ t, Module R (M t)] :
    ((∀ t, M t) ⧸ Module.jacobson R (∀ t, M t)) ≃ₗ[R]
      (∀ t, M t ⧸ Module.jacobson R (M t)) :=
  (Submodule.quotEquivOfEq
    (Module.jacobson R (∀ t, M t))
    (Submodule.pi Set.univ (fun t ↦ Module.jacobson R (M t)))
    (jacobson_finite_pi M)).trans
      (quotientPiLinearEquiv M (fun t ↦ Module.jacobson R (M t)))

/-- The second radical of a finite product is linearly equivalent to the
product of the second radicals. -/
noncomputable def secondRadicalFinitePiEquiv
    {R : Type u} [Ring R]
    {J : Type*} [Fintype J]
    (M : J → Type v)
    [∀ t, AddCommGroup (M t)] [∀ t, Module R (M t)] :
    Module.jacobson R (Module.jacobson R (∀ t, M t)) ≃ₗ[R]
      (∀ t, Module.jacobson R (Module.jacobson R (M t))) :=
  let e₁ :
      Module.jacobson R (∀ t, M t) ≃ₗ[R]
        (∀ t, Module.jacobson R (M t)) :=
    radicalFinitePiEquiv M
  (radicalRestrictionEquiv e₁).trans <|
    radicalFinitePiEquiv (fun t ↦ Module.jacobson R (M t))

/-! ## Pure two-arrow rank core -/

namespace TwoStepRankCore

universe a b c d

variable {K : Type a} [Field K]
  {V : Type b} [AddCommGroup V] [Module K V]
  {W : Type c} [AddCommGroup W] [Module K W]
  {Z : Type d} [AddCommGroup Z] [Module K Z]

/-- A representation of a composable two-arrow chain is idempotent
indecomposable when its only compatible idempotent triples are the zero
and identity triples. -/
def IsIdempotentIndecomposableChain
    (f : V →ₗ[K] W) (g : W →ₗ[K] Z) : Prop :=
  ∀ (p : V →ₗ[K] V) (q : W →ₗ[K] W) (r : Z →ₗ[K] Z),
    p.comp p = p →
    q.comp q = q →
    r.comp r = r →
    q.comp f = f.comp p →
    r.comp g = g.comp q →
    (p = 0 ∧ q = 0 ∧ r = 0) ∨
      (p = LinearMap.id ∧ q = LinearMap.id ∧
        r = LinearMap.id)

private theorem exists_dual_eq_one
    {X : Type*} [AddCommGroup X] [Module K X]
    (x : X) (hx : x ≠ 0) :
    ∃ φ : X →ₗ[K] K, φ x = 1 := by
  have hli : LinearIndependent K (fun _ : Unit ↦ x) :=
    LinearIndependent.of_subsingleton () hx
  obtain ⟨φ, hφ⟩ :=
    Module.exists_dual_forall_apply_eq_one
      (s := Set.univ) (hli.linearIndepOn Set.univ)
  exact ⟨φ, hφ () (Set.mem_univ ())⟩

private theorem rankOneProjection_idempotent
    {X : Type*} [AddCommGroup X] [Module K X]
    (x : X) (φ : X →ₗ[K] K) (hφx : φ x = 1) :
    (LinearMap.smulRight φ x).comp
        (LinearMap.smulRight φ x) =
      LinearMap.smulRight φ x := by
  ext y
  simp [LinearMap.comp_apply, hφx]

private theorem rankOneProjection_ne_zero
    {X : Type*} [AddCommGroup X] [Module K X]
    (x : X) (hx : x ≠ 0) (φ : X →ₗ[K] K) (hφx : φ x = 1) :
    LinearMap.smulRight φ x ≠ 0 := by
  intro hzero
  have hxImage := LinearMap.congr_fun hzero x
  apply hx
  simpa [hφx] using hxImage

private theorem rankOneProjection_ne_id_of_finrank_two_le
    {X : Type*} [AddCommGroup X] [Module K X]
    [FiniteDimensional K X]
    (hX : 2 ≤ Module.finrank K X)
    (x : X) (φ : X →ₗ[K] K) :
    LinearMap.smulRight φ x ≠ LinearMap.id := by
  have hRange : Module.finrank K φ.range ≤ 1 := by
    simpa using φ.range.finrank_le
  have hsum := LinearMap.finrank_range_add_finrank_ker φ
  have hKerPos : 0 < Module.finrank K φ.ker := by
    omega
  letI : Nontrivial φ.ker :=
    Module.nontrivial_of_finrank_pos hKerPos
  obtain ⟨y, hy⟩ := exists_ne (0 : φ.ker)
  have hyVal : y.1 ≠ 0 := by
    intro hyzero
    apply hy
    apply Subtype.ext
    exact hyzero
  intro heq
  have happly := LinearMap.congr_fun heq y.1
  apply hyVal
  simpa [LinearMap.mem_ker.mp y.2] using happly.symm

/-- A surjective representation of the two-arrow chain which is
idempotent indecomposable has source dimension at most one.  This is the
candidate linear-algebraic multiplicity-one core for the length-three
uniserial problem, conditional on a later filtered model which supplies
both surjectivity and idempotent reflection. -/
theorem source_finrank_le_one_of_surjective
    [FiniteDimensional K V] [FiniteDimensional K W]
    [FiniteDimensional K Z]
    {f : V →ₗ[K] W} {g : W →ₗ[K] Z}
    (hf : Function.Surjective f)
    (hg : Function.Surjective g)
    (hchain : IsIdempotentIndecomposableChain f g) :
    Module.finrank K V ≤ 1 := by
  by_contra hVle
  have hV : 2 ≤ Module.finrank K V := by omega
  have hVPos : 0 < Module.finrank K V := by omega
  letI : Nontrivial V :=
    Module.nontrivial_of_finrank_pos hVPos
  by_cases hZzero : Subsingleton Z
  · by_cases hWzero : Subsingleton W
    · obtain ⟨v, hv⟩ := exists_ne (0 : V)
      obtain ⟨α, hαv⟩ := exists_dual_eq_one (K := K) v hv
      let p : V →ₗ[K] V := LinearMap.smulRight α v
      have hpIdem : p.comp p = p :=
        rankOneProjection_idempotent v α hαv
      have hpNe : p ≠ 0 :=
        rankOneProjection_ne_zero v hv α hαv
      have hpNeId : p ≠ LinearMap.id :=
        rankOneProjection_ne_id_of_finrank_two_le hV v α
      have hfzero : f = 0 := by
        ext y
        exact Subsingleton.elim _ _
      have hgzero : g = 0 := by
        ext y
        exact Subsingleton.elim _ _
      rcases hchain p 0 0 hpIdem (by ext; simp) (by ext; simp)
          (by simp [hfzero]) (by simp [hgzero]) with hzero | hone
      · exact hpNe hzero.1
      · exact hpNeId hone.1
    · letI : Nontrivial W := not_subsingleton_iff_nontrivial.mp hWzero
      obtain ⟨w, hw⟩ := exists_ne (0 : W)
      obtain ⟨v, hfv⟩ := hf w
      obtain ⟨β, hβw⟩ := exists_dual_eq_one (K := K) w hw
      let α : V →ₗ[K] K := β.comp f
      let p : V →ₗ[K] V := LinearMap.smulRight α v
      let q : W →ₗ[K] W := LinearMap.smulRight β w
      have hαv : α v = 1 := by simp [α, hfv, hβw]
      have hpIdem : p.comp p = p :=
        rankOneProjection_idempotent v α hαv
      have hqIdem : q.comp q = q :=
        rankOneProjection_idempotent w β hβw
      have hqNe : q ≠ 0 :=
        rankOneProjection_ne_zero w hw β hβw
      have hpNeId : p ≠ LinearMap.id :=
        rankOneProjection_ne_id_of_finrank_two_le hV v α
      have hqf : q.comp f = f.comp p := by
        ext y
        simp [p, q, α, LinearMap.comp_apply, hfv]
      have hgzero : g = 0 := by
        ext y
        exact Subsingleton.elim _ _
      rcases hchain p q 0 hpIdem hqIdem (by ext; simp)
          hqf (by simp [hgzero]) with hzero | hone
      · exact hqNe hzero.2.1
      · exact hpNeId hone.1
  · letI : Nontrivial Z := not_subsingleton_iff_nontrivial.mp hZzero
    obtain ⟨z, hz⟩ := exists_ne (0 : Z)
    obtain ⟨w, hgw⟩ := hg z
    obtain ⟨v, hfv⟩ := hf w
    obtain ⟨γ, hγz⟩ := exists_dual_eq_one (K := K) z hz
    let β : W →ₗ[K] K := γ.comp g
    let α : V →ₗ[K] K := β.comp f
    let p : V →ₗ[K] V := LinearMap.smulRight α v
    let q : W →ₗ[K] W := LinearMap.smulRight β w
    let r : Z →ₗ[K] Z := LinearMap.smulRight γ z
    have hβw : β w = 1 := by simp [β, hgw, hγz]
    have hαv : α v = 1 := by simp [α, hfv, hβw]
    have hpIdem : p.comp p = p :=
      rankOneProjection_idempotent v α hαv
    have hqIdem : q.comp q = q :=
      rankOneProjection_idempotent w β hβw
    have hrIdem : r.comp r = r :=
      rankOneProjection_idempotent z γ hγz
    have hrNe : r ≠ 0 :=
      rankOneProjection_ne_zero z hz γ hγz
    have hpNeId : p ≠ LinearMap.id :=
      rankOneProjection_ne_id_of_finrank_two_le hV v α
    have hqf : q.comp f = f.comp p := by
      ext y
      simp [p, q, α, LinearMap.comp_apply, hfv]
    have hrg : r.comp g = g.comp q := by
      ext y
      simp [q, r, β, LinearMap.comp_apply, hgw]
    rcases hchain p q r hpIdem hqIdem hrIdem hqf hrg with hzero | hone
    · exact hrNe hzero.2.2
    · exact hpNeId hone.1

end TwoStepRankCore

namespace IndecomposableSkeleton

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- The first radical of a length-three uniserial representative has
composition length two. -/
theorem moduleRadical_length_eq_two_of_isLengthThreeUniserial
    {x : ι} (hx : σ.IsLengthThreeUniserial x) :
    Module.length R (σ.moduleRadical x) = 2 := by
  letI : IsArtinian R (σ.obj x) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (σ.finiteLength x)).2
  have htotal : Module.length R (σ.obj x) = 3 := by
    rw [← σ.coe_compositionLength x, hx.1]
    norm_num
  have htopSimple : IsSimpleModule R (σ.moduleTop x) :=
    σ.moduleTop_isSimple_of_isUniserial hx.2
  have htopLength : Module.length R (σ.moduleTop x) = 1 :=
    Module.length_eq_one_iff.mpr htopSimple
  have hlength :
      Module.length R (σ.obj x) =
        Module.length R (σ.moduleRadical x) +
          Module.length R (σ.moduleTop x) :=
    Module.length_eq_add_of_exact
      (σ.moduleRadical x).subtype
      (σ.moduleRadical x).mkQ
      (σ.moduleRadical x).subtype_injective
      (σ.moduleRadical x).mkQ_surjective
      (LinearMap.exact_subtype_mkQ (σ.moduleRadical x))
  rw [htotal, htopLength] at hlength
  apply WithTop.add_right_cancel ENat.one_ne_top
  calc
    Module.length R (σ.moduleRadical x) + 1 = 3 := hlength.symm
    _ = 2 + 1 := by norm_num

/-- The second radical of a length-three uniserial representative is
simple. -/
theorem secondModuleRadical_isSimple_of_isLengthThreeUniserial
    {x : ι} (hx : σ.IsLengthThreeUniserial x) :
    IsSimpleModule R
      (Module.jacobson R (σ.moduleRadical x)) := by
  letI : IsNoetherian R (σ.obj x) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (σ.finiteLength x)).1
  letI : IsArtinian R (σ.obj x) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (σ.finiteLength x)).2
  let J : Submodule R (σ.obj x) := σ.moduleRadical x
  let J2 : Submodule R J := Module.jacobson R J
  have hJLength : Module.length R J = 2 :=
    σ.moduleRadical_length_eq_two_of_isLengthThreeUniserial hx
  letI : Nontrivial J :=
    Module.length_pos_iff.mp (by rw [hJLength]; norm_num)
  have hJuniserial : IsUniserialModule R J :=
    hx.2.submodule J
  have hJindec : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R J :=
    hJuniserial.isIndecomposableModule
  letI : IsNoetherian R J := by infer_instance
  letI : IsArtinian R J := by infer_instance
  have htopSimple : IsSimpleModule R (J ⧸ J2) :=
    QuotientSubmoduleEquidistribution.BottomTwoSimpleTop.simple_top_of_isIndecomposableModule_of_length_eq_two
      hJindec hJLength
  have htopLength : Module.length R (J ⧸ J2) = 1 :=
    Module.length_eq_one_iff.mpr htopSimple
  have hlength :
      Module.length R J =
        Module.length R J2 + Module.length R (J ⧸ J2) :=
    Module.length_eq_add_of_exact
      J2.subtype J2.mkQ J2.subtype_injective J2.mkQ_surjective
      (LinearMap.exact_subtype_mkQ J2)
  have hJ2Length : Module.length R J2 = 1 := by
    rw [hJLength, htopLength] at hlength
    apply WithTop.add_right_cancel ENat.one_ne_top
    calc
      Module.length R J2 + 1 = 2 := hlength.symm
      _ = 1 + 1 := by norm_num
  exact Module.length_eq_one_iff.mp hJ2Length

/-- The radical of the length-three uniserial source is the chosen
length-two submodule, not merely an abstract module with the same length. -/
noncomputable def moduleRadicalLinearEquivLengthTwoSubmodule
    {x : ι} (hx : σ.IsLengthThreeUniserial x)
    (W : σ.LengthTwoSubmodule x) :
    σ.moduleRadical x ≃ₗ[R] σ.obj W.index := by
  letI : IsNoetherian R (σ.obj x) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (σ.finiteLength x)).1
  letI : IsArtinian R (σ.obj x) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (σ.finiteLength x)).2
  letI : Mono W.map := W.mono
  have hWInjective : Function.Injective W.map.hom.hom :=
    (_root_.QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_mono_iff_injective
      W.map).mp inferInstance
  let A : Submodule R (σ.obj x) := LinearMap.range W.map.hom.hom
  let eA : σ.obj W.index ≃ₗ[R] A :=
    LinearEquiv.ofInjective W.map.hom.hom hWInjective
  have hAlength : Module.length R A = 2 := by
    calc
      Module.length R A = Module.length R (σ.obj W.index) :=
        (LinearEquiv.length_eq eA).symm
      _ = 2 := by
        rw [← σ.coe_compositionLength W.index, W.length_two]
        norm_num
  have hJlength : Module.length R (σ.moduleRadical x) = 2 :=
    σ.moduleRadical_length_eq_two_of_isLengthThreeUniserial hx
  have hAJ : A = σ.moduleRadical x :=
    hx.2.eq_of_length_eq (hAlength.trans hJlength.symm)
  exact
    (LinearEquiv.ofEq (σ.moduleRadical x) A hAJ.symm).trans eA.symm

/-- On radicals, a finite power of the length-three source is a finite
power of any chosen length-two uniserial submodule representative. -/
noncomputable def moduleRadicalPowerLinearEquivLengthTwoSubmodulePower
    {x : ι} (hx : σ.IsLengthThreeUniserial x)
    (W : σ.LengthTwoSubmodule x)
    (J : FintypeCat.{0}) :
    Module.jacobson R
        (σ.sumOver J (fun _ : J ↦ x)) ≃ₗ[R]
      σ.sumOver J (fun _ : J ↦ W.index) := by
  letI : Fintype J := FintypeCat.fintype
  let eSource :
      σ.sumOver J (fun _ : J ↦ x) ≃ₗ[R]
        (∀ _ : J, σ.obj x) :=
    FGModuleCat.isoToLinearEquiv
      (_root_.QuotientSubmoduleEquidistribution.IndecomposableSkeleton.biproductIsoPiFG _)
  let eRadical :
      Module.jacobson R
          (σ.sumOver J (fun _ : J ↦ x)) ≃ₗ[R]
        (∀ _ : J, σ.moduleRadical x) :=
    (radicalRestrictionEquiv eSource).trans
      (radicalFinitePiEquiv (fun _ : J ↦ σ.obj x))
  let eComponents :
      (∀ _ : J, σ.moduleRadical x) ≃ₗ[R]
        (∀ _ : J, σ.obj W.index) :=
    LinearEquiv.piCongrRight
      (fun _ : J ↦
        σ.moduleRadicalLinearEquivLengthTwoSubmodule hx W)
  let eTarget :
      σ.sumOver J (fun _ : J ↦ W.index) ≃ₗ[R]
        (∀ _ : J, σ.obj W.index) :=
    FGModuleCat.isoToLinearEquiv
      (_root_.QuotientSubmoduleEquidistribution.IndecomposableSkeleton.biproductIsoPiFG _)
  exact (eRadical.trans eComponents).trans eTarget.symm

/-- The top of a finite skeleton biproduct is the product of the tops of
its indecomposable components. -/
noncomputable def moduleTopSumOverLinearEquiv
    (J : FintypeCat.{0}) (a : J → ι) :
    ((σ.sumOver J a) ⧸
        Module.jacobson R (σ.sumOver J a)) ≃ₗ[R]
      (∀ t : J, σ.moduleTop (a t)) := by
  letI : Fintype J := FintypeCat.fintype
  let e :
      σ.sumOver J a ≃ₗ[R] (∀ t : J, σ.obj (a t)) :=
    FGModuleCat.isoToLinearEquiv
      (_root_.QuotientSubmoduleEquidistribution.IndecomposableSkeleton.biproductIsoPiFG _)
  exact
    (moduleTopLinearEquiv e).trans
      (moduleTopFinitePiEquiv (fun t : J ↦ σ.obj (a t)))

/-- Isotypy of all component tops passes to the top of their finite
biproduct. -/
theorem moduleTop_sumOver_isIsotypicOfType
    (J : FintypeCat.{0}) (a : J → ι)
    {S : Type*} [AddCommGroup S] [Module R S]
    (hcomponent :
      ∀ t : J, IsIsotypicOfType R (σ.moduleTop (a t)) S) :
    IsIsotypicOfType R
      ((σ.sumOver J a) ⧸ Module.jacobson R (σ.sumOver J a)) S := by
  letI : Fintype J := FintypeCat.fintype
  let e := σ.moduleTopSumOverLinearEquiv J a
  have hproduct :
      IsIsotypicOfType R (∀ t : J, σ.moduleTop (a t)) S :=
    QuotientSubmoduleEquidistribution.LengthTwoGabrielBridge.isIsotypicOfType_pi hcomponent
  exact e.isIsotypicOfType_iff.mpr hproduct

/-- The second radical of a finite power of a length-three uniserial
representative is semisimple. -/
theorem secondModuleRadical_power_isSemisimple
    {x : ι} (hx : σ.IsLengthThreeUniserial x)
    (J : FintypeCat.{0}) :
    IsSemisimpleModule R
      (Module.jacobson R
        (Module.jacobson R
          (σ.sumOver J (fun _ : J ↦ x)))) := by
  letI : Fintype J := FintypeCat.fintype
  let e :
      σ.sumOver J (fun _ : J ↦ x) ≃ₗ[R]
        (∀ _ : J, σ.obj x) :=
    FGModuleCat.isoToLinearEquiv
      (_root_.QuotientSubmoduleEquidistribution.IndecomposableSkeleton.biproductIsoPiFG _)
  let e₂ :
      Module.jacobson R
          (Module.jacobson R
            (σ.sumOver J (fun _ : J ↦ x))) ≃ₗ[R]
        (∀ _ : J,
          Module.jacobson R (Module.jacobson R (σ.obj x))) :=
    (radicalRestrictionEquiv (radicalRestrictionEquiv e)).trans
      (secondRadicalFinitePiEquiv (fun _ : J ↦ σ.obj x))
  letI (t : J) :
      IsSimpleModule R
        (Module.jacobson R (Module.jacobson R (σ.obj x))) :=
    σ.secondModuleRadical_isSimple_of_isLengthThreeUniserial hx
  exact e₂.isSemisimpleModule_iff.mpr inferInstance

/-- The second radical of a finite power is isotypic of the unique
second-radical simple of the uniserial source. -/
theorem secondModuleRadical_power_isIsotypic
    {x : ι} (hx : σ.IsLengthThreeUniserial x)
    (J : FintypeCat.{0}) :
    IsIsotypicOfType R
      (Module.jacobson R
        (Module.jacobson R
          (σ.sumOver J (fun _ : J ↦ x))))
      (Module.jacobson R (Module.jacobson R (σ.obj x))) := by
  letI : Fintype J := FintypeCat.fintype
  let e :
      σ.sumOver J (fun _ : J ↦ x) ≃ₗ[R]
        (∀ _ : J, σ.obj x) :=
    FGModuleCat.isoToLinearEquiv
      (_root_.QuotientSubmoduleEquidistribution.IndecomposableSkeleton.biproductIsoPiFG _)
  let e₂ :
      Module.jacobson R
          (Module.jacobson R
            (σ.sumOver J (fun _ : J ↦ x))) ≃ₗ[R]
        (∀ _ : J,
          Module.jacobson R (Module.jacobson R (σ.obj x))) :=
    (radicalRestrictionEquiv (radicalRestrictionEquiv e)).trans
      (secondRadicalFinitePiEquiv (fun _ : J ↦ σ.obj x))
  letI :
      IsSimpleModule R
        (Module.jacobson R (Module.jacobson R (σ.obj x))) :=
    σ.secondModuleRadical_isSimple_of_isLengthThreeUniserial hx
  have hproduct :
      IsIsotypicOfType R
        (∀ _ : J,
          Module.jacobson R (Module.jacobson R (σ.obj x)))
        (Module.jacobson R (Module.jacobson R (σ.obj x))) :=
    QuotientSubmoduleEquidistribution.LengthTwoGabrielBridge.isIsotypicOfType_pi
      (fun _ ↦ IsIsotypicOfType.of_isSimpleModule R _)
  exact e₂.isIsotypicOfType_iff.mpr hproduct

/-- Every object in a quotient-chain support is generated by its
length-three source alone. -/
theorem LengthThreeQuotientChain.support_subset_qClosure_singleton
    {x : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeQuotientChain x) :
    C.support ⊆ σ.qClosure ({x.1} : Set ι) := by
  intro i hi
  obtain ⟨f, hf⟩ := C.exists_epi_to_mem_support σ hi
  let a : Fin 1 → ι := fun _ ↦ x.1
  let g :
      σ.sumOver (FintypeCat.of (Fin 1)) a ⟶ σ.obj i :=
    (biproductUniqueIso fun t : Fin 1 ↦ σ.obj (a t)).hom ≫ f
  refine ⟨{
    index := FintypeCat.of (Fin 1)
    label := a
    mem := fun _ ↦ by simp [a]
    map := g
    epi := ?_ }⟩
  letI : Epi f := hf
  dsimp only [g]
  infer_instance

/-- The collective quotient closure of the three-object chain is exactly
the collective quotient closure of its length-three source. -/
theorem LengthThreeQuotientChain.qClosure_support_eq_singleton
    {x : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeQuotientChain x) :
    σ.qClosure C.support = σ.qClosure ({x.1} : Set ι) := by
  apply Set.Subset.antisymm
  · intro i hi
    have hmono :=
      σ.qClosure.monotone
        (C.support_subset_qClosure_singleton σ)
        hi
    simpa only [σ.qClosure.idempotent] using hmono
  · apply σ.qClosure.monotone
    intro i hi
    have hix : i = x.1 := by simpa using hi
    subst i
    simp [LengthThreeQuotientChain.support]

/-- Hence every generated target already has a presentation by copies of
the length-three source alone. -/
theorem inFac_singleton_source_of_inFac_quotientChain
    {x : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeQuotientChain x)
    {j : ι} (hj : σ.InFac C.support (σ.obj j)) :
    σ.InFac ({x.1} : Set ι) (σ.obj j) := by
  have hj' : j ∈ σ.qClosure C.support := hj
  rw [C.qClosure_support_eq_singleton σ] at hj'
  exact hj'

/-- A singleton `Fac` presentation can be rewritten literally as an
epimorphism from a finite biproduct of copies of the selected object. -/
theorem exists_epi_power_of_inFac_singleton
    {x j : ι} (hj : σ.InFac ({x} : Set ι) (σ.obj j)) :
    ∃ (J : FintypeCat.{0})
        (f : σ.sumOver J (fun _ : J ↦ x) ⟶ σ.obj j),
      Epi f := by
  obtain ⟨P⟩ := hj
  let e :
      σ.sumOver P.index (fun _ : P.index ↦ x) ≅
        σ.sumOver P.index P.label :=
    biproduct.mapIso fun t ↦ eqToIso (by
      have htx : P.label t = x := by simpa using P.mem t
      exact congrArg σ.obj htx.symm)
  let f :
      σ.sumOver P.index (fun _ : P.index ↦ x) ⟶ σ.obj j :=
    e.hom ≫ P.map
  refine ⟨P.index, f, ?_⟩
  letI : Epi P.map := P.epi
  dsimp only [f]
  infer_instance

/-- Every target generated by a quotient chain is therefore an
epimorphic image of a finite power of the length-three source. -/
theorem exists_epi_power_source_of_inFac_quotientChain
    {x : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeQuotientChain x)
    {j : ι} (hj : σ.InFac C.support (σ.obj j)) :
    ∃ (J : FintypeCat.{0})
        (f : σ.sumOver J (fun _ : J ↦ x.1) ⟶ σ.obj j),
      Epi f :=
  σ.exists_epi_power_of_inFac_singleton
    (σ.inFac_singleton_source_of_inFac_quotientChain C hj)

/-- A power presentation together with its two induced radical
surjections.  This is the exact two-layer input for a radical-matrix
argument. -/
structure TwoStepPowerPresentation (x j : ι) where
  index : FintypeCat.{0}
  map : σ.sumOver index (fun _ : index ↦ x) ⟶ σ.obj j
  epi : Epi map
  radical_surjective :
    Function.Surjective (radicalRestriction map.hom.hom)
  secondRadical_surjective :
    Function.Surjective
      (radicalRestriction (radicalRestriction map.hom.hom))

/-- Every indecomposable generated by the quotient chain has a finite
power presentation which is surjective on the first two radical layers. -/
theorem exists_twoStepPowerPresentation_of_inFac_quotientChain
    {x : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeQuotientChain x)
    {j : ι} (hj : σ.InFac C.support (σ.obj j)) :
    Nonempty (σ.TwoStepPowerPresentation x.1 j) := by
  obtain ⟨J, f, hf⟩ :=
    σ.exists_epi_power_source_of_inFac_quotientChain C hj
  letI (t : J) : IsArtinian R (σ.obj x.1) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (σ.finiteLength x.1)).2
  let e :
      σ.sumOver J (fun _ : J ↦ x.1) ≅
        FGModuleCat.of R (∀ _ : J, σ.obj x.1) :=
    _root_.QuotientSubmoduleEquidistribution.IndecomposableSkeleton.biproductIsoPiFG _
  letI : IsArtinian R (σ.sumOver J (fun _ : J ↦ x.1)) :=
    (LinearEquiv.isArtinian_iff
      (FGModuleCat.isoToLinearEquiv e)).mpr inferInstance
  letI : Epi f := hf
  have hsurj : Function.Surjective f.hom.hom :=
    (_root_.QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_epi_iff_surjective
      f).mp inferInstance
  exact ⟨{
    index := J
    map := f
    epi := hf
    radical_surjective :=
      radicalRestriction_surjective f.hom.hom hsurj
    secondRadical_surjective :=
      secondRadicalRestriction_surjective f.hom.hom hsurj }⟩

/-- The radical of a target with a power presentation is generated by the
chosen length-two submodule of the length-three source alone. -/
theorem moduleRadical_inFac_singleton_lengthTwoSubmodule
    {x j : ι} (hx : σ.IsLengthThreeUniserial x)
    (W : σ.LengthTwoSubmodule x)
    (P : σ.TwoStepPowerPresentation x j) :
    σ.InFac ({W.index} : Set ι)
      (FGModuleCat.of R (σ.moduleRadical j)) := by
  let e :
      Module.jacobson R
          (σ.sumOver P.index (fun _ : P.index ↦ x)) ≃ₗ[R]
        σ.sumOver P.index (fun _ : P.index ↦ W.index) :=
    σ.moduleRadicalPowerLinearEquivLengthTwoSubmodulePower
      hx W P.index
  let fLinear :
      σ.sumOver P.index (fun _ : P.index ↦ W.index) →ₗ[R]
        σ.moduleRadical j :=
    (radicalRestriction P.map.hom.hom).comp e.symm.toLinearMap
  let f :
      σ.sumOver P.index (fun _ : P.index ↦ W.index) ⟶
        FGModuleCat.of R (σ.moduleRadical j) :=
    FGModuleCat.ofHom fLinear
  have hfSurjective : Function.Surjective f.hom.hom := by
    intro y
    obtain ⟨z, hz⟩ := P.radical_surjective y
    refine ⟨e z, ?_⟩
    change
      radicalRestriction P.map.hom.hom (e.symm (e z)) = y
    rw [e.symm_apply_apply, hz]
  have hfEpi : Epi f :=
    (_root_.QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_epi_iff_surjective
      f).mpr hfSurjective
  exact ⟨{
    index := P.index
    label := fun _ : P.index ↦ W.index
    mem := fun _ ↦ by simp
    map := f
    epi := hfEpi }⟩

/-- Once the already-formalized length-two pair theorem is supplied for
the radical submodule, the whole first radical of a generated target has
an additive normal form using only that length-two module and its top. -/
theorem moduleRadical_inAdd_lengthTwoPair
    {x j : ι} (hx : σ.IsLengthThreeUniserial x)
    (W : σ.LengthTwoSubmodule x)
    (Q : σ.SimpleQuotient W.index)
    (hclosed :
      σ.qClosure.IsClosed ({W.index, Q.index} : Set ι))
    (P : σ.TwoStepPowerPresentation x j) :
    σ.InAdd ({W.index, Q.index} : Set ι)
      (FGModuleCat.of R (σ.moduleRadical j)) := by
  have hfacSingleton :=
    σ.moduleRadical_inFac_singleton_lengthTwoSubmodule hx W P
  have hfacPair :
      σ.InFac ({W.index, Q.index} : Set ι)
        (FGModuleCat.of R (σ.moduleRadical j)) :=
    hfacSingleton.map fun F ↦ F.of_subset σ (by
      intro i hi
      have hiW : i = W.index := by simpa using hi
      subst i
      simp)
  have hadd := σ.inAdd_qSet_of_inFac hfacPair
  change
    σ.InAdd (σ.qClosure ({W.index, Q.index} : Set ι))
      (FGModuleCat.of R (σ.moduleRadical j)) at hadd
  rwa [hclosed.closure_eq] at hadd

/-- An additive normal form for the first radical fixes its semisimple
top: the middle Loewy layer is isotypic of the top of the chosen
length-two radical submodule. -/
theorem middleLoewyLayer_isIsotypicOfType_of_inAdd_lengthTwoPair
    {j : ι}
    (W : σ.LengthTwoSubmodule j) -- only the index and length are used
    (Q : σ.SimpleQuotient W.index)
    {X : ι}
    (hadd :
      σ.InAdd ({W.index, Q.index} : Set ι)
        (FGModuleCat.of R (σ.moduleRadical X))) :
    IsIsotypicOfType R
      ((σ.moduleRadical X) ⧸
        Module.jacobson R (σ.moduleRadical X))
      (σ.obj Q.index) := by
  obtain ⟨P⟩ := hadd
  let eRadical :
      σ.moduleRadical X ≃ₗ[R]
        σ.sumOver P.index P.label :=
    FGModuleCat.isoToLinearEquiv P.iso
  let eTop :
      ((σ.moduleRadical X) ⧸
          Module.jacobson R (σ.moduleRadical X)) ≃ₗ[R]
        ((σ.sumOver P.index P.label) ⧸
          Module.jacobson R (σ.sumOver P.index P.label)) :=
    moduleTopLinearEquiv eRadical
  have hsum :
      IsIsotypicOfType R
        ((σ.sumOver P.index P.label) ⧸
          Module.jacobson R (σ.sumOver P.index P.label))
        (σ.obj Q.index) := by
    apply σ.moduleTop_sumOver_isIsotypicOfType
    intro t
    have hlabelFac :
        σ.InFac ({W.index, Q.index} : Set ι)
          (σ.obj (P.label t)) :=
      σ.subset_qSet ({W.index, Q.index} : Set ι) (P.mem t)
    exact
      QuotientSubmoduleEquidistribution.LengthTwoGabrielBridge.IndecomposableSkeleton.moduleTop_isIsotypicOfType_of_inFac_length_two_pair
        σ W.length_two Q hlabelFac
  exact eTop.isIsotypicOfType_iff.mpr hsum

/-- Consequently, after invoking the length-two pair closure theorem,
all three Loewy layers of a generated target have fixed simple types. -/
theorem middleLoewyLayer_isIsotypicOfType_of_twoStepPowerPresentation
    {x j : ι} (hx : σ.IsLengthThreeUniserial x)
    (W : σ.LengthTwoSubmodule x)
    (Q : σ.SimpleQuotient W.index)
    (hclosed :
      σ.qClosure.IsClosed ({W.index, Q.index} : Set ι))
    (P : σ.TwoStepPowerPresentation x j) :
    IsIsotypicOfType R
      ((σ.moduleRadical j) ⧸
        Module.jacobson R (σ.moduleRadical j))
      (σ.obj Q.index) := by
  exact
    σ.middleLoewyLayer_isIsotypicOfType_of_inAdd_lengthTwoPair
      W Q (σ.moduleRadical_inAdd_lengthTwoPair hx W Q hclosed P)

/-- Unconditionally, the second radical of every indecomposable generated
by the uniserial quotient chain is semisimple. -/
theorem secondModuleRadical_isSemisimple_of_inFac_quotientChain
    {x : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeQuotientChain x)
    {j : ι} (hj : σ.InFac C.support (σ.obj j)) :
    IsSemisimpleModule R
      (Module.jacobson R (σ.moduleRadical j)) := by
  obtain ⟨P⟩ :=
    σ.exists_twoStepPowerPresentation_of_inFac_quotientChain C hj
  letI :
      IsSemisimpleModule R
        (Module.jacobson R
          (Module.jacobson R
            (σ.sumOver P.index (fun _ : P.index ↦ x.1)))) :=
    σ.secondModuleRadical_power_isSemisimple x.2 P.index
  exact IsSemisimpleModule.of_surjective
    (radicalRestriction (radicalRestriction P.map.hom.hom))
    P.secondRadical_surjective

/-- Unconditionally, that semisimple second radical is isotypic of the
source's unique second-radical simple. -/
theorem secondModuleRadical_isIsotypic_of_inFac_quotientChain
    {x : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeQuotientChain x)
    {j : ι} (hj : σ.InFac C.support (σ.obj j)) :
    IsIsotypicOfType R
      (Module.jacobson R (σ.moduleRadical j))
      (Module.jacobson R (σ.moduleRadical x.1)) := by
  obtain ⟨P⟩ :=
    σ.exists_twoStepPowerPresentation_of_inFac_quotientChain C hj
  letI :
      IsSemisimpleModule R
        (Module.jacobson R
          (Module.jacobson R
            (σ.sumOver P.index (fun _ : P.index ↦ x.1)))) :=
    σ.secondModuleRadical_power_isSemisimple x.2 P.index
  have hsource :
      IsIsotypicOfType R
        (Module.jacobson R
          (Module.jacobson R
            (σ.sumOver P.index (fun _ : P.index ↦ x.1))))
        (Module.jacobson R (Module.jacobson R (σ.obj x.1))) :=
    σ.secondModuleRadical_power_isIsotypic x.2 P.index
  exact
    QuotientSubmoduleEquidistribution.LengthTwoGabrielBridge.IsIsotypicOfType.of_surjective_of_semisimple
      hsource
      (radicalRestriction (radicalRestriction P.map.hom.hom))
      P.secondRadical_surjective

/-- Every target generated by the quotient chain has zero third radical.
Equivalently, collective generation by a length-three uniserial source
cannot create a fourth Loewy layer. -/
theorem thirdModuleRadical_eq_bot_of_inFac_quotientChain
    {x : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeQuotientChain x)
    {j : ι} (hj : σ.InFac C.support (σ.obj j)) :
    Module.jacobson R
        (Module.jacobson R (σ.moduleRadical j)) = ⊥ := by
  obtain ⟨P⟩ :=
    σ.exists_twoStepPowerPresentation_of_inFac_quotientChain C hj
  let sourceSecond :=
    Module.jacobson R
      (Module.jacobson R
        (σ.sumOver P.index (fun _ : P.index ↦ x.1)))
  let targetSecond :=
    Module.jacobson R (σ.moduleRadical j)
  let f₂ : sourceSecond →ₗ[R] targetSecond :=
    radicalRestriction (radicalRestriction P.map.hom.hom)
  letI (t : P.index) : IsArtinian R (σ.obj x.1) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (σ.finiteLength x.1)).2
  let e :
      σ.sumOver P.index (fun _ : P.index ↦ x.1) ≃ₗ[R]
        (∀ _ : P.index, σ.obj x.1) :=
    FGModuleCat.isoToLinearEquiv
      (_root_.QuotientSubmoduleEquidistribution.IndecomposableSkeleton.biproductIsoPiFG _)
  letI : IsArtinian R
      (σ.sumOver P.index (fun _ : P.index ↦ x.1)) :=
    (LinearEquiv.isArtinian_iff e).mpr inferInstance
  letI : IsArtinian R sourceSecond := by
    dsimp only [sourceSecond]
    infer_instance
  letI : IsSemisimpleModule R sourceSecond := by
    dsimp only [sourceSecond]
    exact σ.secondModuleRadical_power_isSemisimple x.2 P.index
  have hmap :
      Submodule.map f₂ (Module.jacobson R sourceSecond) =
        Module.jacobson R targetSecond :=
    QuotientSubmoduleEquidistribution.LengthTwoGabrielBridge.map_jacobson_of_surjective_of_isArtinian
      f₂ P.secondRadical_surjective
  have hsourceRadical : Module.jacobson R sourceSecond = ⊥ :=
    IsSemisimpleModule.jacobson_eq_bot R sourceSecond
  change Module.jacobson R targetSecond = ⊥
  calc
    Module.jacobson R targetSecond =
        Submodule.map f₂ (Module.jacobson R sourceSecond) := hmap.symm
    _ = Submodule.map f₂ ⊥ := congrArg (Submodule.map f₂) hsourceRadical
    _ = ⊥ := Submodule.map_bot f₂

/-- The exact collective obstruction can therefore be stated using only
powers of the length-three source. -/
def SingletonFacTargetsHaveSimpleTop
    (x : σ.LengthThreeUniserialIndex) : Prop :=
  ∀ {j : ι},
    σ.InFac ({x.1} : Set ι) (σ.obj j) →
      IsSimpleModule R (σ.moduleTop j)

theorem quotientChainFacTargetsHaveSimpleTop_iff_singleton
    {x : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeQuotientChain x) :
    σ.QuotientChainFacTargetsHaveSimpleTop C ↔
      σ.SingletonFacTargetsHaveSimpleTop x := by
  constructor
  · intro h j hj
    apply h
    exact hj.map fun P ↦ P.of_subset σ (by
      intro i hi
      have hix : i = x.1 := by simpa using hi
      subst i
      simp [LengthThreeQuotientChain.support])
  · intro h j hj
    exact h (σ.inFac_singleton_source_of_inFac_quotientChain C hj)

theorem qClosure_isClosed_quotientChain_iff_singletonTargetsHaveSimpleTop
    {x : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeQuotientChain x) :
    σ.qClosure.IsClosed C.support ↔
      σ.SingletonFacTargetsHaveSimpleTop x := by
  rw [σ.qClosure_isClosed_quotientChain_iff_targetsHaveSimpleTop C,
    σ.quotientChainFacTargetsHaveSimpleTop_iff_singleton C]

end IndecomposableSkeleton

namespace LengthThreePaperSpecialization

universe x

/-- Under the paper's hypotheses, the existing length-two Gabriel theorem
discharges the only hypothesis in the radical additive-normal-form
reduction. -/
theorem moduleRadical_inAdd_lengthTwoPair
    (K A : Type x)
    [Field K] [IsAlgClosed K]
    [Ring A] [Algebra K A] [FiniteDimensional K A] :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K A
    ∀ {ι : Type x} [Finite ι]
      (σ : IndecomposableSkeleton.{x, x, x} Aᵐᵒᵖ ι)
      {u j : ι} (_hu : σ.IsLengthThreeUniserial u)
      (W : σ.LengthTwoSubmodule u)
      (Q : σ.SimpleQuotient W.index)
      (_T : σ.SimpleSubmodule W.index)
      (_P : σ.TwoStepPowerPresentation u j),
      σ.InAdd ({W.index, Q.index} : Set ι)
        (FGModuleCat.of Aᵐᵒᵖ (σ.moduleRadical j)) := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K A
  intro ι _ σ u j hu W Q T P
  exact
    σ.moduleRadical_inAdd_lengthTwoPair hu W Q
      (QuotientSubmoduleEquidistribution.LoewyTwoGabrielClassification.qClosure_isClosed_length_two_top_pair
        K A σ W.length_two Q T)
      P

/-- Hence the paper hypotheses fix the middle Loewy-layer type as well
as the already-fixed top and bottom types. -/
theorem middleLoewyLayer_isIsotypicOfType
    (K A : Type x)
    [Field K] [IsAlgClosed K]
    [Ring A] [Algebra K A] [FiniteDimensional K A] :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K A
    ∀ {ι : Type x} [Finite ι]
      (σ : IndecomposableSkeleton.{x, x, x} Aᵐᵒᵖ ι)
      {u j : ι} (_hu : σ.IsLengthThreeUniserial u)
      (W : σ.LengthTwoSubmodule u)
      (Q : σ.SimpleQuotient W.index)
      (_T : σ.SimpleSubmodule W.index)
      (_P : σ.TwoStepPowerPresentation u j),
      IsIsotypicOfType Aᵐᵒᵖ
        ((σ.moduleRadical j) ⧸
          Module.jacobson Aᵐᵒᵖ (σ.moduleRadical j))
        (σ.obj Q.index) := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K A
  intro ι _ σ u j hu W Q T P
  exact
    σ.middleLoewyLayer_isIsotypicOfType_of_inAdd_lengthTwoPair
      W Q (moduleRadical_inAdd_lengthTwoPair K A σ hu W Q T P)

end LengthThreePaperSpecialization

end QuotientSubmoduleEquidistribution
