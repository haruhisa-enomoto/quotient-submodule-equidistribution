import QuotientSubmoduleEquidistribution.RepresentationTheory.PrincipalRightIdealSurvival
import QuotientSubmoduleEquidistribution.RepresentationTheory.LengthTwoGabrielBridge
import QuotientSubmoduleEquidistribution.RepresentationTheory.SplitBasicGabrielArrowRealization

/-!
# Simple tops of cyclic quotients of vertex projectives

If `M →→ N` is a surjection from an Artinian module, its Jacobson radical
maps onto the Jacobson radical of `N`.  Consequently, a nonzero quotient of a
module with simple top has the same simple top.

For cyclic right ideals this applies to the multiplication map `eA → cA`
when `c e = c`.  This gives the presentation-free simple-top input needed by
the lollipop loop-square argument.
-/

noncomputable section

open CategoryTheory MulOpposite

namespace QuotientSubmoduleEquidistribution.Tsukamoto

universe u v w

variable {R : Type u} [Ring R]

/-- A surjection from an Artinian module with simple top onto a nonzero
finite module induces an equivalence of their tops. -/
noncomputable def topLinearEquivOfSurjectiveOfSimpleTop
    {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [IsArtinian R M] [Module.Finite R N] [Nontrivial N]
    [IsSimpleModule R (M ⧸ Module.jacobson R M)]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    (M ⧸ Module.jacobson R M) ≃ₗ[R]
      (N ⧸ Module.jacobson R N) := by
  let JM := Module.jacobson R M
  let JN := Module.jacobson R N
  have hmap : Submodule.map f JM = JN :=
    QuotientSubmoduleEquidistribution.LengthTwoGabrielBridge.map_jacobson_of_surjective_of_isArtinian
      f hf
  let fTop : (M ⧸ JM) →ₗ[R] (N ⧸ JN) :=
    JM.mapQ JN f (by
      intro y hy
      rw [← hmap]
      exact ⟨y, hy, rfl⟩)
  have hfTop : Function.Surjective fTop := by
    intro z
    refine Quotient.inductionOn' z ?_
    intro y
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨JM.mkQ x, rfl⟩
  letI : Nontrivial (N ⧸ JN) :=
    Submodule.Quotient.nontrivial_iff.mpr
      (Module.jacobson_lt_top R N).ne
  have hfTopNe : fTop ≠ 0 := by
    intro hzero
    obtain ⟨z, hz⟩ := exists_ne (0 : N ⧸ JN)
    obtain ⟨y, rfl⟩ := hfTop z
    exact hz (by rw [hzero]; rfl)
  exact LinearEquiv.ofBijective fTop
    ⟨fTop.injective_of_ne_zero hfTopNe, hfTop⟩

variable {A : Type u} [Ring A]

/-- Right multiplication by `c` sends the cyclic right ideal `eA` to
`cA`. -/
def principalRightIdealToCyclic
    {e c : A} :
    cyclicRightIdealFG e →ₗ[Aᵐᵒᵖ] cyclicRightIdealFG c where
  toFun y :=
    ⟨y.1 * op c,
      (principalRightIdeal c).mul_mem_left y.1
        (Ideal.subset_span (Set.mem_singleton (op c)))⟩
  map_add' x y := Subtype.ext (add_mul x.1 y.1 (op c))
  map_smul' r x := Subtype.ext (mul_assoc r x.1 (op c))

/-- The multiplication map `eA → cA` is surjective when `c e = c`. -/
theorem principalRightIdealToCyclic_surjective
    {e c : A} (hce : c * e = c) :
    Function.Surjective
      (principalRightIdealToCyclic (e := e) (c := c)) := by
  rw [← LinearMap.range_eq_top]
  apply top_unique
  rintro ⟨z, hz⟩ -
  induction hz using Submodule.span_induction with
  | mem z hz =>
      let ee : cyclicRightIdealFG e :=
        ⟨op e, Ideal.subset_span (Set.mem_singleton (op e))⟩
      refine ⟨ee, ?_⟩
      apply Subtype.ext
      change op e * op c = z
      rw [← op_mul, hce, Set.mem_singleton_iff.mp hz]
  | zero =>
      refine ⟨0, ?_⟩
      apply Subtype.ext
      change 0 * op c = 0
      simp
  | add x y hx hy hxRange hyRange =>
      obtain ⟨x', hx'⟩ := hxRange
      obtain ⟨y', hy'⟩ := hyRange
      refine ⟨x' + y', ?_⟩
      apply Subtype.ext
      have hxval := congrArg Subtype.val hx'
      have hyval := congrArg Subtype.val hy'
      change x'.1 * op c = x at hxval
      change y'.1 * op c = y at hyval
      change (x'.1 + y'.1) * op c = x + y
      rw [add_mul]
      rw [hxval, hyval]
  | smul r x hx hxRange =>
      obtain ⟨x', hx'⟩ := hxRange
      refine ⟨r • x', ?_⟩
      apply Subtype.ext
      have hxval := congrArg Subtype.val hx'
      change x'.1 * op c = x at hxval
      change (r * x'.1) * op c = r * x
      rw [mul_assoc]
      rw [hxval]

end QuotientSubmoduleEquidistribution.Tsukamoto

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore

universe u v w

variable {K A : Type u} [Field K] [Ring A] [Algebra K A]
  [FiniteDimensional K A] [IsNoetherianRing Aᵐᵒᵖ]
  {kappa : Type v} [Finite kappa]
  (tau : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, v, u} Aᵐᵒᵖ kappa)
  {Arrow : Type w}
  {source target : Arrow → tau.SimpleIndex}
  (G : SplitBasicGabrielArrowRealization tau source target)

omit [Finite kappa] in
include K in
/-- Every nonzero cyclic quotient of a vertex projective, cut out by an
element `c` satisfying `c e = c`, has the same simple top. -/
theorem cyclicRightIdeal_topIso_of_ne_zero_of_right_fixed
    (i : tau.SimpleIndex) {c : A}
    (hc0 : c ≠ 0) (hce : c * G.vertex i = c) :
    Nonempty
      (FGModuleCat.of Aᵐᵒᵖ
          (QuotientSubmoduleEquidistribution.Tsukamoto.cyclicRightIdealFG c ⧸
            Module.jacobson Aᵐᵒᵖ
              (QuotientSubmoduleEquidistribution.Tsukamoto.cyclicRightIdealFG c)) ≅
        tau.obj i.1) := by
  let f := QuotientSubmoduleEquidistribution.Tsukamoto.principalRightIdealToCyclic
    (e := G.vertex i) (c := c)
  have hf : Function.Surjective f :=
    QuotientSubmoduleEquidistribution.Tsukamoto.principalRightIdealToCyclic_surjective hce
  let generator : QuotientSubmoduleEquidistribution.Tsukamoto.cyclicRightIdealFG c :=
    ⟨op c, Ideal.subset_span (Set.mem_singleton (op c))⟩
  have hgenerator : generator ≠ 0 := by
    intro hzero
    have hval := congrArg Subtype.val hzero
    apply hc0
    have hval' : op c = (0 : Aᵐᵒᵖ) := by
      change op c = (0 : Aᵐᵒᵖ) at hval
      exact hval
    have hval'' := congrArg unop hval'
    simpa using hval''
  letI : Nontrivial (QuotientSubmoduleEquidistribution.Tsukamoto.cyclicRightIdealFG c) :=
    ⟨⟨generator, 0, hgenerator⟩⟩
  have hTargetSimple : IsSimpleModule Aᵐᵒᵖ (tau.obj i.1) :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).mp
      i.2
  have hVertexTopSimple :
      IsSimpleModule Aᵐᵒᵖ
        (QuotientSubmoduleEquidistribution.Tsukamoto.cyclicRightIdealFG (G.vertex i) ⧸
          Module.jacobson Aᵐᵒᵖ
            (QuotientSubmoduleEquidistribution.Tsukamoto.cyclicRightIdealFG (G.vertex i))) :=
    (FGModuleCat.isoToLinearEquiv (G.vertex_topIso i).some).isSimpleModule_iff.mpr
      hTargetSimple
  letI : IsSimpleModule Aᵐᵒᵖ
      (QuotientSubmoduleEquidistribution.Tsukamoto.cyclicRightIdealFG (G.vertex i) ⧸
        Module.jacobson Aᵐᵒᵖ
          (QuotientSubmoduleEquidistribution.Tsukamoto.cyclicRightIdealFG (G.vertex i))) :=
    hVertexTopSimple
  letI : IsArtinianRing Aᵐᵒᵖ := IsArtinianRing.of_finite K Aᵐᵒᵖ
  let eTop :=
    QuotientSubmoduleEquidistribution.Tsukamoto.topLinearEquivOfSurjectiveOfSimpleTop f hf
  let eTopFG :
      FGModuleCat.of Aᵐᵒᵖ
          (QuotientSubmoduleEquidistribution.Tsukamoto.cyclicRightIdealFG c ⧸
            Module.jacobson Aᵐᵒᵖ
              (QuotientSubmoduleEquidistribution.Tsukamoto.cyclicRightIdealFG c)) ≅
        FGModuleCat.of Aᵐᵒᵖ
          (QuotientSubmoduleEquidistribution.Tsukamoto.cyclicRightIdealFG (G.vertex i) ⧸
            Module.jacobson Aᵐᵒᵖ
              (QuotientSubmoduleEquidistribution.Tsukamoto.cyclicRightIdealFG (G.vertex i))) :=
    { hom := FGModuleCat.ofHom eTop.symm
      inv := FGModuleCat.ofHom eTop
      hom_inv_id := by
        apply ObjectProperty.hom_ext
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro z
        exact eTop.right_inv z
      inv_hom_id := by
        apply ObjectProperty.hom_ext
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro z
        exact eTop.left_inv z }
  exact ⟨eTopFG ≪≫ (G.vertex_topIso i).some⟩

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore
