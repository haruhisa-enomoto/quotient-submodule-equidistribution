import QuotientSubmoduleEquidistribution.RepresentationTheory.FiniteTypeAlmostSplit
import QuotientSubmoduleEquidistribution.RepresentationTheory.IrreducibleRadicalQuotient
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.HopkinsLevitzki

/-!
# Finite-generator almost-split evaluation over an Artinian base

This file replaces the vector-space bases used by
`FiniteTypeAlmostSplit` with finite module generators.  For a finite complete
indecomposable skeleton whose representatives are finite over a commutative
Artinian scalar ring, finite radical evaluation constructs a finite-length
right almost-split map and hence a minimal right almost-split decomposition.

Only right almost-split maps are constructed here.  Together with the kernel
theorem, they suffice to construct both sides of Auslander--Reiten mesh
rotation.  No freeness assumption, algebra presentation, or module
classification is used.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe uk uR uι w

variable {k : Type uk} [CommRing k]
  {R : Type uR} [Ring R] [Algebra k R] [IsNoetherianRing R]
  {ι : Type uι} (σ : IndecomposableSkeleton.{uR, uι, w} R ι)
  [∀ i : ι, Module k (σ.obj i)]
  [∀ i : ι, IsScalarTower k R (σ.obj i)]

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

private abbrev asHom {X Y : FGModuleCat.{w} R}
    (f : X →ₗ[R] Y) : X ⟶ Y :=
  ConcreteCategory.ofHom f

omit [IsNoetherianRing R] in
/-- Restriction to finitely many `R`-module generators embeds the module of
`R`-linear maps into a finite product of the target. -/
theorem moduleFinite_linearMap_of_moduleFinite_codomain
    {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    [Module R X] [Module R Y] [Module k X] [Module k Y]
    [IsScalarTower k R X] [IsScalarTower k R Y]
    [Module.Finite R X] [Module.Finite k Y]
    [IsNoetherianRing k] :
    Module.Finite k (X →ₗ[R] Y) := by
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := X)
  let ev : (X →ₗ[R] Y) →ₗ[k] (Fin n → Y) :=
    { toFun := fun f i ↦ f (s i)
      map_add' := by
        intro f g
        ext i
        rfl
      map_smul' := by
        intro c f
        ext i
        rfl }
  apply Module.Finite.of_injective ev
  intro f g hfg
  apply LinearMap.ext
  intro x
  have hx : x ∈ Submodule.span R (Set.range s) := by
    rw [hs]
    trivial
  refine Submodule.span_induction
    (s := Set.range s) (p := fun y _ ↦ f y = g y) ?_ ?_ ?_ ?_ hx
  · intro y hy
    obtain ⟨i, rfl⟩ := hy
    exact congrFun hfg i
  · simp
  · intro x y _ _ hfx hfy
    simp [hfx, hfy]
  · intro r x _ hfx
    simp [hfx]

/-- The nonsplit-epimorphism radical is a submodule over any commutative
central scalar ring; scalar closure does not use division. -/
def finiteGeneratorRadicalHom (x z : ι) :
    Submodule k (σ.obj x →ₗ[R] σ.obj z) where
  carrier := {f | asHom f ∈ σ.radicalHomAddSubgroup x z}
  zero_mem' := (σ.radicalHomAddSubgroup x z).zero_mem
  add_mem' := by
    intro f g hf hg
    exact (σ.radicalHomAddSubgroup x z).add_mem hf hg
  smul_mem' := by
    intro c f hf hcf
    have hf' : ¬ IsSplitEpi (asHom f) :=
      (σ.mem_radicalHomAddSubgroup_iff_not_isSplitEpi
        (asHom f)).1 hf
    let CF : σ.obj x ⟶ σ.obj z := asHom (c • f)
    letI : IsSplitEpi CF := hcf
    let s : σ.obj z ⟶ σ.obj x := section_ CF
    apply hf'
    refine IsSplitEpi.mk'
      { section_ := asHom (c • s.hom.hom)
        id := ?_ }
    apply FGModuleCat.hom_ext
    have hcat : s ≫ CF = 𝟙 _ := IsSplitEpi.id CF
    have hlin := congrArg
      (fun q : σ.obj z ⟶ σ.obj z ↦ q.hom.hom) hcat
    change (c • f).comp s.hom.hom = LinearMap.id at hlin
    change f.comp (c • s.hom.hom) = LinearMap.id
    apply LinearMap.ext
    intro y
    have hy := LinearMap.congr_fun hlin y
    simpa [LinearMap.comp_apply, LinearMap.smul_apply,
      LinearMap.map_smul_of_tower] using hy

@[simp] theorem mem_finiteGeneratorRadicalHom_iff_not_isSplitEpi
    {x z : ι} (f : σ.obj x →ₗ[R] σ.obj z) :
    f ∈ σ.finiteGeneratorRadicalHom (k := k) x z ↔
      ¬ IsSplitEpi (asHom f) :=
  σ.mem_radicalHomAddSubgroup_iff_not_isSplitEpi (asHom f)

omit [IsNoetherianRing R] in
private theorem hom_hom_sum {J : Type} [Fintype J]
    {X Y : FGModuleCat.{w} R} (f : J → (X ⟶ Y)) :
    (∑ j, f j).hom.hom = ∑ j, (f j).hom.hom := by
  let underlying : (X ⟶ Y) →+ (X →ₗ[R] Y) :=
    { toFun := fun q ↦ q.hom.hom
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  change underlying (∑ j, f j) = ∑ j, underlying (f j)
  exact map_sum underlying f Finset.univ

private noncomputable def scalarId
    (M : FGModuleCat.{w} R)
    [Module k M] [IsScalarTower k R M]
    (c : k) : M ⟶ M :=
  ConcreteCategory.ofHom (c • LinearMap.id)

/-- A finite biproduct of finite-length `R`-modules has finite length. -/
private theorem finiteLength_biproduct
    {J : Type} [Fintype J]
    (F : J → FGModuleCat.{w} R)
    (hF : ∀ j, IsFiniteLength R (F j)) :
    let B : FGModuleCat.{w} R := ⨁ F
    IsFiniteLength R B := by
  let B : FGModuleCat.{w} R := ⨁ F
  letI (j : J) : IsNoetherian R (F j) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (hF j)).1
  letI (j : J) : IsArtinian R (F j) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (hF j)).2
  let U := forget₂ (FGModuleCat.{w} R) (ModuleCat.{w} R)
  letI : PreservesBiproduct F U :=
    preservesBiproduct_of_preservesProduct U
  let e : B ≅ FGModuleCat.of R (∀ j, F j) :=
    U.preimageIso
      (U.mapBiproduct F ≪≫
        ModuleCat.biproductIsoPi (fun j ↦ U.obj (F j)))
  rw [isFiniteLength_iff_isNoetherian_isArtinian]
  exact
    ⟨(LinearEquiv.isNoetherian_iff
        (FGModuleCat.isoToLinearEquiv e)).mpr inferInstance,
      (LinearEquiv.isArtinian_iff
        (FGModuleCat.isoToLinearEquiv e)).mpr inferInstance⟩

section FiniteSkeleton

variable [IsNoetherianRing k] [Finite ι]
  [∀ i : ι, Module.Finite k (σ.obj i)]

include k

/-- Finite-generator radical evaluation over a commutative Noetherian base
constructs a finite-length right almost-split morphism. -/
theorem exists_finiteLength_rightAlmostSplit_of_finiteGenerator (z : ι) :
    ∃ (E : FGModuleCat.{w} R) (f : E ⟶ σ.obj z),
      IsFiniteLength R E ∧ IsRightAlmostSplit f := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  let n := Fintype.card ι
  let ε : Fin n ≃ ι := (Fintype.equivFin ι).symm
  let label : Fin n → ι := ε
  letI (t : Fin n) : Module.Finite k
      (σ.obj (label t) →ₗ[R] σ.obj z) :=
    moduleFinite_linearMap_of_moduleFinite_codomain
      (k := k) (R := R)
  let V (t : Fin n) :=
    σ.finiteGeneratorRadicalHom (k := k) (label t) z
  letI (t : Fin n) : Module.Finite k (V t) := inferInstance
  let d (t : Fin n) : ℕ :=
    (Module.Finite.exists_fin (R := k) (M := V t)).choose
  let b (t : Fin n) : Fin (d t) → V t :=
    (Module.Finite.exists_fin (R := k) (M := V t)).choose_spec.choose
  have hb (t : Fin n) :
      Submodule.span k (Set.range (b t)) = ⊤ :=
    (Module.Finite.exists_fin (R := k) (M := V t)).choose_spec.choose_spec
  let B (t : Fin n) : FGModuleCat.{w} R :=
    ⨁ fun _ : Fin (d t) ↦ σ.obj (label t)
  letI (t : Fin n) : Module k (B t) :=
    Module.restrictScalars k R (B t)
  letI (t : Fin n) : IsScalarTower k R (B t) :=
    IsScalarTower.restrictScalars k R (B t)
  let e (t : Fin n) : B t ⟶ σ.obj z :=
    biproduct.desc fun j ↦
      ConcreteCategory.ofHom ((b t j : V t).1)
  let E : FGModuleCat.{w} R := ⨁ B
  let f : E ⟶ σ.obj z := biproduct.desc e
  have factors_obj_aux
      (t : Fin n) (x : ι) (ht : label t = x)
      (g : σ.obj x ⟶ σ.obj z)
      (hg : ¬ IsSplitEpi g) :
      ∃ h : σ.obj x ⟶ E, h ≫ f = g := by
    subst x
    have hradical :
        g.hom.hom ∈
          σ.finiteGeneratorRadicalHom (k := k) (label t) z :=
      (σ.mem_finiteGeneratorRadicalHom_iff_not_isSplitEpi
        (k := k) g.hom.hom).2 hg
    let u : V t := ⟨g.hom.hom, hradical⟩
    have hu : u ∈ Submodule.span k (Set.range (b t)) := by
      rw [hb t]
      trivial
    obtain ⟨c, hc⟩ :=
      (Submodule.mem_span_range_iff_exists_fun k).1 hu
    let q : σ.obj (label t) ⟶ B t :=
      biproduct.lift fun j ↦
        scalarId (k := k) (σ.obj (label t)) (c j)
    refine ⟨q ≫ biproduct.ι B t, ?_⟩
    rw [Category.assoc, biproduct.ι_desc]
    dsimp only [q, e]
    rw [biproduct.lift_desc]
    apply FGModuleCat.hom_ext
    rw [hom_hom_sum]
    simp only [FGModuleCat.hom_hom_comp]
    change
      (∑ j : Fin (d t),
        (b t j : V t).1.comp (c j • LinearMap.id)) = g.hom.hom
    calc
      (∑ j : Fin (d t),
          (b t j : V t).1.comp (c j • LinearMap.id)) =
          ∑ j : Fin (d t), c j • (b t j : V t).1 := by
        apply Finset.sum_congr rfl
        intro j _
        ext y
        simp
      _ =
          ((∑ j : Fin (d t), c j • (b t j : V t) : V t) :
            σ.obj (label t) →ₗ[R] σ.obj z) := by
        symm
        exact map_sum (V t).subtype
          (fun j : Fin (d t) ↦ c j • (b t j : V t)) Finset.univ
      _ = (u : σ.obj (label t) →ₗ[R] σ.obj z) :=
        congrArg Subtype.val hc
      _ = g.hom.hom := rfl
  refine ⟨E, f, ?_, ?_⟩
  · apply finiteLength_biproduct B
    intro t
    exact finiteLength_biproduct
      (fun _ : Fin (d t) ↦ σ.obj (label t))
      (fun _ ↦ σ.finiteLength (label t))
  · apply σ.isRightAlmostSplit_of_factors_obj f
    · dsimp only [f]
      apply σ.biproductDesc_not_isSplitEpi B e
      intro t
      dsimp only [e]
      apply σ.biproductDesc_not_isSplitEpi
        (fun _ : Fin (d t) ↦ σ.obj (label t))
      intro j
      exact
        (σ.mem_finiteGeneratorRadicalHom_iff_not_isSplitEpi
          (k := k) (b t j : V t).1).1 (b t j : V t).2
    · intro x g hg
      let t : Fin n := ε.symm x
      have ht : label t = x := ε.apply_symm_apply x
      exact factors_obj_aux t x ht g hg

/-- Finite-generator radical evaluation followed by finite-length
minimalization gives a minimal right almost-split decomposition at every
vertex. -/
theorem minimalRightAlmostSplitDecomposition_nonempty_of_finiteGenerator
    (z : ι) :
    Nonempty (σ.MinimalRightAlmostSplitDecomposition z) := by
  obtain ⟨E, f, hE, hf⟩ :=
    σ.exists_finiteLength_rightAlmostSplit_of_finiteGenerator (k := k) z
  exact
    MinimalRightAlmostSplitDecomposition.exists_of_rightAlmostSplit_of_finiteLength
      σ f hf hE

end FiniteSkeleton

section ArtinianBase

variable [IsArtinianRing k] [Finite ι]
  [∀ i : ι, Module.Finite k (σ.obj i)]

include k

/-- Paper-facing specialization of finite-generator radical evaluation to a
commutative Artinian base. -/
theorem exists_finiteLength_rightAlmostSplit_of_artinianBase (z : ι) :
    ∃ (E : FGModuleCat.{w} R) (f : E ⟶ σ.obj z),
      IsFiniteLength R E ∧ IsRightAlmostSplit f :=
  σ.exists_finiteLength_rightAlmostSplit_of_finiteGenerator (k := k) z

/-- A finite complete skeleton over a commutative Artinian base has a
minimal right almost-split decomposition at every vertex. -/
theorem minimalRightAlmostSplitDecomposition_nonempty_of_artinianBase
    (z : ι) :
    Nonempty (σ.MinimalRightAlmostSplitDecomposition z) :=
  σ.minimalRightAlmostSplitDecomposition_nonempty_of_finiteGenerator
    (k := k) z

end ArtinianBase

/-- A module finite over a commutative Artinian base has an Artinian
endomorphism ring.  This is the pointwise hypothesis needed by the
anti-exchange and cofinite-level arguments. -/
theorem isArtinianRing_moduleEnd_of_moduleFinite_artinianBase
    [IsArtinianRing k] (i : ι)
    [Module.Finite k (σ.obj i)] :
    IsArtinianRing (Module.End R (σ.obj i)) := by
  letI : Module.Finite k (Module.End R (σ.obj i)) :=
    moduleFinite_linearMap_of_moduleFinite_codomain
      (k := k) (R := R)
  exact isArtinian_of_tower k inferInstance

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
