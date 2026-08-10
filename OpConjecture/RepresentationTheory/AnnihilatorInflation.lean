import OpConjecture.RepresentationTheory.LiteralLevelCount
import OpConjecture.RepresentationTheory.NormalModules
import OpConjecture.RepresentationTheory.SimpleLevels
import OpConjecture.Combinatorics.BottomThreeFourFaithfulRecurrence
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
# Annihilator strata and quotient inflation (scratch)

This scratch file develops the module-side part of the annihilator recurrence
without assuming that the type of all two-sided ideals is finite.
-/

noncomputable section

open Set
open CategoryTheory CategoryTheory.Limits

namespace OpConjecture.AnnihilatorInflation

universe u v w vq

/-! ## Restriction from a quotient ring preserves finite generation -/

namespace Quotient

variable {R : Type u} [Ring R] (I : TwoSidedIdeal R)

abbrev Factor := R ⧸ I.asIdeal

abbrev map : R →+* Factor I := Ideal.Quotient.mk I.asIdeal

/-- A finitely generated module over a quotient ring remains finitely
generated after inflation to the original ring.  The proof uses the same
finite generators and surjectivity of the quotient map. -/
theorem finite_restrict (X : FGModuleCat.{w} (Factor I)) :
    Module.Finite R
      ((ModuleCat.restrictScalars (map I)).obj X.obj) := by
  let Y : ModuleCat.{w} R :=
    (ModuleCat.restrictScalars (map I)).obj X.obj
  letI : Module (Factor I) Y :=
    inferInstanceAs (Module (Factor I) X)
  letI : Module.Finite (Factor I) Y := by
    change Module.Finite (Factor I) X
    infer_instance
  letI : IsScalarTower R (Factor I) Y :=
    ⟨by
      intro r b y
      change (map I r * b) • y = map I r • b • y
      exact mul_smul _ _ _⟩
  exact Module.Finite.trans (Factor I) Y

/-- Inflation of finitely generated modules along `R → R/I`. -/
def obj (X : FGModuleCat.{w} (Factor I)) : FGModuleCat.{w} R :=
  ⟨(ModuleCat.restrictScalars (map I)).obj X.obj,
    finite_restrict I X⟩

/-- Inflation as a functor on finitely generated module categories. -/
def functor :
    CategoryTheory.Functor
      (FGModuleCat.{w} (Factor I)) (FGModuleCat.{w} R) where
  obj := obj I
  map f := ⟨(ModuleCat.restrictScalars (map I)).map f.1⟩
  map_id X := by
    apply FGModuleCat.hom_ext
    rfl
  map_comp f g := by
    apply FGModuleCat.hom_ext
    rfl

@[simp]
theorem functor_map_apply {X Y : FGModuleCat.{w} (Factor I)}
    (f : X ⟶ Y) (x : X) :
    (functor I).map f x = f x := rfl

/-- Every map between inflated quotient modules is automatically linear over
the quotient ring, because the quotient map is surjective. -/
def liftHom {X Y : FGModuleCat.{w} (Factor I)}
    (f : (functor I).obj X ⟶ (functor I).obj Y) : X ⟶ Y :=
  FGModuleCat.ofHom
    { toFun := f.hom.hom
      map_add' := f.hom.hom.map_add
      map_smul' := by
        intro b x
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective b
        exact f.hom.hom.map_smul r x }

/-- Quotient inflation is fully faithful. -/
def fullyFaithful : (functor I).FullyFaithful where
  preimage := liftHom I
  map_preimage f := by
    apply FGModuleCat.hom_ext
    rfl
  preimage_map f := by
    apply FGModuleCat.hom_ext
    rfl

instance : (functor I).Faithful := (fullyFaithful I).faithful

instance : (functor I).Full := (fullyFaithful I).full

end Quotient

/-! ## Common annihilators of finite-skeleton supports -/

variable {R : Type u} [Ring R]
  {J : Type v} (X : J → FGModuleCat.{w} R)

/-- Common two-sided annihilator of a family selected by a support. -/
def supportAnnihilator (S : Set J) : TwoSidedIdeal R :=
  TwoSidedIdeal.mk'
    {r | ∀ j, j ∈ S → ∀ x : X j, r • x = 0}
    (by simp)
    (by
      intro a b ha hb j hj x
      simp [add_smul, ha j hj x, hb j hj x])
    (by
      intro a ha j hj x
      simp [ha j hj x])
    (by
      intro a b hb j hj x
      simp [mul_smul, hb j hj x])
    (by
      intro a b ha j hj x
      simpa only [mul_smul] using ha j hj (b • x))

@[simp]
theorem mem_supportAnnihilator {S : Set J} {r : R} :
    r ∈ supportAnnihilator X S ↔
      ∀ j, j ∈ S → ∀ x : X j, r • x = 0 := by
  simp [supportAnnihilator]

/-- A support is faithful when its common annihilator is zero. -/
def IsFaithfulSupport (S : Set J) : Prop :=
  supportAnnihilator X S = ⊥

theorem supportAnnihilator_antitone :
    Antitone (supportAnnihilator X) := by
  intro S T hST r hr j hj
  exact hr j (hST hj)

/-- Faithfulness is upward-closed under enlargement of the support. -/
theorem isFaithfulSupport_monotone :
    Monotone (IsFaithfulSupport X) := by
  intro S T hST hS
  apply bot_unique
  rw [← hS]
  exact supportAnnihilator_antitone X hST

@[simp]
theorem supportAnnihilator_empty :
    supportAnnihilator X (∅ : Set J) = ⊤ := by
  ext r
  simp

@[simp]
theorem supportAnnihilator_union (S T : Set J) :
    supportAnnihilator X (S ∪ T) =
      supportAnnihilator X S ⊓ supportAnnihilator X T := by
  ext r
  simp only [mem_supportAnnihilator, TwoSidedIdeal.mem_inf,
    Set.mem_union]
  aesop

/-- Common annihilators are unchanged by replacing every selected module by
an isomorphic module and relabeling through an embedding. -/
theorem supportAnnihilator_image_of_iso
    {K : Type vq} (e : K ↪ J)
    (Y : K → FGModuleCat.{w} R)
    (hiso : ∀ k, X (e k) ≅ Y k)
    (T : Set K) :
    supportAnnihilator X (e '' T) = supportAnnihilator Y T := by
  ext r
  simp only [mem_supportAnnihilator]
  constructor
  · intro hr k hk y
    let E := FGModuleCat.isoToLinearEquiv (hiso k)
    obtain ⟨x, rfl⟩ := E.surjective y
    calc
      r • E x = E (r • x) := (E.map_smul r x).symm
      _ = E 0 := congrArg E (hr (e k) ⟨k, hk, rfl⟩ x)
      _ = 0 := E.map_zero
  · intro hr j hj x
    obtain ⟨k, hk, rfl⟩ := hj
    let E := FGModuleCat.isoToLinearEquiv (hiso k)
    apply E.injective
    rw [E.map_smul]
    simpa only [map_zero] using hr k hk (E x)

namespace Quotient

variable {R : Type u} [Ring R] (I : TwoSidedIdeal R)
  {J : Type v} (X : J → FGModuleCat.{w} (Factor I))

/-- The annihilator after inflation is the inverse image of the quotient-side
annihilator under the quotient map. -/
theorem supportAnnihilator_inflation (S : Set J) :
    supportAnnihilator (fun j ↦ (functor I).obj (X j)) S =
      TwoSidedIdeal.comap (map I) (supportAnnihilator X S) := by
  ext r
  simp only [mem_supportAnnihilator, TwoSidedIdeal.mem_comap]
  rfl

/-- A quotient support is faithful exactly when its inflated support has
annihilator equal to the defining ideal. -/
theorem isFaithfulSupport_iff_inflation_annihilator_eq (S : Set J) :
    IsFaithfulSupport X S ↔
      supportAnnihilator (fun j ↦ (functor I).obj (X j)) S = I := by
  constructor
  · intro h
    rw [supportAnnihilator_inflation I X S, h]
    ext r
    simp [TwoSidedIdeal.mem_comap,
      Ideal.Quotient.eq_zero_iff_mem]
  · intro h
    rw [supportAnnihilator_inflation I X S] at h
    unfold IsFaithfulSupport
    ext b
    constructor
    · intro hb
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective b
      have hr : r ∈
          TwoSidedIdeal.comap (map I) (supportAnnihilator X S) := hb
      rw [h] at hr
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hr
    · intro hb
      have : b = 0 := by
        simpa only [TwoSidedIdeal.mem_bot] using hb
      subst b
      exact (supportAnnihilator X S).zero_mem

end Quotient

/-! ## Annihilators and literal quotient/submodule closure -/

namespace Skeleton

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {K : Type v} (sigma : IndecomposableSkeleton.{u, v, w} R K)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- If a scalar kills every summand in a finite biproduct, it kills the
whole biproduct. -/
private theorem smul_sumOver_eq_zero
    {J : FintypeCat.{0}} (a : J → K) (r : R)
    (hr : ∀ t (x : sigma.obj (a t)), r • x = 0)
    (y : sigma.sumOver J a) :
    r • y = 0 := by
  let E := FGModuleCat.isoToLinearEquiv
    (OpConjecture.IndecomposableSkeleton.biproductIsoPiFG
      (fun t : J ↦ sigma.obj (a t)))
  apply E.injective
  ext t
  rw [E.map_smul, E.map_zero]
  change r • E y t = 0
  exact hr t (E y t)

/-- Passing from a support to its literal quotient closure does not change
its common annihilator. -/
theorem supportAnnihilator_qSet (S : Set K) :
    supportAnnihilator sigma.obj (sigma.qSet S) =
      supportAnnihilator sigma.obj S := by
  ext r
  simp only [mem_supportAnnihilator]
  constructor
  · intro hr j hj
    exact hr j (sigma.subset_qSet S hj)
  · intro hr j hj x
    obtain ⟨P⟩ := hj
    letI : Epi P.map := P.epi
    obtain ⟨y, rfl⟩ :=
      (OpConjecture.IndecomposableSkeleton.fg_epi_iff_surjective P.map).mp
        inferInstance x
    rw [← P.map.hom.hom.map_smul]
    have hy : r • y = 0 :=
      smul_sumOver_eq_zero sigma P.label r
        (fun t z ↦ hr (P.label t) (P.mem t) z) y
    rw [hy, map_zero]

/-- Passing from a support to its literal submodule closure does not change
its common annihilator. -/
theorem supportAnnihilator_sSet (S : Set K) :
    supportAnnihilator sigma.obj (sigma.sSet S) =
      supportAnnihilator sigma.obj S := by
  ext r
  simp only [mem_supportAnnihilator]
  constructor
  · intro hr j hj
    exact hr j (sigma.subset_sSet S hj)
  · intro hr j hj x
    obtain ⟨P⟩ := hj
    letI : Mono P.map := P.mono
    apply
      (OpConjecture.IndecomposableSkeleton.fg_mono_iff_injective P.map).mp
        inferInstance
    rw [P.map.hom.hom.map_smul]
    simpa only [map_zero] using
      smul_sumOver_eq_zero sigma P.label r
        (fun t z ↦ hr (P.label t) (P.mem t) z)
        (P.map.hom.hom x)

/-- Closure-operator form of `supportAnnihilator_qSet`. -/
theorem supportAnnihilator_qClosure (S : Set K) :
    supportAnnihilator sigma.obj (sigma.qClosure S) =
      supportAnnihilator sigma.obj S :=
  supportAnnihilator_qSet sigma S

/-- Closure-operator form of `supportAnnihilator_sSet`. -/
theorem supportAnnihilator_sClosure (S : Set K) :
    supportAnnihilator sigma.obj (sigma.sClosure S) =
      supportAnnihilator sigma.obj S :=
  supportAnnihilator_sSet sigma S

/-- The common support annihilator, viewed as a left ideal, is the ordinary
module annihilator of the duplicate-free basic sum on that finite support. -/
theorem supportAnnihilator_asIdeal_eq_annihilator_basicModule
    (B : OpConjecture.IndecomposableSkeleton.FiniteSupport (ι := K)) :
    (supportAnnihilator sigma.obj (B.1 : Set K)).asIdeal =
      Module.annihilator R (sigma.basicModule B) := by
  classical
  ext r
  rw [TwoSidedIdeal.mem_asIdeal, Module.mem_annihilator]
  simp only [mem_supportAnnihilator]
  constructor
  · intro hr y
    exact
      smul_sumOver_eq_zero sigma B.label r
        (fun t z ↦ hr (B.label t) (B.label_mem t) z) y
  · intro hr j hj x
    obtain ⟨t, ht⟩ := B.exists_label_eq hj
    subst j
    let E := FGModuleCat.isoToLinearEquiv
      (OpConjecture.IndecomposableSkeleton.biproductIsoPiFG
        (fun s : B.index ↦ sigma.obj (B.label s)))
    let z : ∀ s : B.index, sigma.obj (B.label s) := Pi.single t x
    have hzero := hr (E.symm z)
    have hcomponent := congrArg (fun y ↦ E y t) hzero
    rw [E.map_smul, E.apply_symm_apply, E.map_zero] at hcomponent
    change r • z t = 0 at hcomponent
    simpa only [z, Pi.single_eq_same] using hcomponent

/-- Faithfulness of a finite support is the ordinary annihilator-zero
condition on its basic module. -/
theorem isFaithfulSupport_iff_annihilator_basicModule_eq_bot
    (B : OpConjecture.IndecomposableSkeleton.FiniteSupport (ι := K)) :
    IsFaithfulSupport sigma.obj (B.1 : Set K) ↔
      Module.annihilator R (sigma.basicModule B) = ⊥ := by
  let hbasic :=
    supportAnnihilator_asIdeal_eq_annihilator_basicModule sigma B
  constructor
  · intro hfaithful
    rw [← hbasic, hfaithful, TwoSidedIdeal.bot_asIdeal]
  · intro hfaithful
    unfold IsFaithfulSupport
    apply TwoSidedIdeal.ext
    intro r
    rw [← TwoSidedIdeal.mem_asIdeal, hbasic, hfaithful]
    simp

end Skeleton

/-! ## Skeleton alignment and exact annihilator fibers -/

namespace Skeleton

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {K : Type v} {L : Type vq}
  (sigma : IndecomposableSkeleton.{u, v, w} R K)
  (I : TwoSidedIdeal R)
  [IsNoetherianRing (Quotient.Factor I)]
  (tau : IndecomposableSkeleton.{u, vq, w}
    (Quotient.Factor I) L)

/-- Alignment data left after constructing the actual quotient-inflation
functor.  `covers` says that every support with exact annihilator `I` uses
only indecomposables inflated from `R/I`; the two closedness fields are the
exact `Fac`/`Sub` invariance statements. -/
structure InflationData where
  label : L ↪ K
  objIso : ∀ l,
    sigma.obj (label l) ≅ (Quotient.functor I).obj (tau.obj l)
  qClosed_image_iff : ∀ T : Set L,
    sigma.qClosure.IsClosed (label '' T) ↔
      tau.qClosure.IsClosed T
  sClosed_image_iff : ∀ T : Set L,
    sigma.sClosure.IsClosed (label '' T) ↔
      tau.sClosure.IsClosed T
  covers : ∀ S : Set K,
    supportAnnihilator sigma.obj S = I →
      S ⊆ Set.range label

namespace InflationData

variable (D : InflationData sigma I tau)

theorem faithful_iff_image_annihilator_eq (T : Set L) :
    IsFaithfulSupport tau.obj T ↔
      supportAnnihilator sigma.obj (D.label '' T) = I := by
  rw [supportAnnihilator_image_of_iso sigma.obj D.label
    (fun l ↦ (Quotient.functor I).obj (tau.obj l)) D.objIso T]
  exact Quotient.isFaithfulSupport_iff_inflation_annihilator_eq I tau.obj T

/-- Quotient-closed supports of a fixed size and exact annihilator. -/
def QAnnihilatorLevel (n : ℕ) :=
  {C : sigma.qClosure.Closeds //
    supportAnnihilator sigma.obj (C : Set K) = I ∧
      (C : Set K).ncard = n}

/-- Submodule-closed supports of a fixed size and exact annihilator. -/
def SAnnihilatorLevel (n : ℕ) :=
  {C : sigma.sClosure.Closeds //
    supportAnnihilator sigma.obj (C : Set K) = I ∧
      (C : Set K).ncard = n}

/-- Faithful quotient-closed supports of a factor at a fixed size. -/
def FaithfulQLevel (n : ℕ) :=
  {C : tau.qClosure.Closeds //
    IsFaithfulSupport tau.obj (C : Set L) ∧
      (C : Set L).ncard = n}

/-- Faithful submodule-closed supports of a factor at a fixed size. -/
def FaithfulSLevel (n : ℕ) :=
  {C : tau.sClosure.Closeds //
    IsFaithfulSupport tau.obj (C : Set L) ∧
      (C : Set L).ncard = n}

private theorem image_preimage_eq_of_annihilator
    {S : Set K} (hS : supportAnnihilator sigma.obj S = I) :
    D.label '' (D.label ⁻¹' S) = S := by
  rw [Set.image_preimage_eq_inter_range]
  exact Set.inter_eq_left.mpr (D.covers S hS)

/-- Inflation identifies faithful quotient-closed factor supports with the
ambient annihilator fiber, preserving cardinality. -/
def faithfulQLevelEquiv (n : ℕ) :
    FaithfulQLevel I tau n ≃ QAnnihilatorLevel sigma I n where
  toFun C := by
    let S : Set K := D.label '' (C.1 : Set L)
    have hclosed : sigma.qClosure.IsClosed S :=
      (D.qClosed_image_iff (C.1 : Set L)).mpr C.1.property
    refine ⟨⟨S, hclosed⟩, ?_, ?_⟩
    · exact (faithful_iff_image_annihilator_eq sigma I tau D
        (C.1 : Set L)).mp C.2.1
    · simpa only [S, Set.ncard_image_of_injective
        (C.1 : Set L) D.label.injective] using C.2.2
  invFun C := by
    let T : Set L := D.label ⁻¹' (C.1 : Set K)
    have himage : D.label '' T = (C.1 : Set K) :=
      image_preimage_eq_of_annihilator sigma I tau D C.2.1
    have hclosed : tau.qClosure.IsClosed T :=
      (D.qClosed_image_iff T).mp (himage ▸ C.1.property)
    refine ⟨⟨T, hclosed⟩, ?_, ?_⟩
    · exact (faithful_iff_image_annihilator_eq sigma I tau D T).mpr
        (by simpa only [himage] using C.2.1)
    · have hcard := Set.ncard_image_of_injective T D.label.injective
      rw [himage, C.2.2] at hcard
      exact hcard.symm
  left_inv C := by
    apply Subtype.ext
    apply Subtype.ext
    exact Set.preimage_image_eq (C.1 : Set L) D.label.injective
  right_inv C := by
    apply Subtype.ext
    apply Subtype.ext
    exact image_preimage_eq_of_annihilator sigma I tau D C.2.1

/-- The corresponding exact inflation fiber on the submodule side. -/
def faithfulSLevelEquiv (n : ℕ) :
    FaithfulSLevel I tau n ≃ SAnnihilatorLevel sigma I n where
  toFun C := by
    let S : Set K := D.label '' (C.1 : Set L)
    have hclosed : sigma.sClosure.IsClosed S :=
      (D.sClosed_image_iff (C.1 : Set L)).mpr C.1.property
    refine ⟨⟨S, hclosed⟩, ?_, ?_⟩
    · exact (faithful_iff_image_annihilator_eq sigma I tau D
        (C.1 : Set L)).mp C.2.1
    · simpa only [S, Set.ncard_image_of_injective
        (C.1 : Set L) D.label.injective] using C.2.2
  invFun C := by
    let T : Set L := D.label ⁻¹' (C.1 : Set K)
    have himage : D.label '' T = (C.1 : Set K) :=
      image_preimage_eq_of_annihilator sigma I tau D C.2.1
    have hclosed : tau.sClosure.IsClosed T :=
      (D.sClosed_image_iff T).mp (himage ▸ C.1.property)
    refine ⟨⟨T, hclosed⟩, ?_, ?_⟩
    · exact (faithful_iff_image_annihilator_eq sigma I tau D T).mpr
        (by simpa only [himage] using C.2.1)
    · have hcard := Set.ncard_image_of_injective T D.label.injective
      rw [himage, C.2.2] at hcard
      exact hcard.symm
  left_inv C := by
    apply Subtype.ext
    apply Subtype.ext
    exact Set.preimage_image_eq (C.1 : Set L) D.label.injective
  right_inv C := by
    apply Subtype.ext
    apply Subtype.ext
    exact image_preimage_eq_of_annihilator sigma I tau D C.2.1

end InflationData

/-! ## Finite joint-range annihilator recurrence -/

section FiniteJointRange

variable [Finite K]

private abbrev QClosed := sigma.qClosure.Closeds

private abbrev SClosed := sigma.sClosure.Closeds

/-- The annihilator map on quotient-closed supports. -/
def qClosedAnnihilator (C : QClosed sigma) : TwoSidedIdeal R :=
  supportAnnihilator sigma.obj (C : Set K)

/-- The annihilator map on submodule-closed supports. -/
def sClosedAnnihilator (C : SClosed sigma) : TwoSidedIdeal R :=
  supportAnnihilator sigma.obj (C : Set K)

/-- Only annihilators actually realized on at least one of the two finite
closed-set lattices.  The ambient ideal type need not be finite. -/
abbrev RealizedAnnihilator :=
  OpConjecture.BottomLevels.FiniteJointStratification.JointRange
    (qClosedAnnihilator sigma) (sClosedAnnihilator sigma)

/-- Realized nonzero annihilators, hence the exact finite index type for
proper quotient factors in the recurrence. -/
abbrev ProperRealizedAnnihilator :=
  {I : RealizedAnnihilator sigma // I.1 ≠ (⊥ : TwoSidedIdeal R)}

noncomputable local instance : Fintype (QClosed sigma) :=
  Fintype.ofFinite _

noncomputable local instance : Fintype (SClosed sigma) :=
  Fintype.ofFinite _

noncomputable instance properRealizedAnnihilatorFintype :
    Fintype (ProperRealizedAnnihilator sigma) :=
  Fintype.ofFinite _

/-- Fixed-cardinality quotient-closed supports, before stratification. -/
private abbrev QLevel (n : ℕ) :=
  {C : QClosed sigma // (C : Set K).ncard = n}

/-- Fixed-cardinality submodule-closed supports, before stratification. -/
private abbrev SLevel (n : ℕ) :=
  {C : SClosed sigma // (C : Set K).ncard = n}

/-- Send a quotient-closed support either to the faithful stratum (`none`)
or to its realized proper annihilator. -/
noncomputable def qStratum (C : QClosed sigma) :
    Option (ProperRealizedAnnihilator sigma) := by
  classical
  exact
    if h : qClosedAnnihilator sigma C = ⊥ then none
    else
      some
        ⟨OpConjecture.BottomLevels.FiniteJointStratification.toJointLeft
            (qClosedAnnihilator sigma) (sClosedAnnihilator sigma) C,
          h⟩

/-- The analogous faithful/proper stratification on the submodule side. -/
noncomputable def sStratum (C : SClosed sigma) :
    Option (ProperRealizedAnnihilator sigma) := by
  classical
  exact
    if h : sClosedAnnihilator sigma C = ⊥ then none
    else
      some
        ⟨OpConjecture.BottomLevels.FiniteJointStratification.toJointRight
            (qClosedAnnihilator sigma) (sClosedAnnihilator sigma) C,
          h⟩

omit [Finite K] in
@[simp]
theorem qStratum_eq_none_iff (C : QClosed sigma) :
    qStratum sigma C = none ↔
      qClosedAnnihilator sigma C = ⊥ := by
  classical
  simp [qStratum]

omit [Finite K] in
@[simp]
theorem sStratum_eq_none_iff (C : SClosed sigma) :
    sStratum sigma C = none ↔
      sClosedAnnihilator sigma C = ⊥ := by
  classical
  simp [sStratum]

omit [Finite K] in
theorem qStratum_eq_some_iff
    (C : QClosed sigma) (I : ProperRealizedAnnihilator sigma) :
    qStratum sigma C = some I ↔
      qClosedAnnihilator sigma C = I.1.1 := by
  classical
  unfold qStratum
  split_ifs with hbot
  · constructor
    · simp
    · intro h
      exact (I.2 (h.symm.trans hbot)).elim
  · constructor
    · intro h
      have hI := Option.some.inj h
      exact congrArg (fun J : ProperRealizedAnnihilator sigma ↦ J.1.1) hI
    · intro h
      congr 1
      apply Subtype.ext
      apply Subtype.ext
      exact h

omit [Finite K] in
theorem sStratum_eq_some_iff
    (C : SClosed sigma) (I : ProperRealizedAnnihilator sigma) :
    sStratum sigma C = some I ↔
      sClosedAnnihilator sigma C = I.1.1 := by
  classical
  unfold sStratum
  split_ifs with hbot
  · constructor
    · simp
    · intro h
      exact (I.2 (h.symm.trans hbot)).elim
  · constructor
    · intro h
      have hI := Option.some.inj h
      exact congrArg (fun J : ProperRealizedAnnihilator sigma ↦ J.1.1) hI
    · intro h
      congr 1
      apply Subtype.ext
      apply Subtype.ext
      exact h

private abbrev QStratumFiber (n : ℕ)
    (z : Option (ProperRealizedAnnihilator sigma)) :=
  {C : QLevel sigma n // qStratum sigma C.1 = z}

private abbrev SStratumFiber (n : ℕ)
    (z : Option (ProperRealizedAnnihilator sigma)) :=
  {C : SLevel sigma n // sStratum sigma C.1 = z}

/-- The `none` quotient fiber is exactly the faithful ambient fiber. -/
private def qNoneFiberEquiv (n : ℕ) :
    QStratumFiber sigma n none ≃
      InflationData.QAnnihilatorLevel sigma ⊥ n where
  toFun C :=
    ⟨C.1.1, (qStratum_eq_none_iff sigma C.1.1).mp C.2, C.1.2⟩
  invFun C :=
    ⟨⟨C.1, C.2.2⟩,
      (qStratum_eq_none_iff sigma C.1).mpr C.2.1⟩
  left_inv C := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv C := by
    apply Subtype.ext
    rfl

/-- Every proper quotient fiber is the corresponding exact-annihilator
fiber. -/
private def qSomeFiberEquiv (n : ℕ)
    (I : ProperRealizedAnnihilator sigma) :
    QStratumFiber sigma n (some I) ≃
      InflationData.QAnnihilatorLevel sigma I.1.1 n where
  toFun C :=
    ⟨C.1.1, (qStratum_eq_some_iff sigma C.1.1 I).mp C.2, C.1.2⟩
  invFun C :=
    ⟨⟨C.1, C.2.2⟩,
      (qStratum_eq_some_iff sigma C.1 I).mpr C.2.1⟩
  left_inv C := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv C := by
    apply Subtype.ext
    rfl

/-- The faithful submodule fiber. -/
private def sNoneFiberEquiv (n : ℕ) :
    SStratumFiber sigma n none ≃
      InflationData.SAnnihilatorLevel sigma ⊥ n where
  toFun C :=
    ⟨C.1.1, (sStratum_eq_none_iff sigma C.1.1).mp C.2, C.1.2⟩
  invFun C :=
    ⟨⟨C.1, C.2.2⟩,
      (sStratum_eq_none_iff sigma C.1).mpr C.2.1⟩
  left_inv C := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv C := by
    apply Subtype.ext
    rfl

/-- Every proper submodule fiber is the corresponding exact-annihilator
fiber. -/
private def sSomeFiberEquiv (n : ℕ)
    (I : ProperRealizedAnnihilator sigma) :
    SStratumFiber sigma n (some I) ≃
      InflationData.SAnnihilatorLevel sigma I.1.1 n where
  toFun C :=
    ⟨C.1.1, (sStratum_eq_some_iff sigma C.1.1 I).mp C.2, C.1.2⟩
  invFun C :=
    ⟨⟨C.1, C.2.2⟩,
      (sStratum_eq_some_iff sigma C.1 I).mpr C.2.1⟩
  left_inv C := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv C := by
    apply Subtype.ext
    rfl

private theorem qLevelCount_eq_natCard (n : ℕ) :
    sigma.qClosure.levelCount n = Nat.card (QLevel sigma n) := by
  unfold OpConjecture.SetClosure.levelCount
  exact (Nat.card_coe_set_eq _).symm

private theorem sLevelCount_eq_natCard (n : ℕ) :
    sigma.sClosure.levelCount n = Nat.card (SLevel sigma n) := by
  unfold OpConjecture.SetClosure.levelCount
  exact (Nat.card_coe_set_eq _).symm

omit [Finite K] in
private theorem qFaithfulLevelCard (n : ℕ) :
    Nat.card (InflationData.QAnnihilatorLevel sigma ⊥ n) =
      OpConjecture.BottomLevels.MinimalFaithfulCore.faithfulLevelCount
        sigma.qClosure (IsFaithfulSupport sigma.obj) n := by
  unfold OpConjecture.BottomLevels.MinimalFaithfulCore.faithfulLevelCount
  rw [← Nat.card_coe_set_eq]
  rfl

omit [Finite K] in
private theorem sFaithfulLevelCard (n : ℕ) :
    Nat.card (InflationData.SAnnihilatorLevel sigma ⊥ n) =
      OpConjecture.BottomLevels.MinimalFaithfulCore.faithfulLevelCount
        sigma.sClosure (IsFaithfulSupport sigma.obj) n := by
  unfold OpConjecture.BottomLevels.MinimalFaithfulCore.faithfulLevelCount
  rw [← Nat.card_coe_set_eq]
  rfl

/-- Exact finite annihilator recurrence on the quotient side, before
identifying each proper fiber with faithful supports over its quotient
ring.  The proper index type is independent of `n`. -/
theorem qLevelCount_eq_faithful_add_sum_annihilatorFibers (n : ℕ) :
    sigma.qClosure.levelCount n =
      OpConjecture.BottomLevels.MinimalFaithfulCore.faithfulLevelCount
          sigma.qClosure (IsFaithfulSupport sigma.obj) n +
        ∑ I : ProperRealizedAnnihilator sigma,
          Nat.card
            (InflationData.QAnnihilatorLevel sigma I.1.1 n) := by
  classical
  let stratum : QLevel sigma n →
      Option (ProperRealizedAnnihilator sigma) :=
    fun C ↦ qStratum sigma C.1
  calc
    sigma.qClosure.levelCount n = Nat.card (QLevel sigma n) :=
      qLevelCount_eq_natCard sigma n
    _ = Nat.card
        (Σ z : Option (ProperRealizedAnnihilator sigma),
          QStratumFiber sigma n z) :=
      Nat.card_congr (Equiv.sigmaFiberEquiv stratum).symm
    _ = ∑ z : Option (ProperRealizedAnnihilator sigma),
        Nat.card (QStratumFiber sigma n z) :=
      Nat.card_sigma
    _ = Nat.card (QStratumFiber sigma n none) +
        ∑ I : ProperRealizedAnnihilator sigma,
          Nat.card (QStratumFiber sigma n (some I)) :=
      Fintype.sum_option _
    _ = Nat.card (InflationData.QAnnihilatorLevel sigma ⊥ n) +
        ∑ I : ProperRealizedAnnihilator sigma,
          Nat.card
            (InflationData.QAnnihilatorLevel sigma I.1.1 n) := by
      congr 1
      · exact Nat.card_congr (qNoneFiberEquiv sigma n)
      · apply Finset.sum_congr rfl
        intro I _
        exact Nat.card_congr (qSomeFiberEquiv sigma n I)
    _ =
        OpConjecture.BottomLevels.MinimalFaithfulCore.faithfulLevelCount
            sigma.qClosure (IsFaithfulSupport sigma.obj) n +
          ∑ I : ProperRealizedAnnihilator sigma,
            Nat.card
              (InflationData.QAnnihilatorLevel sigma I.1.1 n) := by
      rw [qFaithfulLevelCard sigma n]

/-- Exact finite annihilator recurrence on the submodule side. -/
theorem sLevelCount_eq_faithful_add_sum_annihilatorFibers (n : ℕ) :
    sigma.sClosure.levelCount n =
      OpConjecture.BottomLevels.MinimalFaithfulCore.faithfulLevelCount
          sigma.sClosure (IsFaithfulSupport sigma.obj) n +
        ∑ I : ProperRealizedAnnihilator sigma,
          Nat.card
            (InflationData.SAnnihilatorLevel sigma I.1.1 n) := by
  classical
  let stratum : SLevel sigma n →
      Option (ProperRealizedAnnihilator sigma) :=
    fun C ↦ sStratum sigma C.1
  calc
    sigma.sClosure.levelCount n = Nat.card (SLevel sigma n) :=
      sLevelCount_eq_natCard sigma n
    _ = Nat.card
        (Σ z : Option (ProperRealizedAnnihilator sigma),
          SStratumFiber sigma n z) :=
      Nat.card_congr (Equiv.sigmaFiberEquiv stratum).symm
    _ = ∑ z : Option (ProperRealizedAnnihilator sigma),
        Nat.card (SStratumFiber sigma n z) :=
      Nat.card_sigma
    _ = Nat.card (SStratumFiber sigma n none) +
        ∑ I : ProperRealizedAnnihilator sigma,
          Nat.card (SStratumFiber sigma n (some I)) :=
      Fintype.sum_option _
    _ = Nat.card (InflationData.SAnnihilatorLevel sigma ⊥ n) +
        ∑ I : ProperRealizedAnnihilator sigma,
          Nat.card
            (InflationData.SAnnihilatorLevel sigma I.1.1 n) := by
      congr 1
      · exact Nat.card_congr (sNoneFiberEquiv sigma n)
      · apply Finset.sum_congr rfl
        intro I _
        exact Nat.card_congr (sSomeFiberEquiv sigma n I)
    _ =
        OpConjecture.BottomLevels.MinimalFaithfulCore.faithfulLevelCount
            sigma.sClosure (IsFaithfulSupport sigma.obj) n +
          ∑ I : ProperRealizedAnnihilator sigma,
            Nat.card
              (InflationData.SAnnihilatorLevel sigma I.1.1 n) := by
      rw [sFaithfulLevelCard sigma n]

omit [Finite K] in
/-- Exact-annihilator quotient fibers are faithful quotient-side supports
over the corresponding factor algebra. -/
theorem qAnnihilatorFiberCard_eq_factorFaithfulLevelCount
    (I : ProperRealizedAnnihilator sigma)
    {L : Type vq} [Finite L]
    [IsNoetherianRing (Quotient.Factor I.1.1)]
    (tau : IndecomposableSkeleton.{u, vq, w}
      (Quotient.Factor I.1.1) L)
    (D : InflationData sigma I.1.1 tau) (n : ℕ) :
    Nat.card (InflationData.QAnnihilatorLevel sigma I.1.1 n) =
      OpConjecture.BottomLevels.MinimalFaithfulCore.faithfulLevelCount
        tau.qClosure (IsFaithfulSupport tau.obj) n := by
  calc
    Nat.card (InflationData.QAnnihilatorLevel sigma I.1.1 n) =
        Nat.card (InflationData.FaithfulQLevel I.1.1 tau n) :=
      Nat.card_congr
        (InflationData.faithfulQLevelEquiv sigma I.1.1 tau D n).symm
    _ =
        OpConjecture.BottomLevels.MinimalFaithfulCore.faithfulLevelCount
          tau.qClosure (IsFaithfulSupport tau.obj) n := by
      unfold OpConjecture.BottomLevels.MinimalFaithfulCore.faithfulLevelCount
      rw [← Nat.card_coe_set_eq]
      rfl

omit [Finite K] in
/-- Submodule-side exact-annihilator fibers satisfy the same quotient
inflation identification. -/
theorem sAnnihilatorFiberCard_eq_factorFaithfulLevelCount
    (I : ProperRealizedAnnihilator sigma)
    {L : Type vq} [Finite L]
    [IsNoetherianRing (Quotient.Factor I.1.1)]
    (tau : IndecomposableSkeleton.{u, vq, w}
      (Quotient.Factor I.1.1) L)
    (D : InflationData sigma I.1.1 tau) (n : ℕ) :
    Nat.card (InflationData.SAnnihilatorLevel sigma I.1.1 n) =
      OpConjecture.BottomLevels.MinimalFaithfulCore.faithfulLevelCount
        tau.sClosure (IsFaithfulSupport tau.obj) n := by
  calc
    Nat.card (InflationData.SAnnihilatorLevel sigma I.1.1 n) =
        Nat.card (InflationData.FaithfulSLevel I.1.1 tau n) :=
      Nat.card_congr
        (InflationData.faithfulSLevelEquiv sigma I.1.1 tau D n).symm
    _ =
        OpConjecture.BottomLevels.MinimalFaithfulCore.faithfulLevelCount
          tau.sClosure (IsFaithfulSupport tau.obj) n := by
      unfold OpConjecture.BottomLevels.MinimalFaithfulCore.faithfulLevelCount
      rw [← Nat.card_coe_set_eq]
      rfl

end FiniteJointRange

end Skeleton

end OpConjecture.AnnihilatorInflation
