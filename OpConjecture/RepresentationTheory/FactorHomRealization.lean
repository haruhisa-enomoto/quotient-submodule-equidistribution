import OpConjecture.RepresentationTheory.FactorHomCriterion
import OpConjecture.RepresentationTheory.FaithfulCore
import OpConjecture.RepresentationTheory.OnePointCosemisimple

/-!
# The factor-Hom realization of trace holes

This file constructs the factor-Hom input in the paper's factor-ladder
criterion.  A factor Hom is nonzero precisely when it contains a morphism
which does not factor through the selected additive subcategory.  Evaluation
against the finite projective decomposition proves that a deleted trace hole
is detected by one of the deleted indecomposable projectives.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace OpConjecture.IndecomposableSkeleton

open OpConjecture.IndecomposableSkeleton.FaithfulCore

universe u v

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} [Finite ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- Nonvanishing in the factor category `add(ind R) / [add K]`, expressed
by a representative which does not factor through `add K`. -/
def factorHomNonzero (K : Set ι)
    (p x : DeletedLabel K) : Prop :=
  ∃ f : σ.obj p.1 ⟶ σ.obj x.1,
    ¬ FactorsThroughAdd σ K f

/-- The boundary labels used by the factor-ladder criterion are precisely
the deleted indecomposable projectives. -/
def deletedProjectiveSet (K : Set ι) : Set (DeletedLabel K) :=
  {p | Projective (σ.obj p.1)}

omit [Finite ι] in
/-- A morphism which factors through `add K` has image in the trace of
`add K`. -/
theorem range_le_trace_of_factorsThroughAdd
    {K : Set ι} {X Y : FGModuleCat.{u} R} {f : X ⟶ Y}
    (hf : FactorsThroughAdd σ K f) :
    LinearMap.range f.hom.hom ≤ σ.trace K Y := by
  rcases hf with ⟨M, hM, left, right, rfl⟩
  exact (LinearMap.range_comp_le_range left.hom.hom right.hom.hom).trans
    (range_le_trace_of_inFac σ (inFac_of_inAdd σ hM) right)

omit [Finite ι] in
/-- For a projective source, having image in the trace is equivalent to
factoring through the selected additive subcategory. -/
theorem factorsThroughAdd_of_projective_of_range_le_trace
    {K : Set ι} {P Y : FGModuleCat.{u} R} (hP : Projective P)
    (f : P ⟶ Y)
    (hf : LinearMap.range f.hom.hom ≤ σ.trace K Y) :
    FactorsThroughAdd σ K f := by
  let gLinear : P →ₗ[R] σ.trace K Y :=
    f.hom.hom.codRestrict (σ.trace K Y) fun p ↦ hf ⟨p, rfl⟩
  let g : P ⟶ σ.traceObject K Y :=
    ConcreteCategory.ofHom gLinear
  have hg : g ≫ σ.traceι K Y = f := by
    apply FGModuleCat.hom_ext
    ext p
    rfl
  obtain ⟨Q⟩ := traceObject_inFac σ K Y
  letI : Epi Q.map := Q.epi
  letI : Projective P := hP
  let lift : P ⟶ σ.sumOver Q.index Q.label :=
    Projective.factorThru g Q.map
  have hlift : lift ≫ Q.map = g :=
    Projective.factorThru_comp g Q.map
  refine ⟨σ.sumOver Q.index Q.label, ?_, lift,
    Q.map ≫ σ.traceι K Y, ?_⟩
  · exact ⟨{
      index := Q.index
      label := Q.label
      mem := Q.mem
      iso := Iso.refl _ }⟩
  · rw [← Category.assoc, hlift, hg]

omit [Finite ι] in
/-- Projective-source factor Hom is nonzero exactly when the image is not
contained in the selected trace. -/
theorem factorHomNonzero_iff_exists_range_not_le_trace
    (K : Set ι) (p x : DeletedLabel K)
    (hp : Projective (σ.obj p.1)) :
    factorHomNonzero σ K p x ↔
      ∃ f : σ.obj p.1 ⟶ σ.obj x.1,
        ¬ LinearMap.range f.hom.hom ≤ σ.trace K (σ.obj x.1) := by
  constructor
  · rintro ⟨f, hnot⟩
    refine ⟨f, ?_⟩
    intro hrange
    exact hnot
      (factorsThroughAdd_of_projective_of_range_le_trace
        σ hp f hrange)
  · rintro ⟨f, hrange⟩
    refine ⟨f, ?_⟩
    intro hfac
    exact hrange (range_le_trace_of_factorsThroughAdd σ hfac)

omit [Finite ι] in
/-- A deleted trace hole is detected by a nonzero factor Hom from a deleted
indecomposable projective. -/
theorem traceHole_iff_exists_deletedProjective_factorHom
    (K : Set ι) (x : DeletedLabel K) :
    HasTraceHole σ K x ↔
      ∃ p : DeletedLabel K,
        p ∈ deletedProjectiveSet σ K ∧
          factorHomNonzero σ K p x := by
  constructor
  · intro hhole
    by_contra hnone
    push Not at hnone
    obtain ⟨Q⟩ := inFac_projectiveLabels σ (σ.obj x.1)
    have hcomponent (t : Q.index) :
        FactorsThroughAdd σ K
          (biproduct.ι (fun j : Q.index ↦ σ.obj (Q.label j)) t ≫
            Q.map) := by
      by_cases ht : Q.label t ∈ K
      · refine ⟨σ.obj (Q.label t), inAdd_obj σ ht,
          𝟙 _,
          biproduct.ι (fun j : Q.index ↦ σ.obj (Q.label j)) t ≫
            Q.map, ?_⟩
        simp
      · let p : DeletedLabel K := ⟨Q.label t, ht⟩
        have hp : p ∈ deletedProjectiveSet σ K := Q.mem t
        have hzero := hnone p hp
        by_contra hnot
        exact hzero ⟨_, hnot⟩
    choose M hM left right hfactor using hcomponent
    let middle : FGModuleCat.{u} R := ⨁ fun t : Q.index ↦ M t
    have hmiddle : σ.InAdd K middle :=
      inAdd_biproduct σ Q.index M hM
    let leftMap : σ.sumOver Q.index Q.label ⟶ middle :=
      biproduct.map left
    let rightMap : middle ⟶ σ.obj x.1 :=
      biproduct.desc right
    have hmap : leftMap ≫ rightMap = Q.map := by
      apply biproduct.hom_ext'
      intro t
      dsimp only [leftMap, rightMap]
      rw [← Category.assoc, biproduct.ι_map,
        Category.assoc, biproduct.ι_desc]
      exact hfactor t
    letI : Epi Q.map := Q.epi
    letI : Epi rightMap := epi_of_epi_fac hmap
    obtain ⟨A⟩ := hmiddle
    have hinFac : σ.InFac K (σ.obj x.1) := ⟨{
      index := A.index
      label := A.label
      mem := A.mem
      map := A.iso.inv ≫ rightMap
      epi := inferInstance }⟩
    exact hhole ((inFac_iff_trace_eq_top σ K (σ.obj x.1)).1 hinFac)
  · rintro ⟨p, hp, hhom⟩ htop
    obtain ⟨f, hnot⟩ := hhom
    apply hnot
    apply factorsThroughAdd_of_projective_of_range_le_trace σ hp f
    rw [htop]
    exact le_top

/-- The factor-Hom input required by the abstract factor-ladder criterion is
therefore canonical. -/
def holeFactorHomInput (K : Set ι) :
    HoleFactorHomInput σ K (deletedProjectiveSet σ K) where
  factorHomNonzero := factorHomNonzero σ K
  hole_iff_projective_factorHom :=
    traceHole_iff_exists_deletedProjective_factorHom σ K

end OpConjecture.IndecomposableSkeleton
