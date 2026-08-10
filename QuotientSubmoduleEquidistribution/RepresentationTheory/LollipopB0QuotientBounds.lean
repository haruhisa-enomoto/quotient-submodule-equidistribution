import QuotientSubmoduleEquidistribution.RepresentationTheory.LollipopB0Modules
import QuotientSubmoduleEquidistribution.RepresentationTheory.LollipopZeroHomCertificates

/-!
# A second genuine quotient-good row for the dead-path lollipop

For the four explicitly enumerated sources `S₂, X, A, S₁` and target `P`, every
map has image in one common proper submodule of `P`.  A generic finite-biproduct
lemma then packages such a common range bound as the maintained quotient
omission certificate.

No completeness statement about the five named modules is used here.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.LollipopConcrete.ModuleLayer.PBound

universe u

variable (K : Type u) [Field K]

/-- The first coordinate in the vertex-`1` space of `P`. -/
def pTopCoord (v : PModule K) : K :=
  (FiniteB0Rep.fst K (PData K) v).1

@[simp] theorem pTopCoord_zero : pTopCoord K (0 : PModule K) = 0 := rfl

@[simp] theorem pTopCoord_add (v w : PModule K) :
    pTopCoord K (v + w) = pTopCoord K v + pTopCoord K w := rfl

theorem b0Action_first_eq
    (V₂ : Type u) [AddCommGroup V₂] [Module K V₂]
    (loop : (K × K) →ₗ[K] (K × K)) (stem : (K × K) →ₗ[K] V₂)
    (hloop : ∀ v, loop (loop v) = 0) (hstem : ∀ v, stem (loop v) = 0)
    (hfirst : ∀ v, (loop v).1 = 0)
    (b : B0Model K) (v : (K × K) × V₂) :
    (b0Action K (K × K) V₂ loop stem hloop hstem b v).1.1 =
      b.fst.1 * v.1.1 := by
  unfold b0Action
  rw [TrivSqZeroExt.lift_def]
  change b.fst.1 * v.1.1 + b.snd.x * (loop v.1).1 = b.fst.1 * v.1.1
  rw [hfirst]
  simp

@[simp] theorem pTopCoord_smul (b : B0Model K) (v : PModule K) :
    pTopCoord K (b • v) = b.fst.1 * pTopCoord K v := by
  exact b0Action_first_eq K K (PData K).loop.hom.hom (PData K).stem.hom.hom
    (PData K).loop_sq (PData K).stem_loop (by intro w; rfl) b v

/-- The proper `B₀`-submodule `{((0,v),w) : v,w ∈ K}` of `P`. -/
def pRadicalBound : Submodule (B0Model K) (PModule K) where
  carrier := {v | pTopCoord K v = 0}
  zero_mem' := rfl
  add_mem' := by
    intro v w hv hw
    change pTopCoord K v = 0 at hv
    change pTopCoord K w = 0 at hw
    change pTopCoord K (v + w) = 0
    simp only [pTopCoord_add, hv, hw, add_zero]
  smul_mem' := by
    intro b v hv
    change pTopCoord K v = 0 at hv
    change pTopCoord K (b • v) = 0
    simp only [pTopCoord_smul, hv, mul_zero]

/-- The second coordinate at vertex `1`; after multiplication by `x` it reads the old top
coordinate. -/
def pLoopDetector (v : PModule K) : K :=
  (FiniteB0Rep.fst K (PData K) v).2

/-- The vertex-`2` coordinate; after multiplication by `a` it reads the old top coordinate. -/
def pStemDetector (v : PModule K) : K :=
  FiniteB0Rep.snd K (PData K) v

@[simp] theorem pLoopDetector_zero : pLoopDetector K (0 : PModule K) = 0 := rfl

@[simp] theorem pStemDetector_zero : pStemDetector K (0 : PModule K) = 0 := rfl

@[simp] theorem pLoopDetector_x_smul (v : PModule K) :
    pLoopDetector K (x K • v) = pTopCoord K v := by
  rw [FiniteB0Rep.x_smul]
  rfl

@[simp] theorem pStemDetector_a_smul (v : PModule K) :
    pStemDetector K (a K • v) = pTopCoord K v := by
  rw [FiniteB0Rep.a_smul]
  rfl

theorem x_smul_eq_zero_of_loop_eq_zero
    (D : FiniteB0Rep K)
    (hloop : ∀ v, D.loop.hom.hom v = 0)
    (v : FiniteB0Rep.Carrier K D) : x K • v = 0 := by
  rw [FiniteB0Rep.x_smul]
  apply FiniteB0Rep.carrier_ext K D
  · exact hloop _
  · rfl

theorem a_smul_eq_zero_of_stem_eq_zero
    (D : FiniteB0Rep K)
    (hstem : ∀ v, D.stem.hom.hom v = 0)
    (v : FiniteB0Rep.Carrier K D) : a K • v = 0 := by
  rw [FiniteB0Rep.a_smul]
  apply FiniteB0Rep.carrier_ext K D
  · rfl
  · exact hstem _

/-- A zero source loop forces every map to `P` to miss its top coordinate. -/
theorem range_le_pRadicalBound_of_loop_eq_zero
    (D : FiniteB0Rep K)
    (hloop : ∀ v, D.loop.hom.hom v = 0)
    (f : FiniteB0Rep.asFGModule K D ⟶ PModule K) :
    LinearMap.range f.hom.hom ≤ pRadicalBound K := by
  rintro _ ⟨v, rfl⟩
  change pTopCoord K (f.hom.hom v) = 0
  have hx : x K • f.hom.hom v = 0 := by
    calc
      x K • f.hom.hom v = f.hom.hom (x K • v) := (f.hom.hom.map_smul _ _).symm
      _ = f.hom.hom 0 := by rw [x_smul_eq_zero_of_loop_eq_zero K D hloop v]
      _ = 0 := f.hom.hom.map_zero
  calc
    pTopCoord K (f.hom.hom v) = pLoopDetector K (x K • f.hom.hom v) :=
      (pLoopDetector_x_smul K _).symm
    _ = pLoopDetector K 0 := congrArg (pLoopDetector K) hx
    _ = 0 := pLoopDetector_zero K

/-- A zero source stem forces every map to `P` to miss its top coordinate. -/
theorem range_le_pRadicalBound_of_stem_eq_zero
    (D : FiniteB0Rep K)
    (hstem : ∀ v, D.stem.hom.hom v = 0)
    (f : FiniteB0Rep.asFGModule K D ⟶ PModule K) :
    LinearMap.range f.hom.hom ≤ pRadicalBound K := by
  rintro _ ⟨v, rfl⟩
  change pTopCoord K (f.hom.hom v) = 0
  have ha : a K • f.hom.hom v = 0 := by
    calc
      a K • f.hom.hom v = f.hom.hom (a K • v) := (f.hom.hom.map_smul _ _).symm
      _ = f.hom.hom 0 := by rw [a_smul_eq_zero_of_stem_eq_zero K D hstem v]
      _ = 0 := f.hom.hom.map_zero
  calc
    pTopCoord K (f.hom.hom v) = pStemDetector K (a K • f.hom.hom v) :=
      (pStemDetector_a_smul K _).symm
    _ = pStemDetector K 0 := congrArg (pStemDetector K) ha
    _ = 0 := pStemDetector_zero K

/-- A vector outside the proposed bound. -/
def pTopGenerator : PModule K :=
  FiniteB0Rep.ofV₁ K (PData K) (1, 0)

@[simp] theorem pTopCoord_pTopGenerator :
    pTopCoord K (pTopGenerator K) = 1 := rfl

theorem pRadicalBound_ne_top : pRadicalBound K ≠ ⊤ := by
  intro htop
  have hmem : pTopGenerator K ∈ pRadicalBound K := by
    rw [htop]
    exact Submodule.mem_top
  change pTopCoord K (pTopGenerator K) = 0 at hmem
  rw [pTopCoord_pTopGenerator] at hmem
  exact one_ne_zero hmem

theorem range_S2_P_le (f : S2Module K ⟶ PModule K) :
    LinearMap.range f.hom.hom ≤ pRadicalBound K :=
  range_le_pRadicalBound_of_loop_eq_zero K (S2Data K) (by intro v; rfl) f

theorem range_X_P_le (f : XModule K ⟶ PModule K) :
    LinearMap.range f.hom.hom ≤ pRadicalBound K :=
  range_le_pRadicalBound_of_stem_eq_zero K (XData K) (by intro v; rfl) f

theorem range_A_P_le (f : AModule K ⟶ PModule K) :
    LinearMap.range f.hom.hom ≤ pRadicalBound K :=
  range_le_pRadicalBound_of_loop_eq_zero K (AData K) (by intro v; rfl) f

theorem range_S1_P_le (f : S1Module K ⟶ PModule K) :
    LinearMap.range f.hom.hom ≤ pRadicalBound K :=
  range_le_pRadicalBound_of_loop_eq_zero K (S1Data K) (by intro v; rfl) f

inductive SelectedLabel where
  | s2
  | x
  | a
  | s1

def selectedModule : SelectedLabel → FGModuleCat (B0Model K)
  | .s2 => S2Module K
  | .x => XModule K
  | .a => AModule K
  | .s1 => S1Module K

/-- All four selected genuine source modules have image inside the same proper bound in `P`. -/
theorem selected_range_le
    (i : SelectedLabel) (f : selectedModule K i ⟶ PModule K) :
    LinearMap.range f.hom.hom ≤ pRadicalBound K := by
  cases i with
  | s2 => exact range_S2_P_le K f
  | x => exact range_X_P_le K f
  | a => exact range_A_P_le K f
  | s1 => exact range_S1_P_le K f

section TraceBound

universe v w

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {iota : Type v} (sigma : IndecomposableSkeleton.{u, v, w} R iota)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- Abstract range-bounded analogue of the maintained zero-Hom trace lemma. -/
theorem trace_le_of_forall_range_le
    {S : Set iota} {Y : FGModuleCat.{w} R}
    (bound : Submodule R Y)
    (hrange : ∀ i : iota, i ∈ S → ∀ f : sigma.obj i ⟶ Y,
      LinearMap.range f.hom.hom ≤ bound) :
    sigma.trace S Y ≤ bound := by
  apply iSup_le
  intro F
  let Q : FGModuleCat.{w} R := FGModuleCat.of R (Y ⧸ bound)
  let q : Y ⟶ Q := FGModuleCat.ofHom bound.mkQ
  have hcomp : F.map ≫ q = 0 := by
    apply biproduct.hom_ext'
    intro t
    let g : sigma.obj (F.label t) ⟶ Y :=
      biproduct.ι (fun t : F.index => sigma.obj (F.label t)) t ≫ F.map
    change g ≫ q = 0
    apply FGModuleCat.hom_ext
    change bound.mkQ.comp g.hom.hom = 0
    rw [← LinearMap.range_le_ker_iff, Submodule.ker_mkQ]
    exact hrange (F.label t) (F.mem t) g
  rw [← Submodule.ker_mkQ bound, LinearMap.range_le_ker_iff]
  have hlinear := congrArg (fun z => z.hom.hom) hcomp
  change bound.mkQ.comp F.map.hom.hom = 0 at hlinear
  exact hlinear

/-- Package a common proper range bound as the maintained quotient-omission certificate. -/
def omissionCertificateOfRangeBound
    [Finite iota]
    {S : Set iota} {j : iota}
    (hnot : j ∉ S)
    (bound : Submodule R (sigma.obj j))
    (bound_ne_top : bound ≠ ⊤)
    (hrange : ∀ i : iota, i ∈ S → ∀ f : sigma.obj i ⟶ sigma.obj j,
      LinearMap.range f.hom.hom ≤ bound) :
    QuotientSubmoduleEquidistribution.BottomLevels.LollipopTableCertificates.Quotient.OmissionCertificate
      sigma S j where
  not_mem := hnot
  bound := bound
  bound_ne_top := bound_ne_top
  trace_le_bound := trace_le_of_forall_range_le sigma bound hrange

end TraceBound

end QuotientSubmoduleEquidistribution.LollipopConcrete.ModuleLayer.PBound
