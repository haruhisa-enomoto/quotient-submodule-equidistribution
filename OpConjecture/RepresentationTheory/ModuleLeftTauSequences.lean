import OpConjecture.RepresentationTheory.FiniteTypeAlmostSplit
import OpConjecture.RepresentationTheory.ModuleRightTauSequences

/-!
# Left tau-sequences from module Auslander--Reiten data

At a noninjective indecomposable, rotate the corresponding chosen right
Auslander--Reiten sequence. At an injective indecomposable, finite radical
evaluation supplies a minimal left almost-split map; injectivity makes it an
epimorphism, so its cokernel is zero. Together these constructions give the
ambient left tau meshes without using any concrete module classification.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace OpConjecture

open CategoricalRadical

universe u v w

variable {C : Type u} [Category.{v} C]

/-- Transporting the source and target of an indexed family of morphisms
commutes with the corresponding morphism. -/
theorem eqToHom_comp_dependent_morphism
    {J : Type w} (X Y : J → C) (f : ∀ j, X j ⟶ Y j)
    {i j : J} (h : i = j) :
    eqToHom (congrArg X h) ≫ f j =
      f i ≫ eqToHom (congrArg Y h) := by
  subst j
  simp

variable [Abelian C]

theorem IsLeftAlmostSplit.epi_of_injective_source_of_leftMinimal
    {A B : C} (f : A ⟶ B) [Injective A]
    (hf : IsLeftAlmostSplit f) (hmin : IsLeftMinimal f) :
    Epi f := by
  let p : A ⟶ Abelian.image f := Abelian.factorThruImage f
  let i : Abelian.image f ⟶ B := Abelian.image.ι f
  have hpnot : ¬ IsSplitMono p := by
    intro hp
    letI : IsSplitMono p := hp
    haveI : IsIso p := isIso_of_epi_of_isSplitMono p
    have hmono : Mono f := by
      rw [← Abelian.image.fac f]
      infer_instance
    letI : Mono f := hmono
    apply hf.not_isSplitMono
    exact IsSplitMono.mk'
      { retraction := Injective.factorThru (𝟙 A) f
        id := Injective.comp_factorThru (𝟙 A) f }
  obtain ⟨h, hh⟩ := hf.factors p hpnot
  let e : B ⟶ B := h ≫ i
  have he : f ≫ e = f := by
    dsimp only [e, i]
    rw [← Category.assoc, hh, Abelian.image.fac]
  haveI : IsIso e := hmin e he
  have hiSplit : IsSplitEpi i :=
    IsSplitEpi.mk'
      { section_ := inv e ≫ h
        id := by
          dsimp only [e]
          rw [Category.assoc, IsIso.inv_hom_id] }
  letI : IsSplitEpi i := hiSplit
  haveI : IsIso i := isIso_of_mono_of_isSplitEpi i
  rw [← Abelian.image.fac f]
  infer_instance

namespace IndecomposableSkeleton

universe uR uι

variable {k R : Type uR} [Field k] [Ring R] [Algebra k R]
  [FiniteDimensional k R] [IsNoetherianRing R]
  {ι : Type uι} [Fintype ι]
  (σ : IndecomposableSkeleton.{uR, uι, uR} R ι)

namespace FiniteARTranslationData

variable (D : σ.FiniteARTranslationData)

/-- The canonical cokernel isomorphism identifies the second map of the
chosen left AR complex with the corresponding chosen right AR map. -/
theorem chosenLeftAR_cokernel_π_comp_iso
    (x : σ.NoninjectiveLabel) :
    cokernel.π (chosenLeftAR σ D x).map ≫
        (chosenLeftARCokernelIso σ D x).hom =
      (chosenRightAR σ D ((arTranslationEquiv σ D).symm x)).map := by
  simp [chosenLeftARCokernelIso, chosenLeftAR, arKernelMap,
    MinimalLeftAlmostSplitDecomposition.ofMap]
  rw [cokernelKernelIsoTarget]
  exact colimit.isoColimitCocone_ι_hom _ WalkingParallelPair.one

/-- Identify a noninjective label with the source of the corresponding
chosen right AR sequence. -/
def noninjectiveLeftSourceIso (x : σ.NoninjectiveLabel) :
    σ.obj x.1 ≅
      σ.obj (arTranslation σ D ((arTranslationEquiv σ D).symm x)).1 := by
  let z : σ.NonprojectiveLabel := (arTranslationEquiv σ D).symm x
  have hτ : arTranslationEquiv σ D z = x :=
    (arTranslationEquiv σ D).apply_symm_apply x
  exact eqToIso (congrArg σ.obj (congrArg Subtype.val hτ).symm)

/-- The chosen left almost-split map at a noninjective indecomposable,
followed by the corresponding chosen right almost-split map. -/
def noninjectiveLeftMesh (x : σ.NoninjectiveLabel) :
    ShortComplex (FGModuleCat.{uR} R) := by
  let z : σ.NonprojectiveLabel := (arTranslationEquiv σ D).symm x
  let f : σ.obj x.1 ⟶ (chosenRightAR σ D z).middle :=
    (noninjectiveLeftSourceIso σ D x).hom ≫ arKernelMap σ D z
  exact ShortComplex.mk f (chosenRightAR σ D z).map (by
    dsimp only [f, arKernelMap]
    rw [Category.assoc, Category.assoc, kernel.condition, comp_zero,
      comp_zero])

/-- The chosen noninjective left AR complex is a left tau-sequence. -/
theorem noninjectiveLeftTau (x : σ.NoninjectiveLabel) :
    Iyama.LeftTauSequence (noninjectiveLeftMesh σ D x) := by
  let z : σ.NonprojectiveLabel := (arTranslationEquiv σ D).symm x
  let B := chosenRightAR σ D z
  let e : σ.obj x.1 ≅ σ.obj (arTranslation σ D z).1 :=
    noninjectiveLeftSourceIso σ D x
  let f : σ.obj x.1 ⟶ B.middle := e.hom ≫ arKernelMap σ D z
  change Iyama.LeftTauSequence
    (ShortComplex.mk f B.map (by
      dsimp only [f, arKernelMap]
      rw [Category.assoc, Category.assoc, kernel.condition, comp_zero,
        comp_zero]))
  have hfLeft : IsLeftAlmostSplit f :=
    (arKernelMap_leftAlmostSplit σ D z).precomp_iso e
  have hfRad : IsRadicalMorphism f :=
    (σ.isRadicalMorphism_iff_not_isSplitMono_from_obj f).2
      hfLeft.not_isSplitMono
  have hgB : IsRadicalMorphism B.map :=
    (σ.isRadicalMorphism_iff_not_isSplitEpi_to_obj B.map).2
      B.rightAlmostSplit.not_isSplitEpi
  have hBEpi : Epi B.map :=
    IsRightAlmostSplit.epi_of_not_projective_obj σ B.map
      B.rightAlmostSplit z.2
  letI : Epi B.map := hBEpi
  refine
    { f_radical := hfRad
      g_radical := hgB
      factors_from_left := ?_
      factors_into_right := ?_
      minimalWeakCokernel := ?_ }
  · intro W a ha
    exact hfLeft.factors a
      ((σ.isRadicalMorphism_iff_not_isSplitMono_from_obj a).1 ha)
  · intro W a ha
    exact B.rightAlmostSplit.factors a
      ((σ.isRadicalMorphism_iff_not_isSplitEpi_to_obj a).1 ha)
  · constructor
    · rw [Iyama.ShortComplex.isWeakCokernel_iff]
      intro W a ha
      have hk : kernel.ι B.map ≫ a = 0 := by
        rw [← cancel_epi (arTranslationKernelIso σ D z).inv]
        change arKernelMap σ D z ≫ a = 0
        rw [← cancel_epi e.hom]
        exact ha
      exact ⟨Abelian.epiDesc B.map a hk,
        Abelian.comp_epiDesc B.map a hk⟩
    · intro q hq
      have hqeq : q = 𝟙 _ := by
        apply (cancel_epi B.map).1
        simpa only [Category.comp_id] using hq
      rw [hqeq]
      infer_instance

/-- Choose a minimal left almost-split decomposition at an injective
boundary label by finite radical evaluation. -/
def injectiveLeftAR (x : {x : ι // Injective (σ.obj x)}) :
    σ.MinimalLeftAlmostSplitDecomposition x.1 :=
  Classical.choice
    (σ.minimalLeftAlmostSplitDecomposition_nonempty_of_finiteDimensional
      k x.1)

/-- The injective-boundary left complex, ending in the canonical cokernel
of its minimal left almost-split map. -/
def injectiveLeftMesh (x : {x : ι // Injective (σ.obj x)}) :
    ShortComplex (FGModuleCat.{uR} R) :=
  ShortComplex.mk (injectiveLeftAR (k := k) σ x).map
    (cokernel.π (injectiveLeftAR (k := k) σ x).map)
    (cokernel.condition (injectiveLeftAR (k := k) σ x).map)

/-- The chosen injective-boundary complex is a left tau-sequence. -/
theorem injectiveLeftTau (x : {x : ι // Injective (σ.obj x)}) :
    Iyama.LeftTauSequence (injectiveLeftMesh (k := k) σ x) := by
  let A := injectiveLeftAR (k := k) σ x
  change Iyama.LeftTauSequence
    (ShortComplex.mk A.map (cokernel.π A.map)
      (cokernel.condition A.map))
  letI : Injective (σ.obj x.1) := x.2
  have hfEpi : Epi A.map :=
    A.leftAlmostSplit.epi_of_injective_source_of_leftMinimal
      A.map A.leftMinimal
  letI : Epi A.map := hfEpi
  have hgzero : cokernel.π A.map = 0 := by
    apply (cancel_epi A.map).1
    rw [cokernel.condition, comp_zero]
  have hCok : IsZero (cokernel A.map) := by
    rw [IsZero.iff_id_eq_zero]
    apply (cancel_epi (cokernel.π A.map)).1
    rw [Category.comp_id, hgzero, zero_comp]
  have hfRad : IsRadicalMorphism A.map :=
    (σ.isRadicalMorphism_iff_not_isSplitMono_from_obj A.map).2
      A.leftAlmostSplit.not_isSplitMono
  have hgRad : IsRadicalMorphism (cokernel.π A.map) := by
    rw [hgzero]
    exact isRadicalMorphism_zero
  refine
    { f_radical := hfRad
      g_radical := hgRad
      factors_from_left := ?_
      factors_into_right := ?_
      minimalWeakCokernel := ?_ }
  · intro W a ha
    exact A.leftAlmostSplit.factors a
      ((σ.isRadicalMorphism_iff_not_isSplitMono_from_obj a).1 ha)
  · intro W a _ha
    refine ⟨0, ?_⟩
    rw [zero_comp]
    exact (hCok.eq_of_tgt a 0).symm
  · constructor
    · rw [Iyama.ShortComplex.isWeakCokernel_iff]
      intro W a ha
      exact ⟨cokernel.desc A.map a ha, cokernel.π_desc _ _ _⟩
    · intro e _he
      have heq : e = 𝟙 _ := hCok.eq_of_src e (𝟙 _)
      rw [heq]
      infer_instance

/-- The unified ambient left mesh at a skeleton label. -/
def moduleLeftMesh (x : ι) : ShortComplex (FGModuleCat.{uR} R) := by
  classical
  by_cases hx : Injective (σ.obj x)
  · exact injectiveLeftMesh (k := k) σ ⟨x, hx⟩
  · exact noninjectiveLeftMesh σ D ⟨x, hx⟩

/-- Every unified ambient left mesh is a left tau-sequence. -/
theorem moduleLeftTau (x : ι) :
    Iyama.LeftTauSequence (moduleLeftMesh (k := k) σ D x) := by
  classical
  by_cases hx : Injective (σ.obj x)
  · simpa [moduleLeftMesh, hx] using
      injectiveLeftTau (k := k) σ ⟨x, hx⟩
  · simpa [moduleLeftMesh, hx] using
      noninjectiveLeftTau σ D ⟨x, hx⟩

/-- The left endpoint of the unified mesh is literally the selected
indecomposable. -/
theorem moduleLeftMesh_X₁ (x : ι) :
    (moduleLeftMesh (k := k) σ D x).X₁ = σ.obj x := by
  classical
  by_cases hx : Injective (σ.obj x) <;>
    simp [moduleLeftMesh, hx, injectiveLeftMesh,
      noninjectiveLeftMesh]

/-- At an injective label the unified left mesh ends in a zero object. -/
theorem moduleLeftMesh_X₃_isZero_of_injective
    (x : ι) (hx : Injective (σ.obj x)) :
    IsZero (moduleLeftMesh (k := k) σ D x).X₃ := by
  simp only [moduleLeftMesh, hx, ↓reduceDIte, injectiveLeftMesh]
  let A := injectiveLeftAR (k := k) σ ⟨x, hx⟩
  letI : Injective (σ.obj x) := hx
  have hfEpi : Epi A.map :=
    A.leftAlmostSplit.epi_of_injective_source_of_leftMinimal
      A.map A.leftMinimal
  letI : Epi A.map := hfEpi
  have hgzero : cokernel.π A.map = 0 := by
    apply (cancel_epi A.map).1
    rw [cokernel.condition, comp_zero]
  rw [IsZero.iff_id_eq_zero]
  apply (cancel_epi (cokernel.π A.map)).1
  rw [Category.comp_id, hgzero, zero_comp]

/-- At a noninjective label the unified mesh ends at its inverse
Auslander--Reiten translate. -/
theorem moduleLeftMesh_X₃_of_not_injective
    (x : ι) (hx : ¬ Injective (σ.obj x)) :
    (moduleLeftMesh (k := k) σ D x).X₃ =
      σ.obj ((arTranslationEquiv σ D).symm ⟨x, hx⟩).1 := by
  simp [moduleLeftMesh, hx, noninjectiveLeftMesh]

/-- A chosen nonprojective right AR mesh is the left mesh at its
Auslander--Reiten translate. -/
def nonprojectiveRightMeshIso_moduleLeftMesh
    (z : σ.NonprojectiveLabel) :
    nonprojectiveRightMesh σ D z ≅
      moduleLeftMesh (k := k) σ D (arTranslationEquiv σ D z).1 := by
  let x : σ.NoninjectiveLabel := arTranslationEquiv σ D z
  have hx : ¬ Injective (σ.obj x.1) := x.2
  let y : σ.NonprojectiveLabel := (arTranslationEquiv σ D).symm x
  let hz : z = y :=
    ((arTranslationEquiv σ D).symm_apply_apply z).symm
  let e₁ : σ.obj (arTranslation σ D z).1 ≅ σ.obj x.1 :=
    eqToIso (congrArg σ.obj (congrArg Subtype.val rfl))
  let e₂ : (chosenRightAR σ D z).middle ≅
      (chosenRightAR σ D y).middle :=
    eqToIso (congrArg (fun t : σ.NonprojectiveLabel ↦
      (chosenRightAR σ D t).middle) hz)
  let e₃ : σ.obj z.1 ≅ σ.obj y.1 :=
    eqToIso (congrArg (fun t : σ.NonprojectiveLabel ↦ σ.obj t.1) hz)
  have hsource : e₁.hom ≫ (noninjectiveLeftSourceIso σ D x).hom =
      eqToHom (congrArg (fun t : σ.NonprojectiveLabel ↦
        σ.obj (arTranslation σ D t).1) hz) := by
    simp only [e₁, noninjectiveLeftSourceIso, eqToIso.hom]
    rw [eqToHom_trans]
  rw [show moduleLeftMesh (k := k) σ D x.1 =
      noninjectiveLeftMesh σ D x by
    simp [moduleLeftMesh, hx]]
  refine ShortComplex.isoMk e₁ e₂ e₃ ?_ ?_
  · dsimp only [nonprojectiveRightMesh, noninjectiveLeftMesh]
    rw [← Category.assoc, hsource]
    simpa only [y, e₂, eqToIso.hom] using eqToHom_comp_dependent_morphism
      (fun t : σ.NonprojectiveLabel ↦
        σ.obj (arTranslation σ D t).1)
      (fun t : σ.NonprojectiveLabel ↦
        (chosenRightAR σ D t).middle)
      (arKernelMap σ D) hz
  · dsimp only [nonprojectiveRightMesh, noninjectiveLeftMesh]
    simpa only [y, e₂, e₃, eqToIso.hom] using
      eqToHom_comp_dependent_morphism
        (fun t : σ.NonprojectiveLabel ↦
          (chosenRightAR σ D t).middle)
        (fun t : σ.NonprojectiveLabel ↦ σ.obj t.1)
        (fun t ↦ (chosenRightAR σ D t).map) hz


end FiniteARTranslationData
end IndecomposableSkeleton
end OpConjecture
