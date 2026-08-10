import QuotientSubmoduleEquidistribution.RepresentationTheory.ARNoTransitiveTriangles

/-!
# Sectional compositions and cycles in finite AR quivers

This file develops the categorical input for the standard theorem that a
sectional sequence of irreducible maps has nonzero composite.  The first
step is the length-two zero-composite lemma: a zero composite of two
irreducible maps forces the first endpoint to be the AR translate of the
last endpoint.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

universe u v

variable {K R : Type u} [Field K] [Ring R] [Algebra K R]
  [FiniteDimensional K R] [IsNoetherianRing R]
  {ι : Type v} [Fintype ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)

omit [Fintype ι] in
/-- An irreducible map between two chosen indecomposable representatives is
nonzero. -/
theorem irreducibleMorphism_ne_zero_obj
    {x y : ι} {f : σ.obj x ⟶ σ.obj y}
    (hf : IsIrreducibleMorphism f) : f ≠ 0 := by
  have hrad :=
    (σ.isIrreducibleMorphism_iff_mem_radical_not_mem_radicalSquare f).1 hf
  intro hzero
  apply hrad.2
  rw [hzero]
  exact AddSubgroup.zero_mem _

omit [Fintype ι] in
private theorem fg_end_pow_hom
    {x : ι} (f : σ.obj x ⟶ σ.obj x) (n : ℕ) :
    ((CategoryTheory.End.of f) ^ n : End (σ.obj x)).hom.hom =
      f.hom.hom ^ n := by
  induction n with
  | zero =>
      ext y
      rfl
  | succ n ih =>
      rw [pow_succ, pow_succ, CategoryTheory.End.mul_def]
      change
        ((CategoryTheory.End.of f) ^ n).hom.hom.comp f.hom.hom =
          (f.hom.hom ^ n).comp f.hom.hom
      rw [ih]

omit [Fintype ι] in
/-- Every noninvertible endomorphism of a chosen indecomposable
finite-length module is nilpotent. -/
theorem endomorphism_isNilpotent_of_not_isIso_obj
    {x : ι} (f : σ.obj x ⟶ σ.obj x) (hf : ¬ IsIso f) :
    IsNilpotent (CategoryTheory.End.of f) := by
  obtain ⟨hN, hA⟩ :=
    isFiniteLength_iff_isNoetherian_isArtinian.mp (σ.finiteLength x)
  letI : IsNoetherian R (σ.obj x) := hN
  letI : IsArtinian R (σ.obj x) := hA
  have hfNonunit : ¬ IsUnit f.hom.hom := by
    intro hfUnit
    have hbij : Function.Bijective f.hom.hom :=
      (Module.End.isUnit_iff f.hom.hom).1 hfUnit
    let U := forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)
    letI : IsIso (U.map f) := by
      change IsIso f.hom
      exact (ConcreteCategory.isIso_iff_bijective f.hom).2 hbij
    exact hf (isIso_of_reflects_iso f U)
  have hnil : IsNilpotent f.hom.hom :=
    ((σ.indecomposable x).isNilpotent_iff_not_isUnit f.hom.hom).2
      hfNonunit
  obtain ⟨n, hn⟩ := hnil
  refine ⟨n, ?_⟩
  apply FGModuleCat.hom_ext
  rw [fg_end_pow_hom]
  exact hn

omit [Fintype ι] in
/-- If a map out of the biproduct of two nonisomorphic chosen
indecomposables is split monic on each summand, then it is split monic.
The two provisional retractions are corrected by the invertible Schur
complements `1 - αβ` and `1 - βα`; Fitting nilpotence supplies their
invertibility. -/
theorem isSplitMono_biprod_of_components_of_ne
    {x y : ι} (hxy : x ≠ y) {M : FGModuleCat.{u} R}
    (q : σ.obj x ⊞ σ.obj y ⟶ M)
    (hx : IsSplitMono (biprod.inl ≫ q))
    (hy : IsSplitMono (biprod.inr ≫ q)) :
    IsSplitMono q := by
  let qx : σ.obj x ⟶ M := biprod.inl ≫ q
  let qy : σ.obj y ⟶ M := biprod.inr ≫ q
  letI : IsSplitMono qx := hx
  letI : IsSplitMono qy := hy
  let rx₀ : M ⟶ σ.obj x := retraction qx
  let ry₀ : M ⟶ σ.obj y := retraction qy
  let α : σ.obj x ⟶ σ.obj y := qx ≫ ry₀
  let β : σ.obj y ⟶ σ.obj x := qy ≫ rx₀
  have hαβ : ¬ IsIso (α ≫ β) := by
    intro h
    letI : IsIso (α ≫ β) := h
    have hαsplit : IsSplitMono α := IsSplitMono.mk'
      { retraction := β ≫ inv (α ≫ β)
        id := by
          rw [Category.assoc]
          exact IsIso.hom_inv_id (α ≫ β) }
    letI : IsSplitMono α := hαsplit
    letI : IsSplitEpi α :=
      σ.isSplitEpi_of_isSplitMono_between_obj α
    letI : IsIso α := isIso_of_epi_of_isSplitMono α
    exact hxy (σ.eq_of_iso ⟨asIso α⟩)
  have hβα : ¬ IsIso (β ≫ α) := by
    intro h
    letI : IsIso (β ≫ α) := h
    have hβsplit : IsSplitMono β := IsSplitMono.mk'
      { retraction := α ≫ inv (β ≫ α)
        id := by
          rw [Category.assoc]
          exact IsIso.hom_inv_id (β ≫ α) }
    letI : IsSplitMono β := hβsplit
    letI : IsSplitEpi β :=
      σ.isSplitEpi_of_isSplitMono_between_obj β
    letI : IsIso β := isIso_of_epi_of_isSplitMono β
    exact hxy (σ.eq_of_iso ⟨asIso β⟩).symm
  let dx : σ.obj x ⟶ σ.obj x := 𝟙 _ - α ≫ β
  let dy : σ.obj y ⟶ σ.obj y := 𝟙 _ - β ≫ α
  have hdxUnit : IsUnit (CategoryTheory.End.of dx) := by
    have hnil := σ.endomorphism_isNilpotent_of_not_isIso_obj
      (α ≫ β) hαβ
    change IsUnit (1 - CategoryTheory.End.of (α ≫ β))
    exact hnil.isUnit_one_sub
  have hdyUnit : IsUnit (CategoryTheory.End.of dy) := by
    have hnil := σ.endomorphism_isNilpotent_of_not_isIso_obj
      (β ≫ α) hβα
    change IsUnit (1 - CategoryTheory.End.of (β ≫ α))
    exact hnil.isUnit_one_sub
  letI : IsIso dx :=
    (CategoryTheory.isUnit_iff_isIso (CategoryTheory.End.of dx)).1 hdxUnit
  letI : IsIso dy :=
    (CategoryTheory.isUnit_iff_isIso (CategoryTheory.End.of dy)).1 hdyUnit
  let rx : M ⟶ σ.obj x := (rx₀ - ry₀ ≫ β) ≫ inv dx
  let ry : M ⟶ σ.obj y := (ry₀ - rx₀ ≫ α) ≫ inv dy
  have hxx : qx ≫ rx = 𝟙 (σ.obj x) := by
    calc
      qx ≫ rx =
          (qx ≫ rx₀ - (qx ≫ ry₀) ≫ β) ≫ inv dx := by
        dsimp only [rx]
        rw [← Category.assoc, Preadditive.comp_sub]
        simp only [Category.assoc]
      _ = dx ≫ inv dx := by
        rw [IsSplitMono.id]
      _ = 𝟙 (σ.obj x) := IsIso.hom_inv_id dx
  have hxy₀ : qx ≫ ry = 0 := by
    calc
      qx ≫ ry =
          (qx ≫ ry₀ - (qx ≫ rx₀) ≫ α) ≫ inv dy := by
        dsimp only [ry]
        rw [← Category.assoc, Preadditive.comp_sub]
        simp only [Category.assoc]
      _ = (α - α) ≫ inv dy := by
        rw [IsSplitMono.id, Category.id_comp]
      _ = 0 := by simp
  have hyx₀ : qy ≫ rx = 0 := by
    calc
      qy ≫ rx =
          (qy ≫ rx₀ - (qy ≫ ry₀) ≫ β) ≫ inv dx := by
        dsimp only [rx]
        rw [← Category.assoc, Preadditive.comp_sub]
        simp only [Category.assoc]
      _ = (β - β) ≫ inv dx := by
        rw [IsSplitMono.id, Category.id_comp]
      _ = 0 := by simp
  have hyy : qy ≫ ry = 𝟙 (σ.obj y) := by
    calc
      qy ≫ ry =
          (qy ≫ ry₀ - (qy ≫ rx₀) ≫ α) ≫ inv dy := by
        dsimp only [ry]
        rw [← Category.assoc, Preadditive.comp_sub]
        simp only [Category.assoc]
      _ = dy ≫ inv dy := by
        rw [IsSplitMono.id]
      _ = 𝟙 (σ.obj y) := IsIso.hom_inv_id dy
  apply IsSplitMono.mk'
  refine { retraction := biprod.lift rx ry, id := ?_ }
  apply biprod.hom_ext
  · apply biprod.hom_ext'
    · simpa only [Category.assoc, biprod.lift_fst,
        Category.comp_id, Category.id_comp, biprod.inl_fst, qx] using hxx
    · simpa only [Category.assoc, biprod.lift_fst,
        Category.comp_id, Category.id_comp, biprod.inr_fst, qy] using hyx₀
  · apply biprod.hom_ext'
    · simpa only [Category.assoc, biprod.lift_snd,
        Category.comp_id, Category.id_comp, biprod.inl_snd, qx] using hxy₀
    · simpa only [Category.assoc, biprod.lift_snd,
        Category.comp_id, Category.id_comp, biprod.inr_snd, qy] using hyy

omit [Fintype ι] in
/-- A row of irreducible maps from two nonisomorphic chosen
indecomposables is irreducible. -/
theorem irreducible_biprod_desc_of_ne
    {x y z : ι} (hxy : x ≠ y)
    {f : σ.obj x ⟶ σ.obj z} {g : σ.obj y ⟶ σ.obj z}
    (hf : IsIrreducibleMorphism f)
    (hg : IsIrreducibleMorphism g) :
    IsIrreducibleMorphism (biprod.desc f g) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    letI : IsSplitMono (biprod.desc f g) := h
    apply hf.not_isSplitMono
    exact IsSplitMono.mk'
      { retraction := retraction (biprod.desc f g) ≫ biprod.fst
        id := by
          calc
            f ≫ (retraction (biprod.desc f g) ≫ biprod.fst) =
                (biprod.inl ≫ biprod.desc f g) ≫
                  retraction (biprod.desc f g) ≫ biprod.fst := by
              rw [biprod.inl_desc]
            _ = biprod.inl ≫
                  (biprod.desc f g ≫ retraction (biprod.desc f g)) ≫
                    biprod.fst := by simp only [Category.assoc]
            _ = 𝟙 (σ.obj x) := by simp }
  · intro h
    letI : IsSplitEpi (biprod.desc f g) := h
    let rt : Retract (σ.obj z) (σ.obj x ⊞ σ.obj y) :=
      { i := section_ (biprod.desc f g)
        r := biprod.desc f g
        retract := IsSplitEpi.id _ }
    have hz : z = x ∨ z = y := by
      let S : Set ι := {x, y}
      have hsum : σ.InAdd S (σ.obj x ⊞ σ.obj y) := by
        let F : WalkingPair → FGModuleCat.{u} R :=
          pairFunction (σ.obj x) (σ.obj y)
        have hF : ∀ j, σ.InAdd S (F j) := by
          intro j
          cases j with
          | left => exact inAdd_obj σ (by simp [S])
          | right => exact inAdd_obj σ (by simp [S])
        have hsum' : σ.InAdd S (biproduct F) :=
          inAdd_biproduct σ (FintypeCat.of WalkingPair) F hF
        let b : BinaryBicone (σ.obj x) (σ.obj y) :=
          (biproduct.bicone F).toBinaryBicone
        have hb : b.IsBilimit :=
          (Bicone.toBinaryBiconeIsBilimit
            (biproduct.bicone F)).symm
            (biproduct.isBilimit F)
        exact (inAdd_iff_of_iso σ
          (biprod.uniqueUpToIso _ _ hb)).1 hsum'
      have := index_mem_of_retract_inAdd σ rt hsum
      simpa only [S, Set.mem_insert_iff, Set.mem_singleton_iff] using this
    rcases hz with hzx | hzy
    · subst z
      exact σ.hasNoIrreducibleEndomorphism_obj x ⟨f, hf⟩
    · subst z
      exact σ.hasNoIrreducibleEndomorphism_obj y ⟨g, hg⟩
  · intro M q r hqr
    by_cases hr : IsSplitEpi r
    · exact Or.inr hr
    · left
      apply σ.isSplitMono_biprod_of_components_of_ne hxy q
      · apply (hf.factorization (biprod.inl ≫ q) r ?_).resolve_right hr
        calc
          (biprod.inl ≫ q) ≫ r = biprod.inl ≫ (q ≫ r) :=
            Category.assoc _ _ _
          _ = biprod.inl ≫ biprod.desc f g := by rw [hqr]
          _ = f := biprod.inl_desc f g
      · apply (hg.factorization (biprod.inr ≫ q) r ?_).resolve_right hr
        calc
          (biprod.inr ≫ q) ≫ r = biprod.inr ≫ (q ≫ r) :=
            Category.assoc _ _ _
          _ = biprod.inr ≫ biprod.desc f g := by rw [hqr]
          _ = g := biprod.inr_desc f g

omit [Fintype ι] in
/-- A component of a minimal left almost-split map along an arbitrary
displayed indecomposable retract of its target is irreducible. -/
theorem irreducible_comp_retraction_of_leftAlmostSplit
    {z x : ι} {M : FGModuleCat.{u} R}
    (k : σ.obj z ⟶ M)
    (hk : IsLeftAlmostSplit k) (hkmin : IsLeftMinimal k)
    (i : σ.obj x ⟶ M) (r : M ⟶ σ.obj x)
    (hir : i ≫ r = 𝟙 (σ.obj x)) :
    IsIrreducibleMorphism (k ≫ r) := by
  let g : σ.obj z ⟶ σ.obj x := k ≫ r
  have hnotmono : ¬ IsSplitMono g := by
    intro hg
    apply hk.not_isSplitMono
    letI : IsSplitMono g := hg
    exact IsSplitMono.mk'
      { retraction := r ≫ retraction g
        id := by simpa only [g, Category.assoc] using IsSplitMono.id g }
  have hnotepi : ¬ IsSplitEpi g := by
    intro hg
    letI : IsSplitEpi g := hg
    exact hnotmono (σ.isSplitMono_of_isSplitEpi_between_obj g)
  refine ⟨hnotmono, hnotepi, ?_⟩
  intro N a b hab
  by_cases ha : IsSplitMono a
  · exact Or.inl ha
  · right
    obtain ⟨c, hc⟩ := hk.factors a ha
    let e : M ⟶ M := 𝟙 M + (c ≫ b - r) ≫ i
    have hefix : k ≫ e = k := by
      dsimp only [e]
      rw [Preadditive.comp_add, Category.comp_id,
        ← Category.assoc, Preadditive.comp_sub]
      have hcb : k ≫ (c ≫ b) = g := by
        rw [← Category.assoc, hc, hab]
      rw [hcb]
      change k + (g - g) ≫ i = k
      simp
    have heir : e ≫ r = c ≫ b := by
      dsimp only [e]
      rw [Preadditive.add_comp, Category.id_comp,
        Category.assoc, hir, Category.comp_id]
      abel
    letI : IsIso e := hkmin e hefix
    exact IsSplitEpi.mk'
      { section_ := i ≫ inv e ≫ c
        id := by
          calc
            (i ≫ inv e ≫ c) ≫ b =
                i ≫ inv e ≫ (c ≫ b) := by
              simp only [Category.assoc]
            _ = i ≫ inv e ≫ (e ≫ r) := by rw [← heir]
            _ = 𝟙 (σ.obj x) := by
              simp only [IsIso.inv_hom_id_assoc, hir] }

omit [Fintype ι] in
/-- The composite around an irreducible directed triangle is a nilpotent
endomorphism.  The sectional-path theorem will contradict one of its zero
powers. -/
theorem irreducibleTriangle_composite_isNilpotent
    {a b c : ι}
    {f : σ.obj a ⟶ σ.obj b} {g : σ.obj b ⟶ σ.obj c}
    {h : σ.obj c ⟶ σ.obj a}
    (hf : IsIrreducibleMorphism f) :
    IsNilpotent (CategoryTheory.End.of (f ≫ g ≫ h)) := by
  apply σ.endomorphism_isNilpotent_of_not_isIso_obj
  intro hIso
  letI : IsIso (f ≫ g ≫ h) := hIso
  apply hf.not_isSplitMono
  exact IsSplitMono.mk'
    { retraction := (g ≫ h) ≫ inv (f ≫ g ≫ h)
      id := by
        simpa only [Category.assoc] using
          IsIso.hom_inv_id (f ≫ g ≫ h) }

namespace FiniteARTranslationData

variable (AR : σ.FiniteARTranslationData)

omit [Fintype ι] in
/-- Peel an irreducible terminal row from a nonzero relation.  The
penultimate indecomposable is displayed as a retract of the row source.
The AR kernel then supplies an irreducible map from the translate of the
endpoint through which the preceding composite factors. -/
theorem exists_irreducible_arTranslation_factor
    {a b c : ι} {E : FGModuleCat.{u} R}
    (row : E ⟶ σ.obj c) (hrow : IsIrreducibleMorphism row)
    (column : σ.obj a ⟶ E) (hcolumnNe : column ≠ 0)
    (hzero : column ≫ row = 0)
    (inc : σ.obj b ⟶ E) (ret : E ⟶ σ.obj b)
    (hincRet : inc ≫ ret = 𝟙 (σ.obj b))
    (p : σ.obj a ⟶ σ.obj b) (hp : column ≫ ret = p) :
    ∃ (hcNP : ¬ Projective (σ.obj c))
      (qTau : σ.obj a ⟶ σ.obj (AR.arTranslation σ ⟨c, hcNP⟩).1)
      (tTau : σ.obj (AR.arTranslation σ ⟨c, hcNP⟩).1 ⟶ σ.obj b),
      IsIrreducibleMorphism tTau ∧ qTau ≫ tTau = p := by
  have hrowNotMono : ¬ Mono row := by
    intro hmono
    letI : Mono row := hmono
    apply hcolumnNe
    apply (cancel_mono row).1
    simpa only [zero_comp] using hzero
  have hrowEpi : Epi row :=
    (QuotientSubmoduleEquidistribution.RepresentationDirected.mono_or_epi_of_isIrreducibleMorphism
      hrow).resolve_left hrowNotMono
  letI : Epi row := hrowEpi
  have hcNP : ¬ Projective (σ.obj c) :=
    QuotientSubmoduleEquidistribution.RepresentationDirected.not_projective_target_of_isIrreducibleMorphism_of_epi
      hrow
  let cNP : σ.NonprojectiveLabel := ⟨c, hcNP⟩
  let A := AR.chosenRightAR σ cNP
  letI : Epi A.map :=
    IsRightAlmostSplit.epi_of_not_projective_obj σ A.map
      A.rightAlmostSplit hcNP
  obtain ⟨s, hs⟩ := A.rightAlmostSplit.factors row hrow.not_isSplitEpi
  have hsSplit : IsSplitMono s := by
    rcases hrow.factorization s A.map hs with hsSplit | hASsplit
    · exact hsSplit
    · exact (A.rightAlmostSplit.not_isSplitEpi hASsplit).elim
  letI : IsSplitMono s := hsSplit
  let inc' : σ.obj b ⟶ A.middle := inc ≫ s
  let ret' : A.middle ⟶ σ.obj b := retraction s ≫ ret
  have hincRet' : inc' ≫ ret' = 𝟙 (σ.obj b) := by
    dsimp only [inc', ret']
    rw [Category.assoc, ← Category.assoc s, IsSplitMono.id,
      Category.id_comp, hincRet]
  let l : σ.obj a ⟶ kernel A.map :=
    kernel.lift A.map (column ≫ s) (by
      rw [Category.assoc, hs, hzero])
  let qTau : σ.obj a ⟶ σ.obj (AR.arTranslation σ cNP).1 :=
    l ≫ (AR.arTranslationKernelIso σ cNP).hom
  have hqKernel :
      qTau ≫ AR.arKernelMap σ cNP = column ≫ s := by
    dsimp only [qTau, FiniteARTranslationData.arKernelMap]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact kernel.lift_ι A.map (column ≫ s) _
  let tTau : σ.obj (AR.arTranslation σ cNP).1 ⟶ σ.obj b :=
    AR.arKernelMap σ cNP ≫ ret'
  have htTauIrreducible : IsIrreducibleMorphism tTau := by
    apply σ.irreducible_comp_retraction_of_leftAlmostSplit
      (AR.arKernelMap σ cNP)
      (AR.arKernelMap_leftAlmostSplit σ cNP)
      (AR.arKernelMap_leftMinimal σ cNP) inc' ret' hincRet'
  refine ⟨hcNP, qTau, tTau, htTauIrreducible, ?_⟩
  change (qTau ≫ AR.arKernelMap σ cNP) ≫ ret' = p
  rw [hqKernel]
  dsimp only [ret']
  rw [Category.assoc, ← Category.assoc s, IsSplitMono.id,
    Category.id_comp, hp]

omit [Fintype ι] in
/-- The length-two case of the sectional-composition theorem.  If two
irreducible maps have zero composite, the path is nonsectional: the first
endpoint is the AR translate of the last endpoint. -/
theorem arTranslation_eq_source_of_irreducible_comp_eq_zero
    {a b c : ι}
    {f : σ.obj a ⟶ σ.obj b} {g : σ.obj b ⟶ σ.obj c}
    (hf : IsIrreducibleMorphism f)
    (hg : IsIrreducibleMorphism g)
    (hzero : f ≫ g = 0) :
    ∃ hcNP : ¬ Projective (σ.obj c),
      (AR.arTranslation σ ⟨c, hcNP⟩).1 = a := by
  have hgNotMono : ¬ Mono g := by
    intro hgMono
    letI : Mono g := hgMono
    apply σ.irreducibleMorphism_ne_zero_obj hf
    apply (cancel_mono g).1
    simpa only [zero_comp] using hzero
  have hgEpi : Epi g :=
    (QuotientSubmoduleEquidistribution.RepresentationDirected.mono_or_epi_of_isIrreducibleMorphism
      hg).resolve_left hgNotMono
  letI : Epi g := hgEpi
  have hcNP : ¬ Projective (σ.obj c) :=
    QuotientSubmoduleEquidistribution.RepresentationDirected.not_projective_target_of_isIrreducibleMorphism_of_epi
      hg
  refine ⟨hcNP, ?_⟩
  let cNP : σ.NonprojectiveLabel := ⟨c, hcNP⟩
  let A := AR.chosenRightAR σ cNP
  letI : Epi A.map :=
    IsRightAlmostSplit.epi_of_not_projective_obj σ A.map
      A.rightAlmostSplit hcNP
  obtain ⟨s, hs⟩ := A.rightAlmostSplit.factors g hg.not_isSplitEpi
  have hsSplit : IsSplitMono s := by
    rcases hg.factorization s A.map hs with hsSplit | hASsplit
    · exact hsSplit
    · exact (A.rightAlmostSplit.not_isSplitEpi hASsplit).elim
  letI : IsSplitMono s := hsSplit
  let l : σ.obj a ⟶ kernel A.map :=
    kernel.lift A.map (f ≫ s) (by
      rw [Category.assoc, hs, hzero])
  let q : σ.obj a ⟶ σ.obj (AR.arTranslation σ cNP).1 :=
    l ≫ (AR.arTranslationKernelIso σ cNP).hom
  have hqKernel :
      q ≫ AR.arKernelMap σ cNP = f ≫ s := by
    dsimp only [q, FiniteARTranslationData.arKernelMap]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact kernel.lift_ι A.map (f ≫ s) _
  let t : σ.obj (AR.arTranslation σ cNP).1 ⟶ σ.obj b :=
    AR.arKernelMap σ cNP ≫ retraction s
  have hfactor : q ≫ t = f := by
    change (q ≫ AR.arKernelMap σ cNP) ≫ retraction s = f
    rw [hqKernel, Category.assoc,
      IsSplitMono.id, Category.comp_id]
  rcases hf.factorization q t hfactor with hqSplit | htSplit
  · letI : IsSplitMono q := hqSplit
    letI : IsSplitEpi q := σ.isSplitEpi_of_isSplitMono_between_obj q
    letI : IsIso q := isIso_of_epi_of_isSplitMono q
    exact (σ.eq_of_iso ⟨asIso q⟩).symm
  · letI : IsSplitEpi t := htSplit
    letI : IsSplitMono t := σ.isSplitMono_of_isSplitEpi_between_obj t
    letI : IsIso t := isIso_of_mono_of_isSplitEpi t
    have htLabel : (AR.arTranslation σ cNP).1 = b :=
      σ.eq_of_iso ⟨asIso t⟩
    exfalso
    apply AR.no_irreducible_arTranslation_to_endpoint σ cNP
    have hbc : HasIrreducibleMorphism (σ.obj b) (σ.obj c) := ⟨g, hg⟩
    simpa only [htLabel] using hbc

omit [Fintype ι] in
/-- The factor-through alternative in the length-two
Auslander--Reiten induction.  If the composite of `a → b → c` factors
through a second summand `d → c`, and the displayed row into `c` is
irreducible, then again `τ c = a`. -/
theorem arTranslation_eq_source_of_irreducible_comp_factor
    {a b c d : ι}
    {f : σ.obj a ⟶ σ.obj b} {g : σ.obj b ⟶ σ.obj c}
    {q : σ.obj a ⟶ σ.obj d} {t : σ.obj d ⟶ σ.obj c}
    (hf : IsIrreducibleMorphism f)
    (hg : IsIrreducibleMorphism g)
    (hrow : IsIrreducibleMorphism (biprod.desc g t))
    (hfac : f ≫ g = q ≫ t) :
    ∃ hcNP : ¬ Projective (σ.obj c),
      (AR.arTranslation σ ⟨c, hcNP⟩).1 = a := by
  let column : σ.obj a ⟶ σ.obj b ⊞ σ.obj d :=
    biprod.lift f (-q)
  let row : σ.obj b ⊞ σ.obj d ⟶ σ.obj c :=
    biprod.desc g t
  have hcolumnRow : column ≫ row = 0 := by
    dsimp only [column, row]
    rw [biprod.lift_desc, Preadditive.neg_comp, hfac]
    abel
  have hcolumnNe : column ≠ 0 := by
    intro hzero
    apply σ.irreducibleMorphism_ne_zero_obj hf
    calc
      f = column ≫ biprod.fst := by
        simp [column]
      _ = 0 := by rw [hzero, zero_comp]
  have hrowNotMono : ¬ Mono row := by
    intro hmono
    letI : Mono row := hmono
    apply hcolumnNe
    apply (cancel_mono row).1
    simpa only [zero_comp] using hcolumnRow
  have hrowEpi : Epi row :=
    (QuotientSubmoduleEquidistribution.RepresentationDirected.mono_or_epi_of_isIrreducibleMorphism
      hrow).resolve_left hrowNotMono
  letI : Epi row := hrowEpi
  have hcNP : ¬ Projective (σ.obj c) :=
    QuotientSubmoduleEquidistribution.RepresentationDirected.not_projective_target_of_isIrreducibleMorphism_of_epi
      hrow
  refine ⟨hcNP, ?_⟩
  let cNP : σ.NonprojectiveLabel := ⟨c, hcNP⟩
  let A := AR.chosenRightAR σ cNP
  letI : Epi A.map :=
    IsRightAlmostSplit.epi_of_not_projective_obj σ A.map
      A.rightAlmostSplit hcNP
  obtain ⟨s, hs⟩ := A.rightAlmostSplit.factors row hrow.not_isSplitEpi
  have hsSplit : IsSplitMono s := by
    rcases hrow.factorization s A.map hs with hsSplit | hASsplit
    · exact hsSplit
    · exact (A.rightAlmostSplit.not_isSplitEpi hASsplit).elim
  letI : IsSplitMono s := hsSplit
  let inc : σ.obj b ⟶ A.middle := biprod.inl ≫ s
  let ret : A.middle ⟶ σ.obj b := retraction s ≫ biprod.fst
  have hincRet : inc ≫ ret = 𝟙 (σ.obj b) := by
    dsimp only [inc, ret]
    rw [Category.assoc, ← Category.assoc s, IsSplitMono.id,
      Category.id_comp, biprod.inl_fst]
  let l : σ.obj a ⟶ kernel A.map :=
    kernel.lift A.map (column ≫ s) (by
      rw [Category.assoc, hs, hcolumnRow])
  let qTau : σ.obj a ⟶ σ.obj (AR.arTranslation σ cNP).1 :=
    l ≫ (AR.arTranslationKernelIso σ cNP).hom
  have hqKernel :
      qTau ≫ AR.arKernelMap σ cNP = column ≫ s := by
    dsimp only [qTau, FiniteARTranslationData.arKernelMap]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact kernel.lift_ι A.map (column ≫ s) _
  let tTau : σ.obj (AR.arTranslation σ cNP).1 ⟶ σ.obj b :=
    AR.arKernelMap σ cNP ≫ ret
  have htTauIrreducible : IsIrreducibleMorphism tTau := by
    apply σ.irreducible_comp_retraction_of_leftAlmostSplit
      (AR.arKernelMap σ cNP)
      (AR.arKernelMap_leftAlmostSplit σ cNP)
      (AR.arKernelMap_leftMinimal σ cNP) inc ret hincRet
  have hfactor : qTau ≫ tTau = f := by
    change (qTau ≫ AR.arKernelMap σ cNP) ≫ ret = f
    rw [hqKernel]
    dsimp only [ret]
    rw [Category.assoc, ← Category.assoc s, IsSplitMono.id,
      Category.id_comp]
    exact biprod.lift_fst f (-q)
  rcases hf.factorization qTau tTau hfactor with hqSplit | htSplit
  · letI : IsSplitMono qTau := hqSplit
    letI : IsSplitEpi qTau :=
      σ.isSplitEpi_of_isSplitMono_between_obj qTau
    letI : IsIso qTau := isIso_of_epi_of_isSplitMono qTau
    exact (σ.eq_of_iso ⟨asIso qTau⟩).symm
  · letI : IsSplitEpi tTau := htSplit
    letI : IsSplitMono tTau :=
      σ.isSplitMono_of_isSplitEpi_between_obj tTau
    letI : IsIso tTau := isIso_of_mono_of_isSplitEpi tTau
    have htLabel : (AR.arTranslation σ cNP).1 = b :=
      σ.eq_of_iso ⟨asIso tTau⟩
    exfalso
    apply AR.no_irreducible_arTranslation_to_endpoint σ cNP
    have hbc : HasIrreducibleMorphism (σ.obj b) (σ.obj c) := ⟨g, hg⟩
    simpa only [htLabel] using hbc

omit [Fintype ι] in
/-- A sectional path of length two has nonzero composite. -/
theorem irreducible_comp_ne_zero_of_arTranslation_ne_source
    {a b c : ι}
    {f : σ.obj a ⟶ σ.obj b} {g : σ.obj b ⟶ σ.obj c}
    (hf : IsIrreducibleMorphism f)
    (hg : IsIrreducibleMorphism g)
    (hcNP : ¬ Projective (σ.obj c))
    (hsectional : (AR.arTranslation σ ⟨c, hcNP⟩).1 ≠ a) :
    f ≫ g ≠ 0 := by
  intro hzero
  obtain ⟨hcNP', htau⟩ :=
    AR.arTranslation_eq_source_of_irreducible_comp_eq_zero
      σ hf hg hzero
  apply hsectional
  simpa only using htau

/-- An infinite sequence of chosen indecomposable labels and irreducible
maps.  Finite paths are obtained by taking prefixes. -/
structure NatIrreducibleSequence where
  label : ℕ → ι
  map : ∀ n : ℕ, σ.obj (label n) ⟶ σ.obj (label (n + 1))
  irreducible : ∀ n : ℕ, IsIrreducibleMorphism (map n)

namespace NatIrreducibleSequence

variable (S : NatIrreducibleSequence σ)

/-- Composite of the first `n` maps of an irreducible sequence. -/
def composite : ∀ n : ℕ, σ.obj (S.label 0) ⟶ σ.obj (S.label n)
  | 0 => 𝟙 _
  | n + 1 => composite n ≫ S.map n

omit [Fintype ι] in
@[simp]
theorem composite_zero : composite σ S 0 = 𝟙 _ := rfl

omit [Fintype ι] in
@[simp]
theorem composite_succ (n : ℕ) :
    composite σ S (n + 1) = composite σ S n ≫ S.map n := rfl

/-- The strengthened terminal condition in the standard AR induction:
the composite is zero, or it factors through a second summand whose row
with the last path map is irreducible. -/
def HasTerminalRelation (m : ℕ) : Prop :=
  composite σ S (m + 2) = 0 ∨
    ∃ (d : ι)
      (q : σ.obj (S.label 0) ⟶ σ.obj d)
      (t : σ.obj d ⟶ σ.obj (S.label (m + 2))),
      IsIrreducibleMorphism (biprod.desc (S.map (m + 1)) t) ∧
        composite σ S (m + 2) = q ≫ t

omit [Fintype ι] in
/-- Auslander--Reiten--Smalø Lemma VII.2.5 in prefix form.  A zero
composite, or the stronger terminal factor relation used by the induction,
forces a nonsectional length-two corner. -/
theorem exists_nonsectional_corner_of_terminalRelation :
    ∀ m : ℕ, HasTerminalRelation σ S m →
      ∃ j : ℕ, j ≤ m ∧
        ∃ hjNP : ¬ Projective (σ.obj (S.label (j + 2))),
          (AR.arTranslation σ ⟨S.label (j + 2), hjNP⟩).1 =
            S.label j := by
  intro m
  induction m with
  | zero =>
      intro h
      rcases h with hzero | ⟨d, q, t, hrow, hfac⟩
      · have hzero' : S.map 0 ≫ S.map 1 = 0 := by
          simpa only [composite, Category.id_comp] using hzero
        obtain ⟨hNP, htau⟩ :=
          AR.arTranslation_eq_source_of_irreducible_comp_eq_zero σ
            (S.irreducible 0) (S.irreducible 1) hzero'
        exact ⟨0, Nat.le_refl 0, hNP, by simpa only using htau⟩
      · have hfac' : S.map 0 ≫ S.map 1 = q ≫ t := by
          simpa only [composite, Category.id_comp] using hfac
        obtain ⟨hNP, htau⟩ :=
          AR.arTranslation_eq_source_of_irreducible_comp_factor σ
            (S.irreducible 0) (S.irreducible 1) hrow hfac'
        exact ⟨0, Nat.le_refl 0, hNP, by simpa only using htau⟩
  | succ m ih =>
      intro hterminal
      by_cases hprefix : composite σ S (m + 2) = 0
      · obtain ⟨j, hj, hjNP, htau⟩ := ih (Or.inl hprefix)
        exact ⟨j, Nat.le.step hj, hjNP, htau⟩
      · have hpeel :
          ∃ (hcNP : ¬ Projective (σ.obj (S.label (m + 3))))
            (qTau : σ.obj (S.label 0) ⟶
              σ.obj (AR.arTranslation σ
                ⟨S.label (m + 3), hcNP⟩).1)
            (tTau : σ.obj (AR.arTranslation σ
                ⟨S.label (m + 3), hcNP⟩).1 ⟶
              σ.obj (S.label (m + 2))),
            IsIrreducibleMorphism tTau ∧
              qTau ≫ tTau = composite σ S (m + 2) := by
          rcases hterminal with hzero | ⟨d, q, t, hrow, hfac⟩
          · have hzero' :
                composite σ S (m + 2) ≫ S.map (m + 2) = 0 := by
              simpa only [composite, Nat.succ_eq_add_one,
                Nat.add_assoc, Nat.reduceAdd] using hzero
            simpa only [Category.comp_id] using
              (AR.exists_irreducible_arTranslation_factor σ
                (row := S.map (m + 2)) (S.irreducible (m + 2))
                (column := composite σ S (m + 2)) hprefix hzero'
                (inc := 𝟙 _) (ret := 𝟙 _) (by simp)
                (p := composite σ S (m + 2)) (by simp))
          · let column : σ.obj (S.label 0) ⟶
                σ.obj (S.label (m + 2)) ⊞ σ.obj d :=
              biprod.lift (composite σ S (m + 2)) (-q)
            have hcolumnNe : column ≠ 0 := by
              intro hzero
              apply hprefix
              calc
                composite σ S (m + 2) = column ≫ biprod.fst := by
                  simp [column]
                _ = 0 := by rw [hzero, zero_comp]
            have hfac' :
                composite σ S (m + 2) ≫ S.map (m + 2) = q ≫ t := by
              simpa only [composite, Nat.succ_eq_add_one,
                Nat.add_assoc, Nat.reduceAdd] using hfac
            have hzero' :
                column ≫ biprod.desc (S.map (m + 2)) t = 0 := by
              dsimp only [column]
              rw [biprod.lift_desc, Preadditive.neg_comp, hfac']
              abel
            simpa only [column, biprod.lift_fst] using
              (AR.exists_irreducible_arTranslation_factor σ
                (row := biprod.desc (S.map (m + 2)) t) hrow
                (column := column) hcolumnNe hzero'
                (inc := biprod.inl) (ret := biprod.fst) (by simp)
                (p := composite σ S (m + 2)) (by simp [column]))
        obtain ⟨hcNP, qTau, tTau, htTau, hfactor⟩ := hpeel
        by_cases hlast :
            (AR.arTranslation σ ⟨S.label (m + 3), hcNP⟩).1 =
              S.label (m + 1)
        · exact ⟨m + 1, Nat.le_refl _, hcNP, by simpa only using hlast⟩
        · have hne : S.label (m + 1) ≠
              (AR.arTranslation σ ⟨S.label (m + 3), hcNP⟩).1 := by
            exact fun h ↦ hlast h.symm
          have hrow : IsIrreducibleMorphism
              (biprod.desc (S.map (m + 1)) tTau) :=
            σ.irreducible_biprod_desc_of_ne hne
              (S.irreducible (m + 1)) htTau
          obtain ⟨j, hj, hjNP, htau⟩ := ih
            (Or.inr ⟨_, qTau, tTau, hrow, hfactor.symm⟩)
          exact ⟨j, Nat.le.step hj, hjNP, htau⟩

omit [Fintype ι] in
/-- Every finite sectional prefix of irreducible maps has nonzero
composite. -/
theorem composite_ne_zero_of_sectional
    (n : ℕ)
    (hsectional : ∀ j : ℕ, j + 2 ≤ n →
      ∀ hjNP : ¬ Projective (σ.obj (S.label (j + 2))),
        (AR.arTranslation σ ⟨S.label (j + 2), hjNP⟩).1 ≠
          S.label j) :
    composite σ S n ≠ 0 := by
  cases n with
  | zero =>
      intro hzero
      have hobj : IsZero (σ.obj (S.label 0)) :=
        (IsZero.iff_id_eq_zero _).2 (by
          simpa only [composite] using hzero)
      let U := forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)
      have hobj' : IsZero (U.obj (σ.obj (S.label 0))) :=
        U.map_isZero hobj
      have hs : Subsingleton (σ.obj (S.label 0)) :=
        ModuleCat.isZero_iff_subsingleton.mp hobj'
      exact not_nontrivial_iff_subsingleton.mpr hs
        (σ.indecomposable (S.label 0)).1
  | succ n =>
      cases n with
      | zero =>
          simpa only [composite, Category.id_comp] using
            σ.irreducibleMorphism_ne_zero_obj (S.irreducible 0)
      | succ m =>
          intro hzero
          obtain ⟨j, hj, hjNP, htau⟩ :=
            exists_nonsectional_corner_of_terminalRelation σ AR S m
              (Or.inl (by simpa only [Nat.add_comm] using hzero))
          exact hsectional j (by omega) hjNP htau

/-- Three cyclic positions used to unfold an oriented triangle into an
infinite sequence. -/
inductive TrianglePosition
  | first
  | second
  | third
  deriving DecidableEq

namespace TrianglePosition

/-- Advance one edge around the triangle. -/
def next : TrianglePosition → TrianglePosition
  | first => second
  | second => third
  | third => first

@[simp] theorem next_first : next first = second := rfl
@[simp] theorem next_second : next second = third := rfl
@[simp] theorem next_third : next third = first := rfl

theorem next_three (p : TrianglePosition) :
    next (next (next p)) = p := by
  cases p <;> rfl

/-- Position after `n` steps around the triangle. -/
def position : ℕ → TrianglePosition
  | 0 => first
  | n + 1 => next (position n)

@[simp] theorem position_zero : position 0 = first := rfl
@[simp] theorem position_succ (n : ℕ) :
    position (n + 1) = next (position n) := rfl

theorem position_add_two (n : ℕ) :
    position (n + 2) = next (next (position n)) := by
  rfl

theorem position_add_three (n : ℕ) : position (n + 3) = position n := by
  change next (next (next (position n))) = position n
  exact next_three (position n)

theorem position_three_mul (n : ℕ) : position (3 * n) = first := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Nat.mul_succ, position_add_three, ih]

end TrianglePosition

/-- Labels attached to the three cyclic positions. -/
def triangleLabel (a b c : ι) : TrianglePosition → ι
  | .first => a
  | .second => b
  | .third => c

/-- The three maps of an oriented triangle, indexed cyclically. -/
def triangleMap
    {a b c : ι}
    (f : σ.obj a ⟶ σ.obj b)
    (g : σ.obj b ⟶ σ.obj c)
    (h : σ.obj c ⟶ σ.obj a) :
    ∀ p : TrianglePosition,
      σ.obj (triangleLabel a b c p) ⟶
        σ.obj (triangleLabel a b c p.next)
  | .first => f
  | .second => g
  | .third => h

omit [Fintype ι] in
/-- Every cyclicly indexed triangle map is irreducible when its three
components are. -/
theorem triangleMap_irreducible
    {a b c : ι}
    {f : σ.obj a ⟶ σ.obj b}
    {g : σ.obj b ⟶ σ.obj c}
    {h : σ.obj c ⟶ σ.obj a}
    (hf : IsIrreducibleMorphism f)
    (hg : IsIrreducibleMorphism g)
    (hh : IsIrreducibleMorphism h) :
    ∀ p : TrianglePosition,
      IsIrreducibleMorphism (triangleMap σ f g h p)
  | .first => hf
  | .second => hg
  | .third => hh

/-- Unfold an oriented irreducible triangle into an infinite irreducible
sequence. -/
def ofTriangle
    {a b c : ι}
    (f : σ.obj a ⟶ σ.obj b)
    (g : σ.obj b ⟶ σ.obj c)
    (h : σ.obj c ⟶ σ.obj a)
    (hf : IsIrreducibleMorphism f)
    (hg : IsIrreducibleMorphism g)
    (hh : IsIrreducibleMorphism h) :
    NatIrreducibleSequence σ where
  label n := triangleLabel a b c (TrianglePosition.position n)
  map n := triangleMap σ f g h (TrianglePosition.position n)
  irreducible n :=
    triangleMap_irreducible σ hf hg hh (TrianglePosition.position n)

omit [Fintype ι] in
/-- Every third label of the unfolded triangle is its first label. -/
theorem ofTriangle_label_three_mul
    {a b c : ι}
    (f : σ.obj a ⟶ σ.obj b)
    (g : σ.obj b ⟶ σ.obj c)
    (h : σ.obj c ⟶ σ.obj a)
    (hf : IsIrreducibleMorphism f)
    (hg : IsIrreducibleMorphism g)
    (hh : IsIrreducibleMorphism h)
    (n : ℕ) :
    (ofTriangle σ f g h hf hg hh).label (3 * n) = a := by
  change triangleLabel a b c (TrianglePosition.position (3 * n)) = a
  rw [TrianglePosition.position_three_mul]
  rfl

omit [Fintype ι] in
private theorem triangle_three_edge_block_of_eq_first
    {a b c : ι}
    (f : σ.obj a ⟶ σ.obj b)
    (g : σ.obj b ⟶ σ.obj c)
    (h : σ.obj c ⟶ σ.obj a)
    (p : TrianglePosition) (hp : p = TrianglePosition.first) :
    let hp3 : p.next.next.next = TrianglePosition.first := by
      rw [TrianglePosition.next_three, hp]
    let hlabel0 : triangleLabel a b c p = a :=
      congrArg (triangleLabel a b c) hp
    let hlabel3 : triangleLabel a b c p.next.next.next = a :=
      congrArg (triangleLabel a b c) hp3
    triangleMap σ f g h p ≫ triangleMap σ f g h p.next ≫
        triangleMap σ f g h p.next.next ≫
          eqToHom (congrArg σ.obj hlabel3) =
      eqToHom (congrArg σ.obj hlabel0) ≫ f ≫ g ≫ h := by
  subst p
  rfl

omit [Fintype ι] in
/-- One three-edge block of the unfolded triangle is the original cycle,
with the endpoint transports made explicit. -/
theorem ofTriangle_three_edge_block
    {a b c : ι}
    (f : σ.obj a ⟶ σ.obj b)
    (g : σ.obj b ⟶ σ.obj c)
    (h : σ.obj c ⟶ σ.obj a)
    (hf : IsIrreducibleMorphism f)
    (hg : IsIrreducibleMorphism g)
    (hh : IsIrreducibleMorphism h)
    (n : ℕ) :
    let T := ofTriangle σ f g h hf hg hh
    T.map (3 * n) ≫ T.map (3 * n + 1) ≫ T.map (3 * n + 2) ≫
        eqToHom (congrArg σ.obj
          (ofTriangle_label_three_mul σ f g h hf hg hh (n + 1))) =
      eqToHom (congrArg σ.obj
          (ofTriangle_label_three_mul σ f g h hf hg hh n)) ≫
        f ≫ g ≫ h := by
  simp only [ofTriangle, TrianglePosition.position_succ]
  let p := TrianglePosition.position (3 * n)
  have hp : p = TrianglePosition.first :=
    TrianglePosition.position_three_mul n
  have hp3 : p.next.next.next = TrianglePosition.first := by
    rw [TrianglePosition.next_three, hp]
  have hlabel0 : triangleLabel a b c p = a :=
    congrArg (triangleLabel a b c) hp
  have hlabel3 : triangleLabel a b c p.next.next.next = a :=
    congrArg (triangleLabel a b c) hp3
  change
    triangleMap σ f g h p ≫ triangleMap σ f g h p.next ≫
        triangleMap σ f g h p.next.next ≫
          eqToHom (congrArg σ.obj hlabel3) =
      eqToHom (congrArg σ.obj hlabel0) ≫ f ≫ g ≫ h
  exact triangle_three_edge_block_of_eq_first σ f g h p hp

omit [Fintype ι] in
/-- The first `3n` maps of the unfolded triangle compose to the `n`th
power of its cycle endomorphism, after the canonical endpoint transport. -/
theorem ofTriangle_composite_three_mul
    {a b c : ι}
    (f : σ.obj a ⟶ σ.obj b)
    (g : σ.obj b ⟶ σ.obj c)
    (h : σ.obj c ⟶ σ.obj a)
    (hf : IsIrreducibleMorphism f)
    (hg : IsIrreducibleMorphism g)
    (hh : IsIrreducibleMorphism h)
    (n : ℕ) :
    let T := ofTriangle σ f g h hf hg hh
    composite σ T (3 * n) ≫
        eqToHom (congrArg σ.obj
          (ofTriangle_label_three_mul σ f g h hf hg hh n)) =
      ((CategoryTheory.End.of (f ≫ g ≫ h)) ^ n :
        CategoryTheory.End (σ.obj a)) := by
  let T := ofTriangle σ f g h hf hg hh
  induction n with
  | zero => rfl
  | succ n ih =>
      have hblock := ofTriangle_three_edge_block σ f g h hf hg hh n
      change
        composite σ T (3 * n + 3) ≫
            eqToHom (congrArg σ.obj
              (ofTriangle_label_three_mul σ f g h hf hg hh (n + 1))) =
          ((CategoryTheory.End.of (f ≫ g ≫ h)) ^ (n + 1) :
            CategoryTheory.End (σ.obj a))
      have hprev :
        composite σ T (3 * n + 3) ≫
              eqToHom (congrArg σ.obj
                (ofTriangle_label_three_mul σ f g h hf hg hh (n + 1))) =
            ((CategoryTheory.End.of (f ≫ g ≫ h)) ^ n :
              CategoryTheory.End (σ.obj a)) ≫ (f ≫ g ≫ h) := by
        calc
          composite σ T (3 * n + 3) ≫
                eqToHom (congrArg σ.obj
                  (ofTriangle_label_three_mul σ f g h hf hg hh (n + 1))) =
              composite σ T (3 * n) ≫
              (T.map (3 * n) ≫ T.map (3 * n + 1) ≫
                T.map (3 * n + 2) ≫
                  eqToHom (congrArg σ.obj
                    (ofTriangle_label_three_mul σ f g h hf hg hh
                      (n + 1)))) := by
            simp only [composite, Category.assoc]
          _ = composite σ T (3 * n) ≫
              (eqToHom (congrArg σ.obj
                  (ofTriangle_label_three_mul σ f g h hf hg hh n)) ≫
                f ≫ g ≫ h) := by rw [hblock]
          _ = (composite σ T (3 * n) ≫
                eqToHom (congrArg σ.obj
                  (ofTriangle_label_three_mul σ f g h hf hg hh n))) ≫
              f ≫ g ≫ h := by simp only [Category.assoc]
          _ = ((CategoryTheory.End.of (f ≫ g ≫ h)) ^ n :
                CategoryTheory.End (σ.obj a)) ≫
              (f ≫ g ≫ h) := by
            rw [ih]
            rfl
      rw [hprev, pow_succ', CategoryTheory.End.mul_def]

omit [Fintype ι] in
private theorem triangle_sectional_corner
    {a b c : ι}
    (haNP : ¬ Projective (σ.obj a))
    (hbNP : ¬ Projective (σ.obj b))
    (hcNP : ¬ Projective (σ.obj c))
    (hta : (AR.arTranslation σ ⟨a, haNP⟩).1 ≠ b)
    (htb : (AR.arTranslation σ ⟨b, hbNP⟩).1 ≠ c)
    (htc : (AR.arTranslation σ ⟨c, hcNP⟩).1 ≠ a)
    (p : TrianglePosition)
    (hpNP : ¬ Projective
      (σ.obj (triangleLabel a b c p.next.next))) :
    (AR.arTranslation σ
      ⟨triangleLabel a b c p.next.next, hpNP⟩).1 ≠
        triangleLabel a b c p := by
  cases p with
  | first => simpa only [triangleLabel, TrianglePosition.next] using htc
  | second => simpa only [triangleLabel, TrianglePosition.next] using hta
  | third => simpa only [triangleLabel, TrianglePosition.next] using htb

omit [Fintype ι] in
/-- There is no sectional oriented triangle of irreducible maps.  This is
ARS Corollary VII.2.6 specialized to three vertices. -/
theorem not_sectional_irreducibleTriangle
    {a b c : ι}
    {f : σ.obj a ⟶ σ.obj b}
    {g : σ.obj b ⟶ σ.obj c}
    {h : σ.obj c ⟶ σ.obj a}
    (hf : IsIrreducibleMorphism f)
    (hg : IsIrreducibleMorphism g)
    (hh : IsIrreducibleMorphism h)
    (haNP : ¬ Projective (σ.obj a))
    (hbNP : ¬ Projective (σ.obj b))
    (hcNP : ¬ Projective (σ.obj c)) :
    ¬ ((AR.arTranslation σ ⟨a, haNP⟩).1 ≠ b ∧
      (AR.arTranslation σ ⟨b, hbNP⟩).1 ≠ c ∧
      (AR.arTranslation σ ⟨c, hcNP⟩).1 ≠ a) := by
  rintro ⟨hta, htb, htc⟩
  let T := ofTriangle σ f g h hf hg hh
  obtain ⟨n, hn⟩ := σ.irreducibleTriangle_composite_isNilpotent hf
  have hpower := ofTriangle_composite_three_mul σ f g h hf hg hh n
  have hpost :
      composite σ T (3 * n) ≫
          eqToHom (congrArg σ.obj
            (ofTriangle_label_three_mul σ f g h hf hg hh n)) = 0 := by
    exact hpower.trans hn
  have hcomposite : composite σ T (3 * n) = 0 := by
    apply (cancel_mono (eqToHom (congrArg σ.obj
      (ofTriangle_label_three_mul σ f g h hf hg hh n)))).1
    simpa only [zero_comp] using hpost
  apply (composite_ne_zero_of_sectional σ AR T (3 * n) ?_)
    hcomposite
  intro j hj hjNP
  change
    (AR.arTranslation σ
      ⟨triangleLabel a b c (TrianglePosition.position (j + 2)),
        hjNP⟩).1 ≠
      triangleLabel a b c (TrianglePosition.position j)
  simpa only [TrianglePosition.position_add_two] using
    (triangle_sectional_corner σ AR haNP hbNP hcNP hta htb htc
      (TrianglePosition.position j) hjNP)

end NatIrreducibleSequence

end FiniteARTranslationData

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
