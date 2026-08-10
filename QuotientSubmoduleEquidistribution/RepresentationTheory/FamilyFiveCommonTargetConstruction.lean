import QuotientSubmoduleEquidistribution.RepresentationTheory.FamilyFiveCollectiveClosure
import QuotientSubmoduleEquidistribution.RepresentationTheory.GabrielArrowBridge

/-!
# Constructing the common-target family-5 apex
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace QuotientSubmoduleEquidistribution.FamilyFiveCommonTargetConstruction

universe u

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

open QuotientSubmoduleEquidistribution.YonedaExtReflection

/-- The extension whose restrictions to the two binary-biproduct summands
are the prescribed classes. -/
def combinedExt
    {R : Type u} [Ring R]
    {S T U : ModuleCat.{u} R}
    (xi : Ext S U 1) (eta : Ext T U 1) :
    Ext (S ⊞ T) U 1 :=
  Ext.biprodAddEquiv.symm (xi, eta)

@[simp]
theorem extBiprodLeft_combinedExt
    {R : Type u} [Ring R]
    {S T U : ModuleCat.{u} R}
    (xi : Ext S U 1) (eta : Ext T U 1) :
    extBiprodLeft (combinedExt xi eta) = xi := by
  change (Ext.biprodAddEquiv (combinedExt xi eta)).1 = xi
  simp [combinedExt]

@[simp]
theorem extBiprodRight_combinedExt
    {R : Type u} [Ring R]
    {S T U : ModuleCat.{u} R}
    (xi : Ext S U 1) (eta : Ext T U 1) :
    extBiprodRight (combinedExt xi eta) = eta := by
  change (Ext.biprodAddEquiv (combinedExt xi eta)).2 = eta
  simp [combinedExt]

/-- The canonical radical-inclusion/top-projection short complex, named
locally so the construction remains independent of scratch imports. -/
abbrev moduleRadicalShortComplex
    {R : Type u} [Ring R]
    (M : Type u) [AddCommGroup M] [Module R M] :
    ShortComplex (ModuleCat.{u} R) :=
  ModuleCat.shortComplexOfCompEqZero
    (Module.jacobson R M).subtype
    (Module.jacobson R M).mkQ
    (LinearMap.exact_subtype_mkQ
      (Module.jacobson R M)).linearMap_comp_eq_zero

theorem moduleRadicalShortExact
    {R : Type u} [Ring R]
    (M : Type u) [AddCommGroup M] [Module R M] :
    (moduleRadicalShortComplex (R := R) M).ShortExact := by
  apply ModuleCat.shortComplex_shortExact
  · exact LinearMap.exact_subtype_mkQ (Module.jacobson R M)
  · exact (Module.jacobson R M).subtype_injective
  · exact (Module.jacobson R M).mkQ_surjective

/-- A short exact extension of two distinct simples by a simple is
indecomposable when both restricted extension classes are nonzero. -/
theorem indecomposable_middle_of_twoTop_nonzero_rows
    {K R : Type u} [Field K] [IsAlgClosed K]
    [Ring R] [Algebra K R]
    (S T U M : ModuleCat.{u} R)
    [IsSimpleModule R S] [IsSimpleModule R T]
    [IsSimpleModule R U]
    [FiniteDimensional K (S ⟶ S)]
    [FiniteDimensional K (T ⟶ T)]
    [FiniteDimensional K (U ⟶ U)]
    (hST : ¬ Nonempty (S ≅ T))
    (f : U ⟶ M) (g : M ⟶ S ⊞ T)
    (hfg : f ≫ g = 0)
    (hseq : (ShortComplex.mk f g hfg).ShortExact)
    [IsNoetherian R M] [IsArtinian R M]
    (hleft : extBiprodLeft hseq.extClass ≠ 0)
    (hright : extBiprodRight hseq.extClass ≠ 0) :
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R M := by
  let SC := ShortComplex.mk f g hfg
  letI : Mono f := hseq.mono_f
  letI : Epi g := hseq.epi_g
  letI : Simple S :=
    (simple_iff_isSimpleModule' S).mpr inferInstance
  letI : Simple T :=
    (simple_iff_isSimpleModule' T).mpr inferInstance
  letI : Simple U :=
    (simple_iff_isSimpleModule' U).mpr inferInstance
  have hclass : hseq.extClass ≠ 0 := by
    intro hzero
    apply hleft
    rw [hzero]
    simp [extBiprodLeft]
  have hJle : Module.jacobson R M ≤ LinearMap.ker g.hom := by
    intro x hx
    apply LinearMap.mem_ker.mpr
    let j : ModuleCat.of R (Module.jacobson R M) ⟶ S ⊞ T :=
      ModuleCat.ofHom (g.hom.domRestrict (Module.jacobson R M))
    have hjzero : j = 0 := by
      apply biprod.hom_ext
      · apply ModuleCat.hom_ext
        ext z
        have hzmap :
            ((biprod.fst : S ⊞ T ⟶ S).hom.comp g.hom) z.1 ∈
              Module.jacobson R S := by
          apply Module.map_jacobson_le
            ((biprod.fst : S ⊞ T ⟶ S).hom.comp g.hom)
          exact ⟨z.1, z.2, rfl⟩
        rw [IsSimpleModule.jacobson_eq_bot R S] at hzmap
        simpa [j, LinearMap.comp_apply] using hzmap
      · apply ModuleCat.hom_ext
        ext z
        have hzmap :
            ((biprod.snd : S ⊞ T ⟶ T).hom.comp g.hom) z.1 ∈
              Module.jacobson R T := by
          apply Module.map_jacobson_le
            ((biprod.snd : S ⊞ T ⟶ T).hom.comp g.hom)
          exact ⟨z.1, z.2, rfl⟩
        rw [IsSimpleModule.jacobson_eq_bot R T] at hzmap
        simpa [j, LinearMap.comp_apply] using hzmap
    have hjzeroHom := congrArg ModuleCat.Hom.hom hjzero
    exact DFunLike.congr_fun hjzeroHom ⟨x, hx⟩
  let kernelEquiv : U ≃ₗ[R] LinearMap.ker g.hom :=
    (LinearEquiv.ofInjective f.hom hseq.moduleCat_injective_f).trans
      (LinearEquiv.ofEq _ _ hseq.exact.moduleCat_range_eq_ker)
  letI : IsSimpleModule R (LinearMap.ker g.hom) :=
    IsSimpleModule.congr kernelEquiv.symm
  have hkerAtom : IsAtom (LinearMap.ker g.hom) :=
    isSimpleModule_iff_isAtom.mp inferInstance
  have hJcases :
      Module.jacobson R M = ⊥ ∨
        Module.jacobson R M = LinearMap.ker g.hom :=
    hkerAtom.le_iff.mp hJle
  have hJker : Module.jacobson R M = LinearMap.ker g.hom := by
    rcases hJcases with hJzero | hJeq
    · letI : IsSemisimpleModule R M :=
        (IsArtinian.isSemisimpleModule_iff_jacobson R M).mpr hJzero
      obtain ⟨s, hs⟩ :=
        IsSemisimpleModule.lifting_property g.hom
          hseq.moduleCat_surjective_g
          (LinearMap.id :
            ((S ⊞ T : ModuleCat R) : Type u) →ₗ[R]
              ((S ⊞ T : ModuleCat R) : Type u))
      apply False.elim
      apply hclass
      apply QuotientSubmoduleEquidistribution.NoParallelExtOne.extClass_eq_zero_of_section
        hseq (ModuleCat.ofHom s)
      apply ModuleCat.hom_ext
      simpa [LinearMap.comp_apply] using hs
    · exact hJeq
  have hMnontrivial : Nontrivial M := by
    have hUne : Nontrivial U := IsSimpleModule.nontrivial R U
    exact Function.Injective.nontrivial hseq.moduleCat_injective_f
  letI : Nontrivial M := hMnontrivial
  apply QuotientSubmoduleEquidistribution.Foundation.isIndecomposableModule_of_forall_isIdempotentElem
  intro a₂ ha₂
  let a₂c : M ⟶ M := ModuleCat.ofHom a₂
  have ha₂idem : a₂c ≫ a₂c = a₂c := by
    apply ModuleCat.hom_ext
    exact ha₂
  have hcross : f ≫ a₂c ≫ g = 0 := by
    apply ModuleCat.hom_ext
    ext x
    change g.hom (a₂ (f.hom x)) = 0
    apply LinearMap.mem_ker.mp
    rw [← hJker]
    apply Module.map_jacobson_le a₂
    refine ⟨f.hom x, ?_, rfl⟩
    rw [hJker, ← hseq.exact.moduleCat_range_eq_ker]
    exact LinearMap.mem_range_self f.hom x
  let a₁ : U ⟶ U :=
    hseq.exact.lift (f ≫ a₂c) (by simpa [Category.assoc] using hcross)
  have ha₁comm : a₁ ≫ f = f ≫ a₂c :=
    hseq.exact.lift_f _ _
  let a₃ : (S ⊞ T) ⟶ (S ⊞ T) :=
    hseq.exact.desc (a₂c ≫ g) hcross
  have ha₃comm : g ≫ a₃ = a₂c ≫ g :=
    hseq.exact.g_desc _ _
  have ha₁idem : a₁ ≫ a₁ = a₁ := by
    apply (cancel_mono f).mp
    simp only [Category.assoc, ha₁comm]
    rw [← Category.assoc, ha₁comm, Category.assoc, ha₂idem,
      ← ha₁comm]
  have ha₃idem : a₃ ≫ a₃ = a₃ := by
    apply (cancel_epi g).mp
    simp only [← Category.assoc, ha₃comm]
    rw [Category.assoc, ha₃comm, ← Category.assoc, ha₂idem,
      ← ha₃comm]
  let phi : SC ⟶ SC := {
    τ₁ := a₁
    τ₂ := a₂c
    τ₃ := a₃
    comm₁₂ := ha₁comm
    comm₂₃ := ha₃comm.symm }
  have hnatural :=
    ShortComplex.ShortExact.extClass_naturality hseq hseq phi
  obtain ⟨r, hr⟩ :=
    endomorphism_simple_eq_smul_id K a₁
  let aSS : S ⟶ S := biprod.inl ≫ a₃ ≫ biprod.fst
  let aST : S ⟶ T := biprod.inl ≫ a₃ ≫ biprod.snd
  let aTS : T ⟶ S := biprod.inr ≫ a₃ ≫ biprod.fst
  let aTT : T ⟶ T := biprod.inr ≫ a₃ ≫ biprod.snd
  have haST : aST = 0 := by
    by_contra hne
    letI : IsIso aST := isIso_of_hom_simple hne
    exact hST ⟨asIso aST⟩
  have haTS : aTS = 0 := by
    by_contra hne
    letI : IsIso aTS := isIso_of_hom_simple hne
    exact hST ⟨(asIso aTS).symm⟩
  obtain ⟨p, hp⟩ :=
    endomorphism_simple_eq_smul_id K aSS
  obtain ⟨q, hq⟩ :=
    endomorphism_simple_eq_smul_id K aTT
  have ha₃block :
      a₃ = blockDiagonalBiprodEnd (p • 𝟙 S) (q • 𝟙 T) := by
    apply biprod.hom_ext'
    · apply biprod.hom_ext
      · simpa [aSS, blockDiagonalBiprodEnd] using hp.symm
      · simpa [aST, blockDiagonalBiprodEnd] using haST
    · apply biprod.hom_ext
      · simpa [aTS, blockDiagonalBiprodEnd] using haTS
      · simpa [aTT, blockDiagonalBiprodEnd] using hq.symm
  have hleftScalar :
      r • extBiprodLeft hseq.extClass =
        p • extBiprodLeft hseq.extClass := by
    have h := congrArg extBiprodLeft hnatural
    dsimp [phi] at h
    rw [← hr, ha₃block] at h
    have hnormalized :
        (extBiprodLeft hseq.extClass).comp
            (Ext.mk₀ (r • 𝟙 U)) (add_zero 1) =
          (Ext.mk₀ (p • 𝟙 S)).comp
            (extBiprodLeft hseq.extClass) (zero_add 1) := by
      calc
        _ = extBiprodLeft
              (hseq.extClass.comp
                (Ext.mk₀ (r • 𝟙 U)) (add_zero 1)) :=
          Ext.comp_assoc_of_third_deg_zero
            (Ext.mk₀ biprod.inl) hseq.extClass
            (Ext.mk₀ (r • 𝟙 U)) (zero_add 1)
        _ = extBiprodLeft
              ((Ext.mk₀
                (blockDiagonalBiprodEnd
                  (p • 𝟙 S) (q • 𝟙 T))).comp
                hseq.extClass (zero_add 1)) := h
        _ = _ := by
          unfold extBiprodLeft
          rw [← Ext.comp_assoc_of_second_deg_zero,
            Ext.mk₀_comp_mk₀]
          simp [blockDiagonalBiprodEnd]
    simpa only [Ext.mk₀_smul, Ext.comp_smul, Ext.smul_comp,
      Ext.comp_mk₀_id, Ext.mk₀_id_comp] using hnormalized
  have hrightScalar :
      r • extBiprodRight hseq.extClass =
        q • extBiprodRight hseq.extClass := by
    have h := congrArg extBiprodRight hnatural
    dsimp [phi] at h
    rw [← hr, ha₃block] at h
    have hnormalized :
        (extBiprodRight hseq.extClass).comp
            (Ext.mk₀ (r • 𝟙 U)) (add_zero 1) =
          (Ext.mk₀ (q • 𝟙 T)).comp
            (extBiprodRight hseq.extClass) (zero_add 1) := by
      calc
        _ = extBiprodRight
              (hseq.extClass.comp
                (Ext.mk₀ (r • 𝟙 U)) (add_zero 1)) :=
          Ext.comp_assoc_of_third_deg_zero
            (Ext.mk₀ biprod.inr) hseq.extClass
            (Ext.mk₀ (r • 𝟙 U)) (zero_add 1)
        _ = extBiprodRight
              ((Ext.mk₀
                (blockDiagonalBiprodEnd
                  (p • 𝟙 S) (q • 𝟙 T))).comp
                hseq.extClass (zero_add 1)) := h
        _ = _ := by
          unfold extBiprodRight
          rw [← Ext.comp_assoc_of_second_deg_zero,
            Ext.mk₀_comp_mk₀]
          simp [blockDiagonalBiprodEnd]
    simpa only [Ext.mk₀_smul, Ext.comp_smul, Ext.smul_comp,
      Ext.comp_mk₀_id, Ext.mk₀_id_comp] using hnormalized
  have hrp : r = p := by
    apply sub_eq_zero.mp
    apply (smul_eq_zero.mp ?_).resolve_right hleft
    rw [sub_smul, hleftScalar, sub_self]
  have hrq : r = q := by
    apply sub_eq_zero.mp
    apply (smul_eq_zero.mp ?_).resolve_right hright
    rw [sub_smul, hrightScalar, sub_self]
  have hridem : r * r = r := by
    have h := ha₁idem
    rw [← hr] at h
    have hsmul : (r * r - r) • 𝟙 U = 0 := by
      rw [sub_smul]
      exact sub_eq_zero.mpr (by simpa [smul_smul] using h)
    exact sub_eq_zero.mp
      ((smul_eq_zero.mp hsmul).resolve_right (CategoryTheory.id_nonzero U))
  have hrzero_or_one : r = 0 ∨ r = 1 := by
    have hmul : r * (r - 1) = 0 := by
      rw [mul_sub, mul_one, hridem, sub_self]
    rcases mul_eq_zero.mp hmul with hzero | hone
    · exact Or.inl hzero
    · exact Or.inr (sub_eq_zero.mp hone)
  have endpointZero
      (b : M ⟶ M) (hbidem : b ≫ b = b)
      (hfb : f ≫ b = 0) (hbg : b ≫ g = 0) : b = 0 := by
    let c : M ⟶ U := hseq.exact.lift b hbg
    have hc : c ≫ f = b := hseq.exact.lift_f _ _
    have hbsq : b ≫ b = 0 := by
      calc
        b ≫ b = (c ≫ f) ≫ b := congrArg (fun z ↦ z ≫ b) hc.symm
        _ = c ≫ (f ≫ b) := Category.assoc c f b
        _ = 0 := by rw [hfb, comp_zero]
    rw [← hbidem, hbsq]
  rcases hrzero_or_one with hrzero | hrone
  · left
    have ha₁zero : a₁ = 0 := by
      calc
        a₁ = r • 𝟙 U := hr.symm
        _ = 0 := by simp [hrzero]
    have ha₃zero : a₃ = 0 := by
      rw [ha₃block, ← hrp, ← hrq, hrzero]
      simpa only [zero_smul] using
        (blockDiagonalBiprodEnd_zero (X := S) (X' := T))
    have hfa₂ : f ≫ a₂c = 0 := by rw [← ha₁comm, ha₁zero, zero_comp]
    have ha₂g : a₂c ≫ g = 0 := by rw [← ha₃comm, ha₃zero, comp_zero]
    have ha₂zero : a₂c = 0 :=
      endpointZero a₂c ha₂idem hfa₂ ha₂g
    exact ModuleCat.hom_ext_iff.mp ha₂zero
  · right
    have ha₁one : a₁ = 𝟙 U := by
      calc
        a₁ = r • 𝟙 U := hr.symm
        _ = 𝟙 U := by simp [hrone]
    have ha₃one : a₃ = 𝟙 (S ⊞ T) := by
      rw [ha₃block, ← hrp, ← hrq, hrone, one_smul, one_smul]
      exact blockDiagonalBiprodEnd_id
    let d : M ⟶ M := 𝟙 M - a₂c
    have hdidem : d ≫ d = d := by
      dsimp [d]
      simp only [Preadditive.sub_comp, Preadditive.comp_sub,
        Category.id_comp, Category.comp_id, ha₂idem]
      abel
    have hfd : f ≫ d = 0 := by
      dsimp [d]
      rw [Preadditive.comp_sub, Category.comp_id, ← ha₁comm,
        ha₁one, Category.id_comp, sub_self]
    have hdg : d ≫ g = 0 := by
      dsimp [d]
      rw [Preadditive.sub_comp, Category.id_comp, ← ha₃comm,
        ha₃one, Category.comp_id, sub_self]
    have hdzero : d = 0 := endpointZero d hdidem hfd hdg
    have ha₂one : a₂c = 𝟙 M := by
      dsimp [d] at hdzero
      exact (sub_eq_zero.mp hdzero).symm
    exact ModuleCat.hom_ext_iff.mp ha₂one

/-- In any nonsplit extension of a semisimple two-simple top by a simple,
the kernel is exactly the Jacobson radical of the middle. -/
theorem jacobson_eq_kernel_of_twoTop_extension
    {R : Type u} [Ring R]
    (S T U M : ModuleCat.{u} R)
    [IsSimpleModule R S] [IsSimpleModule R T]
    [IsSimpleModule R U]
    (f : U ⟶ M) (g : M ⟶ S ⊞ T)
    (hfg : f ≫ g = 0)
    (hseq : (ShortComplex.mk f g hfg).ShortExact)
    [IsArtinian R M]
    (hclass : hseq.extClass ≠ 0) :
    Module.jacobson R M = LinearMap.ker g.hom := by
  have hJle : Module.jacobson R M ≤ LinearMap.ker g.hom := by
    intro x hx
    apply LinearMap.mem_ker.mpr
    let j : ModuleCat.of R (Module.jacobson R M) ⟶ S ⊞ T :=
      ModuleCat.ofHom (g.hom.domRestrict (Module.jacobson R M))
    have hjzero : j = 0 := by
      apply biprod.hom_ext
      · apply ModuleCat.hom_ext
        ext z
        have hzmap :
            ((biprod.fst : S ⊞ T ⟶ S).hom.comp g.hom) z.1 ∈
              Module.jacobson R S := by
          apply Module.map_jacobson_le
            ((biprod.fst : S ⊞ T ⟶ S).hom.comp g.hom)
          exact ⟨z.1, z.2, rfl⟩
        rw [IsSimpleModule.jacobson_eq_bot R S] at hzmap
        simpa [j, LinearMap.comp_apply] using hzmap
      · apply ModuleCat.hom_ext
        ext z
        have hzmap :
            ((biprod.snd : S ⊞ T ⟶ T).hom.comp g.hom) z.1 ∈
              Module.jacobson R T := by
          apply Module.map_jacobson_le
            ((biprod.snd : S ⊞ T ⟶ T).hom.comp g.hom)
          exact ⟨z.1, z.2, rfl⟩
        rw [IsSimpleModule.jacobson_eq_bot R T] at hzmap
        simpa [j, LinearMap.comp_apply] using hzmap
    have hjzeroHom := congrArg ModuleCat.Hom.hom hjzero
    exact DFunLike.congr_fun hjzeroHom ⟨x, hx⟩
  let kernelEquiv : U ≃ₗ[R] LinearMap.ker g.hom :=
    (LinearEquiv.ofInjective f.hom hseq.moduleCat_injective_f).trans
      (LinearEquiv.ofEq _ _ hseq.exact.moduleCat_range_eq_ker)
  letI : IsSimpleModule R (LinearMap.ker g.hom) :=
    IsSimpleModule.congr kernelEquiv.symm
  have hkerAtom : IsAtom (LinearMap.ker g.hom) :=
    isSimpleModule_iff_isAtom.mp inferInstance
  rcases hkerAtom.le_iff.mp hJle with hJzero | hJker
  · letI : IsSemisimpleModule R M :=
      (IsArtinian.isSemisimpleModule_iff_jacobson R M).mpr hJzero
    obtain ⟨s, hs⟩ :=
      IsSemisimpleModule.lifting_property g.hom
        hseq.moduleCat_surjective_g
        (LinearMap.id :
          ((S ⊞ T : ModuleCat R) : Type u) →ₗ[R]
            ((S ⊞ T : ModuleCat R) : Type u))
    exfalso
    apply hclass
    apply QuotientSubmoduleEquidistribution.NoParallelExtOne.extClass_eq_zero_of_section
      hseq (ModuleCat.ofHom s)
    apply ModuleCat.hom_ext
    simpa [LinearMap.comp_apply] using hs
  · exact hJker

/-- The concrete fields obtained from a constructed two-top extension before
the final exclusion of indecomposable length-two quotients. -/
structure ConstructedTwoTopPreApexData
    {R : Type u} [Ring R] [IsNoetherianRing R]
    {ι : Type u}
    (σ : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, u, u} R ι)
    (leftIndex rightIndex radicalIndex : σ.SimpleIndex) where
  index : ι
  left : σ.SimpleQuotient index
  right : σ.SimpleQuotient index
  left_index_eq : left.index = leftIndex.1
  right_index_eq : right.index = rightIndex.1
  left_ne_right : leftIndex.1 ≠ rightIndex.1
  radicalEquiv :
    σ.obj radicalIndex.1 ≃ₗ[R] σ.moduleRadical index
  topEquiv :
    (σ.obj leftIndex.1 × σ.obj rightIndex.1) ≃ₗ[R]
      σ.moduleTop index
  simpleQuotient_index_eq :
    ∀ Q : σ.SimpleQuotient index,
      Q.index = leftIndex.1 ∨ Q.index = rightIndex.1
  compositionLength_eq_three : σ.compositionLength index = 3
  no_lengthTwo_quotient :
    ∀ {k : ι} (q : σ.obj index ⟶ σ.obj k),
      Epi q → σ.compositionLength k ≠ 2

theorem ConstructedTwoTopPreApexData.simpleQuotientIndexSet_eq
    {R ι : Type u} [Ring R] [IsNoetherianRing R]
    (σ : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, u, u} R ι)
    (s t r : σ.SimpleIndex)
    (D : ConstructedTwoTopPreApexData σ s t r) :
    σ.simpleQuotientIndexSet D.index = {s.1, t.1} := by
  classical
  ext z
  constructor
  · rintro ⟨Q, rfl⟩
    rcases D.simpleQuotient_index_eq Q with h | h
    · simp [h]
    · simp [h]
  · intro hz
    rcases (by simpa only [Set.mem_insert_iff,
      Set.mem_singleton_iff] using hz) with rfl | rfl
    · exact ⟨D.left, D.left_index_eq⟩
    · exact ⟨D.right, D.right_index_eq⟩

/-- The pre-apex data already proves the complete objectwise quotient-shape
predicate, hence determines an actual family-5 apex index. -/
def ConstructedTwoTopPreApexData.toTwoTopQuotientShapeIndex
    {R ι : Type u} [Ring R] [IsNoetherianRing R]
    (σ : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, u, u} R ι)
    (s t r : σ.SimpleIndex)
    (D : ConstructedTwoTopPreApexData σ s t r) :
    σ.TwoTopQuotientShapeIndex :=
  ⟨D.index, D.compositionLength_eq_three,
    by
      rw [D.simpleQuotientIndexSet_eq σ s t r]
      exact Set.ncard_pair D.left_ne_right,
    D.no_lengthTwo_quotient⟩

/-- Package the constructed radical/top information in the maintained
`ActualTwoTopApexData` interface. -/
def ConstructedTwoTopPreApexData.toActualTwoTopApexData
    {R ι : Type u} [Ring R] [IsNoetherianRing R]
    (σ : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, u, u} R ι)
    (s t r : σ.SimpleIndex)
    (D : ConstructedTwoTopPreApexData σ s t r) :
    σ.ActualTwoTopApexData
      (D.toTwoTopQuotientShapeIndex σ s t r) := by
  refine {
    left := D.left
    right := D.right
    left_ne_right := ?_
    radical := r
    radicalEquiv := D.radicalEquiv
    topEquiv := ?_
    simpleQuotient_index_eq := ?_ }
  · intro h
    apply D.left_ne_right
    exact D.left_index_eq.symm.trans (h.trans D.right_index_eq)
  · change
      (σ.obj D.left.index × σ.obj D.right.index) ≃ₗ[R]
        σ.moduleTop D.index
    rw [D.left_index_eq, D.right_index_eq]
    exact D.topEquiv
  · intro Q
    simpa only [D.left_index_eq, D.right_index_eq] using
      D.simpleQuotient_index_eq Q

/-- Completing a two-row short exact extension into the skeleton supplies
all actual two-top apex data except the no-length-two-quotient clause. -/
theorem exists_constructedTwoTopPreApexData_of_shortExact
    {R ι : Type u} [Ring R]
    [IsNoetherianRing R] [IsArtinianRing R]
    (σ : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, u, u} R ι)
    (s t r : σ.SimpleIndex)
    (hst : s.1 ≠ t.1)
    (M : FGModuleCat.{u} R)
    (f : (σ.obj r.1).obj ⟶ M.obj)
    (g : M.obj ⟶ (σ.obj s.1).obj ⊞ (σ.obj t.1).obj)
    (hfg : f ≫ g = 0)
    (hseq : (ShortComplex.mk f g hfg).ShortExact)
    (hleft : extBiprodLeft hseq.extClass ≠ 0)
    (hright : extBiprodRight hseq.extClass ≠ 0)
    (hMindec : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R M) :
    Nonempty (ConstructedTwoTopPreApexData σ s t r) := by
  classical
  let S : ModuleCat.{u} R := (σ.obj s.1).obj
  let T : ModuleCat.{u} R := (σ.obj t.1).obj
  let U : ModuleCat.{u} R := (σ.obj r.1).obj
  let MM : ModuleCat.{u} R := M.obj
  letI : Mono f := hseq.mono_f
  letI : Epi g := hseq.epi_g
  letI : IsSimpleModule R S :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      (σ.obj s.1)).mp s.2
  letI : IsSimpleModule R T :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      (σ.obj t.1)).mp t.2
  letI : IsSimpleModule R U :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      (σ.obj r.1)).mp r.2
  letI : Simple S :=
    (simple_iff_isSimpleModule' S).mpr inferInstance
  letI : Simple T :=
    (simple_iff_isSimpleModule' T).mpr inferInstance
  letI : Simple U :=
    (simple_iff_isSimpleModule' U).mpr inferInstance
  have hclass : hseq.extClass ≠ 0 := by
    intro hzero
    apply hleft
    rw [hzero]
    simp [extBiprodLeft]
  have hJraw : Module.jacobson R M = LinearMap.ker g.hom :=
    jacobson_eq_kernel_of_twoTop_extension
      S T U MM f g hfg hseq hclass
  let kernelEquiv : U ≃ₗ[R] LinearMap.ker g.hom :=
    (LinearEquiv.ofInjective f.hom hseq.moduleCat_injective_f).trans
      (LinearEquiv.ofEq _ _ hseq.exact.moduleCat_range_eq_ker)
  let rawRadicalEquiv : U ≃ₗ[R] Module.jacobson R M :=
    kernelEquiv.trans (LinearEquiv.ofEq _ _ hJraw.symm)
  have hrawRadicalEquiv_apply (x : U) :
      (rawRadicalEquiv x : M) = f.hom x := by
    rfl
  let rawTopEquiv :
      (S × T) ≃ₗ[R] M ⧸ Module.jacobson R M :=
    (ModuleCat.biprodIsoProd S T).toLinearEquiv.symm |>.trans
      ((Submodule.quotEquivOfEq
          (Module.jacobson R M) (LinearMap.ker g.hom) hJraw).trans
        (g.hom.quotKerEquivOfSurjective
          hseq.moduleCat_surjective_g)).symm
  obtain ⟨j, ⟨e⟩⟩ := σ.complete M hMindec
  let eLinear : M ≃ₗ[R] σ.obj j :=
    FGModuleCat.isoToLinearEquiv e
  have hmapJ :
      Submodule.map eLinear.toLinearMap (Module.jacobson R M) =
        Module.jacobson R (σ.obj j) :=
    Module.map_jacobson_of_bijective eLinear.bijective
  let radicalTransport :
      Module.jacobson R M ≃ₗ[R] Module.jacobson R (σ.obj j) :=
    (eLinear.submoduleMap (Module.jacobson R M)).trans
      (LinearEquiv.ofEq _ _ hmapJ)
  let topTransport :
      (M ⧸ Module.jacobson R M) ≃ₗ[R]
        (σ.obj j ⧸ Module.jacobson R (σ.obj j)) :=
    Submodule.Quotient.equiv
      (Module.jacobson R M) (Module.jacobson R (σ.obj j))
      eLinear hmapJ
  let qLeftLinear : σ.obj j →ₗ[R] σ.obj s.1 :=
    (biprod.fst : S ⊞ T ⟶ S).hom.comp
      (g.hom.comp eLinear.symm.toLinearMap)
  have hqLeftSurj : Function.Surjective qLeftLinear := by
    intro y
    obtain ⟨m, hm⟩ :=
      hseq.moduleCat_surjective_g
        ((biprod.inl : S ⟶ S ⊞ T).hom y)
    refine ⟨eLinear m, ?_⟩
    change (biprod.fst : S ⊞ T ⟶ S).hom
      (g.hom (eLinear.symm (eLinear m))) = y
    rw [eLinear.symm_apply_apply, hm]
    have hproj := congrArg
      (fun z : S ⟶ S ↦ z.hom y)
      (biprod.inl_fst :
        (biprod.inl : S ⟶ S ⊞ T) ≫ biprod.fst = 𝟙 S)
    simpa only [ModuleCat.comp_apply, ModuleCat.id_apply] using hproj
  let qLeft : σ.obj j ⟶ σ.obj s.1 :=
    FGModuleCat.ofHom qLeftLinear
  letI : Epi qLeft :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_epi_iff_surjective qLeft).mpr
      hqLeftSurj
  let left : σ.SimpleQuotient j := {
    index := s.1
    simple := s.2
    map := qLeft
    epi := inferInstance }
  let qRightLinear : σ.obj j →ₗ[R] σ.obj t.1 :=
    (biprod.snd : S ⊞ T ⟶ T).hom.comp
      (g.hom.comp eLinear.symm.toLinearMap)
  have hqRightSurj : Function.Surjective qRightLinear := by
    intro y
    obtain ⟨m, hm⟩ :=
      hseq.moduleCat_surjective_g
        ((biprod.inr : T ⟶ S ⊞ T).hom y)
    refine ⟨eLinear m, ?_⟩
    change (biprod.snd : S ⊞ T ⟶ T).hom
      (g.hom (eLinear.symm (eLinear m))) = y
    rw [eLinear.symm_apply_apply, hm]
    have hproj := congrArg
      (fun z : T ⟶ T ↦ z.hom y)
      (biprod.inr_snd :
        (biprod.inr : T ⟶ S ⊞ T) ≫ biprod.snd = 𝟙 T)
    simpa only [ModuleCat.comp_apply, ModuleCat.id_apply] using hproj
  let qRight : σ.obj j ⟶ σ.obj t.1 :=
    FGModuleCat.ofHom qRightLinear
  letI : Epi qRight :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_epi_iff_surjective qRight).mpr
      hqRightSurj
  let right : σ.SimpleQuotient j := {
    index := t.1
    simple := t.2
    map := qRight
    epi := inferInstance }
  have hquotients :
      ∀ Q : σ.SimpleQuotient j,
        Q.index = s.1 ∨ Q.index = t.1 := by
    intro Q
    letI : Simple (σ.obj Q.index) := Q.simple
    letI : IsSimpleModule R (σ.obj Q.index) :=
      (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
        (σ.obj Q.index)).mp Q.simple
    letI : Simple (σ.obj Q.index).obj :=
      (simple_iff_isSimpleModule' (σ.obj Q.index).obj).mpr inferInstance
    let qRawLinear : M →ₗ[R] σ.obj Q.index :=
      Q.map.hom.hom.comp eLinear.toLinearMap
    let qRaw : MM ⟶ (σ.obj Q.index).obj :=
      ModuleCat.ofHom qRawLinear
    have hqRawSurj : Function.Surjective qRawLinear := by
      exact (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_epi_iff_surjective
        Q.map).mp Q.epi |>.comp eLinear.surjective
    letI : Epi qRaw :=
      (ModuleCat.epi_iff_surjective qRaw).mpr hqRawSurj
    have hfq : f ≫ qRaw = 0 := by
      apply ModuleCat.hom_ext
      ext x
      have hfx : f.hom x ∈ Module.jacobson R M := by
        rw [hJraw, ← hseq.exact.moduleCat_range_eq_ker]
        exact LinearMap.mem_range_self f.hom x
      have hJkerQ :
          Module.jacobson R M ≤ LinearMap.ker qRawLinear :=
        IsSemisimpleModule.jacobson_le_ker
          R R M (σ.obj Q.index) qRawLinear
      exact LinearMap.mem_ker.mp (hJkerQ hfx)
    let a : S ⊞ T ⟶ (σ.obj Q.index).obj :=
      hseq.exact.desc qRaw hfq
    have ha : g ≫ a = qRaw := hseq.exact.g_desc _ _
    have haNe : a ≠ 0 := by
      intro hazero
      have hqzero : qRaw = 0 := by
        rw [← ha, hazero, comp_zero]
      exact (Simple.not_isZero (σ.obj Q.index).obj)
        (IsZero.of_epi_eq_zero qRaw hqzero)
    let aLeft : S ⟶ (σ.obj Q.index).obj := biprod.inl ≫ a
    let aRight : T ⟶ (σ.obj Q.index).obj := biprod.inr ≫ a
    by_cases haLeft : aLeft = 0
    · have haRight : aRight ≠ 0 := by
        intro haRight
        apply haNe
        apply biprod.hom_ext'
        · simpa [aLeft] using haLeft
        · simpa [aRight] using haRight
      letI : IsIso aRight := isIso_of_hom_simple haRight
      exact Or.inr (σ.eq_of_iso
        ⟨(asIso aRight).toLinearEquiv.toFGModuleCatIso⟩).symm
    · letI : IsIso aLeft := isIso_of_hom_simple haLeft
      exact Or.inl (σ.eq_of_iso
        ⟨(asIso aLeft).toLinearEquiv.toFGModuleCatIso⟩).symm
  have hlengthM : Module.length R M = 3 := by
    have htargetLength :
        Module.length R
            (((S ⊞ T : ModuleCat R) : Type u)) = 2 := by
      calc
        Module.length R (((S ⊞ T : ModuleCat R) : Type u)) =
            Module.length R (S × T) :=
          (LinearEquiv.length_eq
            (ModuleCat.biprodIsoProd S T).toLinearEquiv)
        _ = Module.length R S + Module.length R T :=
          Module.length_prod R S T
        _ = 2 := by
          rw [Module.length_eq_one_iff.mpr
              (inferInstance : IsSimpleModule R S),
            Module.length_eq_one_iff.mpr
              (inferInstance : IsSimpleModule R T)]
          norm_num
    rw [Module.length_eq_add_of_exact
      f.hom g.hom
      hseq.moduleCat_injective_f hseq.moduleCat_surjective_g]
    · rw [Module.length_eq_one_iff.mpr
          (inferInstance : IsSimpleModule R U), htargetLength]
      norm_num
    · exact
        (LinearMap.exact_iff.mpr
          hseq.exact.moduleCat_range_eq_ker.symm)
  have hjLength : σ.compositionLength j = 3 := by
    rw [← ENat.coe_inj, σ.coe_compositionLength]
    calc
      Module.length R (σ.obj j) = Module.length R M :=
        (LinearEquiv.length_eq eLinear).symm
      _ = 3 := hlengthM
      _ = (3 : ℕ∞) := rfl
  have hST : ¬ Nonempty (S ≅ T) := by
    rintro ⟨eST⟩
    apply hst
    exact σ.eq_of_iso
      ⟨eST.toLinearEquiv.toFGModuleCatIso⟩
  have hnoLengthTwo :
      ∀ {k : ι} (q : σ.obj j ⟶ σ.obj k),
        Epi q → σ.compositionLength k ≠ 2 := by
    intro k q hq hk
    letI : Epi q := hq
    have hqSurj : Function.Surjective q.hom.hom :=
      (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_epi_iff_surjective q).mp
        inferInstance
    let N : ModuleCat.{u} R := (σ.obj k).obj
    let qRawLinear : M →ₗ[R] σ.obj k :=
      q.hom.hom.comp eLinear.toLinearMap
    let qRaw : MM ⟶ N := ModuleCat.ofHom qRawLinear
    have hqRawSurj : Function.Surjective qRawLinear :=
      hqSurj.comp eLinear.surjective
    letI : Epi qRaw :=
      (ModuleCat.epi_iff_surjective qRaw).mpr hqRawSurj
    have hradSimple :
        IsSimpleModule R (Module.jacobson R (σ.obj k)) :=
      QuotientSubmoduleEquidistribution.LengthTwoGabrielBridge.IndecomposableSkeleton.moduleRadical_isSimple_of_compositionLength_eq_two
        σ hk
    have htopSimple :
        IsSimpleModule R
          (σ.obj k ⧸ Module.jacobson R (σ.obj k)) :=
      QuotientSubmoduleEquidistribution.BottomTwoSimpleTop.IndecomposableSkeleton.moduleTop_isSimple_of_compositionLength_eq_two
        σ hk
    letI : IsSimpleModule R (Module.jacobson R (σ.obj k)) :=
      hradSimple
    letI : IsSimpleModule R
        (σ.obj k ⧸ Module.jacobson R (σ.obj k)) :=
      htopSimple
    let JN : ModuleCat.{u} R :=
      ModuleCat.of R (Module.jacobson R (σ.obj k))
    let TopN : ModuleCat.{u} R :=
      ModuleCat.of R (σ.obj k ⧸ Module.jacobson R (σ.obj k))
    letI : Simple JN :=
      (simple_iff_isSimpleModule' JN).mpr inferInstance
    letI : Simple TopN :=
      (simple_iff_isSimpleModule' TopN).mpr inferInstance
    let a₁Linear : U →ₗ[R] Module.jacobson R (σ.obj k) :=
      (QuotientSubmoduleEquidistribution.radicalRestriction qRawLinear).comp
        rawRadicalEquiv.toLinearMap
    let a₁ : U ⟶ JN := ModuleCat.ofHom a₁Linear
    have ha₁Surj : Function.Surjective a₁Linear :=
      (QuotientSubmoduleEquidistribution.radicalRestriction_surjective
        qRawLinear hqRawSurj).comp rawRadicalEquiv.surjective
    letI : Epi a₁ :=
      (ModuleCat.epi_iff_surjective a₁).mpr ha₁Surj
    have ha₁Ne : a₁ ≠ 0 := by
      intro ha₁zero
      exact (Simple.not_isZero JN)
        (IsZero.of_epi_eq_zero a₁ ha₁zero)
    letI : IsIso a₁ := isIso_of_hom_simple ha₁Ne
    let targetSC := moduleRadicalShortComplex (R := R) (σ.obj k)
    let targetSeq : targetSC.ShortExact :=
      moduleRadicalShortExact (R := R) (σ.obj k)
    have ha₁comm : a₁ ≫ targetSC.f = f ≫ qRaw := by
      apply ModuleCat.hom_ext
      ext x
      change qRawLinear (rawRadicalEquiv x) = qRawLinear (f.hom x)
      rw [hrawRadicalEquiv_apply]
    let qTopLinear : M →ₗ[R]
        (σ.obj k ⧸ Module.jacobson R (σ.obj k)) :=
      (Module.jacobson R (σ.obj k)).mkQ.comp qRawLinear
    have hfTop : f ≫ ModuleCat.ofHom qTopLinear = 0 := by
      apply ModuleCat.hom_ext
      ext x
      apply (Submodule.Quotient.mk_eq_zero
        (Module.jacobson R (σ.obj k))).mpr
      have hfx : f.hom x ∈ Module.jacobson R M := by
        rw [hJraw, ← hseq.exact.moduleCat_range_eq_ker]
        exact LinearMap.mem_range_self f.hom x
      apply Module.map_jacobson_le qRawLinear
      exact ⟨f.hom x, hfx, rfl⟩
    let a₃ : S ⊞ T ⟶ TopN :=
      hseq.exact.desc (ModuleCat.ofHom qTopLinear) hfTop
    have ha₃comm : g ≫ a₃ = ModuleCat.ofHom qTopLinear :=
      hseq.exact.g_desc _ _
    let sourceSC := ShortComplex.mk f g hfg
    let phi : sourceSC ⟶ targetSC := {
      τ₁ := a₁
      τ₂ := qRaw
      τ₃ := a₃
      comm₁₂ := ha₁comm
      comm₂₃ := ha₃comm.symm }
    have hnat :=
      ShortComplex.ShortExact.extClass_naturality
        hseq targetSeq phi
    let aLeft : S ⟶ TopN := biprod.inl ≫ a₃
    let aRight : T ⟶ TopN := biprod.inr ≫ a₃
    by_cases haLeft : aLeft = 0
    · apply hleft
      have h := congrArg extBiprodLeft hnat
      dsimp [phi] at h
      have hnormalized :
          (extBiprodLeft hseq.extClass).comp
              (Ext.mk₀ a₁) (add_zero 1) =
            (Ext.mk₀ aLeft).comp targetSeq.extClass
              (zero_add 1) := by
        calc
          _ = extBiprodLeft
                (hseq.extClass.comp
                  (Ext.mk₀ a₁) (add_zero 1)) :=
            Ext.comp_assoc_of_third_deg_zero
              (Ext.mk₀ biprod.inl) hseq.extClass
              (Ext.mk₀ a₁) (zero_add 1)
          _ = extBiprodLeft
                ((Ext.mk₀ a₃).comp targetSeq.extClass
                  (zero_add 1)) := h
          _ = _ := by
            unfold extBiprodLeft
            rw [← Ext.comp_assoc_of_second_deg_zero,
              Ext.mk₀_comp_mk₀]
      have hzero :
          (extBiprodLeft hseq.extClass).comp
              (Ext.mk₀ a₁) (add_zero 1) = 0 := by
        simpa [haLeft] using hnormalized
      have hcancel := congrArg
        (fun z : Ext S JN 1 ↦
          z.comp (Ext.mk₀ (inv a₁)) (add_zero 1)) hzero
      rw [Ext.comp_assoc_of_second_deg_zero,
        Ext.mk₀_comp_mk₀] at hcancel
      simpa using hcancel
    · have haRight : aRight = 0 := by
        by_contra haRight
        letI : IsIso aLeft := isIso_of_hom_simple haLeft
        letI : IsIso aRight := isIso_of_hom_simple haRight
        exact hST ⟨(asIso aLeft).trans (asIso aRight).symm⟩
      apply hright
      have h := congrArg extBiprodRight hnat
      dsimp [phi] at h
      have hnormalized :
          (extBiprodRight hseq.extClass).comp
              (Ext.mk₀ a₁) (add_zero 1) =
            (Ext.mk₀ aRight).comp targetSeq.extClass
              (zero_add 1) := by
        calc
          _ = extBiprodRight
                (hseq.extClass.comp
                  (Ext.mk₀ a₁) (add_zero 1)) :=
            Ext.comp_assoc_of_third_deg_zero
              (Ext.mk₀ biprod.inr) hseq.extClass
              (Ext.mk₀ a₁) (zero_add 1)
          _ = extBiprodRight
                ((Ext.mk₀ a₃).comp targetSeq.extClass
                  (zero_add 1)) := h
          _ = _ := by
            unfold extBiprodRight
            rw [← Ext.comp_assoc_of_second_deg_zero,
              Ext.mk₀_comp_mk₀]
      have hzero :
          (extBiprodRight hseq.extClass).comp
              (Ext.mk₀ a₁) (add_zero 1) = 0 := by
        simpa [haRight] using hnormalized
      have hcancel := congrArg
        (fun z : Ext T JN 1 ↦
          z.comp (Ext.mk₀ (inv a₁)) (add_zero 1)) hzero
      rw [Ext.comp_assoc_of_second_deg_zero,
        Ext.mk₀_comp_mk₀] at hcancel
      simpa using hcancel
  exact ⟨{
    index := j
    left := left
    right := right
    left_index_eq := rfl
    right_index_eq := rfl
    left_ne_right := hst
    radicalEquiv := rawRadicalEquiv.trans radicalTransport
    topEquiv := rawTopEquiv.trans topTransport
    simpleQuotient_index_eq := hquotients
    compositionLength_eq_three := hjLength
    no_lengthTwo_quotient := hnoLengthTwo }⟩

/-- Two distinct length-two representatives with a common simple target
produce an explicit pushout apex carrying all pre-shape two-top data. -/
theorem exists_constructedTwoTopPreApexData_of_commonTarget
    (K B : Type u)
    [Field K] [IsAlgClosed K]
    [Ring B] [Algebra K B] [FiniteDimensional K B] :
    letI : IsNoetherianRing Bᵐᵒᵖ :=
      QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K B
    letI : IsArtinianRing Bᵐᵒᵖ :=
      QuotientSubmoduleEquidistribution.isArtinianRing_op_of_finiteDimensional K B
    ∀ {ι : Type u} [Finite ι]
      (σ : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, u, u} Bᵐᵒᵖ ι)
      (e₁ e₂ : σ.LengthTwoIndex),
      e₁ ≠ e₂ →
      QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.target σ e₂ =
        QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.target σ e₁ →
      Nonempty
        (ConstructedTwoTopPreApexData σ
          (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.source σ e₁)
          (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.source σ e₂)
          (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.target σ e₁)) := by
  letI : IsNoetherianRing Bᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K B
  letI : IsArtinianRing Bᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isArtinianRing_op_of_finiteDimensional K B
  intro ι _ σ e₁ e₂ he₁e₂ htarget
  classical
  let s := QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.source σ e₁
  let t := QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.source σ e₂
  let r := QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.target σ e₁
  let r₂ := QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.target σ e₂
  let S : ModuleCat.{u} Bᵐᵒᵖ := (σ.obj s.1).obj
  let T : ModuleCat.{u} Bᵐᵒᵖ := (σ.obj t.1).obj
  let U : ModuleCat.{u} Bᵐᵒᵖ := (σ.obj r.1).obj
  let U₂ : ModuleCat.{u} Bᵐᵒᵖ := (σ.obj r₂.1).obj
  have hnoParallel :=
    QuotientSubmoduleEquidistribution.GabrielArrowBridge.RightModules.noParallelExtSupport_of_finiteDimensional_of_finiteSkeleton
      K B σ
  have hst : s.1 ≠ t.1 := by
    intro hindex
    have hs : s = t := Subtype.ext hindex
    apply he₁e₂
    apply QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.toGabrielArrow_injective
      σ hnoParallel
    apply Subtype.ext
    exact Prod.ext hs htarget.symm
  have hU : U₂ = U := by
    dsimp [U₂, U, r₂, r]
    exact congrArg
      (fun z : σ.SimpleIndex ↦ (σ.obj z.1).obj) htarget
  let bU : U₂ ⟶ U := eqToHom hU
  let xi : Ext S U 1 :=
    QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.extensionClass σ e₁
  let eta : Ext T U 1 :=
    (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.extensionClass σ e₂).comp
      (Ext.mk₀ bU) (add_zero 1)
  have hxi : xi ≠ 0 := by
    exact
      QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.extensionClass_ne_zero σ e₁
  have heta : eta ≠ 0 := by
    intro hzero
    apply
      QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.extensionClass_ne_zero σ e₂
    have h := congrArg
      (fun z : Ext T U 1 ↦
        z.comp (Ext.mk₀ (inv bU)) (add_zero 1)) hzero
    dsimp [eta] at h
    rw [Ext.comp_assoc_of_second_deg_zero,
      Ext.mk₀_comp_mk₀] at h
    simpa [bU] using h
  let zeta : Ext (S ⊞ T) U 1 := combinedExt xi eta
  letI : Module.Finite Bᵐᵒᵖ (S × T) := inferInstance
  letI : Module.Finite Bᵐᵒᵖ
      (((S ⊞ T : ModuleCat Bᵐᵒᵖ) : Type u)) :=
    Module.Finite.equiv
      (ModuleCat.biprodIsoProd S T).toLinearEquiv.symm
  obtain ⟨n, p, hp⟩ :=
    Module.Finite.exists_fin' Bᵐᵒᵖ
      (((S ⊞ T : ModuleCat Bᵐᵒᵖ) : Type u))
  obtain ⟨push, hpushClass⟩ :=
    QuotientSubmoduleEquidistribution.NoParallelExtOne.PushoutExtension.exists_pushout_with_extClass_eq
      p hp zeta
  let M : FGModuleCat.{u} Bᵐᵒᵖ :=
    FGModuleCat.of Bᵐᵒᵖ
      (QuotientSubmoduleEquidistribution.NoParallelExtOne.PushoutExtension.middle p push)
  let SC :=
    QuotientSubmoduleEquidistribution.NoParallelExtOne.PushoutExtension.shortComplex p push
  let hseq : SC.ShortExact :=
    QuotientSubmoduleEquidistribution.NoParallelExtOne.PushoutExtension.shortExact p hp push
  have hleft : extBiprodLeft hseq.extClass ≠ 0 := by
    rw [hpushClass, extBiprodLeft_combinedExt]
    exact hxi
  have hright : extBiprodRight hseq.extClass ≠ 0 := by
    rw [hpushClass, extBiprodRight_combinedExt]
    exact heta
  letI : IsSimpleModule Bᵐᵒᵖ S :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      (σ.obj s.1)).mp s.2
  letI : IsSimpleModule Bᵐᵒᵖ T :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      (σ.obj t.1)).mp t.2
  letI : IsSimpleModule Bᵐᵒᵖ U :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      (σ.obj r.1)).mp r.2
  letI : Module K (σ.obj s.1) :=
    Module.restrictScalars K Bᵐᵒᵖ (σ.obj s.1)
  letI : Module K (σ.obj t.1) :=
    Module.restrictScalars K Bᵐᵒᵖ (σ.obj t.1)
  letI : Module K (σ.obj r.1) :=
    Module.restrictScalars K Bᵐᵒᵖ (σ.obj r.1)
  letI : IsScalarTower K Bᵐᵒᵖ (σ.obj s.1) :=
    IsScalarTower.restrictScalars K Bᵐᵒᵖ (σ.obj s.1)
  letI : IsScalarTower K Bᵐᵒᵖ (σ.obj t.1) :=
    IsScalarTower.restrictScalars K Bᵐᵒᵖ (σ.obj t.1)
  letI : IsScalarTower K Bᵐᵒᵖ (σ.obj r.1) :=
    IsScalarTower.restrictScalars K Bᵐᵒᵖ (σ.obj r.1)
  letI : FiniteDimensional K (σ.obj s.1) :=
    QuotientSubmoduleEquidistribution.finiteDimensional_rightFGModule K B (σ.obj s.1)
  letI : FiniteDimensional K (σ.obj t.1) :=
    QuotientSubmoduleEquidistribution.finiteDimensional_rightFGModule K B (σ.obj t.1)
  letI : FiniteDimensional K (σ.obj r.1) :=
    QuotientSubmoduleEquidistribution.finiteDimensional_rightFGModule K B (σ.obj r.1)
  letI : FiniteDimensional K (S ⟶ S) :=
    QuotientSubmoduleEquidistribution.NoParallelExtOne.moduleFinite_moduleCatHom_of_finiteDimensional
      (K := K) (R := Bᵐᵒᵖ)
  letI : FiniteDimensional K (T ⟶ T) :=
    QuotientSubmoduleEquidistribution.NoParallelExtOne.moduleFinite_moduleCatHom_of_finiteDimensional
      (K := K) (R := Bᵐᵒᵖ)
  letI : FiniteDimensional K (U ⟶ U) :=
    QuotientSubmoduleEquidistribution.NoParallelExtOne.moduleFinite_moduleCatHom_of_finiteDimensional
      (K := K) (R := Bᵐᵒᵖ)
  have hST : ¬ Nonempty (S ≅ T) := by
    rintro ⟨e⟩
    apply hst
    exact σ.eq_of_iso
      ⟨e.toLinearEquiv.toFGModuleCatIso⟩
  have hMindec : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule Bᵐᵒᵖ M := by
    exact indecomposable_middle_of_twoTop_nonzero_rows
      (K := K) (R := Bᵐᵒᵖ)
      S T U M.obj hST SC.f SC.g SC.zero hseq hleft hright
  exact exists_constructedTwoTopPreApexData_of_shortExact
    σ s t r hst M SC.f SC.g SC.zero hseq hleft hright hMindec

/-- Paper-facing objectwise endpoint: a distinct common-target arrow pair
has an actual family-5 apex with precisely the two source quotient types. -/
theorem exists_actualTwoTopApexData_of_commonTarget
    (K B : Type u)
    [Field K] [IsAlgClosed K]
    [Ring B] [Algebra K B] [FiniteDimensional K B] :
    letI : IsNoetherianRing Bᵐᵒᵖ :=
      QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K B
    letI : IsArtinianRing Bᵐᵒᵖ :=
      QuotientSubmoduleEquidistribution.isArtinianRing_op_of_finiteDimensional K B
    ∀ {ι : Type u} [Finite ι]
      (σ : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, u, u} Bᵐᵒᵖ ι)
      (e₁ e₂ : σ.LengthTwoIndex),
      e₁ ≠ e₂ →
      QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.target σ e₂ =
        QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.target σ e₁ →
      ∃ x : σ.TwoTopQuotientShapeIndex,
        Nonempty (σ.ActualTwoTopApexData x) ∧
          σ.simpleQuotientIndexSet x.1 =
            { (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.source σ e₁).1,
              (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.source σ e₂).1 } := by
  letI : IsNoetherianRing Bᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K B
  letI : IsArtinianRing Bᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isArtinianRing_op_of_finiteDimensional K B
  intro ι _ σ e₁ e₂ he₁e₂ htarget
  obtain ⟨D⟩ :=
    exists_constructedTwoTopPreApexData_of_commonTarget
      K B σ e₁ e₂ he₁e₂ htarget
  let s := QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.source σ e₁
  let t := QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.source σ e₂
  let r := QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.target σ e₁
  let x := D.toTwoTopQuotientShapeIndex σ s t r
  refine ⟨x, ⟨D.toActualTwoTopApexData σ s t r⟩, ?_⟩
  exact D.simpleQuotientIndexSet_eq σ s t r

/-- Every formal `CommonTargetPair` therefore has an actual constructed
apex, with its simple quotient set identified with the pair's source set. -/
theorem exists_actualTwoTopApexData_of_commonTargetPair
    (K B : Type u)
    [Field K] [IsAlgClosed K]
    [Ring B] [Algebra K B] [FiniteDimensional K B] :
    letI : IsNoetherianRing Bᵐᵒᵖ :=
      QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K B
    letI : IsArtinianRing Bᵐᵒᵖ :=
      QuotientSubmoduleEquidistribution.isArtinianRing_op_of_finiteDimensional K B
    ∀ {ι : Type u} [Finite ι]
      (σ : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, u, u} Bᵐᵒᵖ ι)
      (p : σ.CommonTargetPair
        (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.target σ)),
      ∃ x : σ.TwoTopQuotientShapeIndex,
        Nonempty (σ.ActualTwoTopApexData x) ∧
          σ.simpleQuotientIndexSet x.1 =
            σ.commonTargetPairSourceSet
              (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.source σ)
              (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.target σ) p := by
  letI : IsNoetherianRing Bᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K B
  letI : IsArtinianRing Bᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isArtinianRing_op_of_finiteDimensional K B
  intro ι _ σ p
  classical
  obtain ⟨a, b, hab, hpair⟩ := Finset.card_eq_two.mp p.2.2
  have he : a.1 ≠ b.1 := by
    intro h
    apply hab
    exact Subtype.ext h
  have ht :
      QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.target σ b.1 =
        QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.target σ a.1 :=
    b.2.trans a.2.symm
  obtain ⟨x, hactual, hsources⟩ :=
    exists_actualTwoTopApexData_of_commonTarget
      K B σ a.1 b.1 he ht
  refine ⟨x, hactual, hsources.trans ?_⟩
  unfold QuotientSubmoduleEquidistribution.IndecomposableSkeleton.commonTargetPairSourceSet
  rw [hpair]
  ext z
  simp [eq_comm]

/-- The constructed apex together with the two invariants which recover its
common-target pair: its simple quotient types recover the two sources, and its
simple radical recovers the common target. -/
structure ConstructedCommonTargetPairApexData
    {R : Type u} [Ring R] [IsNoetherianRing R]
    {ι : Type u}
    (σ : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, u, u} R ι)
    (source target : σ.LengthTwoIndex → σ.SimpleIndex)
    (p : σ.CommonTargetPair target) where
  apex : σ.TwoTopQuotientShapeIndex
  actual : σ.ActualTwoTopApexData apex
  simpleQuotients_eq_sources :
    σ.simpleQuotientIndexSet apex.1 =
      σ.commonTargetPairSourceSet source target p
  radical_index_eq_target : actual.radical.1 = p.1.1

/-- A formal common-target pair has a constructed apex which remembers both
its source set and its common target. -/
theorem exists_constructedCommonTargetPairApexData
    (K B : Type u)
    [Field K] [IsAlgClosed K]
    [Ring B] [Algebra K B] [FiniteDimensional K B] :
    letI : IsNoetherianRing Bᵐᵒᵖ :=
      QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K B
    letI : IsArtinianRing Bᵐᵒᵖ :=
      QuotientSubmoduleEquidistribution.isArtinianRing_op_of_finiteDimensional K B
    ∀ {ι : Type u} [Finite ι]
      (σ : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, u, u} Bᵐᵒᵖ ι)
      (p : σ.CommonTargetPair
        (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.target σ)),
      Nonempty
        (ConstructedCommonTargetPairApexData σ
          (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.source σ)
          (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.target σ) p) := by
  letI : IsNoetherianRing Bᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K B
  letI : IsArtinianRing Bᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isArtinianRing_op_of_finiteDimensional K B
  intro ι _ σ p
  classical
  obtain ⟨a, b, hab, hpair⟩ := Finset.card_eq_two.mp p.2.2
  have he : a.1 ≠ b.1 := by
    intro h
    apply hab
    exact Subtype.ext h
  have ht :
      QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.target σ b.1 =
        QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.target σ a.1 :=
    b.2.trans a.2.symm
  obtain ⟨D⟩ :=
    exists_constructedTwoTopPreApexData_of_commonTarget
      K B σ a.1 b.1 he ht
  let s := QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.source σ a.1
  let t := QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.source σ b.1
  let r := QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.target σ a.1
  let x := D.toTwoTopQuotientShapeIndex σ s t r
  let actual := D.toActualTwoTopApexData σ s t r
  refine ⟨{
    apex := x
    actual := actual
    simpleQuotients_eq_sources := ?_
    radical_index_eq_target := ?_ }⟩
  · refine (D.simpleQuotientIndexSet_eq σ s t r).trans ?_
    unfold QuotientSubmoduleEquidistribution.IndecomposableSkeleton.commonTargetPairSourceSet
    rw [hpair]
    ext z
    simp [s, t, eq_comm]
  · change
      (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.target σ a.1).1 = p.1.1
    exact congrArg Subtype.val a.2

section DeterministicConstruction

variable (K B : Type u)
  [Field K] [IsAlgClosed K]
  [Ring B] [Algebra K B] [FiniteDimensional K B]
  [IsNoetherianRing Bᵐᵒᵖ] [IsArtinianRing Bᵐᵒᵖ]

variable {ι : Type u} [Finite ι]
  (σ : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, u, u} Bᵐᵒᵖ ι)

/-- Deterministically choose the constructed data.  No mathematical claim
depends on the choice: injectivity below shows that the chosen apex still
remembers its parameter. -/
def constructedCommonTargetPairApexData
    (p : σ.CommonTargetPair
      (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.target σ)) :
    ConstructedCommonTargetPairApexData σ
      (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.source σ)
      (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.target σ) p :=
  Classical.choice
    (exists_constructedCommonTargetPairApexData K B σ p)

/-- The deterministic family-5 apex attached to a common-target pair. -/
def constructedCommonTargetPairApex
    (p : σ.CommonTargetPair
      (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.target σ)) :
    σ.TwoTopQuotientShapeIndex :=
  (constructedCommonTargetPairApexData K B σ p).apex

omit [IsAlgClosed K] [FiniteDimensional K B]
    [IsArtinianRing Bᵐᵒᵖ] [Finite ι] in
/-- Under the no-parallel Ext-support bound, a common-target pair is
determined by its common target and the set of its two sources. -/
theorem commonTargetPair_eq_of_target_eq_of_sourceSet_eq
    (p q : σ.CommonTargetPair
      (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.target σ))
    (hnoParallel :
      QuotientSubmoduleEquidistribution.GabrielArrowBridge.NoParallelExtSupport (K := K) σ)
    (ht : p.1 = q.1)
    (hsources :
      σ.commonTargetPairSourceSet
          (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.source σ)
          (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.target σ) p =
        σ.commonTargetPairSourceSet
          (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.source σ)
          (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.target σ) q) :
    p = q := by
  classical
  rcases p with ⟨tp, P⟩
  rcases q with ⟨tq, Q⟩
  change tp = tq at ht
  subst tq
  have hfInjective : Function.Injective
      (fun e : {e : σ.LengthTwoIndex //
          QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.target σ e = tp} ↦
        (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.source σ e.1).1) := by
    intro e e' hee'
    apply Subtype.ext
    apply
      QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.toGabrielArrow_injective
        σ hnoParallel
    apply Subtype.ext
    exact Prod.ext (Subtype.ext hee') (e.2.trans e'.2.symm)
  have hPQ : P = Q := by
    apply Subtype.ext
    apply Finset.ext
    intro e
    constructor
    · intro heP
      have himage :
          (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.source σ e.1).1 ∈
            σ.commonTargetPairSourceSet
              (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.source σ)
              (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.target σ)
              ⟨tp, P⟩ := by
        exact ⟨e, heP, rfl⟩
      rw [hsources] at himage
      rcases himage with ⟨e', he'Q, he'e⟩
      have heq : e' = e := hfInjective he'e
      simpa [heq] using he'Q
    · intro heQ
      have himage :
          (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.source σ e.1).1 ∈
            σ.commonTargetPairSourceSet
              (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.source σ)
              (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.target σ)
              ⟨tp, Q⟩ := by
        exact ⟨e, heQ, rfl⟩
      rw [← hsources] at himage
      rcases himage with ⟨e', he'P, he'e⟩
      have heq : e' = e := hfInjective he'e
      simpa [heq] using he'P
  subst Q
  rfl

omit [IsArtinianRing Bᵐᵒᵖ] in
/-- The deterministic common-target-pair-to-apex construction is injective.
The apex recovers the common target from its radical and the two sources from
its simple quotient set. -/
theorem constructedCommonTargetPairApex_injective :
    Function.Injective (constructedCommonTargetPairApex K B σ) := by
  intro p q hapex
  let Dp := constructedCommonTargetPairApexData K B σ p
  let Dq := constructedCommonTargetPairApexData K B σ q
  change Dp.apex = Dq.apex at hapex
  have hindex : Dp.apex.1 = Dq.apex.1 :=
    congrArg Subtype.val hapex
  have hsimpleSets :
      σ.simpleQuotientIndexSet Dp.apex.1 =
        σ.simpleQuotientIndexSet Dq.apex.1 :=
    congrArg σ.simpleQuotientIndexSet hindex
  let erRight :
      σ.moduleRadical Dp.apex.1 ≃ₗ[Bᵐᵒᵖ]
        σ.obj Dq.actual.radical.1 := by
    rw [hindex]
    exact Dq.actual.radicalEquiv.symm
  let er :
      σ.obj Dp.actual.radical.1 ≃ₗ[Bᵐᵒᵖ]
        σ.obj Dq.actual.radical.1 :=
    Dp.actual.radicalEquiv.trans erRight
  have hradicalIndex :
      Dp.actual.radical.1 = Dq.actual.radical.1 :=
    σ.eq_of_iso ⟨er.toFGModuleCatIso⟩
  have htarget : p.1 = q.1 := by
    apply Subtype.ext
    exact Dp.radical_index_eq_target.symm.trans
      (hradicalIndex.trans Dq.radical_index_eq_target)
  have hsourceSets :
      σ.commonTargetPairSourceSet
          (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.source σ)
          (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.target σ) p =
        σ.commonTargetPairSourceSet
          (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.source σ)
          (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.target σ) q :=
    Dp.simpleQuotients_eq_sources.symm.trans
      (hsimpleSets.trans Dq.simpleQuotients_eq_sources)
  exact commonTargetPair_eq_of_target_eq_of_sourceSet_eq
    K B σ p q
      (QuotientSubmoduleEquidistribution.GabrielArrowBridge.RightModules.noParallelExtSupport_of_finiteDimensional_of_finiteSkeleton
        K B σ)
      htarget hsourceSets

end DeterministicConstruction

/-- Corrected realization interface for family 5.  The maintained closure
theorem proves `closed` directly from `actual`; no stronger statement about
an epic component of every arbitrary biproduct presentation is required. -/
structure ActualClosedCommonTargetForkRealization
    {R : Type u} [Ring R] [IsNoetherianRing R]
    {ι : Type u}
    (σ : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, u, u} R ι)
    (source target : σ.LengthTwoIndex → σ.SimpleIndex) where
  apex : σ.CommonTargetPair target → σ.TwoTopQuotientShapeIndex
  actual : ∀ p, σ.ActualTwoTopApexData (apex p)
  simpleQuotients_eq_sources :
    ∀ p, σ.simpleQuotientIndexSet (apex p).1 =
      σ.commonTargetPairSourceSet source target p
  apex_injective : Function.Injective apex
  closed : ∀ p,
    σ.qClosure.IsClosed (σ.twoTopQuotientShapeSupport (apex p))

namespace ActualClosedCommonTargetForkRealization

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type u}
  {σ : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, u, u} R ι}
  {source target : σ.LengthTwoIndex → σ.SimpleIndex}

/-- Each corrected realization produces an actual closed support at level
three. -/
def toClosedLevelThree
    (D : ActualClosedCommonTargetForkRealization σ source target)
    (p : σ.CommonTargetPair target) :
    QuotientSubmoduleEquidistribution.BottomLevels.BottomThreeAdapter.ClosedLevelThree
      σ.qClosure :=
  ⟨⟨σ.twoTopQuotientShapeSupport (D.apex p), D.closed p⟩,
    σ.ncard_twoTopQuotientShapeSupport (D.apex p)⟩

/-- Distinct common-target pairs give distinct actual closed supports. -/
theorem toClosedLevelThree_injective
    (D : ActualClosedCommonTargetForkRealization σ source target) :
    Function.Injective D.toClosedLevelThree := by
  intro p q hpq
  apply D.apex_injective
  apply σ.twoTopQuotientShapeSupport_injective
  exact congrArg (fun C ↦ (C.1.1 : Set ι)) hpq

/-- The count-facing embedding supplied by the corrected family-5
realization. -/
def toClosedLevelThreeEmbedding
    (D : ActualClosedCommonTargetForkRealization σ source target) :
    σ.CommonTargetPair target ↪
      QuotientSubmoduleEquidistribution.BottomLevels.BottomThreeAdapter.ClosedLevelThree
        σ.qClosure where
  toFun := D.toClosedLevelThree
  inj' := D.toClosedLevelThree_injective

/-- Consequently the number of common-target pairs is bounded by the actual
third quotient-closure level. -/
theorem natCard_commonTargetPair_le_levelCount_three
    [Finite ι]
    (D : ActualClosedCommonTargetForkRealization σ source target) :
    Nat.card (σ.CommonTargetPair target) ≤ σ.qClosure.levelCount 3 := by
  classical
  letI := Fintype.ofFinite ι
  letI : Fintype σ.qClosure.Closeds :=
    Fintype.ofInjective
      (fun C : σ.qClosure.Closeds ↦ (C : Set ι)) Subtype.coe_injective
  letI : Fintype
      (QuotientSubmoduleEquidistribution.BottomLevels.BottomThreeAdapter.ClosedLevelThree
        σ.qClosure) :=
    Fintype.ofInjective
      (fun C :
        QuotientSubmoduleEquidistribution.BottomLevels.BottomThreeAdapter.ClosedLevelThree
          σ.qClosure ↦ C.1) Subtype.coe_injective
  rw [QuotientSubmoduleEquidistribution.BottomLevels.BottomThreeAdapter.levelCount_three_eq_natCard_closedLevelThree]
  exact Nat.card_le_card_of_injective
    D.toClosedLevelThree D.toClosedLevelThree_injective

end ActualClosedCommonTargetForkRealization

/-- The explicit common-target pushout construction supplies the corrected
realization interface in the paper's finite-dimensional right-module scope. -/
def constructedActualClosedCommonTargetForkRealization
    (K B : Type u)
    [Field K] [IsAlgClosed K]
    [Ring B] [Algebra K B] [FiniteDimensional K B] :
    letI : IsNoetherianRing Bᵐᵒᵖ :=
      QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K B
    letI : IsArtinianRing Bᵐᵒᵖ :=
      QuotientSubmoduleEquidistribution.isArtinianRing_op_of_finiteDimensional K B
    ∀ {ι : Type u} [Finite ι]
      (σ : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, u, u} Bᵐᵒᵖ ι),
      ActualClosedCommonTargetForkRealization σ
        (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.source σ)
        (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.target σ) := by
  letI : IsNoetherianRing Bᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K B
  letI : IsArtinianRing Bᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isArtinianRing_op_of_finiteDimensional K B
  intro ι _ σ
  let data := constructedCommonTargetPairApexData K B σ
  exact {
    apex := constructedCommonTargetPairApex K B σ
    actual := fun p ↦ (data p).actual
    simpleQuotients_eq_sources := fun p ↦
      (data p).simpleQuotients_eq_sources
    apex_injective := constructedCommonTargetPairApex_injective K B σ
    closed := fun p ↦
      QuotientSubmoduleEquidistribution.YonedaTwoSourceReduction.qClosure_isClosed_twoTopQuotientShapeSupport_actual
        K B σ (constructedCommonTargetPairApex K B σ p)
          (data p).actual }

/-- Final count-facing endpoint for the constructed fifth family: formal
common-target arrow pairs inject into the actual third quotient-closure
level. -/
theorem natCard_commonTargetPair_le_qClosure_levelCount_three
    (K B : Type u)
    [Field K] [IsAlgClosed K]
    [Ring B] [Algebra K B] [FiniteDimensional K B] :
    letI : IsNoetherianRing Bᵐᵒᵖ :=
      QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K B
    letI : IsArtinianRing Bᵐᵒᵖ :=
      QuotientSubmoduleEquidistribution.isArtinianRing_op_of_finiteDimensional K B
    ∀ {ι : Type u} [Finite ι]
      (σ : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, u, u} Bᵐᵒᵖ ι),
      Nat.card
          (σ.CommonTargetPair
            (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.target σ)) ≤
        σ.qClosure.levelCount 3 := by
  letI : IsNoetherianRing Bᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K B
  letI : IsArtinianRing Bᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isArtinianRing_op_of_finiteDimensional K B
  intro ι _ σ
  exact
    (constructedActualClosedCommonTargetForkRealization K B σ).natCard_commonTargetPair_le_levelCount_three

end QuotientSubmoduleEquidistribution.FamilyFiveCommonTargetConstruction
