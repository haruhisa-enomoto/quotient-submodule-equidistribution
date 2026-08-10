import QuotientSubmoduleEquidistribution.RepresentationTheory.TrivSqZeroExtSeparatedModuleFunctor
import QuotientSubmoduleEquidistribution.Foundation.RingTheory.KrullSchmidt.Indecomposable

/-!
# Indecomposable separated square-zero data

This file expresses indecomposability intrinsically in the category of
separated data and proves that module reconstruction preserves and reflects
it.  For indecomposables supported on both layers, semisimplicity forces the
action to generate the radical and to have zero common kernel.  These are the
abstract, coordinate-free ingredients of the nonsimple indecomposable
correspondence for separated quivers.
-/

set_option autoImplicit false
noncomputable section
open scoped RightActions
open CategoryTheory

namespace QuotientSubmoduleEquidistribution.TrivSqZeroExtSeparatedIndecomposable

open QuotientSubmoduleEquidistribution
open QuotientSubmoduleEquidistribution.TrivSqZeroExtSeparatedData
open QuotientSubmoduleEquidistribution.TrivSqZeroExtSeparatedCorrespondence
open QuotientSubmoduleEquidistribution.TrivSqZeroExtSeparatedModuleFunctor

universe u v w
variable {S : Type u} {J : Type v}
variable [CommRing S] [AddCommGroup J]
variable [Module S J] [Module Sᵐᵒᵖ J]
variable [SMulCommClass S Sᵐᵒᵖ J]

def IsIndecomposableSeparatedData
    (D : SeparatedData.{u, v, w} (S := S) (J := J)) : Prop :=
  Nontrivial (Reconstructed D) ∧
    ∀ p : D ⟶ D, p ≫ p = p → p = 0 ∨ p = 𝟙 D

theorem isIndecomposableSeparatedData_of_reconstructed
    (D : SeparatedData.{u, v, w} (S := S) (J := J))
    (hD : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule
      (TrivSqZeroExt S J) (Reconstructed D)) :
    IsIndecomposableSeparatedData D := by
  refine ⟨hD.nontrivial, ?_⟩
  intro p hp
  let F := reconstructionFunctor (S := S) (J := J)
  have hpmap : F.map p ≫ F.map p = F.map p := by
    rw [← F.map_comp, hp]
  have hpidem : IsIdempotentElem (F.map p).hom := by
    change (F.map p).hom.comp (F.map p).hom = (F.map p).hom
    exact congrArg ModuleCat.Hom.hom hpmap
  rcases hD.eq_zero_or_eq_one_of_isIdempotentElem hpidem with hzero | hone
  · left
    apply F.map_injective
    ext x
    exact LinearMap.congr_fun hzero x
  · right
    apply F.map_injective
    ext x
    exact LinearMap.congr_fun hone x

theorem reconstructed_isIndecomposable_of_separatedData
    [IsSemisimpleRing S]
    (D : SeparatedData.{u, v, w} (S := S) (J := J))
    (hgen : IsGenerated D) (hD : IsIndecomposableSeparatedData D) :
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule
      (TrivSqZeroExt S J) (Reconstructed D) := by
  let e := reconstructedSeparatedDataIso (S := S) (J := J) D hgen
  letI : Nontrivial (Reconstructed D) := hD.1
  apply QuotientSubmoduleEquidistribution.Foundation.isIndecomposableModule_of_forall_isIdempotentElem
  intro f hf
  let fCat : reconstructedModuleCat D ⟶ reconstructedModuleCat D :=
    ModuleCat.ofHom f
  have hfCat : fCat ≫ fCat = fCat := by
    apply ModuleCat.Hom.ext
    exact hf
  let a : moduleSeparatedData (S := S) (J := J)
      (reconstructedModuleCat D) ⟶
      moduleSeparatedData (S := S) (J := J)
        (reconstructedModuleCat D) :=
    moduleSeparatedDataMap fCat
  have ha : a ≫ a = a := by
    change (moduleSeparatedDataFunctor (S := S) (J := J)).map fCat ≫
        (moduleSeparatedDataFunctor (S := S) (J := J)).map fCat =
      (moduleSeparatedDataFunctor (S := S) (J := J)).map fCat
    rw [← (moduleSeparatedDataFunctor (S := S) (J := J)).map_comp,
      hfCat]
  let p : D ⟶ D := e.inv ≫ a ≫ e.hom
  have hp : p ≫ p = p := by
    dsimp only [p]
    simp only [Category.assoc]
    rw [e.hom_inv_id_assoc]
    rw [← Category.assoc a a e.hom]
    rw [ha]
  rcases hD.2 p hp with hpzero | hpone
  · left
    have hazero : a = 0 := by
      calc
        a = e.hom ≫ p ≫ e.inv := by
          simp [p, Category.assoc]
        _ = 0 := by rw [hpzero]; simp
    have hFzero :
        (moduleSeparatedDataFunctor (S := S) (J := J)).map fCat = 0 :=
      hazero
    have hsq := moduleSeparatedDataFunctor_kernelSquareZero
      (S := S) (J := J) fCat fCat hFzero hFzero
    have hfCatZero : fCat = 0 := by
      rw [← hfCat]
      exact hsq
    exact congrArg ModuleCat.Hom.hom hfCatZero
  · right
    have haone : a = 𝟙 _ := by
      calc
        a = e.hom ≫ p ≫ e.inv := by
          simp [p, Category.assoc]
        _ = 𝟙 _ := by rw [hpone]; simp
    let gCat : reconstructedModuleCat D ⟶ reconstructedModuleCat D :=
      𝟙 _ - fCat
    have hFone :
        (moduleSeparatedDataFunctor (S := S) (J := J)).map fCat = 𝟙 _ :=
      haone
    have hFzero :
        (moduleSeparatedDataFunctor (S := S) (J := J)).map gCat = 0 := by
      simpa [gCat] using (sub_eq_zero.mpr hFone.symm)
    have hgidem : gCat ≫ gCat = gCat := by
      dsimp only [gCat]
      simp only [Preadditive.sub_comp, Preadditive.comp_sub,
        Category.id_comp, Category.comp_id]
      rw [hfCat]
      abel
    have hsq := moduleSeparatedDataFunctor_kernelSquareZero
      (S := S) (J := J) gCat gCat hFzero hFzero
    have hgzero : gCat = 0 := by
      rw [← hgidem]
      exact hsq
    have hfCatOne : fCat = 𝟙 _ := by
      exact (sub_eq_zero.mp hgzero).symm
    exact congrArg ModuleCat.Hom.hom hfCatOne

theorem reconstructed_isIndecomposable_iff
    [IsSemisimpleRing S]
    (D : SeparatedData.{u, v, w} (S := S) (J := J))
    (hgen : IsGenerated D) :
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule
        (TrivSqZeroExt S J) (Reconstructed D) ↔
      IsIndecomposableSeparatedData D :=
  ⟨isIndecomposableSeparatedData_of_reconstructed D,
    reconstructed_isIndecomposable_of_separatedData D hgen⟩

theorem module_isIndecomposable_iff_separatedData
    [IsSemisimpleRing S]
    (X : ModuleCat.{w} (TrivSqZeroExt S J)) :
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule (TrivSqZeroExt S J) X ↔
      IsIndecomposableSeparatedData
        (moduleSeparatedData (S := S) (J := J) X) := by
  let D := moduleSeparatedData (S := S) (J := J) X
  let e := reconstructedModuleIso (S := S) (J := J) X
  constructor
  · intro hX
    have hrec : @QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule
        (TrivSqZeroExt S J) (Reconstructed D) _ _
          (reconstructedModule D) :=
      @QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule.of_linearEquiv
        (TrivSqZeroExt S J) X _ _ X.isModule
        (Reconstructed D) _ (reconstructedModule D)
        hX e.symm.toLinearEquiv
    exact isIndecomposableSeparatedData_of_reconstructed D hrec
  · intro hD
    have hrec : @QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule
        (TrivSqZeroExt S J) (Reconstructed D) _ _
          (reconstructedModule D) :=
      reconstructed_isIndecomposable_of_separatedData D
        (moduleSeparatedData_isGenerated (S := S) (J := J) X) hD
    exact @QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule.of_linearEquiv
      (TrivSqZeroExt S J) (Reconstructed D) _ _
      (reconstructedModule D) X _ X.isModule
      hrec e.toLinearEquiv

omit [SMulCommClass S Sᵐᵒᵖ J] in
theorem isGenerated_of_indecomposable_of_top_nontrivial
    [IsSemisimpleRing S]
    (D : SeparatedData.{u, v, w} (S := S) (J := J))
    (hD : IsIndecomposableSeparatedData D) [Nontrivial D.top] :
    IsGenerated D := by
  by_contra hgen
  obtain ⟨L, hAL⟩ := exists_isCompl (actionRange D)
  let pRad : D.radical →ₗ[S] D.radical :=
    (actionRange D).projection L hAL
  let p : D ⟶ D :=
    ⟨(LinearMap.id, pRad), by
      intro j t
      apply Submodule.projection_apply_of_mem_left hAL
      apply Submodule.subset_span
      exact ⟨j, t, rfl⟩⟩
  have hp : p ≫ p = p := by
    apply Subtype.ext
    apply Prod.ext
    · ext t
      rfl
    · ext d
      exact DFunLike.congr_fun
        (Submodule.isIdempotentElem_projection hAL) d
  rcases hD.2 p hp with hpzero | hpone
  · obtain ⟨t, ht⟩ := exists_ne (0 : D.top)
    have hz := congrArg (fun q ↦ q.val.1) hpzero
    have hzt := LinearMap.congr_fun hz t
    exact ht hzt
  · apply hgen
    apply Submodule.eq_top_iff'.mpr
    intro d
    apply (Submodule.projection_eq_self_iff hAL d).mp
    have ho := congrArg (fun q ↦ q.val.2) hpone
    exact LinearMap.congr_fun ho d

def kernelSummand (D : SeparatedData.{u, v, w} (S := S) (J := J)) :
    Submodule (TrivSqZeroExt S J) (Reconstructed D) where
  carrier := {x | x.1 ∈ commonKernel D ∧ x.2 = 0}
  zero_mem' := ⟨Submodule.zero_mem _, rfl⟩
  add_mem' := by
    intro x y hx hy
    constructor
    · exact Submodule.add_mem _ hx.1 hy.1
    · change x.2 + y.2 = 0
      rw [hx.2, hy.2, add_zero]
  smul_mem' := by
    intro r x hx
    constructor
    · exact Submodule.smul_mem _ r.fst hx.1
    · change r.fst • x.2 + D.action r.snd x.1 = 0
      rw [hx.2, smul_zero, hx.1 r.snd, add_zero]

def kernelComplementSummand
    (D : SeparatedData.{u, v, w} (S := S) (J := J))
    (L : Submodule S D.top) :
    Submodule (TrivSqZeroExt S J) (Reconstructed D) where
  carrier := {x | x.1 ∈ L}
  zero_mem' := Submodule.zero_mem _
  add_mem' := fun hx hy ↦ Submodule.add_mem _ hx hy
  smul_mem' := fun r _ hx ↦ Submodule.smul_mem _ r.fst hx

theorem kernelSummand_isCompl
    (D : SeparatedData.{u, v, w} (S := S) (J := J))
    (L : Submodule S D.top) (hKL : IsCompl (commonKernel D) L) :
    IsCompl (kernelSummand D) (kernelComplementSummand D L) := by
  apply IsCompl.of_eq
  · apply le_antisymm
    · intro x hx
      have hx' := Submodule.mem_inf.mp hx
      have htop : x.1 ∈ commonKernel D ⊓ L :=
        Submodule.mem_inf.mpr ⟨hx'.1.1, hx'.2⟩
      rw [hKL.inf_eq_bot] at htop
      change x = 0
      apply Prod.ext
      · exact htop
      · exact hx'.1.2
    · exact bot_le
  · apply top_unique
    intro x _
    have htop : x.1 ∈ commonKernel D ⊔ L := by
      rw [hKL.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨k, hk, l, hl, hkl⟩ := Submodule.mem_sup.mp htop
    apply Submodule.mem_sup.mpr
    refine ⟨(k, 0), ⟨hk, rfl⟩, (l, x.2), hl, ?_⟩
    apply Prod.ext
    · exact hkl
    · simp

theorem commonKernel_eq_bot_of_reconstructed_indecomposable
    [IsSemisimpleRing S]
    (D : SeparatedData.{u, v, w} (S := S) (J := J))
    (hD : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule
      (TrivSqZeroExt S J) (Reconstructed D))
    [Nontrivial D.radical] :
    commonKernel D = ⊥ := by
  by_contra hK
  obtain ⟨L, hKL⟩ := exists_isCompl (commonKernel D)
  have hcompl := kernelSummand_isCompl D L hKL
  rcases hD.eq_bot_or_eq_bot hcompl with hleft | hright
  · apply hK
    apply le_antisymm
    · intro t ht
      have hmem : ((t, 0) : Reconstructed D) ∈ kernelSummand D :=
        ⟨ht, rfl⟩
      rw [hleft] at hmem
      have hzero : ((t, 0) : Reconstructed D) = 0 := hmem
      exact congrArg Prod.fst hzero
    · exact bot_le
  · obtain ⟨d, hd⟩ := exists_ne (0 : D.radical)
    have hmem : (((0 : D.top), d) : Reconstructed D) ∈
        kernelComplementSummand D L := Submodule.zero_mem L
    rw [hright] at hmem
    have hzero : (((0 : D.top), d) : Reconstructed D) = 0 := hmem
    exact hd (congrArg Prod.snd hzero)

theorem isKernelFree_of_indecomposable_of_radical_nontrivial
    [IsSemisimpleRing S]
    (D : SeparatedData.{u, v, w} (S := S) (J := J))
    (hD : IsIndecomposableSeparatedData D) [Nontrivial D.radical] :
    IsKernelFree D := by
  rcases subsingleton_or_nontrivial D.top with htop | htop
  · letI : Subsingleton D.top := htop
    apply le_antisymm
    · intro t _
      exact Subsingleton.elim t 0
    · exact bot_le
  · letI : Nontrivial D.top := htop
    have hgen := isGenerated_of_indecomposable_of_top_nontrivial D hD
    have hrec := reconstructed_isIndecomposable_of_separatedData D hgen hD
    exact commonKernel_eq_bot_of_reconstructed_indecomposable D hrec

theorem moduleSeparatedData_isKernelFree_of_indecomposable
    [IsSemisimpleRing S]
    (X : ModuleCat.{w} (TrivSqZeroExt S J))
    (hX : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule (TrivSqZeroExt S J) X)
    [Nontrivial (Module.jacobson (TrivSqZeroExt S J) X)] :
    IsKernelFree (moduleSeparatedData (S := S) (J := J) X) := by
  let D := moduleSeparatedData (S := S) (J := J) X
  letI : Nontrivial D.radical := by
    change Nontrivial (Module.jacobson (TrivSqZeroExt S J) X)
    infer_instance
  exact isKernelFree_of_indecomposable_of_radical_nontrivial D
    ((module_isIndecomposable_iff_separatedData
      (S := S) (J := J) X).mp hX)

/-- The separated datum of an indecomposable module with nonzero radical has
the two intrinsic properties used in the separated-quiver correspondence. -/
theorem moduleSeparatedData_of_radical_nontrivial_indecomposable
    [IsSemisimpleRing S]
    (X : ModuleCat.{w} (TrivSqZeroExt S J))
    (hX : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule (TrivSqZeroExt S J) X)
    [Nontrivial (Module.jacobson (TrivSqZeroExt S J) X)] :
    IsGenerated (moduleSeparatedData (S := S) (J := J) X) ∧
      IsKernelFree (moduleSeparatedData (S := S) (J := J) X) ∧
      IsIndecomposableSeparatedData
        (moduleSeparatedData (S := S) (J := J) X) := by
  exact ⟨moduleSeparatedData_isGenerated X,
    moduleSeparatedData_isKernelFree_of_indecomposable X hX,
    (module_isIndecomposable_iff_separatedData X).mp hX⟩

/-- A separated indecomposable with nonzero top and radical reconstructs to
an indecomposable module and is recovered from that module. -/
theorem reconstructedModule_of_bisupported_indecomposable
    [IsSemisimpleRing S]
    (D : SeparatedData.{u, v, w} (S := S) (J := J))
    (hD : IsIndecomposableSeparatedData D)
    [Nontrivial D.top] [Nontrivial D.radical] :
    IsGenerated D ∧ IsKernelFree D ∧
      QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule
        (TrivSqZeroExt S J) (Reconstructed D) ∧
      Nonempty
        (moduleSeparatedData (S := S) (J := J)
          (reconstructedModuleCat D) ≅ D) := by
  have hgen := isGenerated_of_indecomposable_of_top_nontrivial D hD
  exact ⟨hgen,
    isKernelFree_of_indecomposable_of_radical_nontrivial D hD,
    reconstructed_isIndecomposable_of_separatedData D hgen hD,
    ⟨reconstructedSeparatedDataIso D hgen⟩⟩

end QuotientSubmoduleEquidistribution.TrivSqZeroExtSeparatedIndecomposable
