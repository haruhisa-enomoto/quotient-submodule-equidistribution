import QuotientSubmoduleEquidistribution.RepresentationTheory.FiniteType
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Abelian.CommSq

/-!
# Kernel-summand deletion for effective lifting

This file isolates the categorical step in the directed effective-lifting
argument.  A split summand of the kernel of a morphism is quotiented out of
its source.  Postcomposition remains bijective from every test object on
which the original morphism was bijective.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

namespace QuotientSubmoduleEquidistribution.RepresentationDirected

universe v u uR uI

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Postcomposition on a Hom set. -/
def postcompose {U X Y : C} (f : X ⟶ Y) : (U ⟶ X) → (U ⟶ Y) :=
  fun a ↦ a ≫ f

/-- Injectivity of `Hom(U, f)` annihilates `Hom(U, kernel f)`. -/
theorem hom_kernel_eq_zero_of_postcompose_injective
    {U T Y : C} (f : T ⟶ Y)
    (hf : Function.Injective (postcompose (U := U) f))
    (a : U ⟶ kernel f) :
    a = 0 := by
  apply (cancel_mono (kernel.ι f)).1
  apply hf
  simp [postcompose]

/-- If `i` is split mono, then right orthogonality to its target implies
right orthogonality to its cokernel. -/
theorem hom_cokernel_eq_zero_of_splitMono
    {U Z K : C} (i : Z ⟶ K) [IsSplitMono i]
    (hK : ∀ a : U ⟶ K, a = 0)
    (a : U ⟶ cokernel i) :
    a = 0 := by
  let b : BinaryBicone Z (cokernel i) :=
    binaryBiconeOfIsSplitMonoOfCokernel
      (c := CokernelCofork.ofπ
        (cokernel.π i) (cokernel.condition i))
      (cokernelIsCokernel i)
  calc
    a = a ≫ 𝟙 _ := by simp
    _ = a ≫ b.inr ≫ b.snd := by rw [b.inr_snd]
    _ = (a ≫ b.inr) ≫ b.snd :=
      (Category.assoc a b.inr b.snd).symm
    _ = (0 : U ⟶ K) ≫ b.snd := by
      exact congrArg (fun q ↦ q ≫ b.snd) (hK (a ≫ b.inr))
    _ = 0 := zero_comp

section KernelSummandQuotient

variable {U Z T Y : C} (f : T ⟶ Y)
  (i : Z ⟶ kernel f)

/-- The inclusion in the source induced by a map to the kernel. -/
abbrev deletedInclusion : Z ⟶ T := i ≫ kernel.ι f

/-- The source obtained by deleting the chosen kernel summand. -/
abbrev deletedQuotient : C := cokernel (deletedInclusion f i)

/-- The quotient projection after deleting the kernel summand. -/
abbrev deletedProjection : T ⟶ deletedQuotient f i :=
  cokernel.π (deletedInclusion f i)

/-- The original morphism descended to the quotient source. -/
abbrev deletedMap : deletedQuotient f i ⟶ Y :=
  cokernel.desc (deletedInclusion f i) f (by simp [deletedInclusion])

private abbrev kernelQuotientInclusion :
    cokernel i ⟶ deletedQuotient f i :=
  cokernel.map i (deletedInclusion f i) (𝟙 _) (kernel.ι f) (by simp)

private abbrev quotientToKernelCokernel :
    deletedQuotient f i ⟶ cokernel (kernel.ι f) :=
  cokernel.map (deletedInclusion f i) (kernel.ι f) i (𝟙 _) (by simp)

private abbrev kernelCokernelToTarget : cokernel (kernel.ι f) ⟶ Y :=
  cokernel.desc (kernel.ι f) f (kernel.condition f)

private theorem quotientToKernelCokernel_comp :
    quotientToKernelCokernel f i ≫ kernelCokernelToTarget f =
      deletedMap f i := by
  apply (cancel_epi (deletedProjection f i)).1
  simp [deletedProjection, quotientToKernelCokernel,
    kernelCokernelToTarget, deletedMap, deletedInclusion]

private theorem deletedMap_postcompose_injective
    [IsSplitMono i]
    (hK : ∀ a : U ⟶ kernel f, a = 0) :
    Function.Injective (postcompose (U := U) (deletedMap f i)) := by
  intro a b hab
  rw [← sub_eq_zero] at hab ⊢
  let S :=
    ShortComplex.mk
      (kernelQuotientInclusion f i)
      (quotientToKernelCokernel f i)
      (by
        apply (cancel_epi (cokernel.π i)).1
        simp [kernelQuotientInclusion, quotientToKernelCokernel,
          deletedInclusion])
  have hS : S.Exact :=
    (kernelCokernelCompSequence_exact i (kernel.ι f)).exact 3
  haveI : Mono (kernelQuotientInclusion f i) := by
    apply Abelian.mono_cokernel_map_of_isPullback
    apply IsPullback.of_vert_isIso_mono
    exact ⟨by simp [deletedInclusion]⟩
  haveI : Mono (kernelCokernelToTarget f) := by
    exact (ShortComplex.exact_kernel f).mono_cokernelDesc
  have hzero : (a - b) ≫ quotientToKernelCokernel f i = 0 := by
    apply (cancel_mono (kernelCokernelToTarget f)).1
    rw [Category.assoc, quotientToKernelCokernel_comp]
    simpa [postcompose, sub_comp] using hab
  obtain ⟨c, hc⟩ := hS.lift' (a - b) hzero
  have hc0 : c = 0 :=
    hom_cokernel_eq_zero_of_splitMono i hK c
  rw [← hc, hc0, zero_comp]

/-- Deleting a split summand of the kernel preserves the Hom-isomorphism
from a fixed test object.  Both the quotient projection and the descended
map are bijective on `Hom(U, -)`. -/
theorem quotient_preserves_postcompose_bijective
    [IsSplitMono i]
    (hf : Function.Bijective (postcompose (U := U) f)) :
    Function.Bijective (postcompose (U := U) (deletedProjection f i)) ∧
      Function.Bijective (postcompose (U := U) (deletedMap f i)) := by
  have hK : ∀ a : U ⟶ kernel f, a = 0 :=
    hom_kernel_eq_zero_of_postcompose_injective f hf.1
  have hgInjective := deletedMap_postcompose_injective f i hK
  have hqInjective :
      Function.Injective (postcompose (U := U) (deletedProjection f i)) := by
    intro a b hab
    apply hf.1
    simpa [postcompose, deletedProjection, deletedMap,
      deletedInclusion, Category.assoc] using
      congrArg (fun k ↦ k ≫ deletedMap f i) hab
  have hqSurjective :
      Function.Surjective (postcompose (U := U) (deletedProjection f i)) := by
    intro a
    obtain ⟨t, ht⟩ := hf.2 (a ≫ deletedMap f i)
    refine ⟨t, ?_⟩
    apply hgInjective
    simpa [postcompose, deletedProjection, deletedMap,
      deletedInclusion, Category.assoc] using ht
  have hgSurjective :
      Function.Surjective (postcompose (U := U) (deletedMap f i)) := by
    intro a
    obtain ⟨t, ht⟩ := hf.2 a
    refine ⟨t ≫ deletedProjection f i, ?_⟩
    simpa [postcompose, deletedProjection, deletedMap,
      deletedInclusion, Category.assoc] using ht
  exact ⟨⟨hqInjective, hqSurjective⟩, ⟨hgInjective, hgSurjective⟩⟩

/-- Pointwise family form for all already treated skeleton labels. -/
theorem quotient_preserves_postcompose_bijective_family
    {A : Type*} (X : A → C) [IsSplitMono i]
    (hf : ∀ a, Function.Bijective (postcompose (U := X a) f)) :
    (∀ a, Function.Bijective
      (postcompose (U := X a) (deletedProjection f i))) ∧
      (∀ a, Function.Bijective
        (postcompose (U := X a) (deletedMap f i))) := by
  constructor <;> intro a
  · exact (quotient_preserves_postcompose_bijective f i (hf a)).1
  · exact (quotient_preserves_postcompose_bijective f i (hf a)).2

end KernelSummandQuotient

section KernelSummandSelection

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {Iota : Type uI}
  (sigma : IndecomposableSkeleton.{uR, uI, uR} R Iota)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- A skeleton summand of `K` with explicit split inclusion and retraction,
which receives a specified nonzero component from `X`. -/
structure KernelSummandWitness
    (X K : FGModuleCat.{uR} R) where
  label : Iota
  inclusion : sigma.obj label ⟶ K
  retraction : K ⟶ sigma.obj label
  split : inclusion ≫ retraction = 𝟙 _
  component : X ⟶ sigma.obj label
  component_ne_zero : component ≠ 0

namespace KernelSummandWitness

/-- The displayed inclusion is a split monomorphism. -/
theorem inclusion_isSplitMono
    {X K : FGModuleCat.{uR} R}
    (W : KernelSummandWitness sigma X K) :
    IsSplitMono W.inclusion :=
  IsSplitMono.mk' (SplitMono.mk W.retraction W.split)

end KernelSummandWitness

/-- A nonzero map into a module has a nonzero component in one term of its
skeleton decomposition. -/
theorem exists_kernelSummandWitness
    {X T Y : FGModuleCat.{uR} R}
    (f : T ⟶ Y) (h : X ⟶ kernel f) (hh : h ≠ 0) :
    Nonempty (KernelSummandWitness sigma X (kernel f)) := by
  classical
  obtain ⟨n, a, ⟨e⟩⟩ := sigma.decomposes (kernel f)
  have hcomponent :
      ∃ t : Fin n,
        h ≫ e.hom ≫ biproduct.π (fun s ↦ sigma.obj (a s)) t ≠ 0 := by
    by_contra hnone
    push Not at hnone
    apply hh
    apply (cancel_mono e.hom).1
    apply biproduct.hom_ext
    intro t
    simpa [Category.assoc] using hnone t
  obtain ⟨t, ht⟩ := hcomponent
  let inclusion : sigma.obj (a t) ⟶ kernel f :=
    biproduct.ι (fun s ↦ sigma.obj (a s)) t ≫ e.inv
  let retraction : kernel f ⟶ sigma.obj (a t) :=
    e.hom ≫ biproduct.π (fun s ↦ sigma.obj (a s)) t
  let component : X ⟶ sigma.obj (a t) := h ≫ retraction
  refine ⟨{
    label := a t
    inclusion := inclusion
    retraction := retraction
    split := ?_
    component := component
    component_ne_zero := ?_ }⟩
  · simp [inclusion, retraction, Category.assoc]
  · simpa [component, retraction, Category.assoc] using ht

end KernelSummandSelection

end QuotientSubmoduleEquidistribution.RepresentationDirected
