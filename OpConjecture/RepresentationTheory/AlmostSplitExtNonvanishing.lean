import OpConjecture.RepresentationTheory.FGExtRealization
import OpConjecture.RepresentationTheory.FiniteARTranslationData

/-!
# Detecting nonzero extensions with an almost-split kernel

A nonsplit short exact sequence ending at the target of a right almost-split
sequence induces a nonzero morphism between their kernels.  Finite realization
of degree-one Ext classes gives the consequence used in the manuscript's
representation-directed lifting argument: a nonzero `Ext¹(X,Z)` class yields
a nonzero map from `Z` to the intrinsic Auslander--Reiten translate of `X`.

This is strictly weaker than the full injective-stable Auslander--Reiten
duality formula, and it is the only consequence of that formula used by the
argument.  No concrete algebra or module classification is involved.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace OpConjecture

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Let `T -> E -> X` be short exact with right almost-split quotient map.
Every nonsplit short exact sequence `Z -> V -> X` induces a nonzero morphism
`Z -> T`.

Indeed, factor `V -> X` through `E -> X` and lift its restriction to `Z`
through the kernel `T -> E`.  If the lift were zero, the factor would descend
through `V -> X` and split the right almost-split quotient map. -/
theorem exists_ne_zero_kernel_map_of_nonsplit_shortExact
    {T E X Z V : C}
    (i : T ⟶ E) (q : E ⟶ X) (hiq : i ≫ q = 0)
    (hA : (ShortComplex.mk i q hiq).ShortExact)
    (hAS : IsRightAlmostSplit q)
    (j : Z ⟶ V) (p : V ⟶ X) (hjp : j ≫ p = 0)
    (hS : (ShortComplex.mk j p hjp).ShortExact)
    (hp : ¬ IsSplitEpi p) :
    ∃ a : Z ⟶ T, a ≠ 0 := by
  obtain ⟨h, hh⟩ := hAS.factors p hp
  have hzero : (j ≫ h) ≫ q = 0 := by
    rw [Category.assoc, hh, hjp]
  let lifted := KernelFork.IsLimit.lift' hA.fIsKernel (j ≫ h) hzero
  let a : Z ⟶ T := lifted.1
  have ha : a ≫ i = j ≫ h := lifted.2
  refine ⟨a, ?_⟩
  intro ha0
  have hkill : j ≫ h = 0 := by
    rw [← ha, ha0, zero_comp]
  let descended := CokernelCofork.IsColimit.desc' hS.gIsCokernel h hkill
  let s : X ⟶ E := descended.1
  have hs : p ≫ s = h := descended.2
  apply hAS.not_isSplitEpi
  letI : Epi p := hS.epi_g
  exact IsSplitEpi.mk'
    { section_ := s
      id := by
        apply (cancel_epi p).1
        rw [← Category.assoc, hs, hh, Category.comp_id] }

variable {R : Type w} [Ring R] [IsNoetherianRing R]
  [HasExt.{w} (FGModuleCat.{w} R)]

/-- Every nonzero degree-one extension of the endpoint of a right
almost-split short exact sequence by `Z` produces a nonzero map from `Z` to
the sequence's kernel object.

The module-specific input is finite realization of the Ext class. -/
theorem exists_ne_zero_hom_to_rightAlmostSplit_kernel_of_ext_ne_zero
    {A : ShortComplex (FGModuleCat.{w} R)}
    (hA : A.ShortExact) (hAS : IsRightAlmostSplit A.g)
    (Z : FGModuleCat.{w} R) (xi : Ext A.X₃ Z 1) (hxi : xi ≠ 0) :
    ∃ a : Z ⟶ A.X₁, a ≠ 0 := by
  obtain ⟨V, i, q, zero, hS, hclass⟩ :=
    FGExtRealization.exists_shortExact_with_extClass_eq A.X₃ Z xi
  have hq : ¬ IsSplitEpi q := by
    intro hsplit
    letI : IsSplitEpi q := hsplit
    apply hxi
    rw [← hclass]
    exact OpConjecture.NoParallelExtOne.extClass_eq_zero_of_section
      hS (section_ q) (IsSplitEpi.id q)
  exact exists_ne_zero_kernel_map_of_nonsplit_shortExact
    A.f A.g A.zero hA hAS i q zero hS hq

namespace IndecomposableSkeleton

universe uR uIota

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {Iota : Type uIota}
  (sigma : IndecomposableSkeleton.{uR, uIota, uR} R Iota)

/-- A chosen minimal right almost-split decomposition detects every nonzero
extension of its endpoint by a nonzero map into its intrinsic kernel. -/
theorem MinimalRightAlmostSplitDecomposition.exists_ne_zero_hom_to_kernel_of_ext_ne_zero
    [HasExt.{uR} (FGModuleCat.{uR} R)]
    {x : Iota} (A : sigma.MinimalRightAlmostSplitDecomposition x)
    (hx : ¬ Projective (sigma.obj x))
    (Z : FGModuleCat.{uR} R) (xi : Ext (sigma.obj x) Z 1)
    (hxi : xi ≠ 0) :
    ∃ a : Z ⟶ kernel A.map, a ≠ 0 := by
  letI : Epi A.map :=
    OpConjecture.IndecomposableSkeleton.IsRightAlmostSplit.epi_of_not_projective_obj
      sigma A.map A.rightAlmostSplit hx
  let S : ShortComplex (FGModuleCat.{uR} R) :=
    ShortComplex.mk (kernel.ι A.map) A.map (kernel.condition A.map)
  have hS : S.ShortExact :=
    { exact := S.exact_of_f_is_kernel (kernelIsKernel A.map) }
  change Ext S.X₃ Z 1 at xi
  change xi ≠ 0 at hxi
  change ∃ a : Z ⟶ S.X₁, a ≠ 0
  exact exists_ne_zero_hom_to_rightAlmostSplit_kernel_of_ext_ne_zero
    hS A.rightAlmostSplit Z xi hxi

namespace FiniteARTranslationData

variable (D : sigma.FiniteARTranslationData)

/-- The chosen intrinsic AR-translation representative detects every
nonzero degree-one extension of its endpoint. -/
theorem exists_ne_zero_hom_to_arTranslation_of_ext_ne_zero
    [HasExt.{uR} (FGModuleCat.{uR} R)]
    (x : sigma.NonprojectiveLabel)
    (Z : FGModuleCat.{uR} R) (xi : Ext (sigma.obj x.1) Z 1)
    (hxi : xi ≠ 0) :
    ∃ a : Z ⟶ sigma.obj (arTranslation sigma D x).1, a ≠ 0 := by
  obtain ⟨a, ha⟩ :=
    (chosenRightAR sigma D x).exists_ne_zero_hom_to_kernel_of_ext_ne_zero
      sigma x.2 Z xi hxi
  let e := arTranslationKernelIso sigma D x
  refine ⟨a ≫ e.hom, ?_⟩
  intro ha0
  apply ha
  apply (cancel_mono e.hom).1
  simpa using ha0

end FiniteARTranslationData

end IndecomposableSkeleton

end OpConjecture
