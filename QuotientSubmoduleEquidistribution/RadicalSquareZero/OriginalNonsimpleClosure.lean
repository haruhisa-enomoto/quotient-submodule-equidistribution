import QuotientSubmoduleEquidistribution.RadicalSquareZero.ActualTopCoverage
import QuotientSubmoduleEquidistribution.RadicalSquareZero.SimpleSourceTopTrace
import QuotientSubmoduleEquidistribution.RadicalSquareZero.SkeletonTraceBridge
import QuotientSubmoduleEquidistribution.RepresentationTheory.LevelThreeNonUniserialShapes

/-!
# Original-side nonsimple quotient-closure membership

Once an actual square-zero indecomposable skeleton has been labeled as
nonsimples plus simple vertices, generation of a nonsimple target depends
only on the selected nonsimple labels.  This file turns the simple-source
top-trace vanishing theorem into that pointwise statement for the actual
quotient closure.
-/

set_option autoImplicit false

noncomputable section

open Set
open CategoryTheory

namespace QuotientSubmoduleEquidistribution.RadicalSquareZero

open RadicalSquareZeroCombinatorics.CoreFamily.TopCoverage
open TrivSqZeroExtSeparatedTrace

universe u v w x y

variable {S : Type u} {J : Type v}
variable [CommRing S] [AddCommGroup J]
variable [Module S J] [Module Sᵐᵒᵖ J]
variable [SMulCommClass S Sᵐᵒᵖ J]
variable [IsSemisimpleRing S]
variable [IsNoetherianRing (TrivSqZeroExt S J)]

/-- The objectwise properties of a skeleton labeling by nonsimples and
simple vertices which are needed to remove simple sources from nonsimple
generation. -/
structure OriginalNonsimpleLabelData
    (Nonsimple : Type x) (Vertex : Type y)
    (sigma : IndecomposableSkeleton.{max u v, max x y, w}
      (TrivSqZeroExt S J) (Nonsimple ⊕ Vertex)) where
  /-- Every vertex label is represented by a simple module. -/
  simple_simple (v : Vertex) :
    Simple (sigma.obj (Sum.inr v))
  /-- Every nonsimple label has nonzero module radical. -/
  nonsimple_radical_nontrivial (y : Nonsimple) :
    Nontrivial
      (Module.jacobson (TrivSqZeroExt S J) (sigma.obj (Sum.inl y)))

namespace OriginalNonsimpleLabelData

variable {Nonsimple : Type x} {Vertex : Type y}
  [Fintype Nonsimple] [DecidableEq Nonsimple]
  [Fintype Vertex]
  {sigma : IndecomposableSkeleton.{max u v, max x y, w}
    (TrivSqZeroExt S J) (Nonsimple ⊕ Vertex)}

/-- Nonsimple generation, expressed only through the top trace of the
selected nonsimple family. -/
def Generates (C : Finset Nonsimple) (y : Nonsimple) : Prop :=
  moduleFamilyTopTrace
      (fun i : {n : Nonsimple // n ∈ C} ↦
        (sigma.obj (Sum.inl i.1)).obj)
      (sigma.obj (Sum.inl y)).obj = ⊤

/-- The original skeleton support consisting of a chosen finite set of
nonsimple labels. -/
def nonsimpleSupport (C : Finset Nonsimple) :
    Set (Nonsimple ⊕ Vertex) :=
  Sum.inl '' (C : Set Nonsimple)

/-- The original skeleton support consisting of a chosen finite set of
simple vertex labels. -/
def simpleSupport (U : Finset Vertex) :
    Set (Nonsimple ⊕ Vertex) :=
  Sum.inr '' (U : Set Vertex)

omit [Fintype Nonsimple] [Fintype Vertex] [DecidableEq Nonsimple] in
@[simp]
theorem mem_nonsimpleSupport_iff
    (C : Finset Nonsimple) (y : Nonsimple) :
    Sum.inl y ∈ nonsimpleSupport (Vertex := Vertex) C ↔ y ∈ C := by
  simp [nonsimpleSupport]

omit [Fintype Nonsimple] [Fintype Vertex] [DecidableEq Nonsimple] in
@[simp]
theorem mem_simpleSupport_iff
    (U : Finset Vertex) (v : Vertex) :
    Sum.inr v ∈ simpleSupport (Nonsimple := Nonsimple) U ↔ v ∈ U := by
  simp [simpleSupport]

omit [DecidableEq Nonsimple] in
/-- Every support is the union of its nonsimple and simple parts. -/
theorem nonsimpleSupport_union_simpleSupport_parts
    (T : Set (Nonsimple ⊕ Vertex)) :
    nonsimpleSupport (Vertex := Vertex) (nonsimplePart T) ∪
        simpleSupport (Nonsimple := Nonsimple) (simplePart T) = T := by
  ext z
  rcases z with y | v
  · simp [nonsimpleSupport, simpleSupport]
  · simp [nonsimpleSupport, simpleSupport]

/-- Simple vertices forced as quotients by a nonsimple support. -/
noncomputable def forcedTop (C : Finset Nonsimple) : Finset Vertex :=
  by
    classical
    exact Finset.univ.filter fun v ↦
      Sum.inr v ∈
        sigma.qClosure (nonsimpleSupport (Vertex := Vertex) C)

omit [Fintype Nonsimple] [DecidableEq Nonsimple] in
/-- Membership in the forced-top set is exactly top-trace coverage of the
simple target by the chosen nonsimple family. -/
theorem mem_forcedTop_iff_moduleFamilyTopTrace_eq_top
    [DecidableEq Vertex]
    (C : Finset Nonsimple) (v : Vertex) :
    v ∈ forcedTop (sigma := sigma) C ↔
      moduleFamilyTopTrace
          (fun i : {n : Nonsimple // n ∈ C} ↦
            (sigma.obj (Sum.inl i.1)).obj)
          (sigma.obj (Sum.inr v)).obj = ⊤ := by
  let T := nonsimpleSupport (Vertex := Vertex) C
  let e : {n : Nonsimple // n ∈ C} ≃ {i // i ∈ T} :=
    Equiv.Set.image Sum.inl (C : Set Nonsimple) Sum.inl_injective
  simp only [forcedTop, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [IndecomposableSkeleton.mem_qClosure_iff_trace_eq_top]
  rw [skeletonTrace_eq_moduleFamilyTrace]
  rw [moduleFamilyTrace_eq_top_iff_moduleFamilyTopTrace_eq_top]
  have hreindex := moduleFamilyTopTrace_reindex
    e (skeletonSelectedFamily sigma T) (sigma.obj (Sum.inr v)).obj
  have hfamily :
      (fun i : {n : Nonsimple // n ∈ C} ↦
          skeletonSelectedFamily sigma T (e i)) =
        fun i ↦ (sigma.obj (Sum.inl i.1)).obj := by
    funext i
    rfl
  rw [← hreindex, hfamily]

omit [DecidableEq Nonsimple] in
/-- Actual quotient-closure membership of a nonsimple target is independent
of all selected simple labels. -/
theorem nonsimple_mem_qClosure_iff
    (D : OriginalNonsimpleLabelData Nonsimple Vertex sigma)
    (T : Set (Nonsimple ⊕ Vertex)) (y : Nonsimple) :
    Sum.inl y ∈ sigma.qClosure T ↔
      Generates (sigma := sigma) (nonsimplePart T) y := by
  let X : Nonsimple → ModuleCat.{w} (TrivSqZeroExt S J) :=
    fun n ↦ (sigma.obj (Sum.inl n)).obj
  let Z : Vertex → ModuleCat.{w} (TrivSqZeroExt S J) :=
    fun v ↦ (sigma.obj (Sum.inr v)).obj
  let Y : ModuleCat.{w} (TrivSqZeroExt S J) :=
    (sigma.obj (Sum.inl y)).obj
  letI (v : Vertex) :
      Simple (sigma.obj (Sum.inr v)) :=
    QuotientSubmoduleEquidistribution.RadicalSquareZero.OriginalNonsimpleLabelData.simple_simple
      D v
  letI (v : Vertex) :
      IsSimpleModule (TrivSqZeroExt S J) (sigma.obj (Sum.inr v)) :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).mp
      inferInstance
  letI (v : Vertex) :
      IsSemisimpleModule (TrivSqZeroExt S J) (Z v) :=
    inferInstance
  letI : Nontrivial (Module.jacobson (TrivSqZeroExt S J) Y) :=
    QuotientSubmoduleEquidistribution.RadicalSquareZero.OriginalNonsimpleLabelData.nonsimple_radical_nontrivial
      D y
  rw [IndecomposableSkeleton.mem_qClosure_iff_trace_eq_top]
  rw [skeletonTrace_eq_moduleFamilyTrace]
  rw [moduleFamilyTrace_eq_top_iff_moduleFamilyTopTrace_eq_top]
  have hfamily :
      skeletonSelectedFamily sigma T =
        fun i : {z : Nonsimple ⊕ Vertex // z ∈ T} ↦
          Sum.elim X Z i.1 := by
    funext i
    rcases i with ⟨n | v, h⟩ <;> rfl
  rw [hfamily]
  rw [moduleFamilyTopTrace_selected_sum_eq_left_of_semisimple_right
    X Z T Y (sigma.indecomposable (Sum.inl y))]
  let e : {n : Nonsimple // n ∈ nonsimplePart T} ≃
      {n : Nonsimple // Sum.inl n ∈ T} :=
    Equiv.subtypeEquivProp <| by
      funext n
      exact propext (mem_nonsimplePart_iff T n)
  have hreindex := moduleFamilyTopTrace_reindex
    e (fun i : {n : Nonsimple // Sum.inl n ∈ T} ↦ X i.1) Y
  change moduleFamilyTopTrace
      (fun i : {n : Nonsimple // Sum.inl n ∈ T} ↦ X i.1) Y = ⊤ ↔
    Generates (sigma := sigma) (nonsimplePart T) y
  rw [← hreindex]
  rfl

omit [IsSemisimpleRing S] [DecidableEq Nonsimple] in
/-- Actual quotient-closure membership of a simple target is either literal
selection or top coverage forced by the selected nonsimple labels. -/
theorem simple_mem_qClosure_iff
    [DecidableEq Vertex]
    (D : OriginalNonsimpleLabelData Nonsimple Vertex sigma)
    (T : Set (Nonsimple ⊕ Vertex)) (v : Vertex) :
    Sum.inr v ∈ sigma.qClosure T ↔
      Sum.inr v ∈ T ∨
        v ∈ forcedTop (sigma := sigma) (nonsimplePart T) := by
  let S := nonsimpleSupport (Vertex := Vertex) (nonsimplePart T)
  let U := simpleSupport (Nonsimple := Nonsimple) (simplePart T)
  have hsimple : ∀ i ∈ U, Simple (sigma.obj i) := by
    intro i hi
    rcases hi with ⟨w, -, rfl⟩
    exact D.simple_simple w
  have hparts : S ∪ U = T := by
    exact nonsimpleSupport_union_simpleSupport_parts T
  have hclosure : sigma.qClosure T = sigma.qClosure S ∪ U := by
    rw [← hparts]
    exact sigma.qClosure_union_eq_closure_union_of_forall_simple hsimple
  rw [hclosure]
  simp only [Set.mem_union, forcedTop, Finset.mem_filter,
    Finset.mem_univ, true_and]
  change
    (Sum.inr v ∈ sigma.qClosure S ∨ Sum.inr v ∈ U) ↔
      Sum.inr v ∈ T ∨ Sum.inr v ∈ sigma.qClosure S
  have hvU : Sum.inr v ∈ U ↔ Sum.inr v ∈ T := by
    rw [← hparts]
    constructor
    · exact Set.mem_union_right S
    · rintro (hvS | hvU)
      · rcases hvS with ⟨y, -, h⟩
        cases h
      · exact hvU
  rw [hvU]
  exact or_comm

/-- Insert the proved original nonsimple membership law into the paired
pointwise closure interface.  The remaining arguments are exactly the simple
target laws and the comparison with the separated side. -/
noncomputable def toPairedClosureMembership
    [DecidableEq Vertex]
    (D : OriginalNonsimpleLabelData Nonsimple Vertex sigma)
    {clB : QuotientSubmoduleEquidistribution.SetClosure
      (Nonsimple ⊕ (Vertex ⊕ Vertex))}
    (b_nonsimple_mem :
      ∀ (T : Set (Nonsimple ⊕ (Vertex ⊕ Vertex)))
        (y : Nonsimple),
        Sum.inl y ∈ clB T ↔
          Generates (sigma := sigma) (bNonsimplePart T) y)
    (b_covered_simple_mem :
      ∀ (T : Set (Nonsimple ⊕ (Vertex ⊕ Vertex)))
        (v : Vertex),
        Sum.inr (Sum.inl v) ∈ clB T ↔
          Sum.inr (Sum.inl v) ∈ T ∨
            v ∈ forcedTop (sigma := sigma) (bNonsimplePart T))
    (b_free_simple_mem :
      ∀ (T : Set (Nonsimple ⊕ (Vertex ⊕ Vertex)))
        (v : Vertex),
        Sum.inr (Sum.inr v) ∈ clB T ↔
          Sum.inr (Sum.inr v) ∈ T) :
    PairedClosureMembership sigma.qClosure clB where
  Generates := Generates (sigma := sigma)
  forcedTop := forcedTop (sigma := sigma)
  a_nonsimple_mem T y := D.nonsimple_mem_qClosure_iff T y
  a_simple_mem T v := D.simple_mem_qClosure_iff T v
  b_nonsimple_mem := b_nonsimple_mem
  b_covered_simple_mem := b_covered_simple_mem
  b_free_simple_mem := b_free_simple_mem

end OriginalNonsimpleLabelData

end QuotientSubmoduleEquidistribution.RadicalSquareZero
