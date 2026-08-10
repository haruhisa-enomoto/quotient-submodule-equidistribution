import OpConjecture.RepresentationTheory.IndecomposableBiproduct
import OpConjecture.RepresentationTheory.LollipopB1ModuleExtraction
import OpConjecture.RepresentationTheory.LollipopB1NamedModuleProperties
import OpConjecture.RepresentationTheory.LollipopB1SevenObjectAdapter

/-!
# Bridge from a seven-block normal form to the live-path classification

The only future input in this scratch file is `FiniteRepSevenDecomposition`:
every finite live-path representation, regarded as a genuine `B1Model`
module, is isomorphic to a finite biproduct of the seven displayed modules.

Indecomposability and duplicate-freeness of the displayed modules are not
included in that input.  They are supplied by the maintained named-module
property file.  Extraction from an arbitrary finitely generated module and
the local-endomorphism summand theorem then give the exact
`SevenObjectAdapter.Classification` required by the table assembly.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

namespace OpConjecture.LollipopConcrete.B1.ModuleLayer.ClassificationBridge

open ModuleExtraction
open NamedModuleProperties
open SevenObjectAdapter

universe u

variable (K : Type u) [Field K]

/-- The maintained table label, identified with the label used by the
named-module property calculation. -/
def labelEquivNamed : Label ≃ NamedLabel where
  toFun
    | .s1 => .s1
    | .s2 => .s2
    | .x => .x
    | .a => .a
    | .u => .u
    | .w => .w
    | .p => .p
  invFun
    | .s1 => .s1
    | .s2 => .s2
    | .x => .x
    | .a => .a
    | .u => .u
    | .w => .w
    | .p => .p
  left_inv i := by cases i <;> rfl
  right_inv i := by cases i <;> rfl

theorem obj_eq_namedModule (i : Label) :
    obj K i = namedModule K (labelEquivNamed i) := by
  cases i <;> rfl

/-- The weakest output retained from one normal-form construction: an
arbitrary finite indexing type, its seven-object labels, and the resulting
biproduct isomorphism.  In particular, no splitting flag, bases,
multiplicities, or uniqueness of the decomposition is retained. -/
structure SevenBiproductDecomposition (D : FiniteB1Rep K) where
  index : Type
  indexFintype : Fintype index
  label : index → Label
  iso :
    letI := indexFintype
    Nonempty
      (FiniteB1Rep.asFGModule K D ≅
        biproduct (fun t : index ↦ obj K (label t)))

/-- The sole future input: every finite representation has some finite
seven-object biproduct decomposition. -/
def FiniteRepSevenDecomposition : Prop :=
  ∀ D : FiniteB1Rep K, Nonempty (SevenBiproductDecomposition K D)

theorem obj_indecomposable (i : Label) :
    OpConjecture.Foundation.IsIndecomposableModule (B1Model K) (obj K i) := by
  rw [obj_eq_namedModule K i]
  exact namedModule_indec K (labelEquivNamed i)

theorem obj_eq_of_iso {i j : Label}
    (h : Nonempty (obj K i ≅ obj K j)) : i = j := by
  apply (labelEquivNamed : Label ≃ NamedLabel).injective
  by_contra hne
  apply namedModule_not_iso_of_ne K hne
  simpa only [← obj_eq_namedModule K] using h

/-- A seven-block decomposition theorem for finite representations supplies
the exact exhaustive, duplicate-free classification used by the live-path
adapter. -/
theorem classification
    (hdecomp : FiniteRepSevenDecomposition K) :
    SevenObjectAdapter.Classification K := by
  refine
    { indecomposable := obj_indecomposable K
      eq_of_iso := obj_eq_of_iso K
      exhaustive := ?_ }
  intro M hM
  let D : FiniteB1Rep K := extractedRep K M
  obtain ⟨E⟩ := hdecomp D
  letI : Fintype E.index := E.indexFintype
  obtain ⟨eD⟩ := E.iso
  let Y : E.index → FGModuleCat (B1Model K) :=
    fun t ↦ obj K (E.label t)
  let e : M ≅ biproduct Y :=
    (extractedModuleIso K M).symm ≪≫ eD
  have hY : ∀ t, OpConjecture.Foundation.IsIndecomposableModule (B1Model K) (Y t) := by
    intro t
    exact obj_indecomposable K (E.label t)
  obtain ⟨t, ⟨ht⟩⟩ :=
    OpConjecture.IndecomposableBiproduct.exists_iso_summand
      M (SevenObjectAdapter.b1Module_finiteLength K M) hM Y hY e
  exact ⟨E.label t, ⟨ht⟩⟩

/-- Literal existence-and-uniqueness form of the seven-object
classification. -/
theorem indecomposable_iso_exactly_one
    (hdecomp : FiniteRepSevenDecomposition K)
    (M : FGModuleCat.{u} (B1Model K))
    (hM : OpConjecture.Foundation.IsIndecomposableModule (B1Model K) M) :
    ∃! i : Label, Nonempty (M ≅ obj K i) := by
  let C : SevenObjectAdapter.Classification K := classification K hdecomp
  obtain ⟨i, hi⟩ := C.exhaustive M hM
  refine ⟨i, hi, fun j hj ↦ ?_⟩
  exact C.eq_of_iso
    ⟨(Classical.choice hj).symm ≪≫ Classical.choice hi⟩

end OpConjecture.LollipopConcrete.B1.ModuleLayer.ClassificationBridge
