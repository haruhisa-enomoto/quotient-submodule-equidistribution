import QuotientSubmoduleEquidistribution.RepresentationDirected.IyamaNakayamaStrictnessBridge
import QuotientSubmoduleEquidistribution.RepresentationDirected.IyamaRepresentableMesh

/-!
# Pre-strict categorical word meshes

This file packages the precise abstract alignment between a word-indexed
representable mesh complex and a finite tau-category.  The package does not
assume strictness.  The finite-ladder Nakayama theorem supplies strictness,
after which the existing rank argument gives the numerical mesh recurrence.

Constructing this package for Iyama's mesh category is deliberately a separate
obligation.  Thus the file records the remaining realization boundary without
assuming the paper's desired conclusion.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.RepresentationDirected.IyamaMesh

open QuotientSubmoduleEquidistribution.Iyama
open QuotientSubmoduleEquidistribution.RepresentationDirected.PrincipalPositivity

universe v u w uK uL

variable {K : Type uK} [Field K]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear K C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C]
variable {L : Type uL}

/-- The exact pre-strict realization needed to connect a categorical word
mesh with the finite tau-category ladder theorem.  It contains no monicity
or endpoint-weight equality. -/
structure PreStrictWordMeshRealization
    {G : SimpleGraph L} {Q : List L}
    {obj left middle : Fin Q.length → C}
    (E : WordRightMeshRealization (K := K) G Q obj left middle)
    (hRuns : ARWord.HasOnlyBoundaryRepeatedRuns G Q)
    (weight : Fin Q.length → ℤ)
    (hweight : IsPositiveRightAdditive G Q weight) where
  tauCategory : FiniteTauCategoryData C (Fin Q.length)
  categorical : NakayamaStrictnessRealization tauCategory
    (Word.translationQuiver G Q hRuns weight hweight)
  firstMapIso : ∀ x : Fin Q.length,
    Nonempty
      (Arrow.mk (E.toRightRepresentableMeshComplex.nu x) ≅
        Arrow.mk (tauCategory.nuPlus x))

namespace PreStrictWordMeshRealization

variable {G : SimpleGraph L} {Q : List L}
variable {obj left middle : Fin Q.length → C}
variable {E : WordRightMeshRealization (K := K) G Q obj left middle}
variable {hRuns : ARWord.HasOnlyBoundaryRepeatedRuns G Q}
variable {weight : Fin Q.length → ℤ}
variable {hweight : IsPositiveRightAdditive G Q weight}

/-- The categorical realization transports the proved Nakayama bridge to
the displayed first maps of the pre-strict word meshes. -/
def toNakayamaStrictnessBridge
    (R : PreStrictWordMeshRealization E hRuns weight hweight) :
    FiniteAdmissibleTranslationQuiver.NakayamaStrictnessBridge
      (Word.translationQuiver G Q hRuns weight hweight)
      (fun x ↦ Mono (E.toRightRepresentableMeshComplex.nu x)) := by
  let B := R.categorical.toNakayamaStrictnessBridge
  refine
    { nakayamaPair := B.nakayamaPair
      pair_of_not_monic := ?_
      endpoint_weight_eq := B.endpoint_weight_eq }
  intro x hx hmono
  apply B.pair_of_not_monic x hx
  intro hTau
  obtain ⟨e⟩ := R.firstMapIso x
  apply hmono
  exact ((MorphismProperty.monomorphisms C).arrow_mk_iso_iff e).mpr hTau

/-- A pre-strict word-mesh realization therefore gives the exact numerical
mesh recurrence used by the directed-sorting development. -/
def toRepresentableMeshExactnessData
    (R : PreStrictWordMeshRealization E hRuns weight hweight)
    [∀ a x : Fin Q.length, Module.Finite K (obj a ⟶ obj x)]
    [∀ a x : Fin Q.length, Module.Finite K (obj a ⟶ left x)]
    [∀ a x : Fin Q.length, Module.Finite K (obj a ⟶ middle x)] :
    MeshExactness.RepresentableMeshExactnessData G Q :=
  E.toRepresentableMeshExactnessData_of_word_nakayamaBridge
    hRuns weight hweight R.toNakayamaStrictnessBridge

end PreStrictWordMeshRealization

end QuotientSubmoduleEquidistribution.RepresentationDirected.IyamaMesh
