import QuotientSubmoduleEquidistribution.RepresentationDirected.IyamaMeshStrictness
import QuotientSubmoduleEquidistribution.RepresentationDirected.EffectiveLiftingComplement
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Representable mesh exactness after Iyama strictness

This file formalizes the routine categorical and finite-dimensional part of
the manuscript's Iyama input.  A right tau-sequence already gives exactness
at the middle and right representable terms.  Once Iyama's strictness theorem
makes the first mesh map monic, evaluation and rank-nullity give the integral
mesh recurrence consumed by the directed-sorting development.

The file does not assume that recurrence in its categorical structures.  It
derives it from representable exactness, structural identifications of the
word-mesh terms, and monicity of the first map.  It contains no concrete
algebra, quiver presentation, module enumeration, or classification.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open CategoryTheory
open CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.RepresentationDirected.IyamaMesh

universe uV uK uC vC uL

variable {K : Type uK} [Field K]
variable {C : Type uC} [Category.{vC} C] [Preadditive C] [Linear K C]
variable {V : Type uV} [DecidableEq V]

/-! ## Evaluated right mesh complexes -/

/-- A one-dimensional diagonal fiber and the zero vector space off the
diagonal.  This models evaluation of the simple representable `S_x` at the
vertex object `a`. -/
abbrev SimpleRepresentableFiber (K : Type uK) [Field K]
    (a x : V) : Type uK :=
  Fin (if a = x then 1 else 0) → K

@[simp]
theorem finrank_simpleRepresentableFiber (a x : V) :
    Module.finrank K (SimpleRepresentableFiber K a x) =
      if a = x then 1 else 0 := by
  simpa only [SimpleRepresentableFiber] using
    (Module.finrank_fin_fun (R := K)
      (n := if a = x then 1 else 0))

/-- The representable content supplied by a right tau-sequence before
strictness.

The first map need not be monic.  Exactness at the middle and right terms,
and the radical/simple quotient, are retained independently of the desired
Euler recurrence. -/
structure RightRepresentableMeshComplex
    (obj left middle : V → C) where
  nu : ∀ x : V, left x ⟶ middle x
  mu : ∀ x : V, middle x ⟶ obj x
  simpleQuotient :
    ∀ a x : V, (obj a ⟶ obj x) →ₗ[K] SimpleRepresentableFiber K a x
  exact_at_middle :
    ∀ a x : V,
      Function.Exact
        (QuotientSubmoduleEquidistribution.RepresentationDirected.postcompLinearMap
          (K := K) (X := obj a) (nu x))
        (QuotientSubmoduleEquidistribution.RepresentationDirected.postcompLinearMap
          (K := K) (X := obj a) (mu x))
  exact_at_right :
    ∀ a x : V,
      Function.Exact
        (QuotientSubmoduleEquidistribution.RepresentationDirected.postcompLinearMap
          (K := K) (X := obj a) (mu x))
        (simpleQuotient a x)
  simpleQuotient_surjective :
    ∀ a x : V, Function.Surjective (simpleQuotient a x)

namespace RightRepresentableMeshComplex

variable {obj left middle : V → C}

/-- Categorical strictness of every first mesh map. -/
def IsStrict
    (E : RightRepresentableMeshComplex (K := K) obj left middle) : Prop :=
  ∀ x : V, Mono (E.nu x)

/-- Once strictness is known, exactness of the evaluated four-term complex
gives its Euler dimension identity. -/
theorem finrank_euler
    (E : RightRepresentableMeshComplex (K := K) obj left middle)
    (hstrict : E.IsStrict)
    [∀ a x : V, Module.Finite K (obj a ⟶ obj x)]
    [∀ a x : V, Module.Finite K (obj a ⟶ left x)]
    [∀ a x : V, Module.Finite K (obj a ⟶ middle x)]
    (a x : V) :
    Module.finrank K (obj a ⟶ left x) +
        Module.finrank K (obj a ⟶ obj x) =
      Module.finrank K (obj a ⟶ middle x) +
        (if a = x then 1 else 0) := by
  let f := QuotientSubmoduleEquidistribution.RepresentationDirected.postcompLinearMap
    (K := K) (X := obj a) (E.nu x)
  let g := QuotientSubmoduleEquidistribution.RepresentationDirected.postcompLinearMap
    (K := K) (X := obj a) (E.mu x)
  let q := E.simpleQuotient a x
  letI : Mono (E.nu x) := hstrict x
  have hf : Function.Injective f := by
    intro s t hst
    apply (cancel_mono (E.nu x)).1
    exact hst
  have hfg : LinearMap.range f = LinearMap.ker g :=
    (LinearMap.exact_iff.mp (E.exact_at_middle a x)).symm
  have hgq : LinearMap.range g = LinearMap.ker q :=
    (LinearMap.exact_iff.mp (E.exact_at_right a x)).symm
  have hfrange : Module.finrank K (LinearMap.range f) =
      Module.finrank K (obj a ⟶ left x) :=
    LinearMap.finrank_range_of_inj hf
  have hqrange : Module.finrank K (LinearMap.range q) =
      Module.finrank K (SimpleRepresentableFiber K a x) := by
    rw [LinearMap.range_eq_top.mpr (E.simpleQuotient_surjective a x),
      finrank_top]
  have hg_rank_nullity := LinearMap.finrank_range_add_finrank_ker g
  have hq_rank_nullity := LinearMap.finrank_range_add_finrank_ker q
  rw [← hfg, hfrange] at hg_rank_nullity
  rw [← hgq, hqrange, finrank_simpleRepresentableFiber] at hq_rank_nullity
  omega

/-- The categorical strictness theorem obtained by instantiating the
Nakayama bridge with actual monomorphisms of first mesh maps. -/
theorem isStrict_of_positiveRightAdditive
    [Fintype V]
    (E : RightRepresentableMeshComplex (K := K) obj left middle)
    (Q : FiniteAdmissibleTranslationQuiver V)
    (B : Q.NakayamaStrictnessBridge (fun x ↦ Mono (E.nu x)))
    (projective_monic : ∀ x : V, x ∈ Q.projective → Mono (E.nu x))
    (weight : V → ℤ) (hadd : Q.IsPositiveRightAdditive weight) :
    E.IsStrict :=
  Q.strict_all_of_positiveRightAdditive
    (fun x ↦ Mono (E.nu x)) B projective_monic weight hadd

end RightRepresentableMeshComplex

/-! ## Adapter to the word-mesh recurrence -/

open QuotientSubmoduleEquidistribution.RepresentationDirected.PrincipalPositivity
open QuotientSubmoduleEquidistribution.RepresentationDirected.MeshExactness

variable {L : Type uL}

/-- The natural-number middle-term dimension dictated by the word quiver. -/
def wordMiddleFinrank (G : SimpleGraph L) (Q : List L)
    (homDimension : Fin Q.length → Fin Q.length → ℕ)
    (a x : Fin Q.length) : ℕ := by
  classical
  exact ∑ y ∈ Finset.univ.filter
    (fun y : Fin Q.length ↦ ARWord.IsMiddle G Q y x), homDimension a y

/-- Casting the finite middle-term sum to the integers gives the production
scalar middle sum. -/
theorem intCast_wordMiddleFinrank
    (G : SimpleGraph L) (Q : List L)
    (homDimension : Fin Q.length → Fin Q.length → ℕ)
    (a x : Fin Q.length) :
    (wordMiddleFinrank G Q homDimension a x : ℤ) =
      scalarMiddleSum G Q
        (fun y ↦ (homDimension a y : ℤ)) x := by
  classical
  simp [wordMiddleFinrank, scalarMiddleSum]

/-- A categorical word-mesh realization with the structural identifications
of its left and middle terms.

The extra fields are only zero-object and finite-biproduct dimension
identifications.  They do not state the Euler recurrence to be proved. -/
structure WordRightMeshRealization
    (G : SimpleGraph L) (Q : List L)
    (obj left middle : Fin Q.length → C)
    extends RightRepresentableMeshComplex (K := K) obj left middle where
  left_finrank_of_previous :
    ∀ (a p x : Fin Q.length), ARWord.IsPrevious Q p x →
      Module.finrank K (obj a ⟶ left x) =
        Module.finrank K (obj a ⟶ obj p)
  left_isZero_of_first :
    ∀ (x : Fin Q.length), (¬ ∃ p, ARWord.IsPrevious Q p x) →
      IsZero (left x)
  middle_finrank :
    ∀ (a x : Fin Q.length),
      Module.finrank K (obj a ⟶ middle x) =
        wordMiddleFinrank G Q
          (fun a y ↦ Module.finrank K (obj a ⟶ obj y)) a x

namespace WordRightMeshRealization

variable {G : SimpleGraph L} {Q : List L}
variable {obj left middle : Fin Q.length → C}

/-- At a first occurrence the omitted left mesh term has zero Hom dimension. -/
theorem left_finrank_of_first
    (E : WordRightMeshRealization (K := K) G Q obj left middle)
    (a x : Fin Q.length) (hfirst : ¬ ∃ p, ARWord.IsPrevious Q p x) :
    Module.finrank K (obj a ⟶ left x) = 0 := by
  letI : Subsingleton (obj a ⟶ left x) :=
    ⟨(E.left_isZero_of_first x hfirst).eq_of_tgt⟩
  exact Module.finrank_zero_of_subsingleton

/-- The first map out of the omitted zero term is automatically monic at
the projective boundary of the word translation quiver. -/
theorem projective_monic_for_wordTranslationQuiver
    (E : WordRightMeshRealization (K := K) G Q obj left middle)
    (hRuns : ARWord.HasOnlyBoundaryRepeatedRuns G Q)
    (weight : Fin Q.length → ℤ)
    (hweight : IsPositiveRightAdditive G Q weight) :
    ∀ x : Fin Q.length,
      x ∈ (Word.translationQuiver G Q hRuns weight hweight).projective →
        Mono (E.toRightRepresentableMeshComplex.nu x) := by
  intro x hx
  apply (E.left_isZero_of_first x ?_).mono
  exact hx

/-- Strict categorical word meshes produce exactly the numerical data used
by the current production interface. -/
def toRepresentableMeshExactnessData
    (E : WordRightMeshRealization (K := K) G Q obj left middle)
    (hstrict : E.toRightRepresentableMeshComplex.IsStrict)
    [∀ a x : Fin Q.length, Module.Finite K (obj a ⟶ obj x)]
    [∀ a x : Fin Q.length, Module.Finite K (obj a ⟶ left x)]
    [∀ a x : Fin Q.length, Module.Finite K (obj a ⟶ middle x)] :
    RepresentableMeshExactnessData G Q where
  homDimension a x := Module.finrank K (obj a ⟶ obj x)
  exact_recurrence := by
    intro a x
    constructor
    · intro p hp
      have hEuler :=
        E.toRightRepresentableMeshComplex.finrank_euler hstrict a x
      have hEulerInt :
          (Module.finrank K (obj a ⟶ left x) : ℤ) +
              Module.finrank K (obj a ⟶ obj x) =
            Module.finrank K (obj a ⟶ middle x) +
              ((if a = x then 1 else 0 : ℕ) : ℤ) := by
        exact_mod_cast hEuler
      have hMiddle := intCast_wordMiddleFinrank G Q
        (fun a y ↦ Module.finrank K (obj a ⟶ obj y)) a x
      have hLeftInt :
          (Module.finrank K (obj a ⟶ left x) : ℤ) =
            Module.finrank K (obj a ⟶ obj p) := by
        exact_mod_cast E.left_finrank_of_previous a p x hp
      have hMiddleInt :
          (Module.finrank K (obj a ⟶ middle x) : ℤ) =
            scalarMiddleSum G Q
              (fun y ↦ (Module.finrank K (obj a ⟶ obj y) : ℤ)) x := by
        calc
          (Module.finrank K (obj a ⟶ middle x) : ℤ) =
              wordMiddleFinrank G Q
                (fun a y ↦ Module.finrank K (obj a ⟶ obj y)) a x := by
            exact_mod_cast E.middle_finrank a x
          _ = _ := hMiddle
      have hDelta :
          (((if a = x then 1 else 0 : ℕ) : ℤ)) =
            (if a = x then 1 else 0 : ℤ) := by
        by_cases hax : a = x <;> simp [hax]
      change (Module.finrank K (obj a ⟶ obj x) : ℤ) =
        (if a = x then 1 else 0) +
          scalarMiddleSum G Q
            (fun y ↦ (Module.finrank K (obj a ⟶ obj y) : ℤ)) x -
          Module.finrank K (obj a ⟶ obj p)
      linarith [hEulerInt, hLeftInt, hMiddleInt, hDelta]
    · intro hfirst
      have hEuler :=
        E.toRightRepresentableMeshComplex.finrank_euler hstrict a x
      have hEulerInt :
          (Module.finrank K (obj a ⟶ left x) : ℤ) +
              Module.finrank K (obj a ⟶ obj x) =
            Module.finrank K (obj a ⟶ middle x) +
              ((if a = x then 1 else 0 : ℕ) : ℤ) := by
        exact_mod_cast hEuler
      have hMiddle := intCast_wordMiddleFinrank G Q
        (fun a y ↦ Module.finrank K (obj a ⟶ obj y)) a x
      have hLeftInt :
          (Module.finrank K (obj a ⟶ left x) : ℤ) = 0 := by
        exact_mod_cast E.left_finrank_of_first a x hfirst
      have hMiddleInt :
          (Module.finrank K (obj a ⟶ middle x) : ℤ) =
            scalarMiddleSum G Q
              (fun y ↦ (Module.finrank K (obj a ⟶ obj y) : ℤ)) x := by
        calc
          (Module.finrank K (obj a ⟶ middle x) : ℤ) =
              wordMiddleFinrank G Q
                (fun a y ↦ Module.finrank K (obj a ⟶ obj y)) a x := by
            exact_mod_cast E.middle_finrank a x
          _ = _ := hMiddle
      have hDelta :
          (((if a = x then 1 else 0 : ℕ) : ℤ)) =
            (if a = x then 1 else 0 : ℤ) := by
        by_cases hax : a = x <;> simp [hax]
      change (Module.finrank K (obj a ⟶ obj x) : ℤ) =
        (if a = x then 1 else 0) +
          scalarMiddleSum G Q
            (fun y ↦ (Module.finrank K (obj a ⟶ obj y) : ℤ)) x
      linarith [hEulerInt, hLeftInt, hMiddleInt, hDelta]

/-- Combining a categorical word realization with the Nakayama strictness
bridge derives the production mesh-exactness data directly. -/
def toRepresentableMeshExactnessData_of_positiveRightAdditive
    (E : WordRightMeshRealization (K := K) G Q obj left middle)
    (T : FiniteAdmissibleTranslationQuiver (Fin Q.length))
    (B : T.NakayamaStrictnessBridge
      (fun x ↦ Mono (E.toRightRepresentableMeshComplex.nu x)))
    (projective_monic : ∀ x : Fin Q.length, x ∈ T.projective →
      Mono (E.toRightRepresentableMeshComplex.nu x))
    (weight : Fin Q.length → ℤ) (hadd : T.IsPositiveRightAdditive weight)
    [∀ a x : Fin Q.length, Module.Finite K (obj a ⟶ obj x)]
    [∀ a x : Fin Q.length, Module.Finite K (obj a ⟶ left x)]
    [∀ a x : Fin Q.length, Module.Finite K (obj a ⟶ middle x)] :
    RepresentableMeshExactnessData G Q :=
  E.toRepresentableMeshExactnessData
    (E.toRightRepresentableMeshComplex.isStrict_of_positiveRightAdditive
      T B projective_monic weight hadd)

/-- The word-level assembly of the Iyama route.  Boundary-run combinatorics
constructs the finite admissible translation quiver and transports the given
positive right-additive weight to it; the only nonformal input left in this
statement is the genuine Nakayama-ladder bridge for the word mesh category. -/
def toRepresentableMeshExactnessData_of_word_nakayamaBridge
    (E : WordRightMeshRealization (K := K) G Q obj left middle)
    (hRuns : ARWord.HasOnlyBoundaryRepeatedRuns G Q)
    (weight : Fin Q.length → ℤ)
    (hweight : IsPositiveRightAdditive G Q weight)
    (B : FiniteAdmissibleTranslationQuiver.NakayamaStrictnessBridge
      (Word.translationQuiver G Q hRuns weight hweight)
      (fun x ↦ Mono (E.toRightRepresentableMeshComplex.nu x)))
    [∀ a x : Fin Q.length, Module.Finite K (obj a ⟶ obj x)]
    [∀ a x : Fin Q.length, Module.Finite K (obj a ⟶ left x)]
    [∀ a x : Fin Q.length, Module.Finite K (obj a ⟶ middle x)] :
    RepresentableMeshExactnessData G Q :=
  E.toRepresentableMeshExactnessData_of_positiveRightAdditive
    (Word.translationQuiver G Q hRuns weight hweight) B
    (E.projective_monic_for_wordTranslationQuiver hRuns weight hweight) weight
    (Word.translationQuiver_isPositiveRightAdditive
      G Q hRuns weight hweight)

end WordRightMeshRealization

end QuotientSubmoduleEquidistribution.RepresentationDirected.IyamaMesh
