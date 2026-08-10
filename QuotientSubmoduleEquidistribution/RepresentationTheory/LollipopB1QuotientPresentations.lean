import QuotientSubmoduleEquidistribution.RepresentationTheory.LollipopB1SubmoduleBounds

/-!
# Explicit quotient-bad rows for the live-path lollipop

The two bad quotient outsiders are witnessed by the epimorphisms
`P ⟶ W` and `W ⟶ A`.
-/

noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.LollipopConcrete.B1.ModuleLayer.QuotientPresentations

open SubmoduleRows

universe u

variable (K : Type u) [Field K]

/-- The quotient `P ⟶ W`, identity at vertex one and first-coordinate
projection at vertex two. -/
def pToW : PModule K ⟶ WModule K :=
  homOfComponents K (PData K) (WData K)
    LinearMap.id (LinearMap.fst K K K)
    (by intro z; rfl)
    (by intro z; rfl)

@[simp] theorem pToW_apply (z : PModule K) :
    (pToW K).hom.hom z = (z.1, z.2.1) := rfl

theorem pToW_surjective :
    Function.Surjective (pToW K).hom.hom := by
  intro z
  exact ⟨(z.1, (z.2, 0)), rfl⟩

theorem pToW_epi : Epi (pToW K) :=
  (IndecomposableSkeleton.fg_epi_iff_surjective (pToW K)).mpr
    (pToW_surjective K)

/-- The quotient `W ⟶ A`, first-coordinate projection at vertex one and
identity at vertex two. -/
def wToA : WModule K ⟶ AModule K :=
  homOfComponents K (WData K) (AData K)
    (LinearMap.fst K K K) LinearMap.id
    (by intro z; rfl)
    (by intro z; rfl)

@[simp] theorem wToA_apply (z : WModule K) :
    (wToA K).hom.hom z = (z.1.1, z.2) := rfl

theorem wToA_surjective :
    Function.Surjective (wToA K).hom.hom := by
  intro z
  exact ⟨((z.1, 0), z.2), rfl⟩

theorem wToA_epi : Epi (wToA K) :=
  (IndecomposableSkeleton.fg_epi_iff_surjective (wToA K)).mpr
    (wToA_surjective K)

end QuotientSubmoduleEquidistribution.LollipopConcrete.B1.ModuleLayer.QuotientPresentations
