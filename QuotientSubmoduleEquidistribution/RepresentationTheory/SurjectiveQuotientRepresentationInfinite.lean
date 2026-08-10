import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RingTheory.Finiteness.Basic
import QuotientSubmoduleEquidistribution.RepresentationTheory.RepresentationInfiniteCertificate

/-!
# Inflation along a surjective ring map

For a quotient map `R → S`, restriction of scalars is fully faithful on
module homomorphisms.  In particular, it preserves indecomposability and
pairwise nonisomorphism.  Thus an infinite indecomposable family over a
quotient ring contradicts representation-finiteness of the original ring.
-/

noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.RepresentationInfiniteCertificate

universe u v z

section Linear

variable {R S M N : Type u} [Ring R] [Ring S]
  [AddCommGroup M] [AddCommGroup N]
  [Module S M] [Module S N]
  (q : R →+* S) (hq : Function.Surjective q)

/-- An `R`-linear map between modules inflated along a surjective map is
automatically `S`-linear. -/
def extendLinearOfSurjective (hq : Function.Surjective q) :
    letI := Module.compHom M q
    letI := Module.compHom N q
    (M →ₗ[R] N) → (M →ₗ[S] N) := by
  letI : Module R M := Module.compHom M q
  letI : Module R N := Module.compHom N q
  intro f
  exact
    { toFun := f
      map_add' := f.map_add
      map_smul' := by
        intro s m
        obtain ⟨r, rfl⟩ := hq s
        exact f.map_smul r m }

@[simp]
theorem extendLinearOfSurjective_apply
    (f : letI := Module.compHom M q
      letI := Module.compHom N q
      M →ₗ[R] N) (m : M) :
    extendLinearOfSurjective q hq f m = f m := rfl

/-- Finite generation descends along a surjective scalar map. -/
theorem moduleFinite_restrictScalars_of_surjective
    (hq : Function.Surjective q) [Module.Finite S M] :
    letI := Module.compHom M q
    Module.Finite R M := by
  letI : Module R M := Module.compHom M q
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' S M
  let liftCoordinates : (Fin n → R) → (Fin n → S) :=
    fun x i ↦ q (x i)
  have liftCoordinates_add (x y : Fin n → R) :
      liftCoordinates (x + y) = liftCoordinates x + liftCoordinates y := by
    ext i
    exact q.map_add _ _
  have liftCoordinates_smul (r : R) (x : Fin n → R) :
      liftCoordinates (r • x) = q r • liftCoordinates x := by
    ext i
    exact q.map_mul _ _
  let g : (Fin n → R) →ₗ[R] M :=
    { toFun := fun x ↦ p (liftCoordinates x)
      map_add' := by
        intro x y
        rw [liftCoordinates_add, map_add]
      map_smul' := by
        intro r x
        change p (liftCoordinates (r • x)) = q r • p (liftCoordinates x)
        rw [liftCoordinates_smul, map_smul] }
  apply Module.Finite.of_surjective g
  intro m
  obtain ⟨y, rfl⟩ := hp m
  choose x hx using fun i ↦ hq (y i)
  refine ⟨x, ?_⟩
  apply congrArg p
  ext i
  exact hx i

end Linear

section FG

variable {R S : Type u} [Ring R] [Ring S]
  (q : R →+* S) (hq : Function.Surjective q)

/-- Inflation of a finitely generated `S`-module to a finitely generated
`R`-module along a quotient map. -/
def restrictFG (hq : Function.Surjective q)
    (M : FGModuleCat.{u} S) : FGModuleCat.{u} R := by
  letI : Module R M := Module.compHom M q
  letI : Module.Finite R M :=
    moduleFinite_restrictScalars_of_surjective q hq
  exact FGModuleCat.of R M

/-- An isomorphism between two inflated modules lifts to an isomorphism over
the quotient ring. -/
def quotientIsoOfRestrictIso
    (M N : FGModuleCat.{u} S)
    (e : restrictFG q hq M ≅ restrictFG q hq N) :
    M ≅ N where
  hom := FGModuleCat.ofHom <|
    extendLinearOfSurjective q hq
      (FGModuleCat.isoToLinearEquiv e).toLinearMap
  inv := FGModuleCat.ofHom <|
    extendLinearOfSurjective q hq
      (FGModuleCat.isoToLinearEquiv e).symm.toLinearMap
  hom_inv_id := by
    apply FGModuleCat.hom_ext
    ext m
    exact (FGModuleCat.isoToLinearEquiv e).symm_apply_apply m
  inv_hom_id := by
    apply FGModuleCat.hom_ext
    ext m
    exact (FGModuleCat.isoToLinearEquiv e).apply_symm_apply m

/-- Indecomposability is preserved when a quotient module is inflated to the
original ring. -/
theorem indecomposable_restrictFG
    (M : FGModuleCat.{u} S)
    (hM : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule S M) :
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R (restrictFG q hq M) := by
  letI : Module R M := Module.compHom M q
  letI : Module.Finite R M :=
    moduleFinite_restrictScalars_of_surjective q hq
  rw [QuotientSubmoduleEquidistribution.Foundation.isIndecomposableModule_iff_nontrivial_and_forall_isIdempotentElem]
  refine ⟨hM.nontrivial, ?_⟩
  intro f hf
  let fS : Module.End S M := extendLinearOfSurjective q hq f
  have hfS : IsIdempotentElem fS := by
    apply LinearMap.ext
    intro m
    exact DFunLike.congr_fun hf m
  rcases hM.eq_zero_or_eq_one_of_isIdempotentElem hfS with hzero | hone
  · left
    apply LinearMap.ext
    intro m
    exact DFunLike.congr_fun hzero m
  · right
    apply LinearMap.ext
    intro m
    exact DFunLike.congr_fun hone m

/-- An infinite indecomposable family over a quotient ring inflates to one
over the original ring. -/
def InfiniteIndecomposableFamily.restrictScalars
    {Parameter : Type z}
    (F : InfiniteIndecomposableFamily (R := S) Parameter) :
    InfiniteIndecomposableFamily (R := R) Parameter where
  obj a := restrictFG q hq (F.obj a)
  indecomposable a := indecomposable_restrictFG q hq _ (F.indecomposable a)
  eq_of_iso e :=
    F.eq_of_iso ⟨quotientIsoOfRestrictIso q hq _ _ e.some⟩

/-- Consequently a surjective image carrying an infinite indecomposable
family rules out every finite complete skeleton upstairs. -/
theorem false_of_surjective_image_family
    [IsNoetherianRing R]
    {Parameter : Type z} [Infinite Parameter]
    (q : R →+* S) (hq : Function.Surjective q)
    (F : InfiniteIndecomposableFamily (R := S) Parameter)
    {ι : Type v} [Finite ι]
    (σ : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, v, u} R ι) :
    False :=
  (F.restrictScalars q hq).false_of_finite_skeleton σ

end FG

end QuotientSubmoduleEquidistribution.RepresentationInfiniteCertificate
