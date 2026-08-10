import QuotientSubmoduleEquidistribution.RepresentationTheory.RingelImageFunctor

/-!
# Descent of Ringel's image functor to `E/U`

The image of every elementary null complex is projective.  Additivity then
shows that the image functor sends the whole null ideal to morphisms factoring
through projectives.  Consequently `q : E → L` descends strictly to
`q̄ : E/U → L/P`.  The final equivalence is exposed with the exact remaining
categorical obligation (`q̄.IsEquivalence`), separating Ringel's density,
fullness, and faithfulness argument from all quotient bookkeeping.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace QuotientSubmoduleEquidistribution.RingelEta

universe u u'

open QuotientSubmoduleEquidistribution.RingelStable
open QuotientSubmoduleEquidistribution.RingelStable.FaithfulCoreAdapter

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {S : Type u'} [Ring S] [IsNoetherianRing S]

/-- The image functor followed by the projective-stable quotient. -/
def ringelImageStableFunctor
    (H : (FGProjectives (R := R))ᵒᵖ ≌ FGProjectives (R := S)) :
    StronglyExactComplexCategory H ⥤
      TorsionlessStableCategory (R := R) :=
  ringelImageTorsionlessFunctor H ⋙
    torsionlessStableQuotientFunctor (R := R)

/-- Every morphism in Ringel's null ideal has image factoring through a
finite projective module. -/
theorem ringelImage_factorsThroughProjective
    (H : (FGProjectives (R := R))ᵒᵖ ≌ FGProjectives (R := S))
    {X Y : StronglyExactComplexCategory H} {f : X ⟶ Y}
    (hf : FactorsThroughRingelU f) :
    Nonempty
      (FactorsThroughProjective ((ringelImageFunctor H).map f)) := by
  induction hf with
  | zero =>
      exact ⟨by simpa using
        (FactorsThroughProjective.zero :
          FactorsThroughProjective
            (0 : (ringelImageFunctor H).obj X ⟶
              (ringelImageFunctor H).obj Y))⟩
  | basic k P a b =>
      exact ⟨
        { middle :=
            (ringelImageFunctor H).obj
              (elementaryStrongComplex H k P)
          projective := projective_ringelImage_elementary H k P
          left := (ringelImageFunctor H).map a
          right := (ringelImageFunctor H).map b
          fac := (ringelImageFunctor H).map_comp a b |>.symm }⟩
  | add hf hg ihf ihg =>
      rcases ihf with ⟨ihf⟩
      rcases ihg with ⟨ihg⟩
      refine ⟨?_⟩
      rw [(ringelImageFunctor H).map_add (f := _ ) (g := _)]
      exact ihf.add ihg

/-- Ringel's stable image functor respects the congruence defining `E/U`. -/
theorem ringelImageStable_respects_U
    (H : (FGProjectives (R := R))ᵒᵖ ≌ FGProjectives (R := S))
    (X Y : StronglyExactComplexCategory H) (f g : X ⟶ Y)
    (hfg : ringelURel H f g) :
    (ringelImageStableFunctor H).map f =
      (ringelImageStableFunctor H).map g := by
  apply (torsionlessStableQuotientFunctor_map_eq_iff
    ((ringelImageTorsionlessFunctor H).map f)
    ((ringelImageTorsionlessFunctor H).map g)).2
  change Nonempty (FactorsThroughProjective
    ((ringelImageFunctor H).map f - (ringelImageFunctor H).map g))
  rcases hfg with ⟨hfg⟩
  have h := ringelImage_factorsThroughProjective H hfg
  rw [← (ringelImageFunctor H).map_sub]
  exact h

/-- The descended functor `q̄ : E/U → L/P`. -/
def ringelImageQuotientFunctor
    (H : (FGProjectives (R := R))ᵒᵖ ≌ FGProjectives (R := S)) :
    RingelComplexQuotient H ⥤
      TorsionlessStableCategory (R := R) :=
  CategoryTheory.Quotient.lift (ringelURel H)
    (ringelImageStableFunctor H)
    (ringelImageStable_respects_U H)

@[simp]
theorem ringelImageQuotientFunctor_obj
    (H : (FGProjectives (R := R))ᵒᵖ ≌ FGProjectives (R := S))
    (X : StronglyExactComplexCategory H) :
    (ringelImageQuotientFunctor H).obj
        ((ringelComplexQuotientFunctor H).obj X) =
      (ringelImageStableFunctor H).obj X :=
  rfl

@[simp]
theorem ringelImageQuotientFunctor_map
    (H : (FGProjectives (R := R))ᵒᵖ ≌ FGProjectives (R := S))
    {X Y : StronglyExactComplexCategory H} (f : X ⟶ Y) :
    (ringelImageQuotientFunctor H).map
        ((ringelComplexQuotientFunctor H).map f) =
      (ringelImageStableFunctor H).map f :=
  rfl

/-- Exact final seam in Ringel's `q` argument: once density, fullness, and
faithfulness have supplied `IsEquivalence`, the descended image functor is
the claimed equivalence `E/U ≃ L/P`. -/
def ringelImageQuotientEquivalence
    (H : (FGProjectives (R := R))ᵒᵖ ≌ FGProjectives (R := S))
    [(ringelImageQuotientFunctor H).IsEquivalence] :
    RingelComplexQuotient H ≌
      TorsionlessStableCategory (R := R) :=
  (ringelImageQuotientFunctor H).asEquivalence

end QuotientSubmoduleEquidistribution.RingelEta
