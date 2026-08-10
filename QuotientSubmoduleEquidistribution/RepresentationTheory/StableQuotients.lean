import QuotientSubmoduleEquidistribution.RepresentationTheory.StableIsomorphismReflection
import Mathlib.CategoryTheory.Quotient.Preadditive

/-!
# Stable quotients by projectives and injectives

This is the concrete quotient-hom layer used in Ringel's categories
`L/P` and `K/Q`.  Two maps become equal precisely when their difference
factors through a projective, respectively an injective, object.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.RingelStable

universe u

variable {R : Type u} [Ring R]

attribute [local instance]
  HasBinaryBiproducts.of_hasBinaryCoproducts

/-- An explicit zero object of `FGModuleCat`.  The category currently has
no global `HasZeroObject` instance, so the stable ideals use this chosen
finite zero module as their zero factor. -/
def zeroFGModule : FGModuleCat.{u} R :=
  FGModuleCat.of R (Fin 0 → R)

/-- The explicitly chosen finite zero module is categorically zero. -/
theorem isZero_zeroFGModule : IsZero (zeroFGModule (R := R)) where
  unique_to Y := ⟨{
    default := 0
    uniq := by
      intro f
      apply FGModuleCat.hom_ext
      ext x
      have hx : x = 0 := by
        funext i
        exact Fin.elim0 i
      subst x
      simp }⟩
  unique_from Y := ⟨{
    default := 0
    uniq := by
      intro f
      apply FGModuleCat.hom_ext
      ext x
      funext i
      exact Fin.elim0 i }⟩

namespace FactorsThroughProjective

/-- The zero morphism factors through the zero projective. -/
def zero {X Y : FGModuleCat.{u} R} :
    FactorsThroughProjective (0 : X ⟶ Y) := by
  exact
    { middle := zeroFGModule (R := R)
      projective := isZero_zeroFGModule.projective
      left := 0
      right := 0
      fac := by simp }

/-- Factorization through a projective is closed under negation. -/
def neg {X Y : FGModuleCat.{u} R} {f : X ⟶ Y}
    (hf : FactorsThroughProjective f) :
    FactorsThroughProjective (-f) := by
  exact
    { middle := hf.middle
      projective := hf.projective
      left := -hf.left
      right := hf.right
      fac := by rw [Preadditive.neg_comp, hf.fac] }

/-- Factorization through projectives is closed under addition, using
the binary biproduct of the two intermediate projectives. -/
def add {X Y : FGModuleCat.{u} R} {f g : X ⟶ Y}
    (hf : FactorsThroughProjective f)
    (hg : FactorsThroughProjective g) :
    FactorsThroughProjective (f + g) := by
  letI : Projective hf.middle := hf.projective
  letI : Projective hg.middle := hg.projective
  exact
    { middle := hf.middle ⊞ hg.middle
      projective := inferInstance
      left := biprod.lift hf.left hg.left
      right := biprod.desc hf.right hg.right
      fac := by rw [biprod.lift_desc, hf.fac, hg.fac] }

/-- Precomposition preserves factorization through a projective. -/
def precomp {W X Y : FGModuleCat.{u} R} (a : W ⟶ X)
    {f : X ⟶ Y} (hf : FactorsThroughProjective f) :
    FactorsThroughProjective (a ≫ f) := by
  exact
    { middle := hf.middle
      projective := hf.projective
      left := a ≫ hf.left
      right := hf.right
      fac := by rw [Category.assoc, hf.fac] }

/-- Postcomposition preserves factorization through a projective. -/
def postcomp {X Y Z : FGModuleCat.{u} R}
    {f : X ⟶ Y} (hf : FactorsThroughProjective f) (b : Y ⟶ Z) :
    FactorsThroughProjective (f ≫ b) := by
  exact
    { middle := hf.middle
      projective := hf.projective
      left := hf.left
      right := hf.right ≫ b
      fac := by rw [← Category.assoc, hf.fac] }

end FactorsThroughProjective

namespace FactorsThroughInjective

/-- The zero morphism factors through the zero injective. -/
def zero {X Y : FGModuleCat.{u} R} :
    FactorsThroughInjective (0 : X ⟶ Y) := by
  exact
    { middle := zeroFGModule (R := R)
      injective := isZero_zeroFGModule.injective
      left := 0
      right := 0
      fac := by simp }

/-- Factorization through an injective is closed under negation. -/
def neg {X Y : FGModuleCat.{u} R} {f : X ⟶ Y}
    (hf : FactorsThroughInjective f) :
    FactorsThroughInjective (-f) := by
  exact
    { middle := hf.middle
      injective := hf.injective
      left := -hf.left
      right := hf.right
      fac := by rw [Preadditive.neg_comp, hf.fac] }

/-- Factorization through injectives is closed under addition. -/
def add {X Y : FGModuleCat.{u} R} {f g : X ⟶ Y}
    (hf : FactorsThroughInjective f)
    (hg : FactorsThroughInjective g) :
    FactorsThroughInjective (f + g) := by
  letI : Injective hf.middle := hf.injective
  letI : Injective hg.middle := hg.injective
  exact
    { middle := hf.middle ⊞ hg.middle
      injective := inferInstance
      left := biprod.lift hf.left hg.left
      right := biprod.desc hf.right hg.right
      fac := by rw [biprod.lift_desc, hf.fac, hg.fac] }

/-- Precomposition preserves factorization through an injective. -/
def precomp {W X Y : FGModuleCat.{u} R} (a : W ⟶ X)
    {f : X ⟶ Y} (hf : FactorsThroughInjective f) :
    FactorsThroughInjective (a ≫ f) := by
  exact
    { middle := hf.middle
      injective := hf.injective
      left := a ≫ hf.left
      right := hf.right
      fac := by rw [Category.assoc, hf.fac] }

/-- Postcomposition preserves factorization through an injective. -/
def postcomp {X Y Z : FGModuleCat.{u} R}
    {f : X ⟶ Y} (hf : FactorsThroughInjective f) (b : Y ⟶ Z) :
    FactorsThroughInjective (f ≫ b) := by
  exact
    { middle := hf.middle
      injective := hf.injective
      left := hf.left
      right := hf.right ≫ b
      fac := by rw [← Category.assoc, hf.fac] }

end FactorsThroughInjective

/-! ## The two stable congruences -/

/-- Congruence modulo morphisms factoring through projectives. -/
def projectiveStableRel : HomRel (FGModuleCat.{u} R) :=
  fun _ _ f g ↦ Nonempty (FactorsThroughProjective (f - g))

/-- Congruence modulo morphisms factoring through injectives. -/
def injectiveStableRel : HomRel (FGModuleCat.{u} R) :=
  fun _ _ f g ↦ Nonempty (FactorsThroughInjective (f - g))

instance projectiveStableRel_congruence :
    Congruence (projectiveStableRel (R := R)) where
  equivalence :=
    { refl := fun f ↦ by
        exact ⟨by simpa using
          (FactorsThroughProjective.zero :
            FactorsThroughProjective (0 : _ ⟶ _))⟩
      symm := by
        rintro f g ⟨hfg⟩
        have h := hfg.neg
        exact ⟨by
          convert h using 1
          all_goals abel⟩
      trans := by
        rintro f g h ⟨hfg⟩ ⟨hgh⟩
        have hsum := hfg.add hgh
        exact ⟨by
          convert hsum using 1
          all_goals abel⟩ }
  comp_left := by
    rintro X Y Z a f g ⟨hfg⟩
    exact ⟨by simpa only [Preadditive.comp_sub] using hfg.precomp a⟩
  comp_right := by
    rintro X Y Z f g b ⟨hfg⟩
    exact ⟨by simpa only [Preadditive.sub_comp] using hfg.postcomp b⟩

instance injectiveStableRel_congruence :
    Congruence (injectiveStableRel (R := R)) where
  equivalence :=
    { refl := fun f ↦ by
        exact ⟨by simpa using
          (FactorsThroughInjective.zero :
            FactorsThroughInjective (0 : _ ⟶ _))⟩
      symm := by
        rintro f g ⟨hfg⟩
        have h := hfg.neg
        exact ⟨by
          convert h using 1
          all_goals abel⟩
      trans := by
        rintro f g h ⟨hfg⟩ ⟨hgh⟩
        have hsum := hfg.add hgh
        exact ⟨by
          convert hsum using 1
          all_goals abel⟩ }
  comp_left := by
    rintro X Y Z a f g ⟨hfg⟩
    exact ⟨by simpa only [Preadditive.comp_sub] using hfg.precomp a⟩
  comp_right := by
    rintro X Y Z f g b ⟨hfg⟩
    exact ⟨by simpa only [Preadditive.sub_comp] using hfg.postcomp b⟩

/-- Addition respects the projective-stable congruence. -/
theorem projectiveStableRel_add
    {X Y : FGModuleCat.{u} R}
    (f₁ f₂ g₁ g₂ : X ⟶ Y)
    (hf : projectiveStableRel (R := R) f₁ f₂)
    (hg : projectiveStableRel (R := R) g₁ g₂) :
    projectiveStableRel (R := R) (f₁ + g₁) (f₂ + g₂) := by
  rcases hf with ⟨hf⟩
  rcases hg with ⟨hg⟩
  have hsum := hf.add hg
  exact ⟨by
    convert hsum using 1
    all_goals abel⟩

/-- Addition respects the injective-stable congruence. -/
theorem injectiveStableRel_add
    {X Y : FGModuleCat.{u} R}
    (f₁ f₂ g₁ g₂ : X ⟶ Y)
    (hf : injectiveStableRel (R := R) f₁ f₂)
    (hg : injectiveStableRel (R := R) g₁ g₂) :
    injectiveStableRel (R := R) (f₁ + g₁) (f₂ + g₂) := by
  rcases hf with ⟨hf⟩
  rcases hg with ⟨hg⟩
  have hsum := hf.add hg
  exact ⟨by
    convert hsum using 1
    all_goals abel⟩

/-- The addition compatibility in the exact higher-order shape required
by the quotient preadditive construction. -/
theorem projectiveStableAddCompat :
    ∀ ⦃X Y : FGModuleCat.{u} R⦄
      (f₁ f₂ g₁ g₂ : X ⟶ Y),
      projectiveStableRel (R := R) f₁ f₂ →
      projectiveStableRel (R := R) g₁ g₂ →
      projectiveStableRel (R := R) (f₁ + g₁) (f₂ + g₂) :=
  fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
    projectiveStableRel_add (R := R) f₁ f₂ g₁ g₂ hf hg

/-- The injective-stable addition compatibility in the exact shape
required by the quotient preadditive construction. -/
theorem injectiveStableAddCompat :
    ∀ ⦃X Y : FGModuleCat.{u} R⦄
      (f₁ f₂ g₁ g₂ : X ⟶ Y),
      injectiveStableRel (R := R) f₁ f₂ →
      injectiveStableRel (R := R) g₁ g₂ →
      injectiveStableRel (R := R) (f₁ + g₁) (f₂ + g₂) :=
  fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
    injectiveStableRel_add (R := R) f₁ f₂ g₁ g₂ hf hg

/-! ## Quotient categories and exact equality criteria -/

/-- The stable category of finitely generated modules modulo projectives. -/
abbrev ProjectiveStableCategory :=
  CategoryTheory.Quotient (projectiveStableRel (R := R))

/-- The stable category of finitely generated modules modulo injectives. -/
abbrev InjectiveStableCategory :=
  CategoryTheory.Quotient (injectiveStableRel (R := R))

/-- The canonical functor to the projective-stable category. -/
abbrev projectiveStableFunctor :
    FGModuleCat.{u} R ⥤ ProjectiveStableCategory (R := R) :=
  CategoryTheory.Quotient.functor (projectiveStableRel (R := R))

/-- The canonical functor to the injective-stable category. -/
abbrev injectiveStableFunctor :
    FGModuleCat.{u} R ⥤ InjectiveStableCategory (R := R) :=
  CategoryTheory.Quotient.functor (injectiveStableRel (R := R))

@[implicit_reducible]
def projectiveStable_preadditive :
    Preadditive (ProjectiveStableCategory (R := R)) :=
  CategoryTheory.Quotient.preadditive
    (projectiveStableRel (R := R))
    (projectiveStableAddCompat (R := R))

attribute [instance] projectiveStable_preadditive

instance projectiveStableFunctor_additive :
    (projectiveStableFunctor (R := R)).Additive :=
  CategoryTheory.Quotient.functor_additive
    (projectiveStableRel (R := R))
    (projectiveStableAddCompat (R := R))

@[implicit_reducible]
def injectiveStable_preadditive :
    Preadditive (InjectiveStableCategory (R := R)) :=
  CategoryTheory.Quotient.preadditive
    (injectiveStableRel (R := R))
    (injectiveStableAddCompat (R := R))

attribute [instance] injectiveStable_preadditive

instance injectiveStableFunctor_additive :
    (injectiveStableFunctor (R := R)).Additive :=
  CategoryTheory.Quotient.functor_additive
    (injectiveStableRel (R := R))
    (injectiveStableAddCompat (R := R))

/-- Equality in the projective-stable quotient is exactly factorization
of the difference through a projective. -/
theorem projectiveStable_map_eq_iff
    {X Y : FGModuleCat.{u} R} (f g : X ⟶ Y) :
    (projectiveStableFunctor (R := R)).map f =
        (projectiveStableFunctor (R := R)).map g ↔
      Nonempty (FactorsThroughProjective (f - g)) :=
  CategoryTheory.Quotient.functor_map_eq_iff
    (projectiveStableRel (R := R)) f g

/-- Equality in the injective-stable quotient is exactly factorization
of the difference through an injective. -/
theorem injectiveStable_map_eq_iff
    {X Y : FGModuleCat.{u} R} (f g : X ⟶ Y) :
    (injectiveStableFunctor (R := R)).map f =
        (injectiveStableFunctor (R := R)).map g ↔
      Nonempty (FactorsThroughInjective (f - g)) :=
  CategoryTheory.Quotient.functor_map_eq_iff
    (injectiveStableRel (R := R)) f g

/-- An isomorphism between canonical objects in the projective-stable
quotient lifts to the concrete stable inverse data used by the counting
adapter. -/
def stableIsoOfQuotientIso {X Y : FGModuleCat.{u} R}
    (e : (projectiveStableFunctor (R := R)).obj X ≅
      (projectiveStableFunctor (R := R)).obj Y) :
    StableIso X Y where
  hom := (projectiveStableFunctor (R := R)).preimage e.hom
  inv := (projectiveStableFunctor (R := R)).preimage e.inv
  hom_inv_diff := Classical.choice ((projectiveStable_map_eq_iff _ _).1 (by
    calc
      (projectiveStableFunctor (R := R)).map
          ((projectiveStableFunctor (R := R)).preimage e.hom ≫
            (projectiveStableFunctor (R := R)).preimage e.inv) =
          e.hom ≫ e.inv := by
            rw [Functor.map_comp, Functor.map_preimage,
              Functor.map_preimage]
      _ = 𝟙 _ := e.hom_inv_id
      _ = (projectiveStableFunctor (R := R)).map (𝟙 X) :=
        ((projectiveStableFunctor (R := R)).map_id X).symm))
  inv_hom_diff := Classical.choice ((projectiveStable_map_eq_iff _ _).1 (by
    calc
      (projectiveStableFunctor (R := R)).map
          ((projectiveStableFunctor (R := R)).preimage e.inv ≫
            (projectiveStableFunctor (R := R)).preimage e.hom) =
          e.inv ≫ e.hom := by
            rw [Functor.map_comp, Functor.map_preimage,
              Functor.map_preimage]
      _ = 𝟙 _ := e.inv_hom_id
      _ = (projectiveStableFunctor (R := R)).map (𝟙 Y) :=
        ((projectiveStableFunctor (R := R)).map_id Y).symm))

/-- The injective-stable analogue of `stableIsoOfQuotientIso`. -/
def injectiveStableIsoOfQuotientIso {X Y : FGModuleCat.{u} R}
    (e : (injectiveStableFunctor (R := R)).obj X ≅
      (injectiveStableFunctor (R := R)).obj Y) :
    InjectiveStableIso X Y where
  hom := (injectiveStableFunctor (R := R)).preimage e.hom
  inv := (injectiveStableFunctor (R := R)).preimage e.inv
  hom_inv_diff := Classical.choice ((injectiveStable_map_eq_iff _ _).1 (by
    calc
      (injectiveStableFunctor (R := R)).map
          ((injectiveStableFunctor (R := R)).preimage e.hom ≫
            (injectiveStableFunctor (R := R)).preimage e.inv) =
          e.hom ≫ e.inv := by
            rw [Functor.map_comp, Functor.map_preimage,
              Functor.map_preimage]
      _ = 𝟙 _ := e.hom_inv_id
      _ = (injectiveStableFunctor (R := R)).map (𝟙 X) :=
        ((injectiveStableFunctor (R := R)).map_id X).symm))
  inv_hom_diff := Classical.choice ((injectiveStable_map_eq_iff _ _).1 (by
    calc
      (injectiveStableFunctor (R := R)).map
          ((injectiveStableFunctor (R := R)).preimage e.inv ≫
            (injectiveStableFunctor (R := R)).preimage e.hom) =
          e.inv ≫ e.hom := by
            rw [Functor.map_comp, Functor.map_preimage,
              Functor.map_preimage]
      _ = 𝟙 _ := e.inv_hom_id
      _ = (injectiveStableFunctor (R := R)).map (𝟙 Y) :=
        ((injectiveStableFunctor (R := R)).map_id Y).symm))

end QuotientSubmoduleEquidistribution.RingelStable
