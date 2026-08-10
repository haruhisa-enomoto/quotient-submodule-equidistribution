import OpConjecture.RepresentationTheory.RingelComplexQuotient
import OpConjecture.RepresentationTheory.StableCoreCategories
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.Comma

/-!
# The image functor from strongly exact complexes

For a strongly exact projective complex `P₁ → P₀ → P₋₁`, Ringel's functor
`q` takes the image of the second differential.  This file constructs that
functor into the category of torsionless modules and proves that each of the
four elementary complexes has projective image.  The latter is the precise
input needed for `q` to kill the null ideal `U` after passing to the
projective-stable category.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace OpConjecture.RingelEta

universe u u'

open OpConjecture.RingelStable
open OpConjecture.RingelStable.FaithfulCoreAdapter

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {S : Type u'} [Ring S] [IsNoetherianRing S]

instance mapShortComplex_additive
    {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] : F.mapShortComplex.Additive where
  map_add {X Y} f g := by
    ext
    · exact F.map_add
    · exact F.map_add
    · exact F.map_add

instance shortComplex_gFunctor_additive
    {C : Type*} [Category* C] [Preadditive C] :
    (ShortComplex.gFunctor : ShortComplex C ⥤ Arrow C).Additive where
  map_add {X Y} f g := by rfl

private theorem kernel_lift_add
    {C : Type*} [Category* C] [Abelian C]
    {X Y W : C} (f : X ⟶ Y)
    (a b : W ⟶ X) (ha : a ≫ f = 0) (hb : b ≫ f = 0) :
    kernel.lift f (a + b) (by simp [ha, hb]) =
      kernel.lift f a ha + kernel.lift f b hb := by
  rw [← cancel_mono (kernel.ι f)]
  simp

instance abelian_im_additive
    {C : Type*} [Category* C] [Abelian C] :
    (Abelian.im : Arrow C ⥤ C).Additive where
  map_add {X Y} f g := by
    dsimp [Abelian.im]
    convert kernel_lift_add (cokernel.π Y.hom)
      (kernel.ι (cokernel.π X.hom) ≫ f.right)
      (kernel.ι (cokernel.π X.hom) ≫ g.right)
      (by simp [← f.w_assoc]) (by simp [← g.w_assoc]) using 1
    · simp only [Preadditive.comp_add]
    · rfl

/-- Forget a strongly exact projective complex to an ambient short complex
of finitely generated modules. -/
def stronglyExactUnderlyingFunctor
    (H : (FGProjectives (R := R))ᵒᵖ ≌ FGProjectives (R := S)) :
    StronglyExactComplexCategory H ⥤ ShortComplex (FGModuleCat.{u} R) :=
  (stronglyExactProperty H).ι ⋙ forgetProjectiveComplex (R := R)

/-- Ringel's image functor on strongly exact complexes. -/
def ringelImageFunctor
    (H : (FGProjectives (R := R))ᵒᵖ ≌ FGProjectives (R := S)) :
    StronglyExactComplexCategory H ⥤ FGModuleCat.{u} R :=
  stronglyExactUnderlyingFunctor H ⋙
    ShortComplex.gFunctor ⋙ Abelian.im

/-- The induced map on images is additive in a morphism of complexes. -/
instance ringelImageFunctor_additive
    (H : (FGProjectives (R := R))ᵒᵖ ≌ FGProjectives (R := S)) :
    (ringelImageFunctor H).Additive := by
  dsimp [ringelImageFunctor, stronglyExactUnderlyingFunctor,
    forgetProjectiveComplex]
  infer_instance

/-- The image of the second differential is torsionless because its image
inclusion embeds it into the projective third term. -/
theorem ringelImage_torsionless
    (H : (FGProjectives (R := R))ᵒᵖ ≌ FGProjectives (R := S))
    (X : StronglyExactComplexCategory H) :
    Torsionless ((ringelImageFunctor H).obj X) := by
  let T := (stronglyExactUnderlyingFunctor H).obj X
  exact ⟨T.X₃, Abelian.image.ι T.g,
    X.obj.X₃.property,
    (Abelian.imageStrongEpiMonoFactorisation T.g).m_mono⟩

/-- Ringel's functor `q : E → L`, with codomain the full category of
torsionless finitely generated modules. -/
def ringelImageTorsionlessFunctor
    (H : (FGProjectives (R := R))ᵒᵖ ≌ FGProjectives (R := S)) :
    StronglyExactComplexCategory H ⥤
      TorsionlessModuleCategory (R := R) :=
  (torsionlessModuleProperty (R := R)).lift
    (ringelImageFunctor H) (ringelImage_torsionless H)

instance ringelImageTorsionlessFunctor_additive
    (H : (FGProjectives (R := R))ᵒᵖ ≌ FGProjectives (R := S)) :
    (ringelImageTorsionlessFunctor H).Additive where
  map_add {X Y} f g := by
    apply ObjectProperty.hom_ext
    exact (ringelImageFunctor H).map_add (f := f) (g := g)

private theorem projective_image_of_zero_target
    {X Y : FGModuleCat.{u} R} (f : X ⟶ Y)
    (hY : IsZero Y) : Projective (Abelian.image f) := by
  exact (IsZero.of_mono (Abelian.image.ι f) hY).projective

private theorem projective_image_of_zero_source
    {X Y : FGModuleCat.{u} R} (f : X ⟶ Y)
    (hX : IsZero X) : Projective (Abelian.image f) := by
  exact (IsZero.of_epi (Abelian.factorThruImage f) hX).projective

private theorem projective_image_of_mono
    {X Y : FGModuleCat.{u} R} (f : X ⟶ Y) [Mono f]
    (hX : Projective X) : Projective (Abelian.image f) := by
  exact Projective.of_iso (asIso (Abelian.factorThruImage f)) hX

/-- The image under `q` of every elementary object of `U` is projective. -/
theorem projective_ringelImage_elementary
    (H : (FGProjectives (R := R))ᵒᵖ ≌ FGProjectives (R := S))
    (k : ElementaryKind) (P : FGProjectives (R := R)) :
    Projective
      ((ringelImageFunctor H).obj (elementaryStrongComplex H k P)) := by
  cases k with
  | leftStalk =>
      apply projective_image_of_zero_target
      exact isZero_zeroFGModule
  | leftContractible =>
      apply projective_image_of_zero_target
      exact isZero_zeroFGModule
  | rightContractible =>
      letI : Mono
          (ShortComplex.gFunctor.obj
            ((stronglyExactUnderlyingFunctor H).obj
              (elementaryStrongComplex H .rightContractible P))).hom := by
        change Mono
          ((ObjectProperty.ι (fgProjectiveProperty (R := R))).map (𝟙 P))
        rw [(ObjectProperty.ι
          (fgProjectiveProperty (R := R))).map_id P]
        infer_instance
      apply projective_image_of_mono
      exact P.property
  | rightStalk =>
      apply projective_image_of_zero_source
      exact isZero_zeroFGModule

end OpConjecture.RingelEta
