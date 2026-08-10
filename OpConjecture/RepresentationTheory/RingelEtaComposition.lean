import OpConjecture.RepresentationTheory.RingelComplexQuotientDuality
import OpConjecture.RepresentationTheory.RingelImageEquivalence
import OpConjecture.RepresentationTheory.ArtinStableDescent

/-!
# Composing the two stable anti-equivalences

This file performs the final categorical composition in Ringel's
construction.  Strong Hom gives an anti-equivalence of Ringel complex
quotients, the image functors identify those quotients with the two
torsionless stable categories, and Artin duality changes the target from
torsionless right modules to cotorsionless left modules.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace OpConjecture.RingelEta

universe u u'

open OpConjecture.RingelStable
open OpConjecture.RingelStable.FaithfulCoreAdapter

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {S : Type u'} [Ring S] [IsNoetherianRing S]

/-- Finite projective modules are closed under binary biproducts. -/
instance fgProjectives_hasBinaryBiproducts :
    HasBinaryBiproducts (FGProjectives (R := R)) where
  has_binary_biproduct P Q := by
    letI : Projective P.obj := P.property
    letI : Projective Q.obj := Q.property
    let B : FGProjectives (R := R) :=
      ⟨P.obj ⊞ Q.obj, by
        change Projective (P.obj ⊞ Q.obj)
        infer_instance⟩
    let b : BinaryBicone P Q :=
      { pt := B
        fst := ObjectProperty.homMk
          (biprod.fst : P.obj ⊞ Q.obj ⟶ P.obj)
        snd := ObjectProperty.homMk
          (biprod.snd : P.obj ⊞ Q.obj ⟶ Q.obj)
        inl := ObjectProperty.homMk
          (biprod.inl : P.obj ⟶ P.obj ⊞ Q.obj)
        inr := ObjectProperty.homMk
          (biprod.inr : Q.obj ⟶ P.obj ⊞ Q.obj)
        inl_fst := by
          apply ObjectProperty.hom_ext
          simp
        inl_snd := by
          apply ObjectProperty.hom_ext
          simp
        inr_fst := by
          apply ObjectProperty.hom_ext
          simp
        inr_snd := by
          apply ObjectProperty.hom_ext
          simp }
    exact hasBinaryBiproduct_of_total b <| by
      apply ObjectProperty.hom_ext
      change
        (biprod.fst : P.obj ⊞ Q.obj ⟶ P.obj) ≫ biprod.inl +
            biprod.snd ≫ biprod.inr =
          𝟙 (P.obj ⊞ Q.obj)
      exact biprod.total

/-- The concrete projective Hom anti-equivalence is additive. -/
instance regularHomProjectiveAntiEquivalence_functor_additive
    [IsNoetherianRing Rᵐᵒᵖ] :
    (regularHomProjectiveAntiEquivalence (R := R)).functor.Additive :=
  Functor.additive_of_preserves_binary_products
    (regularHomProjectiveAntiEquivalence (R := R)).functor

/-- Strong Hom, conjugated by the two descended image equivalences, is an
anti-equivalence between the torsionless stable categories. -/
def ringelTorsionlessStableAntiEquivalence
    (H : (FGProjectives (R := R))ᵒᵖ ≌ FGProjectives (R := S))
    [H.functor.Additive] :
    (TorsionlessStableCategory (R := R))ᵒᵖ ≌
      TorsionlessStableCategory (R := S) :=
  (ringelImageQuotientEquivalence H).op.symm |>.trans
    (strongHomRingelComplexQuotientAntiEquivalenceStandard H) |>.trans
      (ringelImageQuotientEquivalence H.rightOp.symm)

section Ringel

variable [IsNoetherianRing Rᵐᵒᵖ]
  (K : Type u) [Field K] [Algebra K R] [FiniteDimensional K R]

/-- Ringel's `Dη`: the strong-Hom anti-equivalence followed by Artin
duality gives a covariant equivalence from torsionless modulo projectives
to cotorsionless modulo injectives. -/
def ringelEtaStableEquivalence :
    TorsionlessStableCategory (R := R) ≌
      CotorsionlessStableCategory (R := R) :=
  (ringelTorsionlessStableAntiEquivalence
      (regularHomProjectiveAntiEquivalence (R := R))).rightOp |>.trans
    (artinTorsionlessCotorsionlessStableEquivalence K R)

end Ringel

end OpConjecture.RingelEta
