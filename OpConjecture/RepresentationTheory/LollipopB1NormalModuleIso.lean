import OpConjecture.RepresentationTheory.LollipopB1TargetNormalForm
import OpConjecture.RepresentationTheory.LollipopB1ModuleExtraction

/-!
# Genuine-module isomorphism for the live-path normal form

The source and target coordinate equivalences conjugate both structure maps.
This file packages those coordinates as a genuine `FiniteB1Rep` and upgrades
their product to a `B1Model`-linear module isomorphism.
-/

noncomputable section

open CategoryTheory

namespace OpConjecture.LollipopConcrete.B1.ModuleLayer.ExhaustivenessReduction

universe u

variable (K : Type u) [Field K]

namespace SplittingFlag

variable {K}

/-- The abstract seven-block normal representation attached to a splitting
flag. -/
def normalRep (D : FiniteB1Rep K) (F : SplittingFlag K D) :
    FiniteB1Rep K where
  V₁ := FGModuleCat.of K (NormalV₁ D F)
  V₂ := FGModuleCat.of K (NormalV₂ D F)
  loop := FGModuleCat.ofHom (normalLoop D F)
  stem := FGModuleCat.ofHom (normalStem D F)
  loop_sq := normalLoop_sq D F

/-! ### Genuine-module normal-form isomorphism -/

def normalCarrierLinearEquiv (D : FiniteB1Rep K)
    (F : SplittingFlag K D) :
    FiniteB1Rep.Carrier K (normalRep D F) ≃ₗ[K]
      FiniteB1Rep.Carrier K D := by
  change (NormalV₁ D F × NormalV₂ D F) ≃ₗ[K] (D.V₁ × D.V₂)
  exact (normalV₁Equiv D F).prodCongr (normalV₂Equiv D F)

theorem normalCarrierLinearEquiv_e1 (D : FiniteB1Rep K)
    (F : SplittingFlag K D)
    (v : FiniteB1Rep.Carrier K (normalRep D F)) :
    normalCarrierLinearEquiv D F (e1 K • v) =
      e1 K • normalCarrierLinearEquiv D F v := by
  rw [FiniteB1Rep.e1_smul, FiniteB1Rep.e1_smul]
  apply FiniteB1Rep.carrier_ext K D
  · rfl
  · change normalV₂Equiv D F 0 = 0
    rw [map_zero]

theorem normalCarrierLinearEquiv_e2 (D : FiniteB1Rep K)
    (F : SplittingFlag K D)
    (v : FiniteB1Rep.Carrier K (normalRep D F)) :
    normalCarrierLinearEquiv D F (e2 K • v) =
      e2 K • normalCarrierLinearEquiv D F v := by
  rw [FiniteB1Rep.e2_smul, FiniteB1Rep.e2_smul]
  apply FiniteB1Rep.carrier_ext K D
  · change normalV₁Equiv D F 0 = 0
    rw [map_zero]
  · rfl

theorem normalCarrierLinearEquiv_x (D : FiniteB1Rep K)
    (F : SplittingFlag K D)
    (v : FiniteB1Rep.Carrier K (normalRep D F)) :
    normalCarrierLinearEquiv D F (x K • v) =
      x K • normalCarrierLinearEquiv D F v := by
  rw [FiniteB1Rep.x_smul, FiniteB1Rep.x_smul]
  apply FiniteB1Rep.carrier_ext K D
  · exact normalV₁Equiv_loop D F v.1
  · change normalV₂Equiv D F 0 = 0
    rw [map_zero]

theorem normalCarrierLinearEquiv_a (D : FiniteB1Rep K)
    (F : SplittingFlag K D)
    (v : FiniteB1Rep.Carrier K (normalRep D F)) :
    normalCarrierLinearEquiv D F (a K • v) =
      a K • normalCarrierLinearEquiv D F v := by
  rw [FiniteB1Rep.a_smul, FiniteB1Rep.a_smul]
  apply FiniteB1Rep.carrier_ext K D
  · change normalV₁Equiv D F 0 = 0
    rw [map_zero]
  · exact normalV₂Equiv_stem D F v.1

theorem normalCarrierLinearEquiv_u (D : FiniteB1Rep K)
    (F : SplittingFlag K D)
    (v : FiniteB1Rep.Carrier K (normalRep D F)) :
    normalCarrierLinearEquiv D F (u K • v) =
      u K • normalCarrierLinearEquiv D F v := by
  rw [FiniteB1Rep.u_smul, FiniteB1Rep.u_smul]
  apply FiniteB1Rep.carrier_ext K D
  · change normalV₁Equiv D F 0 = 0
    rw [map_zero]
  · calc
      normalV₂Equiv D F
          (normalStem D F (normalLoop D F v.1)) =
          stemMap K D (normalV₁Equiv D F (normalLoop D F v.1)) :=
        normalV₂Equiv_stem D F (normalLoop D F v.1)
      _ = stemMap K D (loopMap K D (normalV₁Equiv D F v.1)) := by
        rw [normalV₁Equiv_loop]

theorem normalCarrierLinearEquiv_smul (D : FiniteB1Rep K)
    (F : SplittingFlag K D) (r : B1Model K)
    (v : FiniteB1Rep.Carrier K (normalRep D F)) :
    normalCarrierLinearEquiv D F (r • v) =
      r • normalCarrierLinearEquiv D F v := by
  rw [ModuleExtraction.algebra_coordinate_decomposition K r]
  simp only [add_smul, IsScalarTower.smul_assoc, map_add, map_smul]
  rw [normalCarrierLinearEquiv_e1 D F,
    normalCarrierLinearEquiv_e2 D F,
    normalCarrierLinearEquiv_x D F,
    normalCarrierLinearEquiv_a D F,
    normalCarrierLinearEquiv_u D F]

/-- The normal representation is genuinely `B1Model`-linearly equivalent
to the original representation. -/
def normalCarrierModuleLinearEquiv (D : FiniteB1Rep K)
    (F : SplittingFlag K D) :
    FiniteB1Rep.Carrier K (normalRep D F) ≃ₗ[B1Model K]
      FiniteB1Rep.Carrier K D :=
  LinearEquiv.ofBijective
    { toFun := normalCarrierLinearEquiv D F
      map_add' := (normalCarrierLinearEquiv D F).map_add
      map_smul' := normalCarrierLinearEquiv_smul D F }
    (normalCarrierLinearEquiv D F).bijective

/-- Genuine module isomorphism from the seven-block normal representation
to the original finite representation. -/
def normalModuleIso (D : FiniteB1Rep K)
    (F : SplittingFlag K D) :
    FiniteB1Rep.asFGModule K (normalRep D F) ≅
      FiniteB1Rep.asFGModule K D :=
  (normalCarrierModuleLinearEquiv D F).toFGModuleCatIso

end SplittingFlag

end OpConjecture.LollipopConcrete.B1.ModuleLayer.ExhaustivenessReduction
