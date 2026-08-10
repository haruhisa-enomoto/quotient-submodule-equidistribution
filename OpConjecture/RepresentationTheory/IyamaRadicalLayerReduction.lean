import OpConjecture.CategoryTheory.RadicalLayerFiltration
import OpConjecture.RepresentationTheory.FactorHomCriterion

/-!
# Reducing the abstract Iyama input to the radical-layer formula

Once a category has nilpotent categorical radical, the Hom-to-layer
equivalence is formal.  If the ladder is coefficientwise nonnegative, the
same nilpotence exponent and the radical-layer formula also force eventual
ladder vanishing.  Thus the full abstract input used by the factor-ladder
criterion can be constructed from the single projective-cover/layer formula.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace OpConjecture.FactorLadder.IyamaRadicalLayerInput

universe w v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Build the complete Iyama radical-layer interface from a nilpotent
categorical radical and the exact layer-multiplicity formula. -/
def ofNilpotentRadical
    {D : Type w} (A : Data D)
    (obj : D → C) (factorHomNonzero : D → D → Prop)
    (R : CategoricalRadical.NilpotentRadicalData C)
    (hfactor : ∀ p x,
      factorHomNonzero p x ↔
        ∃ f : obj p ⟶ obj x, f ≠ 0)
    (hnonneg : ∀ x n p, 0 ≤ A.ladder x n p)
    (hlayer : ∀ n p x,
      R.LayerNonzero n (obj p) (obj x) ↔
        0 < A.ladder x n p) :
    IyamaRadicalLayerInput A factorHomNonzero where
  layerNonzero n p x := R.LayerNonzero n (obj p) (obj x)
  factorHom_iff_exists_layer := by
    intro p x
    exact (hfactor p x).trans
      (R.exists_ne_zero_iff_exists_layerNonzero (obj p) (obj x))
  layer_nonzero_iff_ladder_occurs := hlayer
  eventually_ladder_zero := by
    obtain ⟨N, hN⟩ := R.nilpotent
    refine fun x ↦ ⟨N, fun n hn ↦ ?_⟩
    funext p
    have hnotlayer :
        ¬ R.LayerNonzero n (obj p) (obj x) :=
      R.ideal.not_layerNonzero_of_pow_eq_bot hN hn _ _
    have hnotpos : ¬ 0 < A.ladder x n p :=
      fun hpos ↦ hnotlayer ((hlayer n p x).2 hpos)
    exact le_antisymm (not_lt.mp hnotpos) (hnonneg x n p)

end OpConjecture.FactorLadder.IyamaRadicalLayerInput
