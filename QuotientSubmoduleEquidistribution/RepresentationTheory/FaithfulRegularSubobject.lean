import QuotientSubmoduleEquidistribution.RepresentationTheory.FaithfulRegularEmbedding
import QuotientSubmoduleEquidistribution.RepresentationTheory.ConormalModules
import QuotientSubmoduleEquidistribution.RepresentationTheory.SimpleLevels

/-!
# The regular module as a subobject of a faithful finite power

This is the categorical form of the finite-basis faithful embedding, with
the target presented as an actual finite biproduct in `FGModuleCat`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.FaithfulRegularEmbedding

universe uK u

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

variable (K : Type uK) (R : Type u) (M : Type u)
  [Field K] [Ring R] [IsNoetherianRing R]
  [AddCommGroup M] [Module K M] [Module R M]
  [SMulCommClass R K M]
  [Module.Free K M] [Module.Finite K M] [Module.Finite R M]

/-- The regular object in the finitely generated module category. -/
abbrev regularObject : FGModuleCat.{u} R :=
  FGModuleCat.of R R

/-- A module as an object of the finitely generated category. -/
abbrev moduleObject : FGModuleCat.{u} R :=
  FGModuleCat.of R M

/-- The finite-basis embedding, with its target presented as a categorical
biproduct of copies of the faithful module. -/
def regularToBiproduct :
    regularObject R ⟶
      ⨁ fun _ : Fin (Module.finrank K M) ↦ moduleObject R M :=
  FGModuleCat.ofHom (regularToBasisProduct K R M) ≫
    (IndecomposableSkeleton.biproductIsoPiFG
      (fun _ : Fin (Module.finrank K M) ↦ moduleObject R M)).inv

/-- The categorical finite-basis map is monic when the module action is
faithful. -/
theorem regularToBiproduct_mono
    [FaithfulSMul R M] :
    Mono (regularToBiproduct K R M) := by
  let f :
      regularObject R ⟶
        FGModuleCat.of R (Fin (Module.finrank K M) → M) :=
    FGModuleCat.ofHom (regularToBasisProduct K R M)
  have hf : Function.Injective f :=
    regularToBasisProduct_injective K R M
  letI : Mono f :=
    ConcreteCategory.mono_of_injective f hf
  change Mono
    (f ≫
      (IndecomposableSkeleton.biproductIsoPiFG
        (fun _ : Fin (Module.finrank K M) ↦ moduleObject R M)).inv)
  infer_instance

/-- Annihilator-zero form of the categorical regular embedding. -/
theorem regularToBiproduct_mono_of_annihilator_eq_bot
    (hM : Module.annihilator R M = ⊥) :
    Mono (regularToBiproduct K R M) := by
  letI : FaithfulSMul R M :=
    Module.annihilator_eq_bot.mp hM
  exact regularToBiproduct_mono K R M

include K in
/-- The regular module belongs to `Sub M` whenever `M` is faithful. -/
theorem regular_inSubOfModule_of_annihilator_eq_bot
    (hM : Module.annihilator R M = ⊥) :
    IndecomposableSkeleton.InSubOfModule
      (moduleObject R M) (regularObject R) := by
  refine
    ⟨FintypeCat.of (Fin (Module.finrank K M)),
      regularToBiproduct K R M, ?_⟩
  exact regularToBiproduct_mono_of_annihilator_eq_bot K R M hM

end QuotientSubmoduleEquidistribution.FaithfulRegularEmbedding
