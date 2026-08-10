import OpConjecture.RepresentationTheory.ConnectedSmallCoreExceptionalArrowIdeals

/-!
# Operational split-basic Gabriel-arrow realization

This file packages the exact concrete algebra data expected from a future
split-basic Gabriel-presentation theorem.  Vertex projectives are represented
by nonzero idempotents and arrows by elements of the Jacobson radical whose
cyclic right ideals lie in the appropriate source projectives and have the
appropriate simple tops.

The main constructor turns this concrete data into
`ExceptionalArrowIdealData`.  In particular, properness of every arrow-ideal
inclusion is derived from radical membership; it is not an additional module
classification hypothesis.  This file does not assert existence of such a
realization for every split-basic algebra.  The structure also does not itself
encode splitness, basicness, completeness or orthogonality of the vertex
idempotents, or a cotangent-basis/Ext-basis theorem; those belong to the
upstream presentation theorem which produces this operational data.
-/

noncomputable section

open Set CategoryTheory MulOpposite

namespace OpConjecture

universe u v w

namespace IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore

variable {A : Type u} [Ring A] [IsNoetherianRing Aᵐᵒᵖ]
  {κ : Type v} [Finite κ]
  (τ : IndecomposableSkeleton.{u, v, u} Aᵐᵒᵖ κ)

/-- The operational data extracted from a split-basic Gabriel-arrow
realization.  For a genuine Gabriel realization, `Arrow` is instantiated by
the Ext-Gabriel arrow type and `source` and `target` by its endpoints. -/
structure SplitBasicGabrielArrowRealization
    {Arrow : Type w}
    (source target : Arrow → τ.SimpleIndex) where
  vertex : τ.SimpleIndex → A
  vertex_idempotent : ∀ i, IsIdempotentElem (vertex i)
  vertex_ne_zero : ∀ i, vertex i ≠ 0
  vertex_topIso : ∀ i,
    Nonempty
      (FGModuleCat.of Aᵐᵒᵖ
          (Tsukamoto.cyclicRightIdealFG (vertex i) ⧸
            Module.jacobson Aᵐᵒᵖ
              (Tsukamoto.cyclicRightIdealFG (vertex i))) ≅
        τ.obj i.1)
  representative : Arrow → A
  representative_mem_jacobson :
    ∀ a, representative a ∈ Ring.jacobson A
  arrowIdeal_le_source : ∀ a,
    Tsukamoto.principalRightIdeal (representative a) ≤
      Tsukamoto.principalRightIdeal (vertex (source a))
  arrow_topIso : ∀ a,
    Nonempty
      (FGModuleCat.of Aᵐᵒᵖ
          (Tsukamoto.cyclicRightIdealFG (representative a) ⧸
            Module.jacobson Aᵐᵒᵖ
              (Tsukamoto.cyclicRightIdealFG (representative a))) ≅
        τ.obj (target a).1)

namespace SplitBasicGabrielArrowRealization

variable {Arrow : Type w}
  {source target : Arrow → τ.SimpleIndex}
  (G : SplitBasicGabrielArrowRealization τ source target)

/-- The skeleton label of the indecomposable cyclic ideal represented by an
arrow. -/
noncomputable def arrowLabel (a : Arrow) : κ :=
  (τ.complete
    (Tsukamoto.cyclicRightIdealFG (G.representative a))
    (CyclicRightIdeal.indecomposable_of_top_iso τ
      (G.representative a) (target a) (G.arrow_topIso a).some)).choose

/-- The chosen cyclic arrow ideal is isomorphic to its selected skeleton
representative. -/
noncomputable def arrowIso (a : Arrow) :
    Tsukamoto.cyclicRightIdealFG (G.representative a) ≅
      τ.obj (arrowLabel τ G a) :=
  ((τ.complete
    (Tsukamoto.cyclicRightIdealFG (G.representative a))
    (CyclicRightIdeal.indecomposable_of_top_iso τ
      (G.representative a) (target a) (G.arrow_topIso a).some)).choose_spec).some

omit [Finite κ] in
/-- Each vertex ideal is projective because its generator is idempotent. -/
theorem vertex_projective (i : τ.SimpleIndex) :
    CategoryTheory.Projective
      (Tsukamoto.cyclicRightIdealFG (G.vertex i)) := by
  apply OpConjecture.RingelStable.fgProjective_of_moduleProjective
  change Module.Projective Aᵐᵒᵖ
    (Tsukamoto.principalRightIdeal (G.vertex i))
  exact Tsukamoto.principalRightIdeal_projective (G.vertex_idempotent i)

omit [Finite κ] in
/-- The simple top of a vertex ideal makes it indecomposable. -/
theorem vertex_indec (i : τ.SimpleIndex) :
    OpConjecture.Foundation.IsIndecomposableModule Aᵐᵒᵖ
      (Tsukamoto.cyclicRightIdealFG (G.vertex i)) :=
  CyclicRightIdeal.indecomposable_of_top_iso τ
    (G.vertex i) i (G.vertex_topIso i).some

/-- A vertex ideal is the chosen indecomposable projective corresponding to
its simple top. -/
noncomputable def vertexIso (i : τ.SimpleIndex) :
    Tsukamoto.cyclicRightIdealFG (G.vertex i) ≅
      τ.obj (ProjectiveSimpleRank.projectiveLabelOfSimple τ i) :=
  (ProjectiveSimpleRank.projective_iso_of_indec_of_top_iso τ
    (Tsukamoto.cyclicRightIdealFG (G.vertex i))
    (vertex_projective τ G i) (vertex_indec τ G i) i
    (G.vertex_topIso i).some).some

/-- Transport the literal inclusion of cyclic ideals to the chosen skeleton
representatives. -/
noncomputable def inclusion (a : Arrow) :
    τ.obj (arrowLabel τ G a) ⟶
      τ.obj (ProjectiveSimpleRank.projectiveLabelOfSimple τ (source a)) :=
  (arrowIso τ G a).inv ≫
    Tsukamoto.cyclicRightIdealInclusionOfLE (G.arrowIdeal_le_source a) ≫
      (vertexIso τ G (source a)).hom

omit [Finite κ] in
/-- The transported arrow-ideal inclusion is monic. -/
theorem inclusion_mono (a : Arrow) : Mono (inclusion τ G a) := by
  letI : Mono
      (Tsukamoto.cyclicRightIdealInclusionOfLE
        (G.arrowIdeal_le_source a)) :=
    Tsukamoto.cyclicRightIdealInclusionOfLE_mono
      (G.arrowIdeal_le_source a)
  dsimp only [inclusion]
  infer_instance

omit [Finite κ] in
/-- Radical membership makes every transported arrow-ideal inclusion
proper, including inclusions belonging to nonloop arrows. -/
theorem inclusion_not_epi (a : Arrow) : ¬ Epi (inclusion τ G a) := by
  intro hEpi
  letI : Epi (inclusion τ G a) := hEpi
  have hRawEpi : Epi
      (Tsukamoto.cyclicRightIdealInclusionOfLE
        (G.arrowIdeal_le_source a)) := by
    let f := Tsukamoto.cyclicRightIdealInclusionOfLE
      (G.arrowIdeal_le_source a)
    have hEq :
        (arrowIso τ G a).hom ≫ inclusion τ G a ≫
            (vertexIso τ G (source a)).inv = f := by
      simp [inclusion, f]
    change Epi f
    rw [← hEq]
    infer_instance
  exact
    (Tsukamoto.cyclicRightIdealInclusionOfLE_not_epi_of_mem_jacobson
      (G.representative_mem_jacobson a)
      (G.vertex_idempotent (source a))
      (G.vertex_ne_zero (source a))
      (G.arrowIdeal_le_source a)) hRawEpi

/-- Isomorphic finite modules have linearly equivalent radical quotients. -/
noncomputable def moduleTopLinearEquivOfIso
    {M N : FGModuleCat.{u} Aᵐᵒᵖ} (e : M ≅ N) :
    (M ⧸ Module.jacobson Aᵐᵒᵖ M) ≃ₗ[Aᵐᵒᵖ]
      (N ⧸ Module.jacobson Aᵐᵒᵖ N) :=
  Submodule.Quotient.equiv
    (Module.jacobson Aᵐᵒᵖ M) (Module.jacobson Aᵐᵒᵖ N)
    (FGModuleCat.isoToLinearEquiv e)
    (Module.map_jacobson_of_bijective
      (FGModuleCat.isoToLinearEquiv e).bijective)

/-- Transport the concrete target-top isomorphism to the selected skeleton
representative of the arrow ideal. -/
noncomputable def transportedTopIso (a : Arrow) :
    FGModuleCat.of Aᵐᵒᵖ (τ.moduleTop (arrowLabel τ G a)) ≅
      τ.obj (target a).1 :=
  (moduleTopLinearEquivOfIso (arrowIso τ G a)).symm.toFGModuleCatIso ≪≫
    (G.arrow_topIso a).some

/-- Concrete split-basic Gabriel-arrow data supplies the complete
module-theoretic interface consumed by the exceptional-core reduction. -/
noncomputable def toExceptionalArrowIdealData :
    ExceptionalArrowIdealData τ source target where
  idealLabel := arrowLabel τ G
  topIso a := ⟨transportedTopIso τ G a⟩
  inclusion := inclusion τ G
  inclusion_mono := inclusion_mono τ G
  inclusion_not_epi := inclusion_not_epi τ G

end SplitBasicGabrielArrowRealization

end IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore

end OpConjecture
