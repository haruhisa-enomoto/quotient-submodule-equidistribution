import QuotientSubmoduleEquidistribution.RepresentationTheory.LollipopB0Modules
import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# A linear-algebra reduction for exhaustiveness of the five lollipop modules

This file constructs, for every finite `B₀` representation, all five
multiplicity spaces in the expected normal form and packages the coordinate
changes into a genuine module isomorphism with a finite biproduct of the five
named modules.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

namespace QuotientSubmoduleEquidistribution.LollipopConcrete.ModuleLayer.ExhaustivenessReduction

universe u

variable (K : Type u) [Field K]

abbrev loopMap (D : FiniteB0Rep K) : D.V₁ →ₗ[K] D.V₁ :=
  D.loop.hom.hom

abbrev stemMap (D : FiniteB0Rep K) : D.V₁ →ₗ[K] D.V₂ :=
  D.stem.hom.hom

/-- Vectors at vertex one killed by both the loop and the stem. -/
def deadSpace (D : FiniteB0Rep K) : Submodule K D.V₁ :=
  LinearMap.ker (loopMap K D) ⊓ LinearMap.ker (stemMap K D)

theorem loop_mem_deadSpace (D : FiniteB0Rep K) (v : D.V₁) :
    loopMap K D v ∈ deadSpace K D := by
  constructor
  · exact D.loop_sq v
  · exact D.stem_loop v

/-- The loop, with its codomain restricted to the subspace on which both
arrows vanish. -/
def loopToDeadSpace (D : FiniteB0Rep K) :
    D.V₁ →ₗ[K] deadSpace K D :=
  LinearMap.codRestrict (deadSpace K D) (loopMap K D)
    (loop_mem_deadSpace K D)

/-- The lower coordinates of all Jordan blocks, regarded inside the dead
subspace. -/
def loopRangeInDead (D : FiniteB0Rep K) :
    Submodule K (deadSpace K D) :=
  LinearMap.range (loopToDeadSpace K D)

/-- Restriction of the stem to the kernel of the loop. -/
def stemOnLoopKernel (D : FiniteB0Rep K) :
    LinearMap.ker (loopMap K D) →ₗ[K] D.V₂ :=
  (stemMap K D).comp (LinearMap.ker (loopMap K D)).subtype

/-- The part of vertex two already hit from a loop-killed vector.  These are
the lower coordinates of the `A` blocks. -/
def stationaryStemRange (D : FiniteB0Rep K) : Submodule K D.V₂ :=
  LinearMap.range (stemOnLoopKernel K D)

/-- Vertex two modulo the part accounted for by the `A` blocks. -/
abbrev residualVertexTwo (D : FiniteB0Rep K) :=
  D.V₂ ⧸ stationaryStemRange K D

/-- For a choice of loop-top complement, the stem seen modulo the `A`-block
image.  Its kernel gives `X` tops and a complement gives `P` tops. -/
def residualStem (D : FiniteB0Rep K)
    (B : Submodule K D.V₁) :
    B →ₗ[K] residualVertexTwo K D :=
  (stationaryStemRange K D).mkQ.comp
    ((stemMap K D).comp B.subtype)

/-- A simultaneous splitting flag exposing the five expected multiplicity
spaces.  The fields are deliberately subspaces rather than chosen bases, so
the construction is valid over every field.

* `loopTop` splits off the tops of all `X` and `P` blocks;
* `stationaryDead` is the `S₁` multiplicity space;
* `activeStem` is the `A` multiplicity space;
* `projectiveTop` is the `P` multiplicity space;
* `residualTail` is the `S₂` multiplicity space.

The kernel of `residualStem` inside `loopTop` is the `X` multiplicity space.
-/
structure SplittingFlag (D : FiniteB0Rep K) where
  loopTop : Submodule K D.V₁
  loopTop_compl :
    IsCompl loopTop (LinearMap.ker (loopMap K D))
  stationaryDead : Submodule K (deadSpace K D)
  stationaryDead_compl :
    IsCompl (loopRangeInDead K D) stationaryDead
  activeStem : Submodule K (LinearMap.ker (loopMap K D))
  activeStem_compl :
    IsCompl activeStem (LinearMap.ker (stemOnLoopKernel K D))
  vertexTwoResidual : Submodule K D.V₂
  vertexTwoResidual_compl :
    IsCompl (stationaryStemRange K D) vertexTwoResidual
  projectiveTop : Submodule K loopTop
  projectiveTop_compl :
    IsCompl projectiveTop
      (LinearMap.ker (residualStem K D loopTop))
  residualTail : Submodule K (residualVertexTwo K D)
  residualTail_compl :
    IsCompl (LinearMap.range (residualStem K D loopTop)) residualTail

/-- Every finite `B₀` representation admits the complete five-space
splitting flag. -/
theorem exists_splittingFlag (D : FiniteB0Rep K) :
    Nonempty (SplittingFlag K D) := by
  obtain ⟨B, hB⟩ :=
    (LinearMap.ker (loopMap K D)).exists_isCompl
  obtain ⟨S, hS⟩ :=
    (loopRangeInDead K D).exists_isCompl
  obtain ⟨A, hA⟩ :=
    (LinearMap.ker (stemOnLoopKernel K D)).exists_isCompl
  obtain ⟨C, hC⟩ :=
    (stationaryStemRange K D).exists_isCompl
  obtain ⟨P, hP⟩ :=
    (LinearMap.ker (residualStem K D B)).exists_isCompl
  obtain ⟨Q, hQ⟩ :=
    (LinearMap.range (residualStem K D B)).exists_isCompl
  exact ⟨{
    loopTop := B
    loopTop_compl := hB.symm
    stationaryDead := S
    stationaryDead_compl := hS
    activeStem := A
    activeStem_compl := hA.symm
    vertexTwoResidual := C
    vertexTwoResidual_compl := hC
    projectiveTop := P
    projectiveTop_compl := hP.symm
    residualTail := Q
    residualTail_compl := hQ }⟩

namespace SplittingFlag

variable {K}

/-- The doubly-killed subspace is the kernel of the stem restricted to the
loop kernel, with only subtype nesting changed. -/
def deadSpaceEquivStemOnLoopKernelKer (D : FiniteB0Rep K) :
    deadSpace K D ≃ₗ[K] LinearMap.ker (stemOnLoopKernel K D) where
  toFun d := ⟨⟨d.1, d.2.1⟩, d.2.2⟩
  invFun z := ⟨z.1.1, z.1.2, z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem ker_loopToDeadSpace (D : FiniteB0Rep K) :
    LinearMap.ker (loopToDeadSpace K D) =
      LinearMap.ker (loopMap K D) := by
  ext v
  change loopToDeadSpace K D v = 0 ↔ loopMap K D v = 0
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    exact h

/-- The loop identifies every chosen loop top with its lower Jordan
coordinate. -/
def loopTopEquivRange (D : FiniteB0Rep K) (F : SplittingFlag K D) :
    F.loopTop ≃ₗ[K] LinearMap.range (loopMap K D) :=
  LinearMap.kerComplementEquivRange (loopMap K D) F.loopTop_compl

/-- The same loop identification with the lower coordinate regarded inside
the doubly-killed subspace. -/
def loopTopEquivLoopRangeInDead (D : FiniteB0Rep K)
    (F : SplittingFlag K D) :
    F.loopTop ≃ₗ[K] loopRangeInDead K D :=
  LinearMap.kerComplementEquivRange (loopToDeadSpace K D) (by
    rw [ker_loopToDeadSpace D]
    exact F.loopTop_compl)

/-- The stem identifies the chosen active-stem space with the entire part of
vertex two generated from the loop kernel. -/
def activeStemEquivRange (D : FiniteB0Rep K) (F : SplittingFlag K D) :
    F.activeStem ≃ₗ[K] stationaryStemRange K D :=
  LinearMap.kerComplementEquivRange (stemOnLoopKernel K D)
    F.activeStem_compl

/-- The quotient by the active-stem image is represented by the chosen
literal complement inside vertex two. -/
def residualVertexTwoEquiv (D : FiniteB0Rep K)
    (F : SplittingFlag K D) :
    residualVertexTwo K D ≃ₗ[K] F.vertexTwoResidual :=
  (stationaryStemRange K D).quotientEquivOfIsCompl
    F.vertexTwoResidual F.vertexTwoResidual_compl

/-- Modulo the active-stem image, the residual stem identifies the chosen
projective tops with its range. -/
def projectiveTopEquivRange (D : FiniteB0Rep K)
    (F : SplittingFlag K D) :
    F.projectiveTop ≃ₗ[K]
      LinearMap.range (residualStem K D F.loopTop) :=
  LinearMap.kerComplementEquivRange (residualStem K D F.loopTop)
    F.projectiveTop_compl

/-- The component of a loop top whose stem lies in the already-accounted-for
active-stem image. -/
def activeCorrection (D : FiniteB0Rep K)
    (F : SplittingFlag K D) : F.loopTop →ₗ[K] D.V₁ := by
  let stemToActiveRange : F.loopTop →ₗ[K] stationaryStemRange K D :=
    ((stationaryStemRange K D).projectionOnto
      F.vertexTwoResidual F.vertexTwoResidual_compl).comp
      ((stemMap K D).comp F.loopTop.subtype)
  exact (LinearMap.ker (loopMap K D)).subtype.comp
    (F.activeStem.subtype.comp
      ((activeStemEquivRange D F).symm.toLinearMap.comp stemToActiveRange))

/-- Subtracting the active correction changes neither the loop image nor the
residual stem class, but moves the literal stem image into the chosen vertex
two complement. -/
def gaugedLoopTopMap (D : FiniteB0Rep K)
    (F : SplittingFlag K D) : F.loopTop →ₗ[K] D.V₁ :=
  F.loopTop.subtype - activeCorrection D F

theorem loop_activeCorrection (D : FiniteB0Rep K)
    (F : SplittingFlag K D) (b : F.loopTop) :
    loopMap K D (activeCorrection D F b) = 0 := by
  simp only [activeCorrection, LinearMap.comp_apply]
  change loopMap K D
    (((activeStemEquivRange D F).symm
      ((stationaryStemRange K D).projectionOnto
        F.vertexTwoResidual F.vertexTwoResidual_compl
        (stemMap K D b.1))).1.1) = 0
  exact ((activeStemEquivRange D F).symm
    ((stationaryStemRange K D).projectionOnto
      F.vertexTwoResidual F.vertexTwoResidual_compl
      (stemMap K D b.1))).1.2

theorem stem_activeCorrection (D : FiniteB0Rep K)
    (F : SplittingFlag K D) (b : F.loopTop) :
    stemMap K D (activeCorrection D F b) =
      ((stationaryStemRange K D).projectionOnto
        F.vertexTwoResidual F.vertexTwoResidual_compl
        (stemMap K D b.1) : D.V₂) := by
  let y : stationaryStemRange K D :=
    (stationaryStemRange K D).projectionOnto
      F.vertexTwoResidual F.vertexTwoResidual_compl
      (stemMap K D b.1)
  have h := (activeStemEquivRange D F).apply_symm_apply y
  have hc := congrArg Subtype.val h
  change stemMap K D
    (((activeStemEquivRange D F).symm y).1.1) = y.1 at hc
  dsimp [y] at hc
  simp only [activeCorrection, LinearMap.comp_apply]
  exact hc

theorem loop_gaugedLoopTopMap (D : FiniteB0Rep K)
    (F : SplittingFlag K D) (b : F.loopTop) :
    loopMap K D (gaugedLoopTopMap D F b) = loopMap K D b.1 := by
  rw [gaugedLoopTopMap, LinearMap.sub_apply, map_sub,
    loop_activeCorrection D F, sub_zero]
  rfl

theorem stem_gaugedLoopTopMap_mem (D : FiniteB0Rep K)
    (F : SplittingFlag K D) (b : F.loopTop) :
    stemMap K D (gaugedLoopTopMap D F b) ∈ F.vertexTwoResidual := by
  rw [gaugedLoopTopMap, LinearMap.sub_apply, map_sub,
    stem_activeCorrection D F]
  change stemMap K D b.1 -
      (stationaryStemRange K D).projection
        F.vertexTwoResidual F.vertexTwoResidual_compl
        (stemMap K D b.1) ∈ F.vertexTwoResidual
  exact Submodule.sub_projection_mem F.vertexTwoResidual_compl
    (stemMap K D b.1)

theorem gaugedLoopTopMap_injective (D : FiniteB0Rep K)
    (F : SplittingFlag K D) :
    Function.Injective (gaugedLoopTopMap D F) := by
  intro b c hbc
  apply (loopTopEquivRange D F).injective
  apply Subtype.ext
  change loopMap K D b.1 = loopMap K D c.1
  rw [← loop_gaugedLoopTopMap D F b,
    ← loop_gaugedLoopTopMap D F c, hbc]

/-- The gauged tops as an actual subspace of vertex one. -/
def gaugedLoopTop (D : FiniteB0Rep K)
    (F : SplittingFlag K D) : Submodule K D.V₁ :=
  LinearMap.range (gaugedLoopTopMap D F)

/-- Gauging preserves the loop-top multiplicity space. -/
def loopTopEquivGaugedLoopTop (D : FiniteB0Rep K)
    (F : SplittingFlag K D) : F.loopTop ≃ₗ[K] gaugedLoopTop D F :=
  LinearEquiv.ofInjective (gaugedLoopTopMap D F)
    (gaugedLoopTopMap_injective D F)

/-- The gauge change replaces the chosen loop-top complement by another
literal complement of the loop kernel. -/
theorem gaugedLoopTop_isCompl_loopKernel (D : FiniteB0Rep K)
    (F : SplittingFlag K D) :
    IsCompl (gaugedLoopTop D F) (LinearMap.ker (loopMap K D)) := by
  apply (Submodule.isCompl_iff_disjoint _ _ ?_).2
  · rw [Submodule.disjoint_def]
    intro z hzTop hzKer
    rcases hzTop with ⟨b, rfl⟩
    have hbLoop : loopMap K D b.1 = 0 := by
      rw [← loop_gaugedLoopTopMap D F b]
      exact hzKer
    have hbZero : b = 0 := by
      apply Subtype.ext
      exact Submodule.disjoint_def.mp F.loopTop_compl.disjoint
        b.1 b.2 hbLoop
    rw [hbZero, map_zero]
  · rw [← (loopTopEquivGaugedLoopTop D F).finrank_eq]
    exact (Submodule.finrank_add_eq_of_isCompl F.loopTop_compl).ge

/-- The literal stem on gauged tops, with codomain restricted to the chosen
vertex-two complement. -/
def gaugedStem (D : FiniteB0Rep K)
    (F : SplittingFlag K D) : F.loopTop →ₗ[K] F.vertexTwoResidual :=
  LinearMap.codRestrict F.vertexTwoResidual
    ((stemMap K D).comp (gaugedLoopTopMap D F))
    (stem_gaugedLoopTopMap_mem D F)

/-- The quotient-valued residual stem is exactly the literal stem after the
gauge change and the quotient/complement identification. -/
theorem residualVertexTwoEquiv_residualStem (D : FiniteB0Rep K)
    (F : SplittingFlag K D) (b : F.loopTop) :
    residualVertexTwoEquiv D F (residualStem K D F.loopTop b) =
      gaugedStem D F b := by
  apply Subtype.ext
  simp only [residualVertexTwoEquiv, residualStem, LinearMap.comp_apply,
    Submodule.mkQ_apply]
  rw [Submodule.quotientEquivOfIsCompl_apply_mk]
  change F.vertexTwoResidual.projection
      (stationaryStemRange K D) F.vertexTwoResidual_compl.symm
      (stemMap K D b.1) =
    stemMap K D (gaugedLoopTopMap D F b)
  rw [Submodule.projection_eq_self_sub_projection
      F.vertexTwoResidual_compl,
    gaugedLoopTopMap, LinearMap.sub_apply, map_sub,
    stem_activeCorrection D F]
  rw [Submodule.coe_projectionOnto_apply]
  rfl

theorem ker_gaugedStem (D : FiniteB0Rep K)
    (F : SplittingFlag K D) :
    LinearMap.ker (gaugedStem D F) =
      LinearMap.ker (residualStem K D F.loopTop) := by
  ext b
  change gaugedStem D F b = 0 ↔ residualStem K D F.loopTop b = 0
  rw [← (residualVertexTwoEquiv D F).map_eq_zero_iff,
    residualVertexTwoEquiv_residualStem D F]

/-- The old quotient-level `X/P` split is therefore an actual split for the
gauged literal stem. -/
theorem projectiveTop_compl_ker_gaugedStem (D : FiniteB0Rep K)
    (F : SplittingFlag K D) :
    IsCompl F.projectiveTop (LinearMap.ker (gaugedStem D F)) := by
  rw [ker_gaugedStem D F]
  exact F.projectiveTop_compl

/-! ### Certified multiplicity equations -/

/-- Vertex one has two coordinates for every `X` and `P` block, one for
every `S₁` block, and one for every `A` block. -/
theorem finrank_vertexOne_five_spaces (D : FiniteB0Rep K)
    (F : SplittingFlag K D) :
    Module.finrank K D.V₁ =
      2 * Module.finrank K (LinearMap.ker
        (residualStem K D F.loopTop)) +
      2 * Module.finrank K F.projectiveTop +
      Module.finrank K F.stationaryDead +
      Module.finrank K F.activeStem := by
  have hPX :=
    Submodule.finrank_add_eq_of_isCompl F.projectiveTop_compl
  have hRS :=
    Submodule.finrank_add_eq_of_isCompl F.stationaryDead_compl
  have hAK :=
    Submodule.finrank_add_eq_of_isCompl F.activeStem_compl
  have hBK :=
    Submodule.finrank_add_eq_of_isCompl F.loopTop_compl
  have hBR := (loopTopEquivLoopRangeInDead D F).finrank_eq
  have hDK := (deadSpaceEquivStemOnLoopKernelKer D).finrank_eq
  omega

/-- Vertex two has one coordinate for every `P`, `A`, and `S₂` block. -/
theorem finrank_vertexTwo_five_spaces (D : FiniteB0Rep K)
    (F : SplittingFlag K D) :
    Module.finrank K D.V₂ =
      Module.finrank K F.projectiveTop +
      Module.finrank K F.activeStem +
      Module.finrank K F.residualTail := by
  have hUC :=
    Submodule.finrank_add_eq_of_isCompl F.vertexTwoResidual_compl
  have hRQ :=
    Submodule.finrank_add_eq_of_isCompl F.residualTail_compl
  have hAU := (activeStemEquivRange D F).finrank_eq
  have hPC := (projectiveTopEquivRange D F).finrank_eq
  have hQC := (residualVertexTwoEquiv D F).finrank_eq
  omega

/-- The total dimension is exactly the weighted sum of the dimensions of the
five multiplicity spaces, with weights `1,1,2,2,3` for
`S₁,S₂,X,A,P`. -/
theorem finrank_carrier_five_spaces (D : FiniteB0Rep K)
    (F : SplittingFlag K D) :
    Module.finrank K (FiniteB0Rep.Carrier K D) =
      Module.finrank K F.stationaryDead +
      Module.finrank K F.residualTail +
      2 * Module.finrank K (LinearMap.ker
        (residualStem K D F.loopTop)) +
      2 * Module.finrank K F.activeStem +
      3 * Module.finrank K F.projectiveTop := by
  change Module.finrank K (D.V₁ × D.V₂) = _
  rw [Module.finrank_prod, finrank_vertexOne_five_spaces D F,
    finrank_vertexTwo_five_spaces D F]
  omega

/-! ### Explicit normal-form coordinate spaces -/

abbrev xSpace (D : FiniteB0Rep K) (F : SplittingFlag K D) :=
  LinearMap.ker (residualStem K D F.loopTop)

abbrev pxSpace (D : FiniteB0Rep K) (F : SplittingFlag K D) :=
  F.projectiveTop × xSpace D F

abbrev normalVertexOne (D : FiniteB0Rep K) (F : SplittingFlag K D) :=
  pxSpace D F ×
    (F.activeStem × (pxSpace D F × F.stationaryDead))

abbrev normalVertexTwo (D : FiniteB0Rep K) (F : SplittingFlag K D) :=
  F.activeStem × (F.projectiveTop × F.residualTail)

/-- Split a loop top into its projective and stem-zero coordinates. -/
def pxEquivLoopTop (D : FiniteB0Rep K) (F : SplittingFlag K D) :
    pxSpace D F ≃ₗ[K] F.loopTop :=
  F.projectiveTop.prodEquivOfIsCompl (xSpace D F)
    F.projectiveTop_compl

/-- The same top coordinates after the gauge change. -/
def pxEquivGaugedLoopTop (D : FiniteB0Rep K)
    (F : SplittingFlag K D) :
    pxSpace D F ≃ₗ[K] gaugedLoopTop D F :=
  (pxEquivLoopTop D F).trans (loopTopEquivGaugedLoopTop D F)

/-- Lower `P/X` coordinates together with the `S₁` coordinates give the
entire doubly-killed subspace. -/
def lowerEquivDeadSpace (D : FiniteB0Rep K)
    (F : SplittingFlag K D) :
    (pxSpace D F × F.stationaryDead) ≃ₗ[K] deadSpace K D :=
  (((pxEquivLoopTop D F).trans (loopTopEquivLoopRangeInDead D F)).prodCongr
      (LinearEquiv.refl K F.stationaryDead)).trans
    ((loopRangeInDead K D).prodEquivOfIsCompl F.stationaryDead
      F.stationaryDead_compl)

/-- Active `A` coordinates together with the lower `P/X/S₁` coordinates
give the full loop kernel. -/
def kernelCoordinatesEquivLoopKernel (D : FiniteB0Rep K)
    (F : SplittingFlag K D) :
    (F.activeStem × (pxSpace D F × F.stationaryDead)) ≃ₗ[K]
      LinearMap.ker (loopMap K D) :=
  ((LinearEquiv.refl K F.activeStem).prodCongr
      ((lowerEquivDeadSpace D F).trans
        (deadSpaceEquivStemOnLoopKernelKer D))).trans
    (F.activeStem.prodEquivOfIsCompl
      (LinearMap.ker (stemOnLoopKernel K D)) F.activeStem_compl)

/-- The complete vertex-one normal coordinates. -/
def normalVertexOneEquiv (D : FiniteB0Rep K)
    (F : SplittingFlag K D) :
    normalVertexOne D F ≃ₗ[K] D.V₁ :=
  ((pxEquivGaugedLoopTop D F).prodCongr
      (kernelCoordinatesEquivLoopKernel D F)).trans
    ((gaugedLoopTop D F).prodEquivOfIsCompl
      (LinearMap.ker (loopMap K D))
      (gaugedLoopTop_isCompl_loopKernel D F))

/-- Projective and `S₂` residual coordinates give the residual quotient. -/
def projectiveTailEquivResidualVertexTwo (D : FiniteB0Rep K)
    (F : SplittingFlag K D) :
    (F.projectiveTop × F.residualTail) ≃ₗ[K]
      residualVertexTwo K D :=
  (((projectiveTopEquivRange D F).prodCongr
      (LinearEquiv.refl K F.residualTail)).trans
    ((LinearMap.range (residualStem K D F.loopTop)).prodEquivOfIsCompl
      F.residualTail F.residualTail_compl))

/-- The complete vertex-two normal coordinates. -/
def normalVertexTwoEquiv (D : FiniteB0Rep K)
    (F : SplittingFlag K D) :
    normalVertexTwo D F ≃ₗ[K] D.V₂ :=
  (((activeStemEquivRange D F).prodCongr
      ((projectiveTailEquivResidualVertexTwo D F).trans
        (residualVertexTwoEquiv D F))).trans
    ((stationaryStemRange K D).prodEquivOfIsCompl
      F.vertexTwoResidual F.vertexTwoResidual_compl))

/-- The loop in five-block normal coordinates. -/
def normalLoop (D : FiniteB0Rep K) (F : SplittingFlag K D) :
    normalVertexOne D F →ₗ[K] normalVertexOne D F where
  toFun z := (0, (0, (z.1, 0)))
  map_add' z w := by ext <;> simp
  map_smul' c z := by ext <;> simp

@[simp] theorem normalLoop_apply (D : FiniteB0Rep K)
    (F : SplittingFlag K D) (z : normalVertexOne D F) :
    normalLoop D F z = (0, (0, (z.1, 0))) := rfl

/-- The stem in five-block normal coordinates. -/
def normalStem (D : FiniteB0Rep K) (F : SplittingFlag K D) :
    normalVertexOne D F →ₗ[K] normalVertexTwo D F where
  toFun z := (z.2.1, (z.1.1, 0))
  map_add' z w := by ext <;> simp
  map_smul' c z := by ext <;> simp

@[simp] theorem normalStem_apply (D : FiniteB0Rep K)
    (F : SplittingFlag K D) (z : normalVertexOne D F) :
    normalStem D F z = (z.2.1, (z.1.1, 0)) := rfl

@[simp] theorem normalLoop_sq (D : FiniteB0Rep K)
    (F : SplittingFlag K D) (z : normalVertexOne D F) :
    normalLoop D F (normalLoop D F z) = 0 := by
  rfl

@[simp] theorem normalStem_loop (D : FiniteB0Rep K)
    (F : SplittingFlag K D) (z : normalVertexOne D F) :
    normalStem D F (normalLoop D F z) = 0 := by
  rfl

/-- The abstract five-block normal representation attached to a splitting
flag. -/
def normalRep (D : FiniteB0Rep K) (F : SplittingFlag K D) :
    FiniteB0Rep K where
  V₁ := FGModuleCat.of K (normalVertexOne D F)
  V₂ := FGModuleCat.of K (normalVertexTwo D F)
  loop := FGModuleCat.ofHom (normalLoop D F)
  stem := FGModuleCat.ofHom (normalStem D F)
  loop_sq := normalLoop_sq D F
  stem_loop := normalStem_loop D F

theorem normalVertexOneEquiv_apply (D : FiniteB0Rep K)
    (F : SplittingFlag K D) (z : normalVertexOne D F) :
    normalVertexOneEquiv D F z =
      gaugedLoopTopMap D F (pxEquivLoopTop D F z.1) +
        (z.2.1.1.1 +
          (loopMap K D (pxEquivLoopTop D F z.2.2.1).1 +
            z.2.2.2.1.1)) := by
  rfl

/-- The vertex-one coordinate equivalence conjugates the normal loop to the
given loop. -/
theorem normalVertexOneEquiv_loop (D : FiniteB0Rep K)
    (F : SplittingFlag K D) (z : normalVertexOne D F) :
    normalVertexOneEquiv D F (normalLoop D F z) =
      loopMap K D (normalVertexOneEquiv D F z) := by
  rw [normalVertexOneEquiv_apply D F,
    normalVertexOneEquiv_apply D F]
  rw [normalLoop_apply]
  simp only [map_zero]
  simp only [zero_add, map_add]
  rw [loop_gaugedLoopTopMap D F]
  rw [z.2.1.1.2, D.loop_sq, z.2.2.2.1.2.1]
  simp

theorem normalVertexTwoEquiv_apply (D : FiniteB0Rep K)
    (F : SplittingFlag K D) (z : normalVertexTwo D F) :
    normalVertexTwoEquiv D F z =
      (activeStemEquivRange D F z.1).1 +
        (residualVertexTwoEquiv D F
          (projectiveTailEquivResidualVertexTwo D F z.2)).1 := by
  rfl

theorem pxEquivLoopTop_apply (D : FiniteB0Rep K)
    (F : SplittingFlag K D) (z : pxSpace D F) :
    pxEquivLoopTop D F z = z.1.1 + z.2.1 := by
  rfl

theorem activeStemEquivRange_apply_coe (D : FiniteB0Rep K)
    (F : SplittingFlag K D) (z : F.activeStem) :
    (activeStemEquivRange D F z).1 = stemMap K D z.1.1 := by
  rfl

theorem projectiveTailEquiv_apply_projective_zero
    (D : FiniteB0Rep K) (F : SplittingFlag K D)
    (p : F.projectiveTop) :
    projectiveTailEquivResidualVertexTwo D F (p, 0) =
      residualStem K D F.loopTop p.1 := by
  change residualStem K D F.loopTop p.1 + 0 =
    residualStem K D F.loopTop p.1
  rw [add_zero]

/-- The residual output selected by the projective coordinate is the literal
stem of the full gauged top; the `X` coordinate contributes zero. -/
theorem residual_projective_coordinate_eq_gaugedStem
    (D : FiniteB0Rep K) (F : SplittingFlag K D)
    (z : pxSpace D F) :
    residualVertexTwoEquiv D F
        (projectiveTailEquivResidualVertexTwo D F (z.1, 0)) =
      gaugedStem D F (pxEquivLoopTop D F z) := by
  rw [projectiveTailEquiv_apply_projective_zero]
  rw [← residualVertexTwoEquiv_residualStem D F
    (pxEquivLoopTop D F z)]
  apply congrArg (residualVertexTwoEquiv D F)
  rw [pxEquivLoopTop_apply, map_add, z.2.2, add_zero]

theorem gaugedStem_coe (D : FiniteB0Rep K)
    (F : SplittingFlag K D) (b : F.loopTop) :
    (gaugedStem D F b).1 = stemMap K D (gaugedLoopTopMap D F b) :=
  rfl

/-- The two vertex coordinate equivalences also conjugate the normal stem to
the given stem. -/
theorem normalVertexEquiv_stem (D : FiniteB0Rep K)
    (F : SplittingFlag K D) (z : normalVertexOne D F) :
    normalVertexTwoEquiv D F (normalStem D F z) =
      stemMap K D (normalVertexOneEquiv D F z) := by
  rw [normalVertexTwoEquiv_apply D F,
    normalVertexOneEquiv_apply D F, normalStem_apply]
  change (activeStemEquivRange D F z.2.1).1 +
      (residualVertexTwoEquiv D F
        (projectiveTailEquivResidualVertexTwo D F (z.1.1, 0))).1 =
    stemMap K D
      (gaugedLoopTopMap D F (pxEquivLoopTop D F z.1) +
        (z.2.1.1.1 +
          (loopMap K D (pxEquivLoopTop D F z.2.2.1).1 +
            z.2.2.2.1.1)))
  rw [activeStemEquivRange_apply_coe,
    residual_projective_coordinate_eq_gaugedStem]
  rw [gaugedStem_coe, map_add, map_add, map_add,
    D.stem_loop, z.2.2.2.1.2.2]
  simp [add_comm]

/-! ### Genuine-module normal-form isomorphism -/

def normalCarrierLinearEquiv (D : FiniteB0Rep K)
    (F : SplittingFlag K D) :
    FiniteB0Rep.Carrier K (normalRep D F) ≃ₗ[K]
      FiniteB0Rep.Carrier K D := by
  change (normalVertexOne D F × normalVertexTwo D F) ≃ₗ[K]
    (D.V₁ × D.V₂)
  exact (normalVertexOneEquiv D F).prodCongr
    (normalVertexTwoEquiv D F)

theorem normalCarrierLinearEquiv_e1 (D : FiniteB0Rep K)
    (F : SplittingFlag K D)
    (v : FiniteB0Rep.Carrier K (normalRep D F)) :
    normalCarrierLinearEquiv D F (e1 K • v) =
      e1 K • normalCarrierLinearEquiv D F v := by
  rw [FiniteB0Rep.e1_smul, FiniteB0Rep.e1_smul]
  apply FiniteB0Rep.carrier_ext K D
  · rfl
  · change normalVertexTwoEquiv D F 0 = 0
    rw [map_zero]

theorem normalCarrierLinearEquiv_e2 (D : FiniteB0Rep K)
    (F : SplittingFlag K D)
    (v : FiniteB0Rep.Carrier K (normalRep D F)) :
    normalCarrierLinearEquiv D F (e2 K • v) =
      e2 K • normalCarrierLinearEquiv D F v := by
  rw [FiniteB0Rep.e2_smul, FiniteB0Rep.e2_smul]
  apply FiniteB0Rep.carrier_ext K D
  · change normalVertexOneEquiv D F 0 = 0
    rw [map_zero]
  · rfl

theorem normalCarrierLinearEquiv_x (D : FiniteB0Rep K)
    (F : SplittingFlag K D)
    (v : FiniteB0Rep.Carrier K (normalRep D F)) :
    normalCarrierLinearEquiv D F (x K • v) =
      x K • normalCarrierLinearEquiv D F v := by
  rw [FiniteB0Rep.x_smul, FiniteB0Rep.x_smul]
  apply FiniteB0Rep.carrier_ext K D
  · exact normalVertexOneEquiv_loop D F v.1
  · change normalVertexTwoEquiv D F 0 = 0
    rw [map_zero]

theorem normalCarrierLinearEquiv_a (D : FiniteB0Rep K)
    (F : SplittingFlag K D)
    (v : FiniteB0Rep.Carrier K (normalRep D F)) :
    normalCarrierLinearEquiv D F (a K • v) =
      a K • normalCarrierLinearEquiv D F v := by
  rw [FiniteB0Rep.a_smul, FiniteB0Rep.a_smul]
  apply FiniteB0Rep.carrier_ext K D
  · change normalVertexOneEquiv D F 0 = 0
    rw [map_zero]
  · exact normalVertexEquiv_stem D F v.1

theorem algebra_coordinate_decomposition (r : B0Model K) :
    r = (TrivSqZeroExt.fst r).1 • e1 K +
      (TrivSqZeroExt.fst r).2 • e2 K +
      (TrivSqZeroExt.snd r).x • x K +
      (TrivSqZeroExt.snd r).a • a K := by
  ext <;> simp [e1, e2, x, a]

theorem normalCarrierLinearEquiv_smul (D : FiniteB0Rep K)
    (F : SplittingFlag K D) (r : B0Model K)
    (v : FiniteB0Rep.Carrier K (normalRep D F)) :
    normalCarrierLinearEquiv D F (r • v) =
      r • normalCarrierLinearEquiv D F v := by
  rw [algebra_coordinate_decomposition r]
  simp only [add_smul, IsScalarTower.smul_assoc, map_add, map_smul]
  rw [normalCarrierLinearEquiv_e1 D F,
    normalCarrierLinearEquiv_e2 D F,
    normalCarrierLinearEquiv_x D F,
    normalCarrierLinearEquiv_a D F]

/-- The abstract five-block normal representation is genuinely isomorphic to
the original representation module. -/
def normalCarrierModuleLinearEquiv (D : FiniteB0Rep K)
    (F : SplittingFlag K D) :
    FiniteB0Rep.Carrier K (normalRep D F) ≃ₗ[B0Model K]
      FiniteB0Rep.Carrier K D :=
  LinearEquiv.ofBijective
    { toFun := normalCarrierLinearEquiv D F
      map_add' := (normalCarrierLinearEquiv D F).map_add
      map_smul' := normalCarrierLinearEquiv_smul D F }
    (normalCarrierLinearEquiv D F).bijective

def normalModuleIso (D : FiniteB0Rep K)
    (F : SplittingFlag K D) :
    FiniteB0Rep.asFGModule K (normalRep D F) ≅
      FiniteB0Rep.asFGModule K D :=
  (normalCarrierModuleLinearEquiv D F).toFGModuleCatIso

/-! ### Expansion of multiplicity spaces into named copies -/

inductive BlockTag where
  | s1
  | s2
  | x
  | a
  | p
  deriving DecidableEq

instance : Fintype BlockTag where
  elems := {.s1, .s2, .x, .a, .p}
  complete t := by cases t <;> simp

def blockMultiplicity (D : FiniteB0Rep K) (F : SplittingFlag K D) :
    BlockTag → ℕ
  | .s1 => Module.finrank K F.stationaryDead
  | .s2 => Module.finrank K F.residualTail
  | .x => Module.finrank K (xSpace D F)
  | .a => Module.finrank K F.activeStem
  | .p => Module.finrank K F.projectiveTop

abbrev BlockIndex (D : FiniteB0Rep K) (F : SplittingFlag K D) :=
  Σ t : BlockTag, Fin (blockMultiplicity D F t)

def namedBlockData : BlockTag → FiniteB0Rep K
  | .s1 => S1Data K
  | .s2 => S2Data K
  | .x => XData K
  | .a => AData K
  | .p => PData K

abbrev namedBlockCarrier (D : FiniteB0Rep K) (F : SplittingFlag K D)
    (i : BlockIndex D F) :=
  FiniteB0Rep.Carrier K (namedBlockData (K := K) i.1)

def namedBlockModule (D : FiniteB0Rep K) (F : SplittingFlag K D)
    (i : BlockIndex D F) : FGModuleCat (B0Model K) :=
  FiniteB0Rep.asFGModule K (namedBlockData (K := K) i.1)

def s1BasisEquiv (D : FiniteB0Rep K) (F : SplittingFlag K D) :
    F.stationaryDead ≃ₗ[K]
      Fin (blockMultiplicity D F .s1) → K :=
  (Module.finBasis K F.stationaryDead).equivFun

def s2BasisEquiv (D : FiniteB0Rep K) (F : SplittingFlag K D) :
    F.residualTail ≃ₗ[K]
      Fin (blockMultiplicity D F .s2) → K :=
  (Module.finBasis K F.residualTail).equivFun

def xBasisEquiv (D : FiniteB0Rep K) (F : SplittingFlag K D) :
    xSpace D F ≃ₗ[K]
      Fin (blockMultiplicity D F .x) → K :=
  (Module.finBasis K (xSpace D F)).equivFun

def aBasisEquiv (D : FiniteB0Rep K) (F : SplittingFlag K D) :
    F.activeStem ≃ₗ[K]
      Fin (blockMultiplicity D F .a) → K :=
  (Module.finBasis K F.activeStem).equivFun

def pBasisEquiv (D : FiniteB0Rep K) (F : SplittingFlag K D) :
    F.projectiveTop ≃ₗ[K]
      Fin (blockMultiplicity D F .p) → K :=
  (Module.finBasis K F.projectiveTop).equivFun

/-- Concrete finite-product model of a finite biproduct in `FGModuleCat`. -/
def biproductIsoPiFG
    {R : Type u} [Ring R] [IsNoetherianRing R]
    {J : Type} [Finite J] (f : J → FGModuleCat.{u} R) :
    biproduct f ≅ FGModuleCat.of R (∀ j, f j) := by
  let G := forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)
  letI : PreservesBiproduct f G :=
    preservesBiproduct_of_preservesProduct G
  exact G.preimageIso
    (G.mapBiproduct f ≪≫
      ModuleCat.biproductIsoPi (fun j ↦ G.obj (f j)))

@[simp] theorem carrier_fst_add (E : FiniteB0Rep K)
    (v w : FiniteB0Rep.Carrier K E) :
    FiniteB0Rep.fst K E (v + w) =
      FiniteB0Rep.fst K E v + FiniteB0Rep.fst K E w := by
  change (v + w).1 = v.1 + w.1
  rfl

@[simp] theorem carrier_snd_add (E : FiniteB0Rep K)
    (v w : FiniteB0Rep.Carrier K E) :
    FiniteB0Rep.snd K E (v + w) =
      FiniteB0Rep.snd K E v + FiniteB0Rep.snd K E w := by
  change (v + w).2 = v.2 + w.2
  rfl

@[simp] theorem carrier_fst_smul (E : FiniteB0Rep K)
    (c : K) (v : FiniteB0Rep.Carrier K E) :
    FiniteB0Rep.fst K E (c • v) =
      c • FiniteB0Rep.fst K E v := by
  change (c • v).1 = c • v.1
  rfl

@[simp] theorem carrier_snd_smul (E : FiniteB0Rep K)
    (c : K) (v : FiniteB0Rep.Carrier K E) :
    FiniteB0Rep.snd K E (c • v) =
      c • FiniteB0Rep.snd K E v := by
  change (c • v).2 = c • v.2
  rfl

@[simp] theorem carrier_mk_add (E : FiniteB0Rep K)
    (v₁ w₁ : E.V₁) (v₂ w₂ : E.V₂) :
    ((v₁, v₂) : FiniteB0Rep.Carrier K E) + (w₁, w₂) =
      (v₁ + w₁, v₂ + w₂) := rfl

@[simp] theorem carrier_smul_mk (E : FiniteB0Rep K)
    (c : K) (v₁ : E.V₁) (v₂ : E.V₂) :
    c • ((v₁, v₂) : FiniteB0Rep.Carrier K E) =
      (c • v₁, c • v₂) := rfl

theorem rep_v1_zero_add (E : FiniteB0Rep K) :
    (0 : E.V₁) + 0 = 0 := zero_add 0

theorem rep_v2_zero_add (E : FiniteB0Rep K) :
    (0 : E.V₂) + 0 = 0 := zero_add 0

theorem rep_v1_smul_zero (E : FiniteB0Rep K) (c : K) :
    c • (0 : E.V₁) = 0 := smul_zero c

theorem rep_v2_smul_zero (E : FiniteB0Rep K) (c : K) :
    c • (0 : E.V₂) = 0 := smul_zero c

@[simp] theorem normal_v1_fst_add (D : FiniteB0Rep K)
    (F : SplittingFlag K D) (v w : (normalRep D F).V₁) :
    (v + w).1 = v.1 + w.1 := rfl

@[simp] theorem normal_v1_snd_add (D : FiniteB0Rep K)
    (F : SplittingFlag K D) (v w : (normalRep D F).V₁) :
    (v + w).2 = v.2 + w.2 := rfl

@[simp] theorem normal_v2_fst_add (D : FiniteB0Rep K)
    (F : SplittingFlag K D) (v w : (normalRep D F).V₂) :
    (v + w).1 = v.1 + w.1 := rfl

@[simp] theorem normal_v2_snd_add (D : FiniteB0Rep K)
    (F : SplittingFlag K D) (v w : (normalRep D F).V₂) :
    (v + w).2 = v.2 + w.2 := rfl

@[simp] theorem normal_v1_fst_smul (D : FiniteB0Rep K)
    (F : SplittingFlag K D) (c : K) (v : (normalRep D F).V₁) :
    (c • v).1 = c • v.1 := rfl

@[simp] theorem normal_v1_snd_smul (D : FiniteB0Rep K)
    (F : SplittingFlag K D) (c : K) (v : (normalRep D F).V₁) :
    (c • v).2 = c • v.2 := rfl

@[simp] theorem normal_v2_fst_smul (D : FiniteB0Rep K)
    (F : SplittingFlag K D) (c : K) (v : (normalRep D F).V₂) :
    (c • v).1 = c • v.1 := rfl

@[simp] theorem normal_v2_snd_smul (D : FiniteB0Rep K)
    (F : SplittingFlag K D) (c : K) (v : (normalRep D F).V₂) :
    (c • v).2 = c • v.2 := rfl

@[simp] theorem normal_v1_zero_eq (D : FiniteB0Rep K)
    (F : SplittingFlag K D) :
    (0 : (normalRep D F).V₁) =
      ((0, 0) : normalVertexOne D F) := rfl

@[simp] theorem normal_v2_zero_eq (D : FiniteB0Rep K)
    (F : SplittingFlag K D) :
    (0 : (normalRep D F).V₂) =
      ((0, 0) : normalVertexTwo D F) := rfl

@[simp] theorem S1_loop_apply (z : (S1Data K).V₁) :
    (S1Data K).loop.hom.hom z = 0 := rfl

@[simp] theorem S2_loop_apply (z : (S2Data K).V₁) :
    (S2Data K).loop.hom.hom z = 0 := rfl

@[simp] theorem X_loop_apply (z : (XData K).V₁) :
    (XData K).loop.hom.hom z = (0, z.1) := rfl

@[simp] theorem A_loop_apply (z : (AData K).V₁) :
    (AData K).loop.hom.hom z = 0 := rfl

@[simp] theorem P_loop_apply (z : (PData K).V₁) :
    (PData K).loop.hom.hom z = (0, z.1) := rfl

@[simp] theorem S1_stem_apply (z : (S1Data K).V₁) :
    (S1Data K).stem.hom.hom z = 0 := rfl

@[simp] theorem S2_stem_apply (z : (S2Data K).V₁) :
    (S2Data K).stem.hom.hom z = 0 := rfl

@[simp] theorem X_stem_apply (z : (XData K).V₁) :
    (XData K).stem.hom.hom z = 0 := rfl

@[simp] theorem A_stem_apply (z : (AData K).V₁) :
    (AData K).stem.hom.hom z = z := rfl

@[simp] theorem P_stem_apply (z : (PData K).V₁) :
    (PData K).stem.hom.hom z = z.1 := rfl

/-- Read normal-form coordinates one basis coefficient at a time as a family
of the five named modules. -/
def normalToBlockPi (D : FiniteB0Rep K) (F : SplittingFlag K D) :
    FiniteB0Rep.Carrier K (normalRep D F) →ₗ[K]
      (∀ i, namedBlockCarrier D F i) where
  toFun v
    | ⟨.s1, j⟩ =>
        (s1BasisEquiv D F
          (FiniteB0Rep.fst K (normalRep D F) v).2.2.2 j, 0)
    | ⟨.s2, j⟩ =>
        (0, s2BasisEquiv D F
          (FiniteB0Rep.snd K (normalRep D F) v).2.2 j)
    | ⟨.x, j⟩ =>
        ((xBasisEquiv D F
            (FiniteB0Rep.fst K (normalRep D F) v).1.2 j,
          xBasisEquiv D F
            (FiniteB0Rep.fst K (normalRep D F) v).2.2.1.2 j), 0)
    | ⟨.a, j⟩ =>
        (aBasisEquiv D F
            (FiniteB0Rep.fst K (normalRep D F) v).2.1 j,
          aBasisEquiv D F
            (FiniteB0Rep.snd K (normalRep D F) v).1 j)
    | ⟨.p, j⟩ =>
        ((pBasisEquiv D F
            (FiniteB0Rep.fst K (normalRep D F) v).1.1 j,
          pBasisEquiv D F
            (FiniteB0Rep.fst K (normalRep D F) v).2.2.1.1 j),
          pBasisEquiv D F
            (FiniteB0Rep.snd K (normalRep D F) v).2.1 j)
  map_add' v w := by
    funext i
    rcases i with ⟨t, j⟩
    cases t <;>
      change _ = (_ + _, _ + _) <;>
      simp [carrier_fst_add, carrier_snd_add, normal_v1_fst_add,
        normal_v1_snd_add, normal_v2_fst_add, normal_v2_snd_add,
        Prod.fst_add, Prod.snd_add, namedBlockData] <;>
      constructor <;>
        first
        | rfl
        | exact (rep_v1_zero_add (K := K) _).symm
        | exact (rep_v2_zero_add (K := K) _).symm
  map_smul' c v := by
    funext i
    rcases i with ⟨t, j⟩
    cases t <;>
      change _ = (c • _, c • _) <;>
      simp [carrier_fst_smul, carrier_snd_smul, normal_v1_fst_smul,
        normal_v1_snd_smul, normal_v2_fst_smul, normal_v2_snd_smul,
        namedBlockData] <;>
      constructor <;>
        first
        | rfl
        | exact (rep_v1_smul_zero (K := K) _ c).symm
        | exact (rep_v2_smul_zero (K := K) _ c).symm

/-- Reassemble one copy of each normal coordinate from its family of named
block coordinates. -/
def blockPiToNormal (D : FiniteB0Rep K) (F : SplittingFlag K D)
    (g : ∀ i, namedBlockCarrier D F i) :
    FiniteB0Rep.Carrier K (normalRep D F) := by
  let pTop := (pBasisEquiv D F).symm (fun j =>
    (FiniteB0Rep.fst K (namedBlockData (K := K) .p)
      (g ⟨.p, j⟩)).1)
  let xTop := (xBasisEquiv D F).symm (fun j =>
    (FiniteB0Rep.fst K (namedBlockData (K := K) .x)
      (g ⟨.x, j⟩)).1)
  let aOne := (aBasisEquiv D F).symm (fun j =>
    FiniteB0Rep.fst K (namedBlockData (K := K) .a)
      (g ⟨.a, j⟩))
  let pLower := (pBasisEquiv D F).symm (fun j =>
    (FiniteB0Rep.fst K (namedBlockData (K := K) .p)
      (g ⟨.p, j⟩)).2)
  let xLower := (xBasisEquiv D F).symm (fun j =>
    (FiniteB0Rep.fst K (namedBlockData (K := K) .x)
      (g ⟨.x, j⟩)).2)
  let sOne := (s1BasisEquiv D F).symm (fun j =>
    FiniteB0Rep.fst K (namedBlockData (K := K) .s1)
      (g ⟨.s1, j⟩))
  let aTwo := (aBasisEquiv D F).symm (fun j =>
    FiniteB0Rep.snd K (namedBlockData (K := K) .a)
      (g ⟨.a, j⟩))
  let pTail := (pBasisEquiv D F).symm (fun j =>
    FiniteB0Rep.snd K (namedBlockData (K := K) .p)
      (g ⟨.p, j⟩))
  let sTwo := (s2BasisEquiv D F).symm (fun j =>
    FiniteB0Rep.snd K (namedBlockData (K := K) .s2)
      (g ⟨.s2, j⟩))
  exact (((pTop, xTop), (aOne, ((pLower, xLower), sOne))),
    (aTwo, (pTail, sTwo)))

theorem blockPiToNormal_normalToBlockPi
    (D : FiniteB0Rep K) (F : SplittingFlag K D)
    (v : FiniteB0Rep.Carrier K (normalRep D F)) :
    blockPiToNormal D F (normalToBlockPi D F v) = v := by
  apply FiniteB0Rep.carrier_ext K (normalRep D F)
  · simp [blockPiToNormal, normalToBlockPi, FiniteB0Rep.fst]
  · simp [blockPiToNormal, normalToBlockPi, FiniteB0Rep.snd]

theorem normalToBlockPi_blockPiToNormal
    (D : FiniteB0Rep K) (F : SplittingFlag K D)
    (g : ∀ i, namedBlockCarrier D F i) :
    normalToBlockPi D F (blockPiToNormal D F g) = g := by
  funext i
  rcases i with ⟨t, j⟩
  cases t <;>
    apply FiniteB0Rep.carrier_ext K _ <;>
    simp [blockPiToNormal, normalToBlockPi, namedBlockData,
      FiniteB0Rep.fst, FiniteB0Rep.snd]
  all_goals apply Subsingleton.elim

def normalBlockLinearEquiv (D : FiniteB0Rep K)
    (F : SplittingFlag K D) :
    FiniteB0Rep.Carrier K (normalRep D F) ≃ₗ[K]
      (∀ i, namedBlockCarrier D F i) :=
  LinearEquiv.ofBijective (normalToBlockPi D F)
    ⟨fun v w h => by
        rw [← blockPiToNormal_normalToBlockPi D F v,
          ← blockPiToNormal_normalToBlockPi D F w, h],
      fun g => ⟨blockPiToNormal D F g,
        normalToBlockPi_blockPiToNormal D F g⟩⟩

theorem normalToBlockPi_e1 (D : FiniteB0Rep K)
    (F : SplittingFlag K D)
    (v : FiniteB0Rep.Carrier K (normalRep D F)) :
    normalToBlockPi D F (e1 K • v) =
      e1 K • normalToBlockPi D F v := by
  funext i
  change normalToBlockPi D F (e1 K • v) i =
    e1 K • normalToBlockPi D F v i
  rw [FiniteB0Rep.e1_smul, FiniteB0Rep.e1_smul]
  rcases i with ⟨t, j⟩
  cases t <;>
    simp [normalToBlockPi, namedBlockData, FiniteB0Rep.fst,
      FiniteB0Rep.snd] <;> rfl

theorem normalToBlockPi_e2 (D : FiniteB0Rep K)
    (F : SplittingFlag K D)
    (v : FiniteB0Rep.Carrier K (normalRep D F)) :
    normalToBlockPi D F (e2 K • v) =
      e2 K • normalToBlockPi D F v := by
  funext i
  change normalToBlockPi D F (e2 K • v) i =
    e2 K • normalToBlockPi D F v i
  rw [FiniteB0Rep.e2_smul, FiniteB0Rep.e2_smul]
  rcases i with ⟨t, j⟩
  cases t <;>
    simp [normalToBlockPi, namedBlockData, FiniteB0Rep.fst,
      FiniteB0Rep.snd] <;> rfl

theorem normalToBlockPi_x (D : FiniteB0Rep K)
    (F : SplittingFlag K D)
    (v : FiniteB0Rep.Carrier K (normalRep D F)) :
    normalToBlockPi D F (x K • v) =
      x K • normalToBlockPi D F v := by
  funext i
  change normalToBlockPi D F (x K • v) i =
    x K • normalToBlockPi D F v i
  rw [FiniteB0Rep.x_smul]
  change normalToBlockPi D F (normalLoop D F v.1, 0) i =
    x K • normalToBlockPi D F v i
  rw [FiniteB0Rep.x_smul]
  rcases i with ⟨t, j⟩
  cases t <;>
    simp [normalToBlockPi, normalLoop, namedBlockData, jordan,
      FiniteB0Rep.fst, FiniteB0Rep.snd] <;> rfl

theorem normalToBlockPi_a (D : FiniteB0Rep K)
    (F : SplittingFlag K D)
    (v : FiniteB0Rep.Carrier K (normalRep D F)) :
    normalToBlockPi D F (a K • v) =
      a K • normalToBlockPi D F v := by
  funext i
  change normalToBlockPi D F (a K • v) i =
    a K • normalToBlockPi D F v i
  rw [FiniteB0Rep.a_smul]
  change normalToBlockPi D F (0, normalStem D F v.1) i =
    a K • normalToBlockPi D F v i
  rw [FiniteB0Rep.a_smul]
  rcases i with ⟨t, j⟩
  cases t <;>
    simp [normalToBlockPi, normalStem, namedBlockData, forkStem,
      FiniteB0Rep.fst, FiniteB0Rep.snd] <;> rfl

theorem normalToBlockPi_smul (D : FiniteB0Rep K)
    (F : SplittingFlag K D) (r : B0Model K)
    (v : FiniteB0Rep.Carrier K (normalRep D F)) :
    normalToBlockPi D F (r • v) =
      r • normalToBlockPi D F v := by
  rw [algebra_coordinate_decomposition r]
  simp only [add_smul, IsScalarTower.smul_assoc, map_add, map_smul]
  rw [normalToBlockPi_e1 D F, normalToBlockPi_e2 D F,
    normalToBlockPi_x D F, normalToBlockPi_a D F]

def normalBlockModuleLinearEquiv (D : FiniteB0Rep K)
    (F : SplittingFlag K D) :
    FiniteB0Rep.Carrier K (normalRep D F) ≃ₗ[B0Model K]
      (∀ i, namedBlockCarrier D F i) :=
  LinearEquiv.ofBijective
    { toFun := normalToBlockPi D F
      map_add' := (normalToBlockPi D F).map_add
      map_smul' := normalToBlockPi_smul D F }
    (normalBlockLinearEquiv D F).bijective

def normalBlockPiModuleIso (D : FiniteB0Rep K)
    (F : SplittingFlag K D) :
    FiniteB0Rep.asFGModule K (normalRep D F) ≅
      FGModuleCat.of (B0Model K)
        (∀ i, namedBlockCarrier D F i) :=
  (normalBlockModuleLinearEquiv D F).toFGModuleCatIso

/-- The abstract normal representation is a finite biproduct of the five
named modules, with one copy for every basis vector of its multiplicity
space. -/
def normalNamedBiproductIso (D : FiniteB0Rep K)
    (F : SplittingFlag K D) :
    FiniteB0Rep.asFGModule K (normalRep D F) ≅
      biproduct (namedBlockModule D F) :=
  normalBlockPiModuleIso D F ≪≫
    (biproductIsoPiFG (namedBlockModule D F)).symm

/-- Every finite `B₀` representation module decomposes as a finite
biproduct of copies of `S₁`, `S₂`, `X`, `A`, and `P`. -/
def finiteRepNamedBiproductIso (D : FiniteB0Rep K)
    (F : SplittingFlag K D) :
    FiniteB0Rep.asFGModule K D ≅
      biproduct (namedBlockModule D F) :=
  (normalModuleIso D F).symm ≪≫ normalNamedBiproductIso D F

theorem finiteRep_decomposes_named (D : FiniteB0Rep K) :
    ∃ F : SplittingFlag K D,
      Nonempty (FiniteB0Rep.asFGModule K D ≅
        biproduct (namedBlockModule D F)) := by
  obtain ⟨F⟩ := exists_splittingFlag K D
  exact ⟨F, ⟨finiteRepNamedBiproductIso D F⟩⟩

/-- The complementary-space equations behind the five blocks. -/
theorem splitting_equations (D : FiniteB0Rep K)
    (F : SplittingFlag K D) :
    (F.loopTop ⊔ LinearMap.ker (loopMap K D) = ⊤) ∧
    (loopRangeInDead K D ⊔ F.stationaryDead = ⊤) ∧
    (F.activeStem ⊔ LinearMap.ker (stemOnLoopKernel K D) = ⊤) ∧
    (stationaryStemRange K D ⊔ F.vertexTwoResidual = ⊤) ∧
    (F.projectiveTop ⊔
      LinearMap.ker (residualStem K D F.loopTop) = ⊤) ∧
    (LinearMap.range (residualStem K D F.loopTop) ⊔
      F.residualTail = ⊤) := by
  exact ⟨F.loopTop_compl.codisjoint.eq_top,
    F.stationaryDead_compl.codisjoint.eq_top,
    F.activeStem_compl.codisjoint.eq_top,
    F.vertexTwoResidual_compl.codisjoint.eq_top,
    F.projectiveTop_compl.codisjoint.eq_top,
    F.residualTail_compl.codisjoint.eq_top⟩

end SplittingFlag

end QuotientSubmoduleEquidistribution.LollipopConcrete.ModuleLayer.ExhaustivenessReduction
