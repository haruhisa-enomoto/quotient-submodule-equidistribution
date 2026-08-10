import QuotientSubmoduleEquidistribution.RepresentationTheory.PeirceCotangentCornerDimension
import QuotientSubmoduleEquidistribution.RepresentationTheory.CoordinateGabrielRealization
import QuotientSubmoduleEquidistribution.RepresentationTheory.ProjectiveRadicalExt
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Peirce cotangent corners and degree-one Ext

The dual of each Peirce corner of `J/J²` is canonically equivalent to the
corresponding coordinate radical-Hom space.  Dimension shifting and the
coordinate-simple alignment identify it with the aligned `Ext¹` space, giving
an exact cornerwise dimension equality.  No bound quiver or concrete module
classification occurs here.
-/

noncomputable section

namespace QuotientSubmoduleEquidistribution.QuotientSurvival

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MulOpposite

universe u v

variable {K B : Type u}
  [Field K] [Ring B] [Algebra K B] [IsArtinianRing B]

private abbrev J (B : Type u) [Ring B] := Ring.jacobson B

namespace TwoCoordinateData

variable (D : TwoCoordinateData (K := K) (B := B))

/-- A radical element, projected to one Peirce corner and reduced modulo
`J²`. -/
def cornerCotangentElement
    (i j : Fin 2) (z : B) (hz : z ∈ J B) :
    D.jacobsonCotangentCornerSubmodule i j :=
  ⟨(jacobsonSquareSubmodule (K := K) (B := B)).mkQ
      (D.liftedCoordinate i * z * D.liftedCoordinate j),
    ⟨z, hz, rfl⟩⟩

@[simp]
theorem cornerCotangentElement_val
    (i j : Fin 2) (z : B) (hz : z ∈ J B) :
    (D.cornerCotangentElement i j z hz :
      B ⧸ jacobsonSquareSubmodule (K := K) (B := B)) =
        (jacobsonSquareSubmodule (K := K) (B := B)).mkQ
          (D.liftedCoordinate i * z * D.liftedCoordinate j) := rfl

/-- A functional on one Peirce cotangent corner gives a right-module map
from the kernel of the coordinate-projective top to the target coordinate
simple. -/
def cornerDualKernelMap
    (i j : Fin 2)
    (phi : Module.Dual K (D.jacobsonCotangentCornerSubmodule i j)) :
    QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.KernelToCoordinateLinearMap
      D i j := by
  letI : Module Bᵐᵒᵖ K :=
    QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleModule D j
  exact
    { toFun := fun x ↦
        phi (D.cornerCotangentElement i j (unop x.1.1)
          (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.unop_mem_jacobson_of_mem_vertexTop_ker
            D i x))
      map_add' := fun x y ↦ by
        rw [← map_add]
        congr 1
        apply Subtype.ext
        simp [cornerCotangentElement, mul_add, add_mul]
      map_smul' := fun b x ↦ by
        let a : B := unop x.1.1
        let d : B := unop b
        let ei : B := D.liftedCoordinate i
        let ej : B := D.liftedCoordinate j
        let q : K :=
          QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateCharacter
            D j d
        have ha : a ∈ J B :=
          QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.unop_mem_jacobson_of_mem_vertexTop_ker
            D i x
        have had : a * d ∈ J B := (J B).mul_mem_right d ha
        have hright :
            d * ej - algebraMap K B q * ej ∈ J B := by
          simpa [d, ej, q] using
            QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.mul_liftedCoordinate_sub_coordinate_mem_jacobson
              D j d
        have hdiff :
            a * d * ej - algebraMap K B q * (a * ej) ∈
              (J B) ^ 2 := by
          have hscalar :
              algebraMap K B q * (a * ej) =
                a * (algebraMap K B q * ej) := by
            calc
              algebraMap K B q * (a * ej) =
                  (algebraMap K B q * a) * ej := by noncomm_ring
              _ = (a * algebraMap K B q) * ej := by
                rw [Algebra.commutes q a]
              _ = a * (algebraMap K B q * ej) := by noncomm_ring
          rw [hscalar]
          have hprod : a * (d * ej - algebraMap K B q * ej) ∈
              J B * J B := Ideal.mul_mem_mul ha hright
          rw [show (2 : Nat) = 1 + 1 by omega,
            Ideal.IsTwoSided.pow_add, Submodule.pow_one]
          simpa [mul_sub, mul_assoc] using hprod
        let J2K := jacobsonSquareSubmodule (K := K) (B := B)
        have hleftDiff :
            ei * (a * d * ej - algebraMap K B q * (a * ej)) ∈
              (J B) ^ 2 := ((J B) ^ 2).mul_mem_left ei hdiff
        have hclass :
            J2K.mkQ (ei * (a * d) * ej) =
              q • J2K.mkQ (ei * a * ej) := by
          apply (Submodule.Quotient.eq J2K).mpr
          have heq :
              ei * (a * d) * ej - q • (ei * a * ej) =
                ei * (a * d * ej - algebraMap K B q * (a * ej)) := by
            simp only [Algebra.smul_def]
            have hscalarEi :
                algebraMap K B q * (ei * a * ej) =
                  ei * (algebraMap K B q * (a * ej)) := by
              calc
                algebraMap K B q * (ei * a * ej) =
                    (algebraMap K B q * ei) * a * ej := by noncomm_ring
                _ = (ei * algebraMap K B q) * a * ej := by
                  rw [Algebra.commutes q ei]
                _ = ei * (algebraMap K B q * (a * ej)) := by
                  noncomm_ring
            rw [hscalarEi]
            noncomm_ring
          rw [heq]
          simpa [J2K, jacobsonSquareSubmodule] using hleftDiff
        have hcorner :
            D.cornerCotangentElement i j (a * d) had =
              q • D.cornerCotangentElement i j a ha := by
          apply Subtype.ext
          exact hclass
        change
          phi (D.cornerCotangentElement i j (a * d) had) =
            q * phi (D.cornerCotangentElement i j a ha)
        rw [hcorner, map_smul]
        rfl }

/-- Dependence of `cornerDualKernelMap` on the corner functional is
`K`-linear. -/
def cornerDualToKernelLinearMap (i j : Fin 2) :
    Module.Dual K (D.jacobsonCotangentCornerSubmodule i j) →ₗ[K]
      (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.vertexPresentation D i).X₁ ⟶
        QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimple D j where
  toFun phi :=
    QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.kernelToCoordinateMorphism
      D i j (D.cornerDualKernelMap i j phi)
  map_add' phi psi := by
    apply ModuleCat.hom_ext
    rfl
  map_smul' c phi := by
    apply ModuleCat.hom_ext
    ext x
    simp only [RingHom.id_apply, ModuleCat.hom_smul, LinearMap.smul_apply]
    change
      c * phi _ =
        QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateCharacterOp
          D j (algebraMap K Bᵐᵒᵖ c) * phi _
    simp [QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateCharacterOp,
      QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateCharacter]

/-- Evaluation on the canonical kernel element recovers evaluation of the
original corner functional. -/
theorem cornerDualKernelMap_vertexKernelElementOfJacobian
    (i j : Fin 2)
    (phi : Module.Dual K (D.jacobsonCotangentCornerSubmodule i j))
    (z : B) (hz : z ∈ J B) :
    D.cornerDualKernelMap i j phi
        (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.vertexKernelElementOfJacobian
          D i z hz) =
      phi (D.cornerCotangentElement i j z hz) := by
  change phi (D.cornerCotangentElement i j
      (D.liftedCoordinate i * z) _) =
    phi (D.cornerCotangentElement i j z hz)
  congr 1
  apply Subtype.ext
  simp only [cornerCotangentElement_val]
  congr 1
  calc
    D.liftedCoordinate i * (D.liftedCoordinate i * z) *
          D.liftedCoordinate j =
        (D.liftedCoordinate i * D.liftedCoordinate i) * z *
          D.liftedCoordinate j := by noncomm_ring
    _ = D.liftedCoordinate i * z * D.liftedCoordinate j := by
      rw [D.liftedCoordinate_complete.idem i]

/-- The dual of every Peirce cotangent corner embeds into maps from the
coordinate projective radical to the target coordinate simple. -/
theorem cornerDualToKernelLinearMap_injective (i j : Fin 2) :
    Function.Injective (cornerDualToKernelLinearMap D i j) := by
  intro phi psi h
  apply LinearMap.ext
  intro q
  rcases q.2 with ⟨z, hz, hq⟩
  have happly := congrArg
    (fun g ↦ g.hom
      (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.vertexKernelElementOfJacobian
        D i z hz)) h
  change
    (D.cornerDualKernelMap i j phi)
        (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.vertexKernelElementOfJacobian
          D i z hz) =
      (D.cornerDualKernelMap i j psi)
        (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.vertexKernelElementOfJacobian
          D i z hz) at happly
  have hphi := D.cornerDualKernelMap_vertexKernelElementOfJacobian
    i j phi z hz
  have hpsi := D.cornerDualKernelMap_vertexKernelElementOfJacobian
    i j psi z hz
  have hq' : D.cornerCotangentElement i j z hz = q := by
    apply Subtype.ext
    exact hq
  rw [hphi, hpsi, hq'] at happly
  exact happly

/-- The restricted Peirce quotient map whose range is the corresponding
cotangent corner. -/
def cornerCotangentPresentationLinearMap (i j : Fin 2) :
    ((J B : Submodule B B).restrictScalars K) →ₗ[K]
      (B ⧸ jacobsonSquareSubmodule (K := K) (B := B)) :=
  ((jacobsonSquareSubmodule (K := K) (B := B)).mkQ.comp
    (D.peirceLinearMap i j)).domRestrict
      ((J B : Submodule B B).restrictScalars K)

@[simp]
theorem range_cornerCotangentPresentationLinearMap (i j : Fin 2) :
    LinearMap.range (D.cornerCotangentPresentationLinearMap i j) =
      D.jacobsonCotangentCornerSubmodule i j := by
  simp [cornerCotangentPresentationLinearMap,
    jacobsonCotangentCornerSubmodule]

/-- A map from the coordinate-projective kernel evaluates Jacobson elements
`K`-linearly. -/
def kernelMapOnJacobianLinearMap
    (i j : Fin 2)
    (f :
      QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.KernelToCoordinateLinearMap
        D i j) :
    ((J B : Submodule B B).restrictScalars K) →ₗ[K] K := by
  letI : Module Bᵐᵒᵖ K :=
    QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleModule D j
  exact
    { toFun := fun z ↦
        f
          (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.vertexKernelElementOfJacobian
            D i z.1 z.2)
      map_add' := fun x y ↦ by
        have hadd :
            QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.vertexKernelElementOfJacobian
                D i (x + y).1 (x + y).2 =
              QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.vertexKernelElementOfJacobian
                  D i x.1 x.2 +
                QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.vertexKernelElementOfJacobian
                  D i y.1 y.2 := by
          apply Subtype.ext
          apply Subtype.ext
          simp [QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.vertexKernelElementOfJacobian,
            mul_add]
        rw [hadd, map_add]
      map_smul' := fun c z ↦ by
        have hsmul :
            QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.vertexKernelElementOfJacobian
                D i (c • z).1 (c • z).2 =
              op (algebraMap K B c) •
                QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.vertexKernelElementOfJacobian
                  D i z.1 z.2 := by
          apply Subtype.ext
          apply Subtype.ext
          simp only [QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.vertexKernelElementOfJacobian,
            Algebra.smul_def, Submodule.coe_smul_of_tower]
          simp [mul_assoc, Algebra.commutes]
        rw [hsmul, map_smul]
        change
          QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateCharacterOp
              D j (op (algebraMap K B c)) * _ =
            c * _
        simp [QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateCharacterOp,
          QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateCharacter] }

/-- The Jacobson evaluation attached to a kernel map depends only on the
Peirce cotangent class. -/
theorem ker_cornerCotangentPresentation_le_ker_kernelMapOnJacobian
    (i j : Fin 2)
    (f :
      QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.KernelToCoordinateLinearMap
        D i j) :
    LinearMap.ker (D.cornerCotangentPresentationLinearMap i j) ≤
      LinearMap.ker (D.kernelMapOnJacobianLinearMap i j f) := by
  letI : Module Bᵐᵒᵖ K :=
    QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleModule D j
  intro z hz
  rw [LinearMap.mem_ker] at hz ⊢
  change
    (jacobsonSquareSubmodule (K := K) (B := B)).mkQ
        (D.liftedCoordinate i * z.1 * D.liftedCoordinate j) = 0 at hz
  have hsq :
      D.liftedCoordinate i * z.1 * D.liftedCoordinate j ∈
        (J B) ^ 2 := by
    exact (Submodule.Quotient.mk_eq_zero
      (jacobsonSquareSubmodule (K := K) (B := B))).mp hz
  have hcornerJ :
      D.liftedCoordinate i * z.1 * D.liftedCoordinate j ∈ J B :=
    (J B).mul_mem_right _ ((J B).mul_mem_left _ z.2)
  have hzero :=
    QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.kernelMap_eq_zero_on_jacobson_sq
      D i j f hsq
  have hproject :
      QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.vertexKernelElementOfJacobian
          D i (D.liftedCoordinate i * z.1 * D.liftedCoordinate j) hcornerJ =
        op (D.liftedCoordinate j) •
          QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.vertexKernelElementOfJacobian
            D i z.1 z.2 := by
    apply Subtype.ext
    apply Subtype.ext
    change
      op (D.liftedCoordinate i *
          (D.liftedCoordinate i * z.1 * D.liftedCoordinate j)) =
        op ((D.liftedCoordinate i * z.1) * D.liftedCoordinate j)
    congr 1
    calc
      D.liftedCoordinate i *
            (D.liftedCoordinate i * z.1 * D.liftedCoordinate j) =
          (D.liftedCoordinate i * D.liftedCoordinate i) * z.1 *
            D.liftedCoordinate j := by noncomm_ring
      _ = D.liftedCoordinate i * z.1 * D.liftedCoordinate j := by
        rw [D.liftedCoordinate_complete.idem i]
  change
    f
      (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.vertexKernelElementOfJacobian
        D i z.1 z.2) = 0
  rw [hproject, map_smul] at hzero
  change
    QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateCharacterOp
        D j (op (D.liftedCoordinate j)) * _ = 0 at hzero
  simpa [QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateCharacterOp]
    using hzero

/-- A kernel morphism descends through the restricted Peirce quotient to a
functional on the cotangent corner. -/
noncomputable def cornerDualOfKernelMap
    (i j : Fin 2)
    (f :
      QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.KernelToCoordinateLinearMap
        D i j) :
    Module.Dual K (D.jacobsonCotangentCornerSubmodule i j) := by
  let p := D.cornerCotangentPresentationLinearMap i j
  let g := D.kernelMapOnJacobianLinearMap i j f
  let eRange : LinearMap.range p ≃ₗ[K]
      D.jacobsonCotangentCornerSubmodule i j :=
    LinearEquiv.ofEq _ _ (D.range_cornerCotangentPresentationLinearMap i j)
  exact
    (LinearMap.ker p).liftQ g
        (D.ker_cornerCotangentPresentation_le_ker_kernelMapOnJacobian i j f) ∘ₗ
      p.quotKerEquivRange.symm.toLinearMap ∘ₗ
        eRange.symm.toLinearMap

@[simp]
theorem cornerDualOfKernelMap_cornerCotangentElement
    (i j : Fin 2)
    (f :
      QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.KernelToCoordinateLinearMap
        D i j)
    (z : B) (hz : z ∈ J B) :
    D.cornerDualOfKernelMap i j f (D.cornerCotangentElement i j z hz) =
      f
        (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.vertexKernelElementOfJacobian
          D i z hz) := by
  let p := D.cornerCotangentPresentationLinearMap i j
  let g := D.kernelMapOnJacobianLinearMap i j f
  let eRange : LinearMap.range p ≃ₗ[K]
      D.jacobsonCotangentCornerSubmodule i j :=
    LinearEquiv.ofEq _ _ (D.range_cornerCotangentPresentationLinearMap i j)
  let zJ : (J B : Submodule B B).restrictScalars K := ⟨z, hz⟩
  have hcorner :
      D.cornerCotangentElement i j z hz = eRange (p.rangeRestrict zJ) := by
    apply Subtype.ext
    rfl
  have hker : LinearMap.ker p ≤ LinearMap.ker g :=
    D.ker_cornerCotangentPresentation_le_ker_kernelMapOnJacobian i j f
  rw [hcorner]
  simp only [cornerDualOfKernelMap]
  change
    ((LinearMap.ker p).liftQ g hker)
        (p.quotKerEquivRange.symm
          ⟨p zJ, LinearMap.mem_range_self p zJ⟩) =
      f
        (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.vertexKernelElementOfJacobian
          D i z hz)
  rw [LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

/-- Every module map from the coordinate-projective kernel is induced by a
cotangent-corner functional.  Uniqueness follows by combining this theorem
with `cornerDualToKernelLinearMap_injective`. -/
theorem cornerDualToKernelLinearMap_surjective (i j : Fin 2) :
    Function.Surjective (cornerDualToKernelLinearMap D i j) := by
  intro g
  let f :
      QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.KernelToCoordinateLinearMap
        D i j := g.hom
  let phi := D.cornerDualOfKernelMap i j f
  refine ⟨phi, ?_⟩
  apply ModuleCat.hom_ext
  ext x
  let z : B := unop x.1.1
  have hz : z ∈ J B :=
    QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.unop_mem_jacobson_of_mem_vertexTop_ker
      D i x
  have hvertex :
      QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.vertexKernelElementOfJacobian
          D i z hz = x := by
    apply Subtype.ext
    change
      (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.vertexKernelElementOfJacobian
        D i z hz).1 = x.1
    apply Subtype.ext
    change op (D.liftedCoordinate i * z) = x.1.1
    have hfixed :
        x.1.1 * op (D.liftedCoordinate i) = x.1.1 :=
      QuotientSubmoduleEquidistribution.Tsukamoto.mul_op_eq_self_of_mem_principalRightIdeal
        (D.liftedCoordinate_complete.idem i) x.1.property
    simpa [z] using hfixed
  change
    phi (D.cornerCotangentElement i j z hz) = g.hom x
  rw [D.cornerDualOfKernelMap_cornerCotangentElement i j f z hz, hvertex]
  rfl

/-- Canonical linear equivalence between the dual Peirce cotangent corner and
maps from the corresponding coordinate-projective radical. -/
noncomputable def cornerDualLinearEquivKernelMorphism (i j : Fin 2) :
    Module.Dual K (D.jacobsonCotangentCornerSubmodule i j) ≃ₗ[K]
      ((QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.vertexPresentation
          D i).X₁ ⟶
        QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimple D j) :=
  LinearEquiv.ofBijective (cornerDualToKernelLinearMap D i j)
    ⟨D.cornerDualToKernelLinearMap_injective i j,
      D.cornerDualToKernelLinearMap_surjective i j⟩

/-- Every map from a coordinate projective to a coordinate simple kills the
kernel of the coordinate-top quotient. -/
theorem vertexPresentation_restrict_zero
    [Small.{u} Bᵐᵒᵖ] (i j : Fin 2) :
    ∀ g :
        (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.vertexPresentation
          D i).X₂ ⟶
          QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimple D j,
      (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.vertexPresentation
          D i).f ≫ g = 0 := by
  have hker :=
    QuotientSubmoduleEquidistribution.CoordinateGabrielRealization.CoordinateData.ker_vertexTopLinearMap_eq_jacobson
      D i
  letI : IsSimpleModule Bᵐᵒᵖ
      (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimple D j) :=
    (simple_iff_isSimpleModule'
      (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimple D j)).mp
        (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimple_simple
          D j)
  letI : IsSemisimpleModule Bᵐᵒᵖ
      (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimple D j) :=
    inferInstance
  intro g
  apply ModuleCat.hom_ext
  ext x
  change g.hom x.1 = 0
  have hxRad :
      (x.1 : QuotientSubmoduleEquidistribution.Tsukamoto.principalRightIdeal
          (D.liftedCoordinate i)) ∈
        Module.jacobson Bᵐᵒᵖ
          (QuotientSubmoduleEquidistribution.Tsukamoto.principalRightIdeal
            (D.liftedCoordinate i)) := by
    rw [← hker]
    exact x.property
  have hxKer :
      (x.1 : QuotientSubmoduleEquidistribution.Tsukamoto.principalRightIdeal
          (D.liftedCoordinate i)) ∈ LinearMap.ker g.hom :=
    IsSemisimpleModule.jacobson_le_ker Bᵐᵒᵖ Bᵐᵒᵖ
      (QuotientSubmoduleEquidistribution.Tsukamoto.principalRightIdeal
        (D.liftedCoordinate i))
      (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimple D j)
      g.hom hxRad
  exact hxKer

/-- Dimension shifting for the coordinate projective presentation, retaining
the native `K`-linear structure on degree-one Ext. -/
noncomputable def kernelMorphismLinearEquivCoordinateExt
    [Small.{u} Bᵐᵒᵖ] (i j : Fin 2) :
    ((QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.vertexPresentation
        D i).X₁ ⟶
      QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimple D j) ≃ₗ[K]
      Ext
        (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimple D i)
        (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimple D j)
        1 := by
  let hS :=
    QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.vertexPresentation_shortExact
      D i
  letI : Projective
      (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.vertexPresentation
        D i).X₂ :=
    QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.vertexPresentation_projective_middle
      D i
  exact
    (Ext.linearEquiv₀ (R := K)).symm.trans
      (LinearEquiv.ofBijective
        (hS.extClass.precompOfLinear K
          (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimple D j)
          (add_zero 1))
        (QuotientSubmoduleEquidistribution.ProjectiveRadicalExt.extClass_precomp_bijective_of_projective_middle_of_restrict_zero
          hS (D.vertexPresentation_restrict_zero i j)))

/-- Canonical identification of the dual Peirce cotangent corner with the
degree-one Ext space between the two coordinate simples. -/
noncomputable def cornerDualLinearEquivCoordinateExt
    [Small.{u} Bᵐᵒᵖ] (i j : Fin 2) :
    Module.Dual K (D.jacobsonCotangentCornerSubmodule i j) ≃ₗ[K]
      Ext
        (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimple D i)
        (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimple D j)
        1 :=
  (D.cornerDualLinearEquivKernelMorphism i j).trans
    (D.kernelMorphismLinearEquivCoordinateExt i j)

/-- The dual Peirce corner embeds `K`-linearly into the corresponding
coordinate-simple `Ext¹` space. -/
noncomputable def cornerDualToCoordinateExtLinearMap
    [Small.{u} Bᵐᵒᵖ] (i j : Fin 2) :
    Module.Dual K (D.jacobsonCotangentCornerSubmodule i j) →ₗ[K]
      Ext
        (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimple D i)
        (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimple D j)
        1 :=
  (D.kernelMorphismLinearEquivCoordinateExt i j).toLinearMap.comp
    (cornerDualToKernelLinearMap D i j)

theorem cornerDualToCoordinateExtLinearMap_injective
    [Small.{u} Bᵐᵒᵖ] (i j : Fin 2) :
    Function.Injective (D.cornerDualToCoordinateExtLinearMap i j) :=
  (D.kernelMorphismLinearEquivCoordinateExt i j).injective.comp
    (D.cornerDualToKernelLinearMap_injective i j)

open QuotientSubmoduleEquidistribution.GabrielArrowBridge

variable {kappa : Type v}
  [Small.{u} Bᵐᵒᵖ] [IsNoetherianRing Bᵐᵒᵖ]
  [IsArtinianRing Bᵐᵒᵖ] [Finite kappa]
  (tau : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, v, u} Bᵐᵒᵖ kappa)

/-- Contravariant `K`-linear transport of coordinate `Ext¹` along the
explicit source-simple alignment. -/
noncomputable def coordinateExtOneLinearEquivAlignedSource
    (i j : Fin 2) :
    Ext
        (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimple D i)
        (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimple D j)
        1 ≃ₗ[K]
      Ext
        (ModuleCat.of Bᵐᵒᵖ
          (tau.obj
            ((QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
              D tau i)).1))
        (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimple D j)
        1 := by
  let e :=
    QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIsoAligned
      D tau i
  exact
    { toFun := fun alpha ↦
        (Ext.mk₀ e.inv).comp alpha (zero_add 1)
      invFun := fun beta ↦
        (Ext.mk₀ e.hom).comp beta (zero_add 1)
      left_inv := fun alpha ↦ by
        dsimp only
        rw [Ext.mk₀_comp_mk₀_assoc]
        simp
      right_inv := fun beta ↦ by
        dsimp only
        rw [Ext.mk₀_comp_mk₀_assoc]
        simp
      map_add' := fun alpha beta ↦ by simp
      map_smul' := fun c alpha ↦ by simp }

/-- Covariant `K`-linear transport along the target-simple alignment, after
the source has already been aligned. -/
noncomputable def alignedSourceExtOneLinearEquivAlignedTarget
    (i j : Fin 2) :
    Ext
        (ModuleCat.of Bᵐᵒᵖ
          (tau.obj
            ((QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
              D tau i)).1))
        (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimple D j)
        1 ≃ₗ[K]
      ExtOne tau
        (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
          D tau i)
        (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
          D tau j) := by
  let e :=
    QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIsoAligned
      D tau j
  exact
    { toFun := fun alpha ↦
        alpha.comp (Ext.mk₀ e.hom) (add_zero 1)
      invFun := fun beta ↦
        beta.comp (Ext.mk₀ e.inv) (add_zero 1)
      left_inv := fun alpha ↦ by
        dsimp only
        rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
        simp
      right_inv := fun beta ↦ by
        dsimp only
        rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
        simp
      map_add' := fun alpha beta ↦ by simp
      map_smul' := fun c alpha ↦ by simp }

/-- The maintained coordinate-to-skeleton alignment upgraded from an
additive isomorphism to the `K`-linear equivalence needed for finrank. -/
noncomputable def coordinateExtOneLinearEquivAligned (i j : Fin 2) :
    Ext
        (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimple D i)
        (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimple D j)
        1 ≃ₗ[K]
      ExtOne tau
        (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
          D tau i)
        (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
          D tau j) :=
  (D.coordinateExtOneLinearEquivAlignedSource tau i j).trans
    (D.alignedSourceExtOneLinearEquivAlignedTarget tau i j)

/-- Canonical linear equivalence from the dual Peirce cotangent corner to the
aligned degree-one Ext space. -/
noncomputable def cornerDualLinearEquivAlignedExt (i j : Fin 2) :
    Module.Dual K (D.jacobsonCotangentCornerSubmodule i j) ≃ₗ[K]
      ExtOne tau
        (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
          D tau i)
        (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
          D tau j) :=
  (D.cornerDualLinearEquivCoordinateExt i j).trans
    (D.coordinateExtOneLinearEquivAligned tau i j)

/-- After choosing a basis of the finite-dimensional corner, the corner
itself is linearly equivalent to aligned `Ext¹`.  The preceding dual-corner
equivalence is the canonical, basis-free statement. -/
noncomputable def cornerLinearEquivAlignedExt
    [FiniteDimensional K B] (i j : Fin 2) :
    D.jacobsonCotangentCornerSubmodule i j ≃ₗ[K]
      ExtOne tau
        (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
          D tau i)
        (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
          D tau j) := by
  classical
  exact
    (Module.Basis.ofVectorSpace K
        (D.jacobsonCotangentCornerSubmodule i j)).toDualEquiv.trans
      (D.cornerDualLinearEquivAlignedExt tau i j)

omit [IsArtinianRing Bᵐᵒᵖ] [Finite kappa] in
/-- Exact dimension equality between every Peirce cotangent corner and its
aligned degree-one Ext space. -/
theorem finrank_jacobsonCotangentCornerSubmodule_eq_alignedExt
    (i j : Fin 2) :
    Module.finrank K (D.jacobsonCotangentCornerSubmodule i j) =
      Module.finrank K
        (ExtOne tau
          (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
            D tau i)
          (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
            D tau j)) := by
  calc
    Module.finrank K (D.jacobsonCotangentCornerSubmodule i j) =
        Module.finrank K
          (Module.Dual K (D.jacobsonCotangentCornerSubmodule i j)) := by
      symm
      exact Subspace.dual_finrank_eq
    _ = Module.finrank K
        (ExtOne tau
          (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
            D tau i)
          (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
            D tau j)) :=
      (D.cornerDualLinearEquivAlignedExt tau i j).finrank_eq

omit [IsArtinianRing Bᵐᵒᵖ] [Finite kappa] in
/-- Each Peirce cotangent corner has dimension at most the corresponding
aligned `Ext¹` space. -/
theorem finrank_jacobsonCotangentCornerSubmodule_le_alignedExt
    (i j : Fin 2) :
    Module.finrank K (D.jacobsonCotangentCornerSubmodule i j) ≤
      Module.finrank K
        (ExtOne tau
          (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
            D tau i)
          (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
            D tau j)) :=
  (D.finrank_jacobsonCotangentCornerSubmodule_eq_alignedExt tau i j).le

omit [IsArtinianRing Bᵐᵒᵖ] [Finite kappa] in
/-- The corner-control proposition follows unconditionally from the
dual-corner/Ext equivalence. -/
theorem cotangentCornerFinrankControlledByAlignedExt :
    D.CotangentCornerFinrankControlledByAlignedExt tau := by
  intro i j
  exact (D.finrank_jacobsonCotangentCornerSubmodule_eq_alignedExt tau i j).le

omit [IsArtinianRing Bᵐᵒᵖ] [Finite kappa] in
/-- Automatic loop--two-cycle endpoint: the exact cotangent--Ext comparison
is unconditional, while no-parallelness supplies the multiplicity bounds. -/
theorem cotangentDimensionAtMostThree_of_loopTwoCycleSupport_automatic
    [FiniteDimensional K B]
    (hNoParallel : NoParallelExtSupport (K := K) tau)
    (hShape :
      (D.alignedExtTwoVertexSupport tau hNoParallel).IsLoopTwoCycleAt 0 1) :
    CotangentDimensionAtMostThree (K := K) (B := B) :=
  D.cotangentDimensionAtMostThree_of_loopTwoCycleSupport tau
    (D.cotangentCornerFinrankControlledByAlignedExt tau)
    hNoParallel hShape

end TwoCoordinateData

end QuotientSubmoduleEquidistribution.QuotientSurvival
