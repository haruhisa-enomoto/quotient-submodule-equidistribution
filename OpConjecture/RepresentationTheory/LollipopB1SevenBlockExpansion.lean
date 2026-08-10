import OpConjecture.RepresentationTheory.LollipopB1Modules
import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Expansion of the canonical seven-block live-path representation

This file isolates the basis-expansion half of the live-path
classification.  It starts with seven arbitrary finite-dimensional
multiplicity spaces, forms the canonical block representation, and identifies
its genuine module with a finite biproduct of the seven named modules.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

namespace OpConjecture.LollipopConcrete.B1.ModuleLayer.SevenBlockExpansion

universe u

variable (K : Type u) [Field K]

/-- The seven multiplicity spaces, without any chosen bases. -/
structure MultiplicitySpaces where
  x : FGModuleCat.{u} K
  u : FGModuleCat.{u} K
  w : FGModuleCat.{u} K
  p : FGModuleCat.{u} K
  s1 : FGModuleCat.{u} K
  a : FGModuleCat.{u} K
  s2 : FGModuleCat.{u} K

variable (S : MultiplicitySpaces K)

/-- The common coordinate space for the tops or lowers of the four
length-two blocks. -/
abbrev FourSpace := (((S.x × S.u) × S.w) × S.p)

/-- Source vertex of the canonical seven-block representation.  The first
`FourSpace` contains the loop tops; the second contains their lowers. -/
abbrev NormalVertexOne :=
  FourSpace K S × ((FourSpace K S × S.s1) × S.a)

/-- Target vertex of the canonical seven-block representation. -/
abbrev NormalVertexTwo :=
  (((S.u × S.w) × (S.p × S.p)) × S.a) × S.s2

abbrev normalV1 : FGModuleCat.{u} K :=
  FGModuleCat.of K (NormalVertexOne K S)

abbrev normalV2 : FGModuleCat.{u} K :=
  FGModuleCat.of K (NormalVertexTwo K S)

/-- The loop sends every `X/U/W/P` top coordinate to its lower coordinate
and kills every other coordinate. -/
def normalLoop : normalV1 K S ⟶ normalV1 K S :=
  FGModuleCat.ofHom
    { toFun := fun z => (0, ((z.1, 0), 0))
      map_add' := by intro z w; ext <;> simp
      map_smul' := by intro c z; ext <;> simp }

/-- The stem is live on the `U` lower, `W` top, both `P` coordinates, and
the loop-zero `A` coordinate. -/
def normalStem : normalV1 K S ⟶ normalV2 K S :=
  FGModuleCat.ofHom
    { toFun := fun z =>
        ((((z.2.1.1.1.1.2, z.1.1.2),
            (z.2.1.1.2, z.1.2)),
          z.2.2), 0)
      map_add' := by intro z w; ext <;> simp
      map_smul' := by intro c z; ext <;> simp }

/-- The canonical seven-block live-path representation attached to the
multiplicity spaces. -/
def normalRep : FiniteB1Rep K where
  V₁ := normalV1 K S
  V₂ := normalV2 K S
  loop := normalLoop K S
  stem := normalStem K S
  loop_sq := by intro z; rfl

@[simp] theorem normalLoop_apply (z : NormalVertexOne K S) :
    (normalRep K S).loop.hom.hom z = (0, ((z.1, 0), 0)) := rfl

@[simp] theorem normalStem_apply (z : NormalVertexOne K S) :
    (normalRep K S).stem.hom.hom z =
      ((((z.2.1.1.1.1.2, z.1.1.2),
          (z.2.1.1.2, z.1.2)),
        z.2.2), 0) := rfl

/-! ## Expansion into basis-indexed named blocks -/

inductive BlockTag where
  | s1
  | s2
  | x
  | a
  | u
  | w
  | p
  deriving DecidableEq

instance : Fintype BlockTag where
  elems := {.s1, .s2, .x, .a, .u, .w, .p}
  complete t := by cases t <;> simp

def multiplicitySpace : BlockTag → FGModuleCat.{u} K
  | .s1 => S.s1
  | .s2 => S.s2
  | .x => S.x
  | .a => S.a
  | .u => S.u
  | .w => S.w
  | .p => S.p

def blockMultiplicity (t : BlockTag) : ℕ :=
  Module.finrank K (multiplicitySpace K S t)

abbrev BlockIndex := Σ t : BlockTag, Fin (blockMultiplicity K S t)

def namedBlockData : BlockTag → FiniteB1Rep K
  | .s1 => S1Data K
  | .s2 => S2Data K
  | .x => XData K
  | .a => AData K
  | .u => UData K
  | .w => WData K
  | .p => PData K

abbrev namedBlockCarrier (i : BlockIndex K S) :=
  FiniteB1Rep.Carrier K (namedBlockData (K := K) i.1)

def namedBlockModule (i : BlockIndex K S) : FGModuleCat (B1Model K) :=
  FiniteB1Rep.asFGModule K (namedBlockData (K := K) i.1)

def blockBasisEquiv (t : BlockTag) :
    multiplicitySpace K S t ≃ₗ[K]
      (Fin (blockMultiplicity K S t) → K) :=
  (Module.finBasis K (multiplicitySpace K S t)).equivFun

@[simp] theorem blockBasisEquiv_zero_apply (t : BlockTag)
    (j : Fin (blockMultiplicity K S t)) :
    blockBasisEquiv K S t (0 : multiplicitySpace K S t) j = 0 := by
  rw [map_zero]
  rfl

@[simp] theorem s1BasisEquiv_zero_apply
    (j : Fin (blockMultiplicity K S .s1)) :
    blockBasisEquiv K S .s1 (0 : S.s1) j = 0 := by
  change blockBasisEquiv K S .s1
    (0 : multiplicitySpace K S .s1) j = 0
  rw [map_zero]
  rfl

@[simp] theorem s2BasisEquiv_zero_apply
    (j : Fin (blockMultiplicity K S .s2)) :
    blockBasisEquiv K S .s2 (0 : S.s2) j = 0 := by
  change blockBasisEquiv K S .s2
    (0 : multiplicitySpace K S .s2) j = 0
  rw [map_zero]
  rfl

@[simp] theorem xBasisEquiv_zero_apply
    (j : Fin (blockMultiplicity K S .x)) :
    blockBasisEquiv K S .x (0 : S.x) j = 0 := by
  change blockBasisEquiv K S .x
    (0 : multiplicitySpace K S .x) j = 0
  rw [map_zero]
  rfl

@[simp] theorem aBasisEquiv_zero_apply
    (j : Fin (blockMultiplicity K S .a)) :
    blockBasisEquiv K S .a (0 : S.a) j = 0 := by
  change blockBasisEquiv K S .a
    (0 : multiplicitySpace K S .a) j = 0
  rw [map_zero]
  rfl

@[simp] theorem uBasisEquiv_zero_apply
    (j : Fin (blockMultiplicity K S .u)) :
    blockBasisEquiv K S .u (0 : S.u) j = 0 := by
  change blockBasisEquiv K S .u
    (0 : multiplicitySpace K S .u) j = 0
  rw [map_zero]
  rfl

@[simp] theorem wBasisEquiv_zero_apply
    (j : Fin (blockMultiplicity K S .w)) :
    blockBasisEquiv K S .w (0 : S.w) j = 0 := by
  change blockBasisEquiv K S .w
    (0 : multiplicitySpace K S .w) j = 0
  rw [map_zero]
  rfl

@[simp] theorem pBasisEquiv_zero_apply
    (j : Fin (blockMultiplicity K S .p)) :
    blockBasisEquiv K S .p (0 : S.p) j = 0 := by
  change blockBasisEquiv K S .p
    (0 : multiplicitySpace K S .p) j = 0
  rw [map_zero]
  rfl

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

@[simp] theorem carrier_fst_add (E : FiniteB1Rep K)
    (v w : FiniteB1Rep.Carrier K E) :
    FiniteB1Rep.fst K E (v + w) =
      FiniteB1Rep.fst K E v + FiniteB1Rep.fst K E w := rfl

@[simp] theorem carrier_snd_add (E : FiniteB1Rep K)
    (v w : FiniteB1Rep.Carrier K E) :
    FiniteB1Rep.snd K E (v + w) =
      FiniteB1Rep.snd K E v + FiniteB1Rep.snd K E w := rfl

@[simp] theorem carrier_fst_smul (E : FiniteB1Rep K)
    (c : K) (v : FiniteB1Rep.Carrier K E) :
    FiniteB1Rep.fst K E (c • v) =
      c • FiniteB1Rep.fst K E v := rfl

@[simp] theorem carrier_snd_smul (E : FiniteB1Rep K)
    (c : K) (v : FiniteB1Rep.Carrier K E) :
    FiniteB1Rep.snd K E (c • v) =
      c • FiniteB1Rep.snd K E v := rfl

@[simp] theorem carrier_fst_mk (E : FiniteB1Rep K)
    (v₁ : E.V₁) (v₂ : E.V₂) :
    FiniteB1Rep.fst K E
      ((v₁, v₂) : FiniteB1Rep.Carrier K E) = v₁ := rfl

@[simp] theorem carrier_snd_mk (E : FiniteB1Rep K)
    (v₁ : E.V₁) (v₂ : E.V₂) :
    FiniteB1Rep.snd K E
      ((v₁, v₂) : FiniteB1Rep.Carrier K E) = v₂ := rfl

@[simp] theorem carrier_fst_apply (E : FiniteB1Rep K)
    (v : FiniteB1Rep.Carrier K E) :
    FiniteB1Rep.fst K E v = v.1 := rfl

@[simp] theorem carrier_snd_apply (E : FiniteB1Rep K)
    (v : FiniteB1Rep.Carrier K E) :
    FiniteB1Rep.snd K E v = v.2 := rfl

@[simp] theorem normal_v1_fst_add (v w : NormalVertexOne K S) :
    (v + w).1 = v.1 + w.1 := rfl

@[simp] theorem normal_v1_snd_add (v w : NormalVertexOne K S) :
    (v + w).2 = v.2 + w.2 := rfl

@[simp] theorem normal_v2_fst_add (v w : NormalVertexTwo K S) :
    (v + w).1 = v.1 + w.1 := rfl

@[simp] theorem normal_v2_snd_add (v w : NormalVertexTwo K S) :
    (v + w).2 = v.2 + w.2 := rfl

@[simp] theorem normal_v1_fst_smul (c : K) (v : NormalVertexOne K S) :
    (c • v).1 = c • v.1 := rfl

@[simp] theorem normal_v1_snd_smul (c : K) (v : NormalVertexOne K S) :
    (c • v).2 = c • v.2 := rfl

@[simp] theorem normal_v2_fst_smul (c : K) (v : NormalVertexTwo K S) :
    (c • v).1 = c • v.1 := rfl

@[simp] theorem normal_v2_snd_smul (c : K) (v : NormalVertexTwo K S) :
    (c • v).2 = c • v.2 := rfl

@[simp] theorem normal_v1_zero_eq :
    (0 : (normalRep K S).V₁) =
      ((0, 0) : NormalVertexOne K S) := rfl

@[simp] theorem normal_v2_zero_eq :
    (0 : (normalRep K S).V₂) =
      ((0, 0) : NormalVertexTwo K S) := rfl

theorem rep_v1_zero_add (E : FiniteB1Rep K) :
    (0 : E.V₁) + 0 = 0 := zero_add 0

theorem rep_v2_zero_add (E : FiniteB1Rep K) :
    (0 : E.V₂) + 0 = 0 := zero_add 0

theorem rep_v1_smul_zero (E : FiniteB1Rep K) (c : K) :
    c • (0 : E.V₁) = 0 := smul_zero c

theorem rep_v2_smul_zero (E : FiniteB1Rep K) (c : K) :
    c • (0 : E.V₂) = 0 := smul_zero c

@[simp] theorem S1_loop_apply (z : (S1Data K).V₁) :
    (S1Data K).loop.hom.hom z = 0 := rfl

@[simp] theorem S2_loop_apply (z : (S2Data K).V₁) :
    (S2Data K).loop.hom.hom z = 0 := rfl

@[simp] theorem X_loop_apply (z : (XData K).V₁) :
    (XData K).loop.hom.hom z = (0, z.1) := rfl

@[simp] theorem A_loop_apply (z : (AData K).V₁) :
    (AData K).loop.hom.hom z = 0 := rfl

@[simp] theorem U_loop_apply (z : (UData K).V₁) :
    (UData K).loop.hom.hom z = (0, z.1) := rfl

@[simp] theorem W_loop_apply (z : (WData K).V₁) :
    (WData K).loop.hom.hom z = (0, z.1) := rfl

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

@[simp] theorem U_stem_apply (z : (UData K).V₁) :
    (UData K).stem.hom.hom z = z.2 := rfl

@[simp] theorem W_stem_apply (z : (WData K).V₁) :
    (WData K).stem.hom.hom z = z.1 := rfl

@[simp] theorem P_stem_apply (z : (PData K).V₁) :
    (PData K).stem.hom.hom z = z := rfl

/-! The following named linear projections avoid transparency problems caused
by the separately derived module structure on `FiniteB1Rep.Carrier`. -/

def carrierV1Linear :
    FiniteB1Rep.Carrier K (normalRep K S) →ₗ[K] NormalVertexOne K S where
  toFun := FiniteB1Rep.fst K (normalRep K S)
  map_add' := carrier_fst_add K (normalRep K S)
  map_smul' := carrier_fst_smul K (normalRep K S)

def carrierV2Linear :
    FiniteB1Rep.Carrier K (normalRep K S) →ₗ[K] NormalVertexTwo K S where
  toFun := FiniteB1Rep.snd K (normalRep K S)
  map_add' := carrier_snd_add K (normalRep K S)
  map_smul' := carrier_snd_smul K (normalRep K S)

def normalV1TopLinear : NormalVertexOne K S →ₗ[K] FourSpace K S where
  toFun := Prod.fst
  map_add' := normal_v1_fst_add K S
  map_smul' := normal_v1_fst_smul K S

def normalV1RestLinear :
    NormalVertexOne K S →ₗ[K] ((FourSpace K S × S.s1) × S.a) where
  toFun := Prod.snd
  map_add' := normal_v1_snd_add K S
  map_smul' := normal_v1_snd_smul K S

abbrev NormalStemCoords :=
  ((S.u × S.w) × (S.p × S.p)) × S.a

def normalV2StemLinear :
    NormalVertexTwo K S →ₗ[K] NormalStemCoords K S where
  toFun := Prod.fst
  map_add' := normal_v2_fst_add K S
  map_smul' := normal_v2_fst_smul K S

def normalV2TailLinear : NormalVertexTwo K S →ₗ[K] S.s2 where
  toFun := Prod.snd
  map_add' := normal_v2_snd_add K S
  map_smul' := normal_v2_snd_smul K S

def fourXLinear : FourSpace K S →ₗ[K] S.x :=
  (LinearMap.fst K S.x S.u).comp
    ((LinearMap.fst K (S.x × S.u) S.w).comp
      (LinearMap.fst K ((S.x × S.u) × S.w) S.p))

def fourULinear : FourSpace K S →ₗ[K] S.u :=
  (LinearMap.snd K S.x S.u).comp
    ((LinearMap.fst K (S.x × S.u) S.w).comp
      (LinearMap.fst K ((S.x × S.u) × S.w) S.p))

def fourWLinear : FourSpace K S →ₗ[K] S.w :=
  (LinearMap.snd K (S.x × S.u) S.w).comp
    (LinearMap.fst K ((S.x × S.u) × S.w) S.p)

def fourPLinear : FourSpace K S →ₗ[K] S.p :=
  LinearMap.snd K ((S.x × S.u) × S.w) S.p

def topFourLinear :
    FiniteB1Rep.Carrier K (normalRep K S) →ₗ[K] FourSpace K S :=
  (normalV1TopLinear K S).comp (carrierV1Linear K S)

def lowerFourLinear :
    FiniteB1Rep.Carrier K (normalRep K S) →ₗ[K] FourSpace K S :=
  (LinearMap.fst K (FourSpace K S) S.s1).comp
    ((LinearMap.fst K (FourSpace K S × S.s1) S.a).comp
      ((normalV1RestLinear K S).comp (carrierV1Linear K S)))

def s1Linear :
    FiniteB1Rep.Carrier K (normalRep K S) →ₗ[K] S.s1 :=
  (LinearMap.snd K (FourSpace K S) S.s1).comp
    ((LinearMap.fst K (FourSpace K S × S.s1) S.a).comp
      ((normalV1RestLinear K S).comp (carrierV1Linear K S)))

def aOneLinear :
    FiniteB1Rep.Carrier K (normalRep K S) →ₗ[K] S.a :=
  (LinearMap.snd K (FourSpace K S × S.s1) S.a).comp
    ((normalV1RestLinear K S).comp (carrierV1Linear K S))

def stemCoordsLinear :
    FiniteB1Rep.Carrier K (normalRep K S) →ₗ[K] NormalStemCoords K S :=
  (normalV2StemLinear K S).comp (carrierV2Linear K S)

def uTailLinear :
    FiniteB1Rep.Carrier K (normalRep K S) →ₗ[K] S.u :=
  (LinearMap.fst K S.u S.w).comp
    ((LinearMap.fst K (S.u × S.w) (S.p × S.p)).comp
      ((LinearMap.fst K ((S.u × S.w) × (S.p × S.p)) S.a).comp
        (stemCoordsLinear K S)))

def wTailLinear :
    FiniteB1Rep.Carrier K (normalRep K S) →ₗ[K] S.w :=
  (LinearMap.snd K S.u S.w).comp
    ((LinearMap.fst K (S.u × S.w) (S.p × S.p)).comp
      ((LinearMap.fst K ((S.u × S.w) × (S.p × S.p)) S.a).comp
        (stemCoordsLinear K S)))

def pTopTailLinear :
    FiniteB1Rep.Carrier K (normalRep K S) →ₗ[K] S.p :=
  (LinearMap.snd K S.p S.p).comp
    ((LinearMap.snd K (S.u × S.w) (S.p × S.p)).comp
      ((LinearMap.fst K ((S.u × S.w) × (S.p × S.p)) S.a).comp
        (stemCoordsLinear K S)))

def pLowerTailLinear :
    FiniteB1Rep.Carrier K (normalRep K S) →ₗ[K] S.p :=
  (LinearMap.fst K S.p S.p).comp
    ((LinearMap.snd K (S.u × S.w) (S.p × S.p)).comp
      ((LinearMap.fst K ((S.u × S.w) × (S.p × S.p)) S.a).comp
        (stemCoordsLinear K S)))

def aTwoLinear :
    FiniteB1Rep.Carrier K (normalRep K S) →ₗ[K] S.a :=
  (LinearMap.snd K ((S.u × S.w) × (S.p × S.p)) S.a).comp
    (stemCoordsLinear K S)

def s2Linear :
    FiniteB1Rep.Carrier K (normalRep K S) →ₗ[K] S.s2 :=
  (normalV2TailLinear K S).comp (carrierV2Linear K S)

def basisCoord (t : BlockTag) (j : Fin (blockMultiplicity K S t)) :
    multiplicitySpace K S t →ₗ[K] K :=
  (LinearMap.proj j).comp (blockBasisEquiv K S t).toLinearMap

def blockComponent (i : BlockIndex K S) :
    FiniteB1Rep.Carrier K (normalRep K S) →ₗ[K]
      namedBlockCarrier K S i := by
  rcases i with ⟨t, j⟩
  cases t with
  | s1 =>
      exact ((basisCoord K S .s1 j).comp (s1Linear K S)).prod 0
  | s2 =>
      exact (0 : FiniteB1Rep.Carrier K (normalRep K S) →ₗ[K]
        (Fin 0 → K)).prod
          ((basisCoord K S .s2 j).comp (s2Linear K S))
  | x =>
      exact (((basisCoord K S .x j).comp
          ((fourXLinear K S).comp (topFourLinear K S))).prod
        ((basisCoord K S .x j).comp
          ((fourXLinear K S).comp (lowerFourLinear K S)))).prod 0
  | a =>
      exact ((basisCoord K S .a j).comp (aOneLinear K S)).prod
        ((basisCoord K S .a j).comp (aTwoLinear K S))
  | u =>
      exact (((basisCoord K S .u j).comp
          ((fourULinear K S).comp (topFourLinear K S))).prod
        ((basisCoord K S .u j).comp
          ((fourULinear K S).comp (lowerFourLinear K S)))).prod
        ((basisCoord K S .u j).comp (uTailLinear K S))
  | w =>
      exact (((basisCoord K S .w j).comp
          ((fourWLinear K S).comp (topFourLinear K S))).prod
        ((basisCoord K S .w j).comp
          ((fourWLinear K S).comp (lowerFourLinear K S)))).prod
        ((basisCoord K S .w j).comp (wTailLinear K S))
  | p =>
      exact (((basisCoord K S .p j).comp
          ((fourPLinear K S).comp (topFourLinear K S))).prod
        ((basisCoord K S .p j).comp
          ((fourPLinear K S).comp (lowerFourLinear K S)))).prod
        (((basisCoord K S .p j).comp (pTopTailLinear K S)).prod
          ((basisCoord K S .p j).comp (pLowerTailLinear K S)))

/-- Read the canonical normal-form coordinates one basis coefficient at a
time as a family of the seven named modules. -/
def normalToBlockPi :
    FiniteB1Rep.Carrier K (normalRep K S) →ₗ[K]
      (∀ i, namedBlockCarrier K S i) :=
  LinearMap.pi (blockComponent K S)

@[simp] theorem blockComponent_s1_apply
    (j : Fin (blockMultiplicity K S .s1))
    (v : FiniteB1Rep.Carrier K (normalRep K S)) :
    blockComponent K S ⟨.s1, j⟩ v =
      (blockBasisEquiv K S .s1
        (FiniteB1Rep.fst K (normalRep K S) v).2.1.2 j, 0) := rfl

@[simp] theorem blockComponent_s2_apply
    (j : Fin (blockMultiplicity K S .s2))
    (v : FiniteB1Rep.Carrier K (normalRep K S)) :
    blockComponent K S ⟨.s2, j⟩ v =
      (0, blockBasisEquiv K S .s2
        (FiniteB1Rep.snd K (normalRep K S) v).2 j) := rfl

@[simp] theorem blockComponent_x_apply
    (j : Fin (blockMultiplicity K S .x))
    (v : FiniteB1Rep.Carrier K (normalRep K S)) :
    blockComponent K S ⟨.x, j⟩ v =
      ((blockBasisEquiv K S .x
          (FiniteB1Rep.fst K (normalRep K S) v).1.1.1.1 j,
        blockBasisEquiv K S .x
          (FiniteB1Rep.fst K (normalRep K S) v).2.1.1.1.1.1 j), 0) := rfl

@[simp] theorem blockComponent_a_apply
    (j : Fin (blockMultiplicity K S .a))
    (v : FiniteB1Rep.Carrier K (normalRep K S)) :
    blockComponent K S ⟨.a, j⟩ v =
      (blockBasisEquiv K S .a
          (FiniteB1Rep.fst K (normalRep K S) v).2.2 j,
        blockBasisEquiv K S .a
          (FiniteB1Rep.snd K (normalRep K S) v).1.2 j) := rfl

@[simp] theorem blockComponent_u_apply
    (j : Fin (blockMultiplicity K S .u))
    (v : FiniteB1Rep.Carrier K (normalRep K S)) :
    blockComponent K S ⟨.u, j⟩ v =
      ((blockBasisEquiv K S .u
          (FiniteB1Rep.fst K (normalRep K S) v).1.1.1.2 j,
        blockBasisEquiv K S .u
          (FiniteB1Rep.fst K (normalRep K S) v).2.1.1.1.1.2 j),
        blockBasisEquiv K S .u
          (FiniteB1Rep.snd K (normalRep K S) v).1.1.1.1 j) := rfl

@[simp] theorem blockComponent_w_apply
    (j : Fin (blockMultiplicity K S .w))
    (v : FiniteB1Rep.Carrier K (normalRep K S)) :
    blockComponent K S ⟨.w, j⟩ v =
      ((blockBasisEquiv K S .w
          (FiniteB1Rep.fst K (normalRep K S) v).1.1.2 j,
        blockBasisEquiv K S .w
          (FiniteB1Rep.fst K (normalRep K S) v).2.1.1.1.2 j),
        blockBasisEquiv K S .w
          (FiniteB1Rep.snd K (normalRep K S) v).1.1.1.2 j) := rfl

@[simp] theorem blockComponent_p_apply
    (j : Fin (blockMultiplicity K S .p))
    (v : FiniteB1Rep.Carrier K (normalRep K S)) :
    blockComponent K S ⟨.p, j⟩ v =
      ((blockBasisEquiv K S .p
          (FiniteB1Rep.fst K (normalRep K S) v).1.2 j,
        blockBasisEquiv K S .p
          (FiniteB1Rep.fst K (normalRep K S) v).2.1.1.2 j),
        (blockBasisEquiv K S .p
            (FiniteB1Rep.snd K (normalRep K S) v).1.1.2.2 j,
          blockBasisEquiv K S .p
            (FiniteB1Rep.snd K (normalRep K S) v).1.1.2.1 j)) := rfl

/-- Reassemble the seven multiplicity-space coordinates from a family of
named block coordinates. -/
def blockPiToNormal (g : ∀ i, namedBlockCarrier K S i) :
    FiniteB1Rep.Carrier K (normalRep K S) := by
  let xTop := (blockBasisEquiv K S .x).symm (fun j =>
    (FiniteB1Rep.fst K (namedBlockData (K := K) .x)
      (g ⟨.x, j⟩)).1)
  let uTop := (blockBasisEquiv K S .u).symm (fun j =>
    (FiniteB1Rep.fst K (namedBlockData (K := K) .u)
      (g ⟨.u, j⟩)).1)
  let wTop := (blockBasisEquiv K S .w).symm (fun j =>
    (FiniteB1Rep.fst K (namedBlockData (K := K) .w)
      (g ⟨.w, j⟩)).1)
  let pTop := (blockBasisEquiv K S .p).symm (fun j =>
    (FiniteB1Rep.fst K (namedBlockData (K := K) .p)
      (g ⟨.p, j⟩)).1)
  let xLower := (blockBasisEquiv K S .x).symm (fun j =>
    (FiniteB1Rep.fst K (namedBlockData (K := K) .x)
      (g ⟨.x, j⟩)).2)
  let uLower := (blockBasisEquiv K S .u).symm (fun j =>
    (FiniteB1Rep.fst K (namedBlockData (K := K) .u)
      (g ⟨.u, j⟩)).2)
  let wLower := (blockBasisEquiv K S .w).symm (fun j =>
    (FiniteB1Rep.fst K (namedBlockData (K := K) .w)
      (g ⟨.w, j⟩)).2)
  let pLower := (blockBasisEquiv K S .p).symm (fun j =>
    (FiniteB1Rep.fst K (namedBlockData (K := K) .p)
      (g ⟨.p, j⟩)).2)
  let s1 := (blockBasisEquiv K S .s1).symm (fun j =>
    FiniteB1Rep.fst K (namedBlockData (K := K) .s1)
      (g ⟨.s1, j⟩))
  let aOne := (blockBasisEquiv K S .a).symm (fun j =>
    FiniteB1Rep.fst K (namedBlockData (K := K) .a)
      (g ⟨.a, j⟩))
  let uTail := (blockBasisEquiv K S .u).symm (fun j =>
    FiniteB1Rep.snd K (namedBlockData (K := K) .u)
      (g ⟨.u, j⟩))
  let wTail := (blockBasisEquiv K S .w).symm (fun j =>
    FiniteB1Rep.snd K (namedBlockData (K := K) .w)
      (g ⟨.w, j⟩))
  let pTopTail := (blockBasisEquiv K S .p).symm (fun j =>
    (FiniteB1Rep.snd K (namedBlockData (K := K) .p)
      (g ⟨.p, j⟩)).1)
  let pLowerTail := (blockBasisEquiv K S .p).symm (fun j =>
    (FiniteB1Rep.snd K (namedBlockData (K := K) .p)
      (g ⟨.p, j⟩)).2)
  let aTwo := (blockBasisEquiv K S .a).symm (fun j =>
    FiniteB1Rep.snd K (namedBlockData (K := K) .a)
      (g ⟨.a, j⟩))
  let s2 := (blockBasisEquiv K S .s2).symm (fun j =>
    FiniteB1Rep.snd K (namedBlockData (K := K) .s2)
      (g ⟨.s2, j⟩))
  exact
    (((((xTop, uTop), wTop), pTop),
      (((((xLower, uLower), wLower), pLower), s1), aOne)),
      ((((uTail, wTail), (pLowerTail, pTopTail)), aTwo), s2))

theorem blockPiToNormal_normalToBlockPi
    (v : FiniteB1Rep.Carrier K (normalRep K S)) :
    blockPiToNormal K S (normalToBlockPi K S v) = v := by
  apply FiniteB1Rep.carrier_ext K (normalRep K S)
  · simp [blockPiToNormal, normalToBlockPi, FiniteB1Rep.fst]
  · simp [blockPiToNormal, normalToBlockPi, FiniteB1Rep.snd]

theorem normalToBlockPi_blockPiToNormal
    (g : ∀ i, namedBlockCarrier K S i) :
    normalToBlockPi K S (blockPiToNormal K S g) = g := by
  funext i
  rcases i with ⟨t, j⟩
  cases t <;>
    apply FiniteB1Rep.carrier_ext K _ <;>
    simp [blockPiToNormal, normalToBlockPi, namedBlockData,
      FiniteB1Rep.fst, FiniteB1Rep.snd]
  all_goals apply Subsingleton.elim

def normalBlockLinearEquiv :
    FiniteB1Rep.Carrier K (normalRep K S) ≃ₗ[K]
      (∀ i, namedBlockCarrier K S i) :=
  LinearEquiv.ofBijective (normalToBlockPi K S)
    ⟨fun v w h => by
        rw [← blockPiToNormal_normalToBlockPi K S v,
          ← blockPiToNormal_normalToBlockPi K S w, h],
      fun g => ⟨blockPiToNormal K S g,
        normalToBlockPi_blockPiToNormal K S g⟩⟩

/-! ## Genuine-module linearity and the biproduct endpoint -/

/-- Coordinate expansion in the five distinguished algebra generators. -/
theorem algebra_coordinate_decomposition (r : B1Model K) :
    r = (TrivSqZeroExt.fst r).1.fst • e1 K +
      (TrivSqZeroExt.fst r).2 • e2 K +
      (TrivSqZeroExt.fst r).1.snd • x K +
      (TrivSqZeroExt.snd r).fst • a K +
      (TrivSqZeroExt.snd r).snd • u K := by
  ext <;> simp [e1, e2, x, a, u]

theorem normalToBlockPi_e1
    (v : FiniteB1Rep.Carrier K (normalRep K S)) :
    normalToBlockPi K S (e1 K • v) =
      e1 K • normalToBlockPi K S v := by
  funext i
  change normalToBlockPi K S (e1 K • v) i =
    e1 K • normalToBlockPi K S v i
  rw [FiniteB1Rep.e1_smul, FiniteB1Rep.e1_smul]
  rcases i with ⟨t, j⟩
  cases t <;>
    simp [normalToBlockPi, normal_v2_zero_eq,
      namedBlockData, FiniteB1Rep.fst, FiniteB1Rep.snd] <;> rfl

theorem normalToBlockPi_e2
    (v : FiniteB1Rep.Carrier K (normalRep K S)) :
    normalToBlockPi K S (e2 K • v) =
      e2 K • normalToBlockPi K S v := by
  funext i
  change normalToBlockPi K S (e2 K • v) i =
    e2 K • normalToBlockPi K S v i
  rw [FiniteB1Rep.e2_smul, FiniteB1Rep.e2_smul]
  rcases i with ⟨t, j⟩
  cases t <;>
    simp [normalToBlockPi, normal_v1_zero_eq,
      namedBlockData, FiniteB1Rep.fst, FiniteB1Rep.snd] <;> rfl

theorem normalToBlockPi_x
    (v : FiniteB1Rep.Carrier K (normalRep K S)) :
    normalToBlockPi K S (x K • v) =
      x K • normalToBlockPi K S v := by
  funext i
  change normalToBlockPi K S (x K • v) i =
    x K • normalToBlockPi K S v i
  rw [FiniteB1Rep.x_smul]
  change normalToBlockPi K S (normalLoop K S v.1, 0) i =
    x K • normalToBlockPi K S v i
  rw [FiniteB1Rep.x_smul]
  rcases i with ⟨t, j⟩
  cases t <;>
    simp [normalToBlockPi, normalLoop, normal_v2_zero_eq,
      namedBlockData, jordan, FiniteB1Rep.fst,
      FiniteB1Rep.snd] <;> rfl

theorem normalToBlockPi_a
    (v : FiniteB1Rep.Carrier K (normalRep K S)) :
    normalToBlockPi K S (a K • v) =
      a K • normalToBlockPi K S v := by
  funext i
  change normalToBlockPi K S (a K • v) i =
    a K • normalToBlockPi K S v i
  rw [FiniteB1Rep.a_smul]
  change normalToBlockPi K S (0, normalStem K S v.1) i =
    a K • normalToBlockPi K S v i
  rw [FiniteB1Rep.a_smul]
  rcases i with ⟨t, j⟩
  cases t <;>
    simp [normalToBlockPi, normalStem, normal_v1_zero_eq,
      namedBlockData, firstStem, secondStem,
      FiniteB1Rep.fst, FiniteB1Rep.snd] <;> rfl

theorem normalToBlockPi_u
    (v : FiniteB1Rep.Carrier K (normalRep K S)) :
    normalToBlockPi K S (u K • v) =
      u K • normalToBlockPi K S v := by
  rw [← a_mul_x]
  simp only [mul_smul]
  rw [normalToBlockPi_a K S, normalToBlockPi_x K S]

theorem normalToBlockPi_smul (r : B1Model K)
    (v : FiniteB1Rep.Carrier K (normalRep K S)) :
    normalToBlockPi K S (r • v) =
      r • normalToBlockPi K S v := by
  rw [algebra_coordinate_decomposition K r]
  simp only [add_smul, IsScalarTower.smul_assoc, map_add, map_smul]
  rw [normalToBlockPi_e1 K S, normalToBlockPi_e2 K S,
    normalToBlockPi_x K S, normalToBlockPi_a K S,
    normalToBlockPi_u K S]

def normalBlockModuleLinearEquiv :
    FiniteB1Rep.Carrier K (normalRep K S) ≃ₗ[B1Model K]
      (∀ i, namedBlockCarrier K S i) :=
  LinearEquiv.ofBijective
    { toFun := normalToBlockPi K S
      map_add' := (normalToBlockPi K S).map_add
      map_smul' := normalToBlockPi_smul K S }
    (normalBlockLinearEquiv K S).bijective

def normalBlockPiModuleIso :
    FiniteB1Rep.asFGModule K (normalRep K S) ≅
      FGModuleCat.of (B1Model K)
        (∀ i, namedBlockCarrier K S i) :=
  (normalBlockModuleLinearEquiv K S).toFGModuleCatIso

/-- The canonical normal representation is a finite biproduct of the seven
named live-path modules, one copy for every basis vector of its multiplicity
space. -/
def normalNamedBiproductIso :
    FiniteB1Rep.asFGModule K (normalRep K S) ≅
      biproduct (namedBlockModule K S) :=
  normalBlockPiModuleIso K S ≪≫
    (biproductIsoPiFG (namedBlockModule K S)).symm

end OpConjecture.LollipopConcrete.B1.ModuleLayer.SevenBlockExpansion
