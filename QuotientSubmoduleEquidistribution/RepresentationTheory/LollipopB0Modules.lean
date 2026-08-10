import QuotientSubmoduleEquidistribution.RepresentationTheory.LollipopB0AlgebraModel
import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.LinearAlgebra.Prod

/-!
# Genuine finitely generated modules for the dead-path lollipop

This file turns a finite pair of vector spaces with maps
`L : V₁ → V₁`, `T : V₁ → V₂` satisfying `L² = 0` and `T L = 0`
into a left module over the tracked square-zero algebra `B0Model K`.
-/

noncomputable section

open CategoryTheory
open scoped RightActions

namespace QuotientSubmoduleEquidistribution.LollipopConcrete.ModuleLayer

universe u

variable (K : Type u) [Field K]

variable (V₁ V₂ : Type u)
variable [AddCommGroup V₁] [Module K V₁]
variable [AddCommGroup V₂] [Module K V₂]

/-- The two vertex coordinates act diagonally on `V₁ × V₂`. -/
def vertexAction : VertexAlgebra K →ₐ[K] Module.End K (V₁ × V₂) where
  toFun r :=
    { toFun := fun v => (r.1 • v.1, r.2 • v.2)
      map_add' := by
        intro v w
        ext <;> simp
      map_smul' := by
        intro c v
        ext <;> simp [smul_smul, mul_comm] }
  map_one' := by
    apply LinearMap.ext
    intro v
    ext <;> simp
  map_mul' := by
    intro r s
    apply LinearMap.ext
    intro v
    ext <;> simp [smul_smul]
  map_zero' := by
    apply LinearMap.ext
    intro v
    ext <;> simp
  map_add' := by
    intro r s
    apply LinearMap.ext
    intro v
    ext <;> simp [add_smul]
  commutes' := by
    intro c
    apply LinearMap.ext
    intro v
    ext <;> simp

/-- The radical coordinates act through the loop and stem maps. -/
def radicalAction (loop : V₁ →ₗ[K] V₁) (stem : V₁ →ₗ[K] V₂) :
    B0Radical K →ₗ[K] Module.End K (V₁ × V₂) where
  toFun m :=
    { toFun := fun v => (m.x • loop v.1, m.a • stem v.1)
      map_add' := by
        intro v w
        ext <;> simp
      map_smul' := by
        intro c v
        ext <;> simp [smul_smul, mul_comm] }
  map_add' := by
    intro m n
    apply LinearMap.ext
    intro v
    ext <;> simp [add_smul]
  map_smul' := by
    intro c m
    apply LinearMap.ext
    intro v
    ext <;> simp [smul_smul]

theorem radicalAction_mul_eq_zero
    (loop : V₁ →ₗ[K] V₁) (stem : V₁ →ₗ[K] V₂)
    (hloop : ∀ v, loop (loop v) = 0) (hstem : ∀ v, stem (loop v) = 0)
    (m n : B0Radical K) :
    radicalAction K V₁ V₂ loop stem m * radicalAction K V₁ V₂ loop stem n = 0 := by
  apply LinearMap.ext
  intro v
  ext
  · simp [radicalAction, hloop, smul_smul]
  · simp [radicalAction, hstem, smul_smul]

theorem radicalAction_left_compat
    (loop : V₁ →ₗ[K] V₁) (stem : V₁ →ₗ[K] V₂)
    (r : VertexAlgebra K) (m : B0Radical K) :
    radicalAction K V₁ V₂ loop stem (r • m) =
      vertexAction K V₁ V₂ r * radicalAction K V₁ V₂ loop stem m := by
  apply LinearMap.ext
  intro v
  ext <;> simp [radicalAction, vertexAction, smul_smul]

theorem radicalAction_right_compat
    (loop : V₁ →ₗ[K] V₁) (stem : V₁ →ₗ[K] V₂)
    (r : VertexAlgebra K) (m : B0Radical K) :
    radicalAction K V₁ V₂ loop stem (MulOpposite.op r • m) =
      radicalAction K V₁ V₂ loop stem m * vertexAction K V₁ V₂ r := by
  apply LinearMap.ext
  intro v
  ext <;> simp [radicalAction, vertexAction, smul_smul, mul_comm]

/-- The algebra action attached to a pair `(loop, stem)` satisfying the dead-path relations. -/
def b0Action
    (loop : V₁ →ₗ[K] V₁) (stem : V₁ →ₗ[K] V₂)
    (hloop : ∀ v, loop (loop v) = 0) (hstem : ∀ v, stem (loop v) = 0) :
    B0Model K →ₐ[K] Module.End K (V₁ × V₂) :=
  TrivSqZeroExt.lift
    (vertexAction K V₁ V₂)
    (radicalAction K V₁ V₂ loop stem)
    (radicalAction_mul_eq_zero K V₁ V₂ loop stem hloop hstem)
    (radicalAction_left_compat K V₁ V₂ loop stem)
    (radicalAction_right_compat K V₁ V₂ loop stem)

theorem b0Action_e1
    (loop : V₁ →ₗ[K] V₁) (stem : V₁ →ₗ[K] V₂)
    (hloop : ∀ v, loop (loop v) = 0) (hstem : ∀ v, stem (loop v) = 0)
    (v : V₁ × V₂) :
    b0Action K V₁ V₂ loop stem hloop hstem (e1 K) v = (v.1, 0) := by
  unfold b0Action e1
  rw [TrivSqZeroExt.lift_apply_inl]
  simp [vertexAction]

theorem b0Action_e2
    (loop : V₁ →ₗ[K] V₁) (stem : V₁ →ₗ[K] V₂)
    (hloop : ∀ v, loop (loop v) = 0) (hstem : ∀ v, stem (loop v) = 0)
    (v : V₁ × V₂) :
    b0Action K V₁ V₂ loop stem hloop hstem (e2 K) v = (0, v.2) := by
  unfold b0Action e2
  rw [TrivSqZeroExt.lift_apply_inl]
  simp [vertexAction]

theorem b0Action_a
    (loop : V₁ →ₗ[K] V₁) (stem : V₁ →ₗ[K] V₂)
    (hloop : ∀ v, loop (loop v) = 0) (hstem : ∀ v, stem (loop v) = 0)
    (v : V₁ × V₂) :
    b0Action K V₁ V₂ loop stem hloop hstem (a K) v = (0, stem v.1) := by
  unfold b0Action a
  rw [TrivSqZeroExt.lift_apply_inr]
  simp [radicalAction]

theorem b0Action_x
    (loop : V₁ →ₗ[K] V₁) (stem : V₁ →ₗ[K] V₂)
    (hloop : ∀ v, loop (loop v) = 0) (hstem : ∀ v, stem (loop v) = 0)
    (v : V₁ × V₂) :
    b0Action K V₁ V₂ loop stem hloop hstem (x K) v = (loop v.1, 0) := by
  unfold b0Action x
  rw [TrivSqZeroExt.lift_apply_inr]
  simp [radicalAction]

/-- Finite-dimensional linear data satisfying the two dead-path relations. -/
structure FiniteB0Rep where
  V₁ : FGModuleCat.{u} K
  V₂ : FGModuleCat.{u} K
  loop : V₁ ⟶ V₁
  stem : V₁ ⟶ V₂
  loop_sq : ∀ v, loop.hom.hom (loop.hom.hom v) = 0
  stem_loop : ∀ v, stem.hom.hom (loop.hom.hom v) = 0

namespace FiniteB0Rep

/-- The underlying vector space of a finite `B₀` representation. -/
def Carrier (D : FiniteB0Rep K) := D.V₁ × D.V₂
  deriving AddCommGroup, Module K

def fst (D : FiniteB0Rep K) (v : D.Carrier) : D.V₁ := v.1

def snd (D : FiniteB0Rep K) (v : D.Carrier) : D.V₂ := v.2

def ofV₁ (D : FiniteB0Rep K) (v : D.V₁) : D.Carrier := (v, 0)

def ofV₂ (D : FiniteB0Rep K) (v : D.V₂) : D.Carrier := (0, v)

@[simp] theorem fst_ofV₁ (D : FiniteB0Rep K) (v : D.V₁) :
    fst K D (ofV₁ K D v) = v := rfl

@[simp] theorem snd_ofV₁ (D : FiniteB0Rep K) (v : D.V₁) :
    snd K D (ofV₁ K D v) = 0 := rfl

@[simp] theorem fst_ofV₂ (D : FiniteB0Rep K) (v : D.V₂) :
    fst K D (ofV₂ K D v) = 0 := rfl

@[simp] theorem snd_ofV₂ (D : FiniteB0Rep K) (v : D.V₂) :
    snd K D (ofV₂ K D v) = v := rfl

@[ext] theorem carrier_ext (D : FiniteB0Rep K) {v w : D.Carrier}
    (h₁ : fst K D v = fst K D w) (h₂ : snd K D v = snd K D w) : v = w := by
  exact Prod.ext h₁ h₂

theorem decompose (D : FiniteB0Rep K) (v : D.Carrier) :
    v = ofV₁ K D (fst K D v) + ofV₂ K D (snd K D v) := by
  apply carrier_ext K D
  · change v.1 = v.1 + 0
    simp
  · change v.2 = 0 + v.2
    simp

instance (D : FiniteB0Rep K) : Module.Finite K D.Carrier := by
  change Module.Finite K (D.V₁ × D.V₂)
  infer_instance

/-- The algebra representation associated to finite lollipop data. -/
def actionHom (D : FiniteB0Rep K) : B0Model K →ₐ[K] Module.End K D.Carrier :=
  b0Action K D.V₁ D.V₂ D.loop.hom.hom D.stem.hom.hom D.loop_sq D.stem_loop

instance (D : FiniteB0Rep K) : Module (B0Model K) D.Carrier :=
  Module.compHom D.Carrier (actionHom K D).toRingHom

instance (D : FiniteB0Rep K) : IsScalarTower K (B0Model K) D.Carrier :=
  IsScalarTower.of_algebraMap_smul fun c v => by
    change actionHom K D (algebraMap K (B0Model K) c) v = c • v
    rw [(actionHom K D).commutes]
    rfl

instance (D : FiniteB0Rep K) : Module.Finite (B0Model K) D.Carrier :=
  Module.Finite.of_restrictScalars_finite K (B0Model K) D.Carrier

/-- The genuine finitely generated left module associated to `D`. -/
abbrev asFGModule (D : FiniteB0Rep K) : FGModuleCat (B0Model K) :=
  FGModuleCat.of (B0Model K) D.Carrier

@[simp] theorem e1_smul (D : FiniteB0Rep K) (v : D.Carrier) :
    e1 K • v = (v.1, 0) := by
  change actionHom K D (e1 K) v = (v.1, 0)
  exact b0Action_e1 K D.V₁ D.V₂ D.loop.hom.hom D.stem.hom.hom
    D.loop_sq D.stem_loop v

@[simp] theorem e2_smul (D : FiniteB0Rep K) (v : D.Carrier) :
    e2 K • v = (0, v.2) := by
  change actionHom K D (e2 K) v = (0, v.2)
  exact b0Action_e2 K D.V₁ D.V₂ D.loop.hom.hom D.stem.hom.hom
    D.loop_sq D.stem_loop v

@[simp] theorem a_smul (D : FiniteB0Rep K) (v : D.Carrier) :
    a K • v = (0, D.stem.hom.hom v.1) := by
  change actionHom K D (a K) v = (0, D.stem.hom.hom v.1)
  exact b0Action_a K D.V₁ D.V₂ D.loop.hom.hom D.stem.hom.hom
    D.loop_sq D.stem_loop v

@[simp] theorem x_smul (D : FiniteB0Rep K) (v : D.Carrier) :
    x K • v = (D.loop.hom.hom v.1, 0) := by
  change actionHom K D (x K) v = (D.loop.hom.hom v.1, 0)
  exact b0Action_x K D.V₁ D.V₂ D.loop.hom.hom D.stem.hom.hom
    D.loop_sq D.stem_loop v

@[simp] theorem e1_smul_ofV₁ (D : FiniteB0Rep K) (v : D.V₁) :
    e1 K • ofV₁ K D v = ofV₁ K D v := by
  rw [e1_smul]
  apply carrier_ext K D <;> rfl

@[simp] theorem a_smul_ofV₁ (D : FiniteB0Rep K) (v : D.V₁) :
    a K • ofV₁ K D v = ofV₂ K D (D.stem.hom.hom v) := by
  rw [a_smul]
  apply carrier_ext K D <;> rfl

end FiniteB0Rep

abbrev K0 : FGModuleCat.{u} K := FGModuleCat.of K (Fin 0 → K)
abbrev K1 : FGModuleCat.{u} K := FGModuleCat.of K K
abbrev K2 : FGModuleCat.{u} K := FGModuleCat.of K (K × K)

/-- The nilpotent Jordan map `(u,v) ↦ (0,u)`. -/
def jordan : K2 K ⟶ K2 K :=
  FGModuleCat.ofHom
    { toFun := fun p => (0, p.1)
      map_add' := by simp
      map_smul' := by simp }

/-- The projective stem map `(u,v) ↦ u`. -/
def forkStem : K2 K ⟶ K1 K :=
  FGModuleCat.ofHom (LinearMap.fst K K K)

abbrev S1Data : FiniteB0Rep K where
  V₁ := K1 K
  V₂ := K0 K
  loop := 0
  stem := 0
  loop_sq := by simp
  stem_loop := by simp

abbrev S2Data : FiniteB0Rep K where
  V₁ := K0 K
  V₂ := K1 K
  loop := 0
  stem := 0
  loop_sq := by simp
  stem_loop := by simp

abbrev XData : FiniteB0Rep K where
  V₁ := K2 K
  V₂ := K0 K
  loop := jordan K
  stem := 0
  loop_sq := by
    intro v
    rfl
  stem_loop := by simp

abbrev AData : FiniteB0Rep K where
  V₁ := K1 K
  V₂ := K1 K
  loop := 0
  stem := 𝟙 _
  loop_sq := by simp
  stem_loop := by simp

abbrev PData : FiniteB0Rep K where
  V₁ := K2 K
  V₂ := K1 K
  loop := jordan K
  stem := forkStem K
  loop_sq := by
    intro v
    rfl
  stem_loop := by
    intro v
    rfl

/-- The five named genuine finitely generated `B₀`-modules. -/
abbrev S1Module : FGModuleCat (B0Model K) := FiniteB0Rep.asFGModule K (S1Data K)
abbrev S2Module : FGModuleCat (B0Model K) := FiniteB0Rep.asFGModule K (S2Data K)
abbrev XModule : FGModuleCat (B0Model K) := FiniteB0Rep.asFGModule K (XData K)
abbrev AModule : FGModuleCat (B0Model K) := FiniteB0Rep.asFGModule K (AData K)
abbrev PModule : FGModuleCat (B0Model K) := FiniteB0Rep.asFGModule K (PData K)

@[simp] theorem S2Data_e1_smul
    (w : FiniteB0Rep.Carrier K (S2Data K)) : e1 K • w = 0 := by
  rw [FiniteB0Rep.e1_smul]
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · rfl

@[simp] theorem S2Data_a_smul
    (w : FiniteB0Rep.Carrier K (S2Data K)) : a K • w = 0 := by
  rw [FiniteB0Rep.a_smul]
  rfl

/-- If the stem map is surjective, every unbundled `B₀`-linear map to `S₂` vanishes. -/
theorem linearMap_S2_eq_zero_of_surjective_stem
    (D : FiniteB0Rep K)
    (hstem : Function.Surjective D.stem.hom.hom)
    (f : FiniteB0Rep.Carrier K D →ₗ[B0Model K]
      FiniteB0Rep.Carrier K (S2Data K)) : f = 0 := by
  apply LinearMap.ext
  intro v
  have hv₁ : f (FiniteB0Rep.ofV₁ K D (FiniteB0Rep.fst K D v)) = 0 := by
    calc
      f (FiniteB0Rep.ofV₁ K D (FiniteB0Rep.fst K D v)) =
          f (e1 K • FiniteB0Rep.ofV₁ K D (FiniteB0Rep.fst K D v)) := by
        rw [FiniteB0Rep.e1_smul_ofV₁]
      _ = e1 K • f (FiniteB0Rep.ofV₁ K D (FiniteB0Rep.fst K D v)) := by
        rw [f.map_smul]
      _ = 0 := S2Data_e1_smul K _
  obtain ⟨u, hu⟩ := hstem (FiniteB0Rep.snd K D v)
  have hv₂ : f (FiniteB0Rep.ofV₂ K D (FiniteB0Rep.snd K D v)) = 0 := by
    calc
      f (FiniteB0Rep.ofV₂ K D (FiniteB0Rep.snd K D v)) =
          f (a K • FiniteB0Rep.ofV₁ K D u) := by
        rw [FiniteB0Rep.a_smul_ofV₁, hu]
      _ = a K • f (FiniteB0Rep.ofV₁ K D u) := by rw [f.map_smul]
      _ = 0 := S2Data_a_smul K _
  calc
    f v = f (FiniteB0Rep.ofV₁ K D (FiniteB0Rep.fst K D v) +
        FiniteB0Rep.ofV₂ K D (FiniteB0Rep.snd K D v)) :=
      congrArg f (FiniteB0Rep.decompose K D v)
    _ = f (FiniteB0Rep.ofV₁ K D (FiniteB0Rep.fst K D v)) +
        f (FiniteB0Rep.ofV₂ K D (FiniteB0Rep.snd K D v)) := by rw [map_add]
    _ = 0 := by rw [hv₁, hv₂, add_zero]

/-- The bundled `FGModuleCat` version of the same zero-Hom criterion. -/
theorem hom_S2_eq_zero_of_surjective_stem
    (D : FiniteB0Rep K)
    (hstem : Function.Surjective D.stem.hom.hom)
    (f : FiniteB0Rep.asFGModule K D ⟶ S2Module K) : f = 0 := by
  apply FGModuleCat.hom_ext
  exact linearMap_S2_eq_zero_of_surjective_stem K D hstem f.hom.hom

theorem S1_stem_surjective : Function.Surjective (S1Data K).stem.hom.hom := by
  intro y
  refine ⟨0, ?_⟩
  exact Subsingleton.elim _ _

theorem X_stem_surjective : Function.Surjective (XData K).stem.hom.hom := by
  intro y
  refine ⟨0, ?_⟩
  exact Subsingleton.elim _ _

theorem A_stem_surjective : Function.Surjective (AData K).stem.hom.hom := by
  intro y
  exact ⟨y, rfl⟩

theorem P_stem_surjective : Function.Surjective (PData K).stem.hom.hom := by
  intro y
  exact ⟨(y, 0), rfl⟩

theorem hom_S1_S2_eq_zero (f : S1Module K ⟶ S2Module K) : f = 0 :=
  hom_S2_eq_zero_of_surjective_stem K (S1Data K) (S1_stem_surjective K) f

theorem hom_X_S2_eq_zero (f : XModule K ⟶ S2Module K) : f = 0 :=
  hom_S2_eq_zero_of_surjective_stem K (XData K) (X_stem_surjective K) f

theorem hom_A_S2_eq_zero (f : AModule K ⟶ S2Module K) : f = 0 :=
  hom_S2_eq_zero_of_surjective_stem K (AData K) (A_stem_surjective K) f

theorem hom_P_S2_eq_zero (f : PModule K ⟶ S2Module K) : f = 0 :=
  hom_S2_eq_zero_of_surjective_stem K (PData K) (P_stem_surjective K) f

inductive QuotientPRowLabel where
  | s1
  | x
  | a
  | p

def quotientPRowModule : QuotientPRowLabel → FGModuleCat (B0Model K)
  | .s1 => S1Module K
  | .x => XModule K
  | .a => AModule K
  | .p => PModule K

/-- The zero-Hom row for the four explicitly enumerated genuine
finitely generated `B₀`-module sources. -/
theorem quotientPRow_hom_S2_eq_zero
    (i : QuotientPRowLabel) (f : quotientPRowModule K i ⟶ S2Module K) : f = 0 := by
  cases i with
  | s1 => exact hom_S1_S2_eq_zero K f
  | x => exact hom_X_S2_eq_zero K f
  | a => exact hom_A_S2_eq_zero K f
  | p => exact hom_P_S2_eq_zero K f

end QuotientSubmoduleEquidistribution.LollipopConcrete.ModuleLayer
