import QuotientSubmoduleEquidistribution.RepresentationTheory.LollipopB0Modules
import QuotientSubmoduleEquidistribution.RepresentationTheory.FiniteType

/-!
# Properties of the five named dead-path lollipop modules

The five displayed genuine `B₀`-modules `S₁, S₂, X, A, P` are nonzero,
indecomposable, and pairwise nonisomorphic.  Their underlying dimensions are
`1, 1, 2, 2, 3`.

This file deliberately does not claim that these five modules exhaust the
indecomposable modules of `B0Model`.
-/

noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.LollipopConcrete.ModuleLayer.NamedModules

universe u

variable (K : Type u) [Field K]

/-! ## Component maps -/

theorem map_smul_ground
    {D E : FiniteB0Rep K}
    (f : FiniteB0Rep.Carrier K D →ₗ[B0Model K]
      FiniteB0Rep.Carrier K E)
    (c : K) (v : FiniteB0Rep.Carrier K D) :
    f (c • v) = c • f v := by
  rw [← IsScalarTower.algebraMap_smul (B0Model K) c v,
    f.map_smul, IsScalarTower.algebraMap_smul]

def inV1 (D : FiniteB0Rep K) : D.V₁ →ₗ[K] D.Carrier := by
  change D.V₁ →ₗ[K] D.V₁ × D.V₂
  exact LinearMap.inl K D.V₁ D.V₂

def inV2 (D : FiniteB0Rep K) : D.V₂ →ₗ[K] D.Carrier := by
  change D.V₂ →ₗ[K] D.V₁ × D.V₂
  exact LinearMap.inr K D.V₁ D.V₂

def outV1 (D : FiniteB0Rep K) : D.Carrier →ₗ[K] D.V₁ := by
  change D.V₁ × D.V₂ →ₗ[K] D.V₁
  exact LinearMap.fst K D.V₁ D.V₂

def outV2 (D : FiniteB0Rep K) : D.Carrier →ₗ[K] D.V₂ := by
  change D.V₁ × D.V₂ →ₗ[K] D.V₂
  exact LinearMap.snd K D.V₁ D.V₂

/-- Vertex-one component of a `B0Model`-linear map. -/
def homV1
    {D E : FiniteB0Rep K}
    (f : FiniteB0Rep.Carrier K D →ₗ[B0Model K]
      FiniteB0Rep.Carrier K E) :
    D.V₁ →ₗ[K] E.V₁ :=
  (outV1 K E).comp ((f.restrictScalars K).comp (inV1 K D))

/-- Vertex-two component of a `B0Model`-linear map. -/
def homV2
    {D E : FiniteB0Rep K}
    (f : FiniteB0Rep.Carrier K D →ₗ[B0Model K]
      FiniteB0Rep.Carrier K E) :
    D.V₂ →ₗ[K] E.V₂ :=
  (outV2 K E).comp ((f.restrictScalars K).comp (inV2 K D))

theorem map_ofV1
    {D E : FiniteB0Rep K}
    (f : FiniteB0Rep.Carrier K D →ₗ[B0Model K]
      FiniteB0Rep.Carrier K E)
    (v : D.V₁) :
    f (FiniteB0Rep.ofV₁ K D v) =
      FiniteB0Rep.ofV₁ K E (homV1 K f v) := by
  calc
    f (FiniteB0Rep.ofV₁ K D v) =
        f (e1 K • FiniteB0Rep.ofV₁ K D v) := by
      rw [FiniteB0Rep.e1_smul_ofV₁]
    _ = e1 K • f (FiniteB0Rep.ofV₁ K D v) := by rw [f.map_smul]
    _ = FiniteB0Rep.ofV₁ K E (homV1 K f v) := by
      rw [FiniteB0Rep.e1_smul]
      rfl

theorem map_ofV2
    {D E : FiniteB0Rep K}
    (f : FiniteB0Rep.Carrier K D →ₗ[B0Model K]
      FiniteB0Rep.Carrier K E)
    (v : D.V₂) :
    f (FiniteB0Rep.ofV₂ K D v) =
      FiniteB0Rep.ofV₂ K E (homV2 K f v) := by
  have he2 :
      e2 K • FiniteB0Rep.ofV₂ K D v =
        FiniteB0Rep.ofV₂ K D v := by
    rw [FiniteB0Rep.e2_smul]
    rfl
  calc
    f (FiniteB0Rep.ofV₂ K D v) =
        f (e2 K • FiniteB0Rep.ofV₂ K D v) := by rw [he2]
    _ = e2 K • f (FiniteB0Rep.ofV₂ K D v) := by rw [f.map_smul]
    _ = FiniteB0Rep.ofV₂ K E (homV2 K f v) := by
      rw [FiniteB0Rep.e2_smul]
      rfl

theorem map_eq_components
    {D E : FiniteB0Rep K}
    (f : FiniteB0Rep.Carrier K D →ₗ[B0Model K]
      FiniteB0Rep.Carrier K E)
    (v : FiniteB0Rep.Carrier K D) :
    f v = FiniteB0Rep.ofV₁ K E
        (homV1 K f (FiniteB0Rep.fst K D v)) +
      FiniteB0Rep.ofV₂ K E
        (homV2 K f (FiniteB0Rep.snd K D v)) := by
  calc
    f v = f (FiniteB0Rep.ofV₁ K D (FiniteB0Rep.fst K D v) +
        FiniteB0Rep.ofV₂ K D (FiniteB0Rep.snd K D v)) :=
      congrArg f (FiniteB0Rep.decompose K D v)
    _ = f (FiniteB0Rep.ofV₁ K D (FiniteB0Rep.fst K D v)) +
        f (FiniteB0Rep.ofV₂ K D (FiniteB0Rep.snd K D v)) := by rw [map_add]
    _ = FiniteB0Rep.ofV₁ K E
          (homV1 K f (FiniteB0Rep.fst K D v)) +
        FiniteB0Rep.ofV₂ K E
          (homV2 K f (FiniteB0Rep.snd K D v)) := by
      rw [map_ofV1 K f, map_ofV2 K f]

theorem hom_ext
    {D E : FiniteB0Rep K}
    {f g : FiniteB0Rep.Carrier K D →ₗ[B0Model K]
      FiniteB0Rep.Carrier K E}
    (h1 : homV1 K f = homV1 K g)
    (h2 : homV2 K f = homV2 K g) : f = g := by
  apply LinearMap.ext
  intro v
  rw [map_eq_components K f v, map_eq_components K g v, h1, h2]

theorem homV1_loop
    {D E : FiniteB0Rep K}
    (f : FiniteB0Rep.Carrier K D →ₗ[B0Model K]
      FiniteB0Rep.Carrier K E)
    (v : D.V₁) :
    homV1 K f (D.loop.hom.hom v) =
      E.loop.hom.hom (homV1 K f v) := by
  have hxD :
      x K • FiniteB0Rep.ofV₁ K D v =
        FiniteB0Rep.ofV₁ K D (D.loop.hom.hom v) := by
    rw [FiniteB0Rep.x_smul]
    rfl
  have hxE :
      x K • FiniteB0Rep.ofV₁ K E (homV1 K f v) =
        FiniteB0Rep.ofV₁ K E (E.loop.hom.hom (homV1 K f v)) := by
    rw [FiniteB0Rep.x_smul]
    rfl
  calc
    homV1 K f (D.loop.hom.hom v) =
        FiniteB0Rep.fst K E
          (f (FiniteB0Rep.ofV₁ K D (D.loop.hom.hom v))) := rfl
    _ = FiniteB0Rep.fst K E
          (f (x K • FiniteB0Rep.ofV₁ K D v)) := by rw [hxD]
    _ = FiniteB0Rep.fst K E
          (x K • f (FiniteB0Rep.ofV₁ K D v)) := by rw [f.map_smul]
    _ = FiniteB0Rep.fst K E
          (x K • FiniteB0Rep.ofV₁ K E (homV1 K f v)) := by
      rw [map_ofV1 K f]
    _ = E.loop.hom.hom (homV1 K f v) := by
      rw [hxE]
      exact FiniteB0Rep.fst_ofV₁ K E _

theorem homV2_stem
    {D E : FiniteB0Rep K}
    (f : FiniteB0Rep.Carrier K D →ₗ[B0Model K]
      FiniteB0Rep.Carrier K E)
    (v : D.V₁) :
    homV2 K f (D.stem.hom.hom v) =
      E.stem.hom.hom (homV1 K f v) := by
  calc
    homV2 K f (D.stem.hom.hom v) =
        FiniteB0Rep.snd K E
          (f (FiniteB0Rep.ofV₂ K D (D.stem.hom.hom v))) := rfl
    _ = FiniteB0Rep.snd K E
          (f (a K • FiniteB0Rep.ofV₁ K D v)) := by
      rw [FiniteB0Rep.a_smul_ofV₁]
    _ = FiniteB0Rep.snd K E
          (a K • f (FiniteB0Rep.ofV₁ K D v)) := by rw [f.map_smul]
    _ = FiniteB0Rep.snd K E
          (a K • FiniteB0Rep.ofV₁ K E (homV1 K f v)) := by
      rw [map_ofV1 K f]
    _ = E.stem.hom.hom (homV1 K f v) := by
      rw [FiniteB0Rep.a_smul_ofV₁]
      rfl

/-! ## Nontriviality and dimensions -/

theorem S1_nontrivial : Nontrivial (S1Module K) := by
  change Nontrivial (K × (Fin 0 → K))
  infer_instance

theorem S2_nontrivial : Nontrivial (S2Module K) := by
  change Nontrivial ((Fin 0 → K) × K)
  infer_instance

theorem X_nontrivial : Nontrivial (XModule K) := by
  change Nontrivial ((K × K) × (Fin 0 → K))
  infer_instance

theorem A_nontrivial : Nontrivial (AModule K) := by
  change Nontrivial (K × K)
  infer_instance

theorem P_nontrivial : Nontrivial (PModule K) := by
  change Nontrivial ((K × K) × K)
  infer_instance

@[simp] theorem finrank_S1 : Module.finrank K (S1Module K) = 1 := by
  change Module.finrank K (K × (Fin 0 → K)) = 1
  simp

@[simp] theorem finrank_S2 : Module.finrank K (S2Module K) = 1 := by
  change Module.finrank K ((Fin 0 → K) × K) = 1
  simp

@[simp] theorem finrank_X : Module.finrank K (XModule K) = 2 := by
  change Module.finrank K ((K × K) × (Fin 0 → K)) = 2
  simp

@[simp] theorem finrank_A : Module.finrank K (AModule K) = 2 := by
  change Module.finrank K (K × K) = 2
  simp

@[simp] theorem finrank_P : Module.finrank K (PModule K) = 3 := by
  change Module.finrank K ((K × K) × K) = 3
  simp

/-! ## Idempotent endomorphisms -/

theorem linearMap_K_apply
    (g : K →ₗ[K] K) (c : K) : g c = c * g 1 := by
  calc
    g c = g (c • (1 : K)) := by simp
    _ = c • g 1 := by rw [map_smul]
    _ = c * g 1 := rfl

theorem homV1_idempotent_apply
    {D : FiniteB0Rep K}
    (f : Module.End (B0Model K) (FiniteB0Rep.Carrier K D))
    (hf : IsIdempotentElem f) (v : D.V₁) :
    homV1 K f (homV1 K f v) = homV1 K f v := by
  have hff : f (f (FiniteB0Rep.ofV₁ K D v)) =
      f (FiniteB0Rep.ofV₁ K D v) := by
    simpa [Module.End.mul_apply] using
      DFunLike.congr_fun hf (FiniteB0Rep.ofV₁ K D v)
  rw [map_ofV1 K f, map_ofV1 K f] at hff
  have h := congrArg (FiniteB0Rep.fst K D) hff
  simpa only [FiniteB0Rep.fst_ofV₁] using h

theorem homV2_idempotent_apply
    {D : FiniteB0Rep K}
    (f : Module.End (B0Model K) (FiniteB0Rep.Carrier K D))
    (hf : IsIdempotentElem f) (v : D.V₂) :
    homV2 K f (homV2 K f v) = homV2 K f v := by
  have hff : f (f (FiniteB0Rep.ofV₂ K D v)) =
      f (FiniteB0Rep.ofV₂ K D v) := by
    simpa [Module.End.mul_apply] using
      DFunLike.congr_fun hf (FiniteB0Rep.ofV₂ K D v)
  rw [map_ofV2 K f, map_ofV2 K f] at hff
  have h := congrArg (FiniteB0Rep.snd K D) hff
  simpa only [FiniteB0Rep.snd_ofV₂] using h

@[simp] theorem homV1_zero {D : FiniteB0Rep K} :
    homV1 K
      (0 : Module.End (B0Model K) (FiniteB0Rep.Carrier K D)) = 0 := by
  apply LinearMap.ext
  intro v
  change FiniteB0Rep.fst K D
    ((0 : Module.End (B0Model K) (FiniteB0Rep.Carrier K D))
      (FiniteB0Rep.ofV₁ K D v)) = 0
  rw [LinearMap.zero_apply]
  rfl

@[simp] theorem homV2_zero {D : FiniteB0Rep K} :
    homV2 K
      (0 : Module.End (B0Model K) (FiniteB0Rep.Carrier K D)) = 0 := by
  apply LinearMap.ext
  intro v
  change FiniteB0Rep.snd K D
    ((0 : Module.End (B0Model K) (FiniteB0Rep.Carrier K D))
      (FiniteB0Rep.ofV₂ K D v)) = 0
  rw [LinearMap.zero_apply]
  rfl

@[simp] theorem homV1_one {D : FiniteB0Rep K} :
    homV1 K
      (1 : Module.End (B0Model K) (FiniteB0Rep.Carrier K D)) =
      LinearMap.id := by
  apply LinearMap.ext
  intro v
  change FiniteB0Rep.fst K D
    ((1 : Module.End (B0Model K) (FiniteB0Rep.Carrier K D))
      (FiniteB0Rep.ofV₁ K D v)) = v
  rw [Module.End.one_apply]
  exact FiniteB0Rep.fst_ofV₁ K D v

@[simp] theorem homV2_one {D : FiniteB0Rep K} :
    homV2 K
      (1 : Module.End (B0Model K) (FiniteB0Rep.Carrier K D)) =
      LinearMap.id := by
  apply LinearMap.ext
  intro v
  change FiniteB0Rep.snd K D
    ((1 : Module.End (B0Model K) (FiniteB0Rep.Carrier K D))
      (FiniteB0Rep.ofV₂ K D v)) = v
  rw [Module.End.one_apply]
  exact FiniteB0Rep.snd_ofV₂ K D v

theorem S1_indec :
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule (B0Model K) (S1Module K) := by
  letI : Nontrivial (S1Module K) := S1_nontrivial K
  apply QuotientSubmoduleEquidistribution.Foundation.isIndecomposableModule_of_forall_isIdempotentElem
  intro f hf
  let g : K →ₗ[K] K := homV1 K f
  have hsq : g 1 * g 1 = g 1 := by
    have h := homV1_idempotent_apply K f hf (1 : K)
    change g (g 1) = g 1 at h
    rw [linearMap_K_apply K] at h
    exact h
  have hpow : (g 1) ^ 2 = g 1 := by simpa [pow_two] using hsq
  rcases eq_zero_or_one_of_sq_eq_self hpow with hzero | hone
  · left
    apply hom_ext K
    · apply LinearMap.ext
      intro c
      simp only [g] at hzero
      rw [linearMap_K_apply K, hzero]
      simp [homV1]
    · apply LinearMap.ext
      intro v
      exact Subsingleton.elim _ _
  · right
    apply hom_ext K
    · apply LinearMap.ext
      intro c
      simp only [g] at hone
      rw [linearMap_K_apply K, hone]
      rw [mul_one]
      change c = (LinearMap.fst K K (Fin 0 → K))
        ((LinearMap.inl K K (Fin 0 → K)) c)
      rfl
    · apply LinearMap.ext
      intro v
      exact Subsingleton.elim _ _

theorem S2_indec :
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule (B0Model K) (S2Module K) := by
  letI : Nontrivial (S2Module K) := S2_nontrivial K
  apply QuotientSubmoduleEquidistribution.Foundation.isIndecomposableModule_of_forall_isIdempotentElem
  intro f hf
  let g : K →ₗ[K] K := homV2 K f
  have hsq : g 1 * g 1 = g 1 := by
    have h := homV2_idempotent_apply K f hf (1 : K)
    change g (g 1) = g 1 at h
    rw [linearMap_K_apply K] at h
    exact h
  have hpow : (g 1) ^ 2 = g 1 := by simpa [pow_two] using hsq
  rcases eq_zero_or_one_of_sq_eq_self hpow with hzero | hone
  · left
    apply hom_ext K
    · apply LinearMap.ext
      intro v
      exact Subsingleton.elim _ _
    · apply LinearMap.ext
      intro c
      simp only [g] at hzero
      rw [linearMap_K_apply K, hzero]
      simp [homV2]
  · right
    apply hom_ext K
    · apply LinearMap.ext
      intro v
      exact Subsingleton.elim _ _
    · apply LinearMap.ext
      intro c
      simp only [g] at hone
      rw [linearMap_K_apply K, hone, mul_one]
      change c = (LinearMap.snd K (Fin 0 → K) K)
        ((LinearMap.inr K (Fin 0 → K) K) c)
      rfl

theorem A_hom_components_eq
    (f : Module.End (B0Model K) (AModule K)) (c : K) :
    homV2 K f c = homV1 K f c := by
  simpa using homV2_stem K f c

theorem A_indec :
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule (B0Model K) (AModule K) := by
  letI : Nontrivial (AModule K) := A_nontrivial K
  apply QuotientSubmoduleEquidistribution.Foundation.isIndecomposableModule_of_forall_isIdempotentElem
  intro f hf
  let g : K →ₗ[K] K := homV1 K f
  have hsq : g 1 * g 1 = g 1 := by
    have h := homV1_idempotent_apply K f hf (1 : K)
    change g (g 1) = g 1 at h
    rw [linearMap_K_apply K] at h
    exact h
  have hpow : (g 1) ^ 2 = g 1 := by simpa [pow_two] using hsq
  rcases eq_zero_or_one_of_sq_eq_self hpow with hzero | hone
  · left
    apply hom_ext K
    · apply LinearMap.ext
      intro c
      simp only [g] at hzero
      rw [linearMap_K_apply K, hzero]
      simp [homV1]
    · apply LinearMap.ext
      intro c
      rw [A_hom_components_eq K]
      simp only [g] at hzero
      rw [linearMap_K_apply K, hzero]
      simp [homV2]
  · right
    apply hom_ext K
    · apply LinearMap.ext
      intro c
      simp only [g] at hone
      rw [linearMap_K_apply K, hone, mul_one]
      change c = (LinearMap.fst K K K) ((LinearMap.inl K K K) c)
      rfl
    · apply LinearMap.ext
      intro c
      rw [A_hom_components_eq K]
      simp only [g] at hone
      rw [linearMap_K_apply K, hone, mul_one]
      change c = (LinearMap.snd K K K) ((LinearMap.inr K K K) c)
      rfl

theorem linearMap_commuting_jordan_formula
    (g : K × K →ₗ[K] K × K)
    (hcomm : ∀ p : K × K, g (0, p.1) = (0, (g p).1))
    (u v : K) :
    g (u, v) =
      (u * (g (1, 0)).1,
        u * (g (1, 0)).2 + v * (g (1, 0)).1) := by
  have h01 : g (0, 1) = (0, (g (1, 0)).1) := by
    simpa using hcomm (1, 0)
  have huv : (u, v) = u • (1, 0) + v • (0, 1) := by
    ext <;> simp
  rw [huv, map_add, map_smul, map_smul, h01]
  ext <;> simp

theorem jordan_idempotent_eq_zero_or_id
    (g : K × K →ₗ[K] K × K)
    (hcomm : ∀ p : K × K, g (0, p.1) = (0, (g p).1))
    (hidem : ∀ p : K × K, g (g p) = g p) :
    g = 0 ∨ g = LinearMap.id := by
  let alpha : K := (g (1, 0)).1
  let beta : K := (g (1, 0)).2
  have hone := hidem (1, 0)
  rw [linearMap_commuting_jordan_formula K g hcomm] at hone
  have halpha : alpha ^ 2 = alpha := by
    have h := congrArg Prod.fst hone
    simpa [alpha, pow_two] using h
  have hbeta : alpha * beta + beta * alpha = beta := by
    have h := congrArg Prod.snd hone
    simpa [alpha, beta] using h
  rcases eq_zero_or_one_of_sq_eq_self halpha with ha | ha
  · have hb : beta = 0 := by simpa [ha] using hbeta.symm
    left
    apply LinearMap.ext
    intro p
    rcases p with ⟨u, v⟩
    rw [linearMap_commuting_jordan_formula K g hcomm]
    change (u * alpha, u * beta + v * alpha) = 0
    simp [ha, hb]
  · have hb : beta = 0 := by simpa [ha] using hbeta
    right
    apply LinearMap.ext
    intro p
    rcases p with ⟨u, v⟩
    rw [linearMap_commuting_jordan_formula K g hcomm]
    change (u * alpha, u * beta + v * alpha) = (u, v)
    simp [ha, hb]

theorem X_homV1_commutes_jordan
    (f : Module.End (B0Model K) (XModule K)) (p : K × K) :
    homV1 K f (0, p.1) = (0, (homV1 K f p).1) := by
  have h := homV1_loop K f p
  change homV1 K f (0, p.1) = (0, (homV1 K f p).1) at h
  exact h

theorem X_indec :
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule (B0Model K) (XModule K) := by
  letI : Nontrivial (XModule K) := X_nontrivial K
  apply QuotientSubmoduleEquidistribution.Foundation.isIndecomposableModule_of_forall_isIdempotentElem
  intro f hf
  let g : K × K →ₗ[K] K × K := homV1 K f
  have hcomm : ∀ p : K × K, g (0, p.1) = (0, (g p).1) := by
    intro p
    exact X_homV1_commutes_jordan K f p
  have hidem : ∀ p : K × K, g (g p) = g p := by
    intro p
    exact homV1_idempotent_apply K f hf p
  rcases jordan_idempotent_eq_zero_or_id K g hcomm hidem with hg | hg
  · left
    apply hom_ext K
    · exact hg.trans (homV1_zero K (D := XData K)).symm
    · apply LinearMap.ext
      intro v
      exact Subsingleton.elim _ _
  · right
    apply hom_ext K
    · exact hg.trans (homV1_one K (D := XData K)).symm
    · apply LinearMap.ext
      intro v
      exact Subsingleton.elim _ _

theorem P_homV1_commutes_jordan
    (f : Module.End (B0Model K) (PModule K)) (p : K × K) :
    homV1 K f (0, p.1) = (0, (homV1 K f p).1) := by
  have h := homV1_loop K f p
  change homV1 K f (0, p.1) = (0, (homV1 K f p).1) at h
  exact h

theorem P_homV2_eq_homV1_fst
    (f : Module.End (B0Model K) (PModule K)) (p : K × K) :
    homV2 K f p.1 = (homV1 K f p).1 := by
  have h := homV2_stem K f p
  change homV2 K f p.1 = (homV1 K f p).1 at h
  exact h

theorem P_indec :
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule (B0Model K) (PModule K) := by
  letI : Nontrivial (PModule K) := P_nontrivial K
  apply QuotientSubmoduleEquidistribution.Foundation.isIndecomposableModule_of_forall_isIdempotentElem
  intro f hf
  let g : K × K →ₗ[K] K × K := homV1 K f
  have hcomm : ∀ p : K × K, g (0, p.1) = (0, (g p).1) := by
    intro p
    exact P_homV1_commutes_jordan K f p
  have hidem : ∀ p : K × K, g (g p) = g p := by
    intro p
    exact homV1_idempotent_apply K f hf p
  rcases jordan_idempotent_eq_zero_or_id K g hcomm hidem with hg | hg
  · left
    apply hom_ext K
    · exact hg.trans (homV1_zero K (D := PData K)).symm
    · have hV2zero : homV2 K f = 0 := by
        apply LinearMap.ext
        intro c
        rw [P_homV2_eq_homV1_fst K f (c, 0)]
        change (g (c, 0)).1 = 0
        rw [hg]
        rfl
      exact hV2zero.trans (homV2_zero K (D := PData K)).symm
  · right
    apply hom_ext K
    · exact hg.trans (homV1_one K (D := PData K)).symm
    · have hV2one : homV2 K f = LinearMap.id := by
        apply LinearMap.ext
        intro c
        rw [P_homV2_eq_homV1_fst K f (c, 0)]
        change (g (c, 0)).1 = c
        rw [hg]
        rfl
      exact hV2one.trans (homV2_one K (D := PData K)).symm

/-! ## Pairwise nonisomorphism -/

theorem not_iso_of_finrank_ne
    {D E : FiniteB0Rep K}
    (h : Module.finrank K (FiniteB0Rep.Carrier K D) ≠
      Module.finrank K (FiniteB0Rep.Carrier K E)) :
    ¬ Nonempty
      (FiniteB0Rep.asFGModule K D ≅ FiniteB0Rep.asFGModule K E) := by
  rintro ⟨e⟩
  apply h
  exact ((FGModuleCat.isoToLinearEquiv e).restrictScalars K).finrank_eq

theorem S1_not_iso_X : ¬ Nonempty (S1Module K ≅ XModule K) := by
  apply not_iso_of_finrank_ne K
  change Module.finrank K (K × (Fin 0 → K)) ≠
    Module.finrank K ((K × K) × (Fin 0 → K))
  simp

theorem S1_not_iso_A : ¬ Nonempty (S1Module K ≅ AModule K) := by
  apply not_iso_of_finrank_ne K
  change Module.finrank K (K × (Fin 0 → K)) ≠
    Module.finrank K (K × K)
  simp

theorem S1_not_iso_P : ¬ Nonempty (S1Module K ≅ PModule K) := by
  apply not_iso_of_finrank_ne K
  change Module.finrank K (K × (Fin 0 → K)) ≠
    Module.finrank K ((K × K) × K)
  simp

theorem S2_not_iso_X : ¬ Nonempty (S2Module K ≅ XModule K) := by
  apply not_iso_of_finrank_ne K
  change Module.finrank K ((Fin 0 → K) × K) ≠
    Module.finrank K ((K × K) × (Fin 0 → K))
  simp

theorem S2_not_iso_A : ¬ Nonempty (S2Module K ≅ AModule K) := by
  apply not_iso_of_finrank_ne K
  change Module.finrank K ((Fin 0 → K) × K) ≠
    Module.finrank K (K × K)
  simp

theorem S2_not_iso_P : ¬ Nonempty (S2Module K ≅ PModule K) := by
  apply not_iso_of_finrank_ne K
  change Module.finrank K ((Fin 0 → K) × K) ≠
    Module.finrank K ((K × K) × K)
  simp

theorem X_not_iso_P : ¬ Nonempty (XModule K ≅ PModule K) := by
  apply not_iso_of_finrank_ne K
  change Module.finrank K ((K × K) × (Fin 0 → K)) ≠
    Module.finrank K ((K × K) × K)
  simp

theorem A_not_iso_P : ¬ Nonempty (AModule K ≅ PModule K) := by
  apply not_iso_of_finrank_ne K
  change Module.finrank K (K × K) ≠
    Module.finrank K ((K × K) × K)
  simp

theorem S1_not_iso_S2 : ¬ Nonempty (S1Module K ≅ S2Module K) := by
  rintro ⟨e⟩
  have hz : e.hom = 0 := hom_S1_S2_eq_zero K e.hom
  let v : S1Module K :=
    FiniteB0Rep.ofV₁ K (S1Data K) (1 : K)
  have hv : (FGModuleCat.isoToLinearEquiv e) v = 0 := by
    change e.hom.hom.hom v = 0
    rw [hz]
    rfl
  have hv0 : (FGModuleCat.isoToLinearEquiv e) v =
      (FGModuleCat.isoToLinearEquiv e) 0 := by
    simpa using hv
  have hvzero : v = 0 :=
    (FGModuleCat.isoToLinearEquiv e).injective hv0
  have hcoord :=
    congrArg (FiniteB0Rep.fst K (S1Data K)) hvzero
  change (1 : K) = 0 at hcoord
  exact one_ne_zero hcoord

theorem X_a_smul_zero (z : XModule K) : a K • z = 0 := by
  rw [FiniteB0Rep.a_smul]
  apply FiniteB0Rep.carrier_ext K (XData K)
  · rfl
  · exact Subsingleton.elim _ _

theorem X_not_iso_A : ¬ Nonempty (XModule K ≅ AModule K) := by
  rintro ⟨e⟩
  let w : AModule K :=
    FiniteB0Rep.ofV₁ K (AData K) (1 : K)
  let g : AModule K ≃ₗ[B0Model K] XModule K :=
    (FGModuleCat.isoToLinearEquiv e).symm
  have hmap : g (a K • w) = 0 := by
    calc
      g (a K • w) = a K • g w := by rw [map_smul]
      _ = 0 := X_a_smul_zero K _
  have hmap0 : g (a K • w) = g 0 := by simpa using hmap
  have haw : a K • w = 0 := g.injective hmap0
  rw [FiniteB0Rep.a_smul_ofV₁] at haw
  have hcoord := congrArg (FiniteB0Rep.snd K (AData K)) haw
  change (1 : K) = 0 at hcoord
  exact one_ne_zero hcoord

end QuotientSubmoduleEquidistribution.LollipopConcrete.ModuleLayer.NamedModules
