import QuotientSubmoduleEquidistribution.RepresentationTheory.LollipopB1Modules
import QuotientSubmoduleEquidistribution.RepresentationTheory.LollipopTableCertificates

/-!
# Quotient-side common-range bounds for the live-path lollipop

For the two quotient-good rows in the seven-object live-path table, this file
proves exact zero-Hom or common proper-range bounds for maps from the four
explicitly named source modules to every omitted named target.  The final
endpoints aggregate arbitrary finite biproducts of exactly those named sources.

No exhaustiveness, skeleton-closure, or path-algebra identification statement
is made here.
-/

noncomputable section

open scoped RightActions

namespace QuotientSubmoduleEquidistribution.LollipopConcrete.B1.ModuleLayer.QuotientRows

open CategoryTheory CategoryTheory.Limits

universe u v w

variable (K : Type u) [Field K]

/-! ## Common proper coordinate bounds in the three omitted targets -/

/-- For any live-path representation with Jordan vertex-one loop, the first
vertex-one coordinate is multiplied only by the scalar part at vertex one. -/
theorem b1Action_first_eq
    (V₂ : Type u) [AddCommGroup V₂] [Module K V₂]
    (loop : (K × K) →ₗ[K] (K × K)) (stem : (K × K) →ₗ[K] V₂)
    (hloop : ∀ z, loop (loop z) = 0)
    (hfirst : ∀ z, (loop z).1 = 0)
    (b : B1Model K) (z : (K × K) × V₂) :
    (b1Action K (K × K) V₂ loop stem hloop b z).1.1 =
      b.fst.1.fst * z.1.1 := by
  unfold b1Action
  rw [TrivSqZeroExt.lift_def]
  simp [baseAction, arrowAction, loopCornerAction_apply, hfirst]

/-- The analogous scalar-coordinate formula for the one-dimensional
vertex-one space of `A`. -/
theorem b1Action_A_first_eq
    (b : B1Model K) (z : K × K) :
    (b1Action K K K (AData K).loop.hom.hom (AData K).stem.hom.hom
      (AData K).loop_sq b z).1 = b.fst.1.fst * z.1 := by
  unfold b1Action
  rw [TrivSqZeroExt.lift_def]
  simp [baseAction, arrowAction, loopCornerAction_apply]

/-- First vertex-one coordinate of `W`. -/
def wTopCoord (z : WModule K) : K := z.1.1

@[simp] theorem wTopCoord_zero : wTopCoord K (0 : WModule K) = 0 := rfl

@[simp] theorem wTopCoord_add (z z' : WModule K) :
    wTopCoord K (z + z') = wTopCoord K z + wTopCoord K z' := rfl

@[simp] theorem wTopCoord_smul (b : B1Model K) (z : WModule K) :
    wTopCoord K (b • z) = b.fst.1.fst * wTopCoord K z := by
  exact b1Action_first_eq K K (WData K).loop.hom.hom
    (WData K).stem.hom.hom (WData K).loop_sq (by intro y; rfl) b z

/-- The common proper bound `{((0,s),t)}` in `W`. -/
def wTopBound : Submodule (B1Model K) (WModule K) where
  carrier := {z | wTopCoord K z = 0}
  zero_mem' := rfl
  add_mem' := by
    intro z z' hz hz'
    change wTopCoord K z = 0 at hz
    change wTopCoord K z' = 0 at hz'
    change wTopCoord K (z + z') = 0
    simp only [wTopCoord_add, hz, hz', add_zero]
  smul_mem' := by
    intro b z hz
    change wTopCoord K z = 0 at hz
    change wTopCoord K (b • z) = 0
    simp only [wTopCoord_smul, hz, mul_zero]

def wTopGenerator : WModule K :=
  FiniteB1Rep.ofV₁ K (WData K) (1, 0)

theorem wTopBound_ne_top : wTopBound K ≠ ⊤ := by
  intro htop
  have hmem : wTopGenerator K ∈ wTopBound K := by
    rw [htop]
    exact Submodule.mem_top
  change (1 : K) = 0 at hmem
  exact one_ne_zero hmem

/-- First vertex-one coordinate of `P`. -/
def pTopCoord (z : PModule K) : K := z.1.1

@[simp] theorem pTopCoord_zero : pTopCoord K (0 : PModule K) = 0 := rfl

@[simp] theorem pTopCoord_add (z z' : PModule K) :
    pTopCoord K (z + z') = pTopCoord K z + pTopCoord K z' := rfl

@[simp] theorem pTopCoord_smul (b : B1Model K) (z : PModule K) :
    pTopCoord K (b • z) = b.fst.1.fst * pTopCoord K z := by
  exact b1Action_first_eq K (K × K) (PData K).loop.hom.hom
    (PData K).stem.hom.hom (PData K).loop_sq (by intro y; rfl) b z

/-- The common proper bound `{((0,s),(r,t))}` in `P`. -/
def pTopBound : Submodule (B1Model K) (PModule K) where
  carrier := {z | pTopCoord K z = 0}
  zero_mem' := rfl
  add_mem' := by
    intro z z' hz hz'
    change pTopCoord K z = 0 at hz
    change pTopCoord K z' = 0 at hz'
    change pTopCoord K (z + z') = 0
    simp only [pTopCoord_add, hz, hz', add_zero]
  smul_mem' := by
    intro b z hz
    change pTopCoord K z = 0 at hz
    change pTopCoord K (b • z) = 0
    simp only [pTopCoord_smul, hz, mul_zero]

def pTopGenerator : PModule K :=
  FiniteB1Rep.ofV₁ K (PData K) (1, 0)

theorem pTopBound_ne_top : pTopBound K ≠ ⊤ := by
  intro htop
  have hmem : pTopGenerator K ∈ pTopBound K := by
    rw [htop]
    exact Submodule.mem_top
  change (1 : K) = 0 at hmem
  exact one_ne_zero hmem

/-- Vertex-one coordinate of `A`; its zero locus is the vertex-two line. -/
def aFirstCoord (z : AModule K) : K := z.1

@[simp] theorem aFirstCoord_zero : aFirstCoord K (0 : AModule K) = 0 := rfl

@[simp] theorem aFirstCoord_add (z z' : AModule K) :
    aFirstCoord K (z + z') = aFirstCoord K z + aFirstCoord K z' := rfl

@[simp] theorem aFirstCoord_smul (b : B1Model K) (z : AModule K) :
    aFirstCoord K (b • z) = b.fst.1.fst * aFirstCoord K z := by
  exact b1Action_A_first_eq K b z

/-- The proper vertex-two line in `A`. -/
def aVertexTwoBound : Submodule (B1Model K) (AModule K) where
  carrier := {z | aFirstCoord K z = 0}
  zero_mem' := rfl
  add_mem' := by
    intro z z' hz hz'
    change aFirstCoord K z = 0 at hz
    change aFirstCoord K z' = 0 at hz'
    change aFirstCoord K (z + z') = 0
    simp only [aFirstCoord_add, hz, hz', add_zero]
  smul_mem' := by
    intro b z hz
    change aFirstCoord K z = 0 at hz
    change aFirstCoord K (b • z) = 0
    simp only [aFirstCoord_smul, hz, mul_zero]

def aTopGenerator : AModule K :=
  FiniteB1Rep.ofV₁ K (AData K) 1

theorem aVertexTwoBound_ne_top : aVertexTwoBound K ≠ ⊤ := by
  intro htop
  have hmem : aTopGenerator K ∈ aVertexTwoBound K := by
    rw [htop]
    exact Submodule.mem_top
  change (1 : K) = 0 at hmem
  exact one_ne_zero hmem

/-! ## Generator detectors for the `W` and `P` bounds -/

def wLoopDetector (z : WModule K) : K := z.1.2

def wStemDetector (z : WModule K) : K := z.2

@[simp] theorem wLoopDetector_zero : wLoopDetector K (0 : WModule K) = 0 := rfl

@[simp] theorem wStemDetector_zero : wStemDetector K (0 : WModule K) = 0 := rfl

@[simp] theorem wLoopDetector_x_smul (z : WModule K) :
    wLoopDetector K (x K • z) = wTopCoord K z := by
  rw [FiniteB1Rep.x_smul]
  rfl

@[simp] theorem wStemDetector_a_smul (z : WModule K) :
    wStemDetector K (a K • z) = wTopCoord K z := by
  rw [FiniteB1Rep.a_smul]
  rfl

def pLoopDetector (z : PModule K) : K := z.1.2

def pStemDetector (z : PModule K) : K := z.2.1

@[simp] theorem pLoopDetector_zero : pLoopDetector K (0 : PModule K) = 0 := rfl

@[simp] theorem pStemDetector_zero : pStemDetector K (0 : PModule K) = 0 := rfl

@[simp] theorem pLoopDetector_x_smul (z : PModule K) :
    pLoopDetector K (x K • z) = pTopCoord K z := by
  rw [FiniteB1Rep.x_smul]
  rfl

@[simp] theorem pStemDetector_a_smul (z : PModule K) :
    pStemDetector K (a K • z) = pTopCoord K z := by
  rw [FiniteB1Rep.a_smul]
  rfl

theorem x_smul_eq_zero_of_loop_eq_zero
    (D : FiniteB1Rep K)
    (hloop : ∀ z, D.loop.hom.hom z = 0)
    (z : D.Carrier K) : x K • z = 0 := by
  rw [FiniteB1Rep.x_smul]
  apply FiniteB1Rep.carrier_ext K D
  · exact hloop _
  · rfl

theorem a_smul_eq_zero_of_stem_eq_zero
    (D : FiniteB1Rep K)
    (hstem : ∀ z, D.stem.hom.hom z = 0)
    (z : D.Carrier K) : a K • z = 0 := by
  rw [FiniteB1Rep.a_smul]
  apply FiniteB1Rep.carrier_ext K D
  · rfl
  · exact hstem _

theorem range_le_wTopBound_of_loop_eq_zero
    (D : FiniteB1Rep K)
    (hloop : ∀ z, D.loop.hom.hom z = 0)
    (f : D.asFGModule K ⟶ WModule K) :
    LinearMap.range f.hom.hom ≤ wTopBound K := by
  rintro _ ⟨z, rfl⟩
  change wTopCoord K (f.hom.hom z) = 0
  have hx : x K • f.hom.hom z = 0 := by
    calc
      x K • f.hom.hom z = f.hom.hom (x K • z) :=
        (f.hom.hom.map_smul _ _).symm
      _ = f.hom.hom 0 := by rw [x_smul_eq_zero_of_loop_eq_zero K D hloop z]
      _ = 0 := f.hom.hom.map_zero
  calc
    wTopCoord K (f.hom.hom z) = wLoopDetector K (x K • f.hom.hom z) :=
      (wLoopDetector_x_smul K _).symm
    _ = wLoopDetector K 0 := congrArg (wLoopDetector K) hx
    _ = 0 := wLoopDetector_zero K

theorem range_le_wTopBound_of_stem_eq_zero
    (D : FiniteB1Rep K)
    (hstem : ∀ z, D.stem.hom.hom z = 0)
    (f : D.asFGModule K ⟶ WModule K) :
    LinearMap.range f.hom.hom ≤ wTopBound K := by
  rintro _ ⟨z, rfl⟩
  change wTopCoord K (f.hom.hom z) = 0
  have ha : a K • f.hom.hom z = 0 := by
    calc
      a K • f.hom.hom z = f.hom.hom (a K • z) :=
        (f.hom.hom.map_smul _ _).symm
      _ = f.hom.hom 0 := by rw [a_smul_eq_zero_of_stem_eq_zero K D hstem z]
      _ = 0 := f.hom.hom.map_zero
  calc
    wTopCoord K (f.hom.hom z) = wStemDetector K (a K • f.hom.hom z) :=
      (wStemDetector_a_smul K _).symm
    _ = wStemDetector K 0 := congrArg (wStemDetector K) ha
    _ = 0 := wStemDetector_zero K

theorem range_le_pTopBound_of_loop_eq_zero
    (D : FiniteB1Rep K)
    (hloop : ∀ z, D.loop.hom.hom z = 0)
    (f : D.asFGModule K ⟶ PModule K) :
    LinearMap.range f.hom.hom ≤ pTopBound K := by
  rintro _ ⟨z, rfl⟩
  change pTopCoord K (f.hom.hom z) = 0
  have hx : x K • f.hom.hom z = 0 := by
    calc
      x K • f.hom.hom z = f.hom.hom (x K • z) :=
        (f.hom.hom.map_smul _ _).symm
      _ = f.hom.hom 0 := by rw [x_smul_eq_zero_of_loop_eq_zero K D hloop z]
      _ = 0 := f.hom.hom.map_zero
  calc
    pTopCoord K (f.hom.hom z) = pLoopDetector K (x K • f.hom.hom z) :=
      (pLoopDetector_x_smul K _).symm
    _ = pLoopDetector K 0 := congrArg (pLoopDetector K) hx
    _ = 0 := pLoopDetector_zero K

theorem range_le_pTopBound_of_stem_eq_zero
    (D : FiniteB1Rep K)
    (hstem : ∀ z, D.stem.hom.hom z = 0)
    (f : D.asFGModule K ⟶ PModule K) :
    LinearMap.range f.hom.hom ≤ pTopBound K := by
  rintro _ ⟨z, rfl⟩
  change pTopCoord K (f.hom.hom z) = 0
  have ha : a K • f.hom.hom z = 0 := by
    calc
      a K • f.hom.hom z = f.hom.hom (a K • z) :=
        (f.hom.hom.map_smul _ _).symm
      _ = f.hom.hom 0 := by rw [a_smul_eq_zero_of_stem_eq_zero K D hstem z]
      _ = 0 := f.hom.hom.map_zero
  calc
    pTopCoord K (f.hom.hom z) = pStemDetector K (a K • f.hom.hom z) :=
      (pStemDetector_a_smul K _).symm
    _ = pStemDetector K 0 := congrArg (pStemDetector K) ha
    _ = 0 := pStemDetector_zero K

theorem range_X_W_le (f : XModule K ⟶ WModule K) :
    LinearMap.range f.hom.hom ≤ wTopBound K :=
  range_le_wTopBound_of_stem_eq_zero K (XData K) (by intro z; rfl) f

theorem range_S1_W_le (f : S1Module K ⟶ WModule K) :
    LinearMap.range f.hom.hom ≤ wTopBound K :=
  range_le_wTopBound_of_stem_eq_zero K (S1Data K) (by intro z; rfl) f

theorem range_A_W_le (f : AModule K ⟶ WModule K) :
    LinearMap.range f.hom.hom ≤ wTopBound K :=
  range_le_wTopBound_of_loop_eq_zero K (AData K) (by intro z; rfl) f

theorem range_S2_W_le (f : S2Module K ⟶ WModule K) :
    LinearMap.range f.hom.hom ≤ wTopBound K :=
  range_le_wTopBound_of_loop_eq_zero K (S2Data K) (by intro z; rfl) f

theorem range_X_P_le (f : XModule K ⟶ PModule K) :
    LinearMap.range f.hom.hom ≤ pTopBound K :=
  range_le_pTopBound_of_stem_eq_zero K (XData K) (by intro z; rfl) f

theorem range_S1_P_le (f : S1Module K ⟶ PModule K) :
    LinearMap.range f.hom.hom ≤ pTopBound K :=
  range_le_pTopBound_of_stem_eq_zero K (S1Data K) (by intro z; rfl) f

theorem range_A_P_le (f : AModule K ⟶ PModule K) :
    LinearMap.range f.hom.hom ≤ pTopBound K :=
  range_le_pTopBound_of_loop_eq_zero K (AData K) (by intro z; rfl) f

theorem range_S2_P_le (f : S2Module K ⟶ PModule K) :
    LinearMap.range f.hom.hom ≤ pTopBound K :=
  range_le_pTopBound_of_loop_eq_zero K (S2Data K) (by intro z; rfl) f

/-! ## Vertex-support and decomposition lemmas for exceptional sources -/

theorem image_ofV₁_snd_eq_zero
    (D E : FiniteB1Rep K)
    (f : D.asFGModule K ⟶ E.asFGModule K) (q : D.V₁) :
    (f.hom.hom (FiniteB1Rep.ofV₁ K D q)).2 = 0 := by
  have hfixed :
      e1 K • f.hom.hom (FiniteB1Rep.ofV₁ K D q) =
        f.hom.hom (FiniteB1Rep.ofV₁ K D q) := by
    calc
      e1 K • f.hom.hom (FiniteB1Rep.ofV₁ K D q) =
          f.hom.hom (e1 K • FiniteB1Rep.ofV₁ K D q) :=
        (f.hom.hom.map_smul _ _).symm
      _ = f.hom.hom (FiniteB1Rep.ofV₁ K D q) := by
        rw [FiniteB1Rep.e1_smul]
        simp [FiniteB1Rep.ofV₁]
  rw [FiniteB1Rep.e1_smul] at hfixed
  exact (congrArg Prod.snd hfixed).symm

theorem image_ofV₂_fst_eq_zero
    (D E : FiniteB1Rep K)
    (f : D.asFGModule K ⟶ E.asFGModule K) (q : D.V₂) :
    (f.hom.hom (FiniteB1Rep.ofV₂ K D q)).1 = 0 := by
  have hfixed :
      e2 K • f.hom.hom (FiniteB1Rep.ofV₂ K D q) =
        f.hom.hom (FiniteB1Rep.ofV₂ K D q) := by
    calc
      e2 K • f.hom.hom (FiniteB1Rep.ofV₂ K D q) =
          f.hom.hom (e2 K • FiniteB1Rep.ofV₂ K D q) :=
        (f.hom.hom.map_smul _ _).symm
      _ = f.hom.hom (FiniteB1Rep.ofV₂ K D q) := by
        rw [FiniteB1Rep.e2_smul]
        simp [FiniteB1Rep.ofV₂]
  rw [FiniteB1Rep.e2_smul] at hfixed
  exact (congrArg Prod.fst hfixed).symm

theorem carrier_eq_ofV₁_add_ofV₂
    (D : FiniteB1Rep K) (z : D.Carrier K) :
    z = FiniteB1Rep.ofV₁ K D z.1 + FiniteB1Rep.ofV₂ K D z.2 := by
  calc
    z = (1 : B1Model K) • z := (one_smul _ _).symm
    _ = (e1 K + e2 K) • z := by rw [e1_add_e2]
    _ = e1 K • z + e2 K • z := add_smul _ _ _
    _ = FiniteB1Rep.ofV₁ K D z.1 + FiniteB1Rep.ofV₂ K D z.2 := by
      rw [FiniteB1Rep.e1_smul, FiniteB1Rep.e2_smul]
      rfl

/-! ## The exceptional live-path source `U` -/

theorem map_U_W_ofV₂_eq_zero
    (f : UModule K ⟶ WModule K) (t : K) :
    f.hom.hom (FiniteB1Rep.ofV₂ K (UData K) t) = 0 := by
  have hu :
      u K • FiniteB1Rep.ofV₁ K (UData K) (t, 0) =
        FiniteB1Rep.ofV₂ K (UData K) t := by
    rw [FiniteB1Rep.u_smul]
    rfl
  calc
    f.hom.hom (FiniteB1Rep.ofV₂ K (UData K) t) =
        f.hom.hom (u K • FiniteB1Rep.ofV₁ K (UData K) (t, 0)) := by rw [hu]
    _ = u K • f.hom.hom (FiniteB1Rep.ofV₁ K (UData K) (t, 0)) :=
      f.hom.hom.map_smul _ _
    _ = 0 := W_u_smul_eq_zero K _

theorem range_U_W_le (f : UModule K ⟶ WModule K) :
    LinearMap.range f.hom.hom ≤ wTopBound K := by
  rintro _ ⟨z, rfl⟩
  change wTopCoord K (f.hom.hom z) = 0
  have haSource :
      a K • z = FiniteB1Rep.ofV₂ K (UData K) z.1.2 := by
    rw [FiniteB1Rep.a_smul]
    rfl
  have ha : a K • f.hom.hom z = 0 := by
    calc
      a K • f.hom.hom z = f.hom.hom (a K • z) :=
        (f.hom.hom.map_smul _ _).symm
      _ = f.hom.hom (FiniteB1Rep.ofV₂ K (UData K) z.1.2) := by rw [haSource]
      _ = 0 := map_U_W_ofV₂_eq_zero K f z.1.2
  calc
    wTopCoord K (f.hom.hom z) = wStemDetector K (a K • f.hom.hom z) :=
      (wStemDetector_a_smul K _).symm
    _ = wStemDetector K 0 := congrArg (wStemDetector K) ha
    _ = 0 := wStemDetector_zero K

theorem map_U_P_top_ofV₁_eq_zero
    (f : UModule K ⟶ PModule K) (t : K) :
    f.hom.hom (FiniteB1Rep.ofV₁ K (UData K) (t, 0)) = 0 := by
  let g := FiniteB1Rep.ofV₁ K (UData K) (t, 0)
  have hag : a K • g = 0 := by
    rw [FiniteB1Rep.a_smul]
    rfl
  have haimage : a K • f.hom.hom g = 0 := by
    calc
      a K • f.hom.hom g = f.hom.hom (a K • g) :=
        (f.hom.hom.map_smul _ _).symm
      _ = 0 := by rw [hag, map_zero]
  have hfst : (f.hom.hom g).1 = 0 := by
    rw [FiniteB1Rep.a_smul] at haimage
    exact congrArg Prod.snd haimage
  have hsnd : (f.hom.hom g).2 = 0 :=
    image_ofV₁_snd_eq_zero K (UData K) (PData K) f (t, 0)
  exact Prod.ext hfst hsnd

theorem map_U_P_ofV₂_eq_zero
    (f : UModule K ⟶ PModule K) (t : K) :
    f.hom.hom (FiniteB1Rep.ofV₂ K (UData K) t) = 0 := by
  have hu :
      u K • FiniteB1Rep.ofV₁ K (UData K) (t, 0) =
        FiniteB1Rep.ofV₂ K (UData K) t := by
    rw [FiniteB1Rep.u_smul]
    rfl
  calc
    f.hom.hom (FiniteB1Rep.ofV₂ K (UData K) t) =
        f.hom.hom (u K • FiniteB1Rep.ofV₁ K (UData K) (t, 0)) := by rw [hu]
    _ = u K • f.hom.hom (FiniteB1Rep.ofV₁ K (UData K) (t, 0)) :=
      f.hom.hom.map_smul _ _
    _ = 0 := by rw [map_U_P_top_ofV₁_eq_zero K f t, smul_zero]

theorem map_U_P_ofV₁_eq_zero
    (f : UModule K ⟶ PModule K) (q : K × K) :
    f.hom.hom (FiniteB1Rep.ofV₁ K (UData K) q) = 0 := by
  have haSource :
      a K • FiniteB1Rep.ofV₁ K (UData K) q =
        FiniteB1Rep.ofV₂ K (UData K) q.2 := by
    rw [FiniteB1Rep.a_smul]
    rfl
  have haimage :
      a K • f.hom.hom (FiniteB1Rep.ofV₁ K (UData K) q) = 0 := by
    calc
      a K • f.hom.hom (FiniteB1Rep.ofV₁ K (UData K) q) =
          f.hom.hom (a K • FiniteB1Rep.ofV₁ K (UData K) q) :=
        (f.hom.hom.map_smul _ _).symm
      _ = f.hom.hom (FiniteB1Rep.ofV₂ K (UData K) q.2) := by rw [haSource]
      _ = 0 := map_U_P_ofV₂_eq_zero K f q.2
  have hfst :
      (f.hom.hom (FiniteB1Rep.ofV₁ K (UData K) q)).1 = 0 := by
    rw [FiniteB1Rep.a_smul] at haimage
    exact congrArg Prod.snd haimage
  have hsnd :
      (f.hom.hom (FiniteB1Rep.ofV₁ K (UData K) q)).2 = 0 :=
    image_ofV₁_snd_eq_zero K (UData K) (PData K) f q
  exact Prod.ext hfst hsnd

theorem map_U_P_eq_zero
    (f : UModule K ⟶ PModule K) (z : UModule K) :
    f.hom.hom z = 0 := by
  rw [carrier_eq_ofV₁_add_ofV₂ K (UData K) z, map_add,
    map_U_P_ofV₁_eq_zero K f z.1, map_U_P_ofV₂_eq_zero K f z.2,
    add_zero]

theorem hom_U_P_eq_zero (f : UModule K ⟶ PModule K) : f = 0 := by
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact map_U_P_eq_zero K f z

theorem range_U_P_le (f : UModule K ⟶ PModule K) :
    LinearMap.range f.hom.hom ≤ pTopBound K := by
  rw [hom_U_P_eq_zero K f]
  simp

/-! ## Exact Hom-zero certificates for the omitted simples/string `A` -/

theorem map_to_S2_eq_zero_of_stem_surjective
    (D : FiniteB1Rep K)
    (hsurj : Function.Surjective D.stem.hom.hom)
    (f : D.asFGModule K ⟶ S2Module K) (z : D.Carrier K) :
    f.hom.hom z = 0 := by
  have hV₁ : ∀ q : D.V₁,
      f.hom.hom (FiniteB1Rep.ofV₁ K D q) = 0 := by
    intro q
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · exact image_ofV₁_snd_eq_zero K D (S2Data K) f q
  have hV₂ : ∀ t : D.V₂,
      f.hom.hom (FiniteB1Rep.ofV₂ K D t) = 0 := by
    intro t
    obtain ⟨q, hq⟩ := hsurj t
    have ha :
        a K • FiniteB1Rep.ofV₁ K D q =
          FiniteB1Rep.ofV₂ K D t := by
      rw [FiniteB1Rep.a_smul]
      apply FiniteB1Rep.carrier_ext K D
      · rfl
      · exact hq
    calc
      f.hom.hom (FiniteB1Rep.ofV₂ K D t) =
          f.hom.hom (a K • FiniteB1Rep.ofV₁ K D q) := by rw [ha]
      _ = a K • f.hom.hom (FiniteB1Rep.ofV₁ K D q) :=
        f.hom.hom.map_smul _ _
      _ = 0 := by
        rw [FiniteB1Rep.a_smul]
        rfl
  rw [carrier_eq_ofV₁_add_ofV₂ K D z, map_add, hV₁ z.1, hV₂ z.2,
    add_zero]

theorem hom_to_S2_eq_zero_of_stem_surjective
    (D : FiniteB1Rep K)
    (hsurj : Function.Surjective D.stem.hom.hom)
    (f : D.asFGModule K ⟶ S2Module K) : f = 0 := by
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact map_to_S2_eq_zero_of_stem_surjective K D hsurj f z

theorem hom_X_S2_eq_zero (f : XModule K ⟶ S2Module K) : f = 0 :=
  hom_to_S2_eq_zero_of_stem_surjective K (XData K)
    (by intro t; exact ⟨0, Subsingleton.elim _ _⟩) f

theorem hom_U_S2_eq_zero (f : UModule K ⟶ S2Module K) : f = 0 :=
  hom_to_S2_eq_zero_of_stem_surjective K (UData K)
    (by intro t; exact ⟨(0, t), rfl⟩) f

theorem hom_S1_S2_eq_zero (f : S1Module K ⟶ S2Module K) : f = 0 :=
  hom_to_S2_eq_zero_of_stem_surjective K (S1Data K)
    (by intro t; exact ⟨0, Subsingleton.elim _ _⟩) f

theorem hom_A_S2_eq_zero (f : AModule K ⟶ S2Module K) : f = 0 :=
  hom_to_S2_eq_zero_of_stem_surjective K (AData K)
    (by intro t; exact ⟨t, rfl⟩) f

theorem map_to_A_eq_zero_of_livePath_surjective
    (D : FiniteB1Rep K)
    (hsurj : Function.Surjective
      (D.stem.hom.hom.comp D.loop.hom.hom))
    (f : D.asFGModule K ⟶ AModule K) (z : D.Carrier K) :
    f.hom.hom z = 0 := by
  have hV₂ : ∀ t : D.V₂,
      f.hom.hom (FiniteB1Rep.ofV₂ K D t) = 0 := by
    intro t
    obtain ⟨q, hq⟩ := hsurj t
    have hu :
        u K • FiniteB1Rep.ofV₁ K D q =
          FiniteB1Rep.ofV₂ K D t := by
      rw [FiniteB1Rep.u_smul]
      apply FiniteB1Rep.carrier_ext K D
      · rfl
      · exact hq
    calc
      f.hom.hom (FiniteB1Rep.ofV₂ K D t) =
          f.hom.hom (u K • FiniteB1Rep.ofV₁ K D q) := by rw [hu]
      _ = u K • f.hom.hom (FiniteB1Rep.ofV₁ K D q) :=
        f.hom.hom.map_smul _ _
      _ = 0 := by
        rw [FiniteB1Rep.u_smul]
        rfl
  have hV₁ : ∀ q : D.V₁,
      f.hom.hom (FiniteB1Rep.ofV₁ K D q) = 0 := by
    intro q
    have haSource :
        a K • FiniteB1Rep.ofV₁ K D q =
          FiniteB1Rep.ofV₂ K D (D.stem.hom.hom q) := by
      rw [FiniteB1Rep.a_smul]
      rfl
    have haimage :
        a K • f.hom.hom (FiniteB1Rep.ofV₁ K D q) = 0 := by
      calc
        a K • f.hom.hom (FiniteB1Rep.ofV₁ K D q) =
            f.hom.hom (a K • FiniteB1Rep.ofV₁ K D q) :=
          (f.hom.hom.map_smul _ _).symm
        _ = f.hom.hom (FiniteB1Rep.ofV₂ K D (D.stem.hom.hom q)) := by
          rw [haSource]
        _ = 0 := hV₂ _
    have hfst :
        (f.hom.hom (FiniteB1Rep.ofV₁ K D q)).1 = 0 := by
      rw [FiniteB1Rep.a_smul] at haimage
      exact congrArg Prod.snd haimage
    have hsnd :
        (f.hom.hom (FiniteB1Rep.ofV₁ K D q)).2 = 0 :=
      image_ofV₁_snd_eq_zero K D (AData K) f q
    exact Prod.ext hfst hsnd
  rw [carrier_eq_ofV₁_add_ofV₂ K D z, map_add, hV₁ z.1, hV₂ z.2,
    add_zero]

theorem hom_to_A_eq_zero_of_livePath_surjective
    (D : FiniteB1Rep K)
    (hsurj : Function.Surjective
      (D.stem.hom.hom.comp D.loop.hom.hom))
    (f : D.asFGModule K ⟶ AModule K) : f = 0 := by
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact map_to_A_eq_zero_of_livePath_surjective K D hsurj f z

theorem hom_X_A_eq_zero (f : XModule K ⟶ AModule K) : f = 0 :=
  hom_to_A_eq_zero_of_livePath_surjective K (XData K)
    (by intro t; exact ⟨0, Subsingleton.elim _ _⟩) f

theorem hom_U_A_eq_zero (f : UModule K ⟶ AModule K) : f = 0 :=
  hom_to_A_eq_zero_of_livePath_surjective K (UData K)
    (by intro t; exact ⟨(t, 0), rfl⟩) f

theorem hom_S1_A_eq_zero (f : S1Module K ⟶ AModule K) : f = 0 :=
  hom_to_A_eq_zero_of_livePath_surjective K (S1Data K)
    (by intro t; exact ⟨0, Subsingleton.elim _ _⟩) f

theorem range_S2_A_le (f : S2Module K ⟶ AModule K) :
    LinearMap.range f.hom.hom ≤ aVertexTwoBound K := by
  rintro _ ⟨z, rfl⟩
  change aFirstCoord K (f.hom.hom z) = 0
  have hz : e2 K • z = z := by
    rw [FiniteB1Rep.e2_smul]
    apply FiniteB1Rep.carrier_ext K (S2Data K)
    · exact Subsingleton.elim _ _
    · rfl
  have hfixed : e2 K • f.hom.hom z = f.hom.hom z := by
    calc
      e2 K • f.hom.hom z = f.hom.hom (e2 K • z) :=
        (f.hom.hom.map_smul _ _).symm
      _ = f.hom.hom z := by rw [hz]
  rw [FiniteB1Rep.e2_smul] at hfixed
  exact (congrArg Prod.fst hfixed).symm

/-! ## The two explicitly enumerated good quotient rows -/

/-- Sources in the maintained row `core {X,U,S₁} + A`. -/
inductive ARowSource where
  | x
  | u
  | s1
  | a
  deriving DecidableEq

def aRowSourceModule : ARowSource → FGModuleCat (B1Model K)
  | .x => XModule K
  | .u => UModule K
  | .s1 => S1Module K
  | .a => AModule K

/-- Every individual map from an `A`-row source to the omitted simple `S₂`
is zero. -/
theorem aRow_hom_S2_eq_zero
    (i : ARowSource) (f : aRowSourceModule K i ⟶ S2Module K) : f = 0 := by
  cases i with
  | x => exact hom_X_S2_eq_zero K f
  | u => exact hom_U_S2_eq_zero K f
  | s1 => exact hom_S1_S2_eq_zero K f
  | a => exact hom_A_S2_eq_zero K f

theorem aRow_range_W_le
    (i : ARowSource) (f : aRowSourceModule K i ⟶ WModule K) :
    LinearMap.range f.hom.hom ≤ wTopBound K := by
  cases i with
  | x => exact range_X_W_le K f
  | u => exact range_U_W_le K f
  | s1 => exact range_S1_W_le K f
  | a => exact range_A_W_le K f

theorem aRow_range_P_le
    (i : ARowSource) (f : aRowSourceModule K i ⟶ PModule K) :
    LinearMap.range f.hom.hom ≤ pTopBound K := by
  cases i with
  | x => exact range_X_P_le K f
  | u => exact range_U_P_le K f
  | s1 => exact range_S1_P_le K f
  | a => exact range_A_P_le K f

/-- Sources in the maintained row `core {X,U,S₁} + S₂`. -/
inductive S2RowSource where
  | x
  | u
  | s1
  | s2
  deriving DecidableEq

def s2RowSourceModule : S2RowSource → FGModuleCat (B1Model K)
  | .x => XModule K
  | .u => UModule K
  | .s1 => S1Module K
  | .s2 => S2Module K

theorem s2Row_range_A_le
    (i : S2RowSource) (f : s2RowSourceModule K i ⟶ AModule K) :
    LinearMap.range f.hom.hom ≤ aVertexTwoBound K := by
  cases i with
  | x =>
      rw [hom_X_A_eq_zero K f]
      change LinearMap.range (0 : XModule K →ₗ[B1Model K] AModule K) ≤ _
      rw [LinearMap.range_zero]
      exact bot_le
  | u =>
      rw [hom_U_A_eq_zero K f]
      change LinearMap.range (0 : UModule K →ₗ[B1Model K] AModule K) ≤ _
      rw [LinearMap.range_zero]
      exact bot_le
  | s1 =>
      rw [hom_S1_A_eq_zero K f]
      change LinearMap.range (0 : S1Module K →ₗ[B1Model K] AModule K) ≤ _
      rw [LinearMap.range_zero]
      exact bot_le
  | s2 => exact range_S2_A_le K f

theorem s2Row_range_W_le
    (i : S2RowSource) (f : s2RowSourceModule K i ⟶ WModule K) :
    LinearMap.range f.hom.hom ≤ wTopBound K := by
  cases i with
  | x => exact range_X_W_le K f
  | u => exact range_U_W_le K f
  | s1 => exact range_S1_W_le K f
  | s2 => exact range_S2_W_le K f

theorem s2Row_range_P_le
    (i : S2RowSource) (f : s2RowSourceModule K i ⟶ PModule K) :
    LinearMap.range f.hom.hom ≤ pTopBound K := by
  cases i with
  | x => exact range_X_P_le K f
  | u => exact range_U_P_le K f
  | s1 => exact range_S1_P_le K f
  | s2 => exact range_S2_P_le K f

/-! ## Finite-biproduct aggregation over exactly the displayed sources -/

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- A map from a finite direct sum of explicitly labelled sources to one
target.  This deliberately does not quantify over an indecomposable skeleton. -/
structure EnumeratedSelectedMapTo
    {R : Type u} [Ring R]
    (I : Type v) (source : I → FGModuleCat.{w} R)
    (target : FGModuleCat.{w} R) where
  index : FintypeCat.{0}
  label : index → I
  map : biproduct (fun t ↦ source (label t)) ⟶ target

/-- Sum of the ranges of all maps from finite direct sums of the explicitly
enumerated sources. -/
def enumeratedTrace
    {R : Type u} [Ring R]
    {I : Type v} (source : I → FGModuleCat.{w} R)
    (target : FGModuleCat.{w} R) : Submodule R target :=
  ⨆ F : EnumeratedSelectedMapTo I source target, LinearMap.range F.map.hom.hom

/-- Common proper-range data for every individual explicitly labelled source. -/
structure EnumeratedCommonRangeCertificate
    {R : Type u} [Ring R]
    (I : Type v) (source : I → FGModuleCat.{w} R)
    (target : FGModuleCat.{w} R) where
  bound : Submodule R target
  bound_ne_top : bound ≠ ⊤
  range_le : ∀ i (f : source i ⟶ target), LinearMap.range f.hom.hom ≤ bound

theorem enumeratedTrace_le_of_forall_range_le
    {R : Type u} [Ring R] [IsNoetherianRing R]
    {I : Type v} {source : I → FGModuleCat.{w} R}
    {target : FGModuleCat.{w} R}
    (bound : Submodule R target)
    (hrange : ∀ i (f : source i ⟶ target),
      LinearMap.range f.hom.hom ≤ bound) :
    enumeratedTrace source target ≤ bound := by
  apply iSup_le
  intro F
  let Q : FGModuleCat.{w} R := FGModuleCat.of R (target ⧸ bound)
  let q : target ⟶ Q := FGModuleCat.ofHom bound.mkQ
  have hcomp : F.map ≫ q = 0 := by
    apply biproduct.hom_ext'
    intro t
    let g : source (F.label t) ⟶ target :=
      biproduct.ι (fun s : F.index ↦ source (F.label s)) t ≫ F.map
    change g ≫ q = 0
    apply FGModuleCat.hom_ext
    change bound.mkQ.comp g.hom.hom = 0
    rw [← LinearMap.range_le_ker_iff, Submodule.ker_mkQ]
    exact hrange (F.label t) g
  rw [← Submodule.ker_mkQ bound, LinearMap.range_le_ker_iff]
  have hlinear := congrArg (fun z ↦ z.hom.hom) hcomp
  change bound.mkQ.comp F.map.hom.hom = 0 at hlinear
  exact hlinear

namespace EnumeratedCommonRangeCertificate

theorem enumeratedTrace_le
    {R : Type u} [Ring R] [IsNoetherianRing R]
    {I : Type v} {source : I → FGModuleCat.{w} R}
    {target : FGModuleCat.{w} R}
    (C : EnumeratedCommonRangeCertificate I source target) :
    QuotientRows.enumeratedTrace source target ≤ C.bound :=
  enumeratedTrace_le_of_forall_range_le C.bound C.range_le

end EnumeratedCommonRangeCertificate

/-- Exact finite-sum form of the `A`-row zero-Hom statement. -/
theorem aRow_finiteSum_hom_S2_eq_zero
    (F : EnumeratedSelectedMapTo ARowSource (aRowSourceModule K) (S2Module K)) :
    F.map = 0 := by
  apply biproduct.hom_ext'
  intro t
  exact aRow_hom_S2_eq_zero K (F.label t)
    (biproduct.ι (fun s : F.index ↦ aRowSourceModule K (F.label s)) t ≫ F.map)

theorem aRow_enumeratedTrace_S2_eq_bot :
    enumeratedTrace (aRowSourceModule K) (S2Module K) = ⊥ := by
  apply le_antisymm
  · apply iSup_le
    intro F
    have hzero : F.map.hom.hom = 0 :=
      congrArg (fun f ↦ f.hom.hom) (aRow_finiteSum_hom_S2_eq_zero K F)
    rw [hzero, LinearMap.range_zero]
  · exact bot_le

def aRowWCommonRangeCertificate :
    EnumeratedCommonRangeCertificate ARowSource (aRowSourceModule K) (WModule K) where
  bound := wTopBound K
  bound_ne_top := wTopBound_ne_top K
  range_le := aRow_range_W_le K

def aRowPCommonRangeCertificate :
    EnumeratedCommonRangeCertificate ARowSource (aRowSourceModule K) (PModule K) where
  bound := pTopBound K
  bound_ne_top := pTopBound_ne_top K
  range_le := aRow_range_P_le K

def s2RowACommonRangeCertificate :
    EnumeratedCommonRangeCertificate S2RowSource (s2RowSourceModule K) (AModule K) where
  bound := aVertexTwoBound K
  bound_ne_top := aVertexTwoBound_ne_top K
  range_le := s2Row_range_A_le K

def s2RowWCommonRangeCertificate :
    EnumeratedCommonRangeCertificate S2RowSource (s2RowSourceModule K) (WModule K) where
  bound := wTopBound K
  bound_ne_top := wTopBound_ne_top K
  range_le := s2Row_range_W_le K

def s2RowPCommonRangeCertificate :
    EnumeratedCommonRangeCertificate S2RowSource (s2RowSourceModule K) (PModule K) where
  bound := pTopBound K
  bound_ne_top := pTopBound_ne_top K
  range_le := s2Row_range_P_le K

theorem aRow_enumeratedTrace_W_le :
    enumeratedTrace (aRowSourceModule K) (WModule K) ≤ wTopBound K :=
  (aRowWCommonRangeCertificate K).enumeratedTrace_le

theorem aRow_enumeratedTrace_P_le :
    enumeratedTrace (aRowSourceModule K) (PModule K) ≤ pTopBound K :=
  (aRowPCommonRangeCertificate K).enumeratedTrace_le

theorem s2Row_enumeratedTrace_A_le :
    enumeratedTrace (s2RowSourceModule K) (AModule K) ≤ aVertexTwoBound K :=
  (s2RowACommonRangeCertificate K).enumeratedTrace_le

theorem s2Row_enumeratedTrace_W_le :
    enumeratedTrace (s2RowSourceModule K) (WModule K) ≤ wTopBound K :=
  (s2RowWCommonRangeCertificate K).enumeratedTrace_le

theorem s2Row_enumeratedTrace_P_le :
    enumeratedTrace (s2RowSourceModule K) (PModule K) ≤ pTopBound K :=
  (s2RowPCommonRangeCertificate K).enumeratedTrace_le

end QuotientSubmoduleEquidistribution.LollipopConcrete.B1.ModuleLayer.QuotientRows
