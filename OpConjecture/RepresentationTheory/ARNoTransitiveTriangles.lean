import OpConjecture.RepresentationTheory.ARLocalRestrictions

/-!
# No transitive triangles in a finite Auslander--Reiten quiver

The length-two case of the no-sectional-bypass theorem needed by the
four-vertex strip argument can be proved directly from mesh incidence and
finite-dimensionality.  If an arrow `a → b` has a length-two bypass
`a → u → b`, rotate the triangle forward or backward according to the
dimension orientation of `a → b`.  Two distinct middle summands in the
relevant AR mesh force the same orientation on the rotated triangle, while
the sum of two successive dimensions strictly increases.  This contradicts
finiteness of the skeleton.

No presentation or classification of modules or algebras enters.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace OpConjecture.IndecomposableSkeleton

universe u v

variable {K R : Type u} [Field K] [Ring R] [Algebra K R]
  [FiniteDimensional K R] [IsNoetherianRing R]
  {ι : Type v} [Fintype ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)

namespace FiniteARTranslationData

variable (AR : σ.FiniteARTranslationData)

omit [Fintype ι] in
include K in
/-- An irreducible arrow cannot run directly from an injective object to a
projective object: the two boundary dimension inequalities point in opposite
directions. -/
theorem no_irreducible_injective_to_projective
    {i p : ι} (hi : Injective (σ.obj i))
    (hp : Projective (σ.obj p)) :
    ¬ HasIrreducibleMorphism (σ.obj i) (σ.obj p) := by
  intro hip
  have hdown := groundFinrank_lt_of_irreducible_from_injective
    (K := K) σ hi hip
  have hup := groundFinrank_lt_of_irreducible_to_projective
    (K := K) σ hp hip
  omega

/-- A directed triangle in the irreducible-morphism graph.  Equivalently,
the arrow `a → b` has a bypass of length two through `u`. -/
@[ext]
structure TransitiveTriangle where
  a : ι
  u : ι
  b : ι
  a_to_u : HasIrreducibleMorphism (σ.obj a) (σ.obj u)
  u_to_b : HasIrreducibleMorphism (σ.obj u) (σ.obj b)
  a_to_b : HasIrreducibleMorphism (σ.obj a) (σ.obj b)

noncomputable instance transitiveTriangleFinite :
    Finite (TransitiveTriangle σ) :=
  Finite.of_injective
    (fun T ↦ (T.a, T.u, T.b)) (by
      intro T₁ T₂ h
      apply TransitiveTriangle.ext
      · exact congrArg (fun x ↦ x.1) h
      · exact congrArg (fun x ↦ x.2.1) h
      · exact congrArg (fun x ↦ x.2.2) h)

namespace TransitiveTriangle

variable (T : TransitiveTriangle σ)

omit [Fintype ι] in
theorem a_ne_u : T.a ≠ T.u := by
  intro h
  exact σ.hasNoIrreducibleEndomorphism_obj T.a (by
    simpa [h] using T.a_to_u)

omit [Fintype ι] in
theorem u_ne_b : T.u ≠ T.b := by
  intro h
  exact σ.hasNoIrreducibleEndomorphism_obj T.u (by
    simpa [h] using T.u_to_b)

omit [Fintype ι] in
theorem a_ne_b : T.a ≠ T.b := by
  intro h
  exact σ.hasNoIrreducibleEndomorphism_obj T.a (by
    simpa [h] using T.a_to_b)

end TransitiveTriangle

omit [Fintype ι] in
/-- Ground-field dimensions at the ends of an irreducible arrow have one
of the two strict orientations. -/
theorem groundFinrank_orientation_of_hasIrreducibleMorphism
    {x y : ι}
    (hxy : HasIrreducibleMorphism (σ.obj x) (σ.obj y)) :
    OpConjecture.RepresentationDirected.groundFinrank
          (K := K) (σ.obj x) <
        OpConjecture.RepresentationDirected.groundFinrank
          (K := K) (σ.obj y) ∨
      OpConjecture.RepresentationDirected.groundFinrank
          (K := K) (σ.obj y) <
        OpConjecture.RepresentationDirected.groundFinrank
          (K := K) (σ.obj x) := by
  obtain ⟨f, hf⟩ := hxy
  letI : Module K (σ.obj x) := Module.restrictScalars K R (σ.obj x)
  letI : IsScalarTower K R (σ.obj x) :=
    IsScalarTower.restrictScalars K R (σ.obj x)
  letI : FiniteDimensional K (σ.obj x) := Module.Finite.trans R (σ.obj x)
  letI : Module K (σ.obj y) := Module.restrictScalars K R (σ.obj y)
  letI : IsScalarTower K R (σ.obj y) :=
    IsScalarTower.restrictScalars K R (σ.obj y)
  letI : FiniteDimensional K (σ.obj y) := Module.Finite.trans R (σ.obj y)
  rcases
      OpConjecture.RepresentationDirected.finrank_orientation_of_isIrreducibleMorphism
        (K := K) hf with h | h
  · exact Or.inl h.1
  · exact Or.inr h.1

omit [Fintype ι] in
/-- A dimension-increasing irreducible arrow cannot start at an injective
object. -/
theorem not_injective_of_hasIrreducibleMorphism_of_groundFinrank_lt
    {x y : ι}
    (hxy : HasIrreducibleMorphism (σ.obj x) (σ.obj y))
    (hdim :
      OpConjecture.RepresentationDirected.groundFinrank
          (K := K) (σ.obj x) <
        OpConjecture.RepresentationDirected.groundFinrank
          (K := K) (σ.obj y)) :
    ¬ Injective (σ.obj x) := by
  obtain ⟨f, hf⟩ := hxy
  letI : Module K (σ.obj x) := Module.restrictScalars K R (σ.obj x)
  letI : IsScalarTower K R (σ.obj x) :=
    IsScalarTower.restrictScalars K R (σ.obj x)
  letI : FiniteDimensional K (σ.obj x) := Module.Finite.trans R (σ.obj x)
  letI : Module K (σ.obj y) := Module.restrictScalars K R (σ.obj y)
  letI : IsScalarTower K R (σ.obj y) :=
    IsScalarTower.restrictScalars K R (σ.obj y)
  letI : FiniteDimensional K (σ.obj y) := Module.Finite.trans R (σ.obj y)
  have hdim' : Module.finrank K (σ.obj x) < Module.finrank K (σ.obj y) := by
    simpa [OpConjecture.RepresentationDirected.groundFinrank] using hdim
  letI : Mono f :=
    OpConjecture.RepresentationDirected.mono_of_isIrreducibleMorphism_of_finrank_lt
      (K := K) hf hdim'
  exact
    OpConjecture.RepresentationDirected.not_injective_source_of_isIrreducibleMorphism_of_mono
      hf

omit [Fintype ι] in
/-- A dimension-decreasing irreducible arrow cannot end at a projective
object. -/
theorem not_projective_of_hasIrreducibleMorphism_of_groundFinrank_gt
    {x y : ι}
    (hxy : HasIrreducibleMorphism (σ.obj x) (σ.obj y))
    (hdim :
      OpConjecture.RepresentationDirected.groundFinrank
          (K := K) (σ.obj y) <
        OpConjecture.RepresentationDirected.groundFinrank
          (K := K) (σ.obj x)) :
    ¬ Projective (σ.obj y) := by
  obtain ⟨f, hf⟩ := hxy
  letI : Module K (σ.obj x) := Module.restrictScalars K R (σ.obj x)
  letI : IsScalarTower K R (σ.obj x) :=
    IsScalarTower.restrictScalars K R (σ.obj x)
  letI : FiniteDimensional K (σ.obj x) := Module.Finite.trans R (σ.obj x)
  letI : Module K (σ.obj y) := Module.restrictScalars K R (σ.obj y)
  letI : IsScalarTower K R (σ.obj y) :=
    IsScalarTower.restrictScalars K R (σ.obj y)
  letI : FiniteDimensional K (σ.obj y) := Module.Finite.trans R (σ.obj y)
  have hdim' : Module.finrank K (σ.obj y) < Module.finrank K (σ.obj x) := by
    simpa [OpConjecture.RepresentationDirected.groundFinrank] using hdim
  letI : Epi f :=
    OpConjecture.RepresentationDirected.epi_of_isIrreducibleMorphism_of_finrank_gt
      (K := K) hf hdim'
  exact
    OpConjecture.RepresentationDirected.not_projective_target_of_isIrreducibleMorphism_of_epi
      hf

include K AR in
/-- Rotate a transitive triangle forward when the chord increases in
dimension.  The next chord has the same orientation. -/
theorem exists_forward_rotated_transitiveTriangle
    (T : TransitiveTriangle σ)
    (hdim :
      OpConjecture.RepresentationDirected.groundFinrank
          (K := K) (σ.obj T.a) <
        OpConjecture.RepresentationDirected.groundFinrank
          (K := K) (σ.obj T.b)) :
    ∃ c : ι,
      HasIrreducibleMorphism (σ.obj T.u) (σ.obj c) ∧
        HasIrreducibleMorphism (σ.obj T.b) (σ.obj c) ∧
        OpConjecture.RepresentationDirected.groundFinrank
            (K := K) (σ.obj T.u) <
          OpConjecture.RepresentationDirected.groundFinrank
            (K := K) (σ.obj c) := by
  classical
  have haNoninjective : ¬ Injective (σ.obj T.a) :=
    not_injective_of_hasIrreducibleMorphism_of_groundFinrank_lt
      (K := K) σ T.a_to_b hdim
  let aNI : σ.NoninjectiveLabel := ⟨T.a, haNoninjective⟩
  let cNP : σ.NonprojectiveLabel := (AR.arTranslationEquiv σ).symm aNI
  let c : ι := cNP.1
  have hTau : (AR.arTranslation σ cNP).1 = T.a := by
    have h := (AR.arTranslationEquiv σ).apply_symm_apply aNI
    exact congrArg Subtype.val h
  have huc : HasIrreducibleMorphism (σ.obj T.u) (σ.obj c) := by
    apply (AR.arTranslation_incidence σ cNP T.u).2
    simpa [c, hTau] using T.a_to_u
  have hbc : HasIrreducibleMorphism (σ.obj T.b) (σ.obj c) := by
    apply (AR.arTranslation_incidence σ cNP T.b).2
    simpa [c, hTau] using T.a_to_b
  let A := AR.chosenRightAR σ cNP
  obtain ⟨tu, htu⟩ := (A.summandIrreducibleCorrespondence T.u).2 huc
  obtain ⟨tb, htb⟩ := (A.summandIrreducibleCorrespondence T.b).2 hbc
  have htne : tu ≠ tb := by
    intro h
    apply T.u_ne_b σ
    rw [← htu, ← htb, h]
  have hmiddle := add_groundFinrank_le_middle_of_two_occurrences
    (K := K) σ A tu tb htne
  rw [htu, htb] at hmiddle
  have hmesh := AR.arTranslation_add_endpoint_groundFinrank_eq_middle
    (K := K) σ cNP
  rw [hTau] at hmesh
  change
    OpConjecture.RepresentationDirected.groundFinrank
          (K := K) (σ.obj T.a) +
        OpConjecture.RepresentationDirected.groundFinrank
          (K := K) (σ.obj c) =
      OpConjecture.RepresentationDirected.groundFinrank
        (K := K) A.middle at hmesh
  refine ⟨c, huc, hbc, ?_⟩
  omega

omit [Fintype ι] in
include K AR in
/-- Rotate a transitive triangle backward when the chord decreases in
dimension.  The preceding chord has the same orientation. -/
theorem exists_backward_rotated_transitiveTriangle
    (T : TransitiveTriangle σ)
    (hdim :
      OpConjecture.RepresentationDirected.groundFinrank
          (K := K) (σ.obj T.b) <
        OpConjecture.RepresentationDirected.groundFinrank
          (K := K) (σ.obj T.a)) :
    ∃ c : ι,
      HasIrreducibleMorphism (σ.obj c) (σ.obj T.a) ∧
        HasIrreducibleMorphism (σ.obj c) (σ.obj T.u) ∧
        OpConjecture.RepresentationDirected.groundFinrank
            (K := K) (σ.obj T.u) <
          OpConjecture.RepresentationDirected.groundFinrank
            (K := K) (σ.obj c) := by
  classical
  have hbNonprojective : ¬ Projective (σ.obj T.b) :=
    not_projective_of_hasIrreducibleMorphism_of_groundFinrank_gt
      (K := K) σ T.a_to_b hdim
  let bNP : σ.NonprojectiveLabel := ⟨T.b, hbNonprojective⟩
  let c : ι := (AR.arTranslation σ bNP).1
  have hca : HasIrreducibleMorphism (σ.obj c) (σ.obj T.a) := by
    exact (AR.arTranslation_incidence σ bNP T.a).1 T.a_to_b
  have hcu : HasIrreducibleMorphism (σ.obj c) (σ.obj T.u) := by
    exact (AR.arTranslation_incidence σ bNP T.u).1 T.u_to_b
  let A := AR.chosenRightAR σ bNP
  obtain ⟨ta, hta⟩ := (A.summandIrreducibleCorrespondence T.a).2 T.a_to_b
  obtain ⟨tu, htu⟩ := (A.summandIrreducibleCorrespondence T.u).2 T.u_to_b
  have htne : ta ≠ tu := by
    intro h
    apply T.a_ne_u σ
    rw [← hta, ← htu, h]
  have hmiddle := add_groundFinrank_le_middle_of_two_occurrences
    (K := K) σ A ta tu htne
  rw [hta, htu] at hmiddle
  have hmesh := AR.arTranslation_add_endpoint_groundFinrank_eq_middle
    (K := K) σ bNP
  change
    OpConjecture.RepresentationDirected.groundFinrank
          (K := K) (σ.obj c) +
        OpConjecture.RepresentationDirected.groundFinrank
          (K := K) (σ.obj T.b) =
      OpConjecture.RepresentationDirected.groundFinrank
        (K := K) A.middle at hmesh
  refine ⟨c, hca, hcu, ?_⟩
  omega

include K AR in
/-- There is no transitive triangle whose chord increases in ground-field
dimension. -/
theorem no_increasing_transitiveTriangle :
    ¬ ∃ T : TransitiveTriangle σ,
      OpConjecture.RepresentationDirected.groundFinrank
          (K := K) (σ.obj T.a) <
        OpConjecture.RepresentationDirected.groundFinrank
          (K := K) (σ.obj T.b) := by
  apply OpConjecture.RepresentationDirected.not_exists_of_finite_strict_ascent
    (P := fun T : TransitiveTriangle σ ↦
      OpConjecture.RepresentationDirected.groundFinrank
          (K := K) (σ.obj T.a) <
        OpConjecture.RepresentationDirected.groundFinrank
          (K := K) (σ.obj T.b))
    (weight := fun T ↦
      OpConjecture.RepresentationDirected.groundFinrank
          (K := K) (σ.obj T.a) +
        OpConjecture.RepresentationDirected.groundFinrank
          (K := K) (σ.obj T.u))
  intro T hdim
  obtain ⟨c, huc, hbc, hdim'⟩ :=
    exists_forward_rotated_transitiveTriangle (K := K) σ AR T hdim
  let T' : TransitiveTriangle σ :=
    { a := T.u
      u := T.b
      b := c
      a_to_u := T.u_to_b
      u_to_b := hbc
      a_to_b := huc }
  refine ⟨T', hdim', ?_⟩
  dsimp [T']
  omega

include K AR in
/-- There is no transitive triangle whose chord decreases in ground-field
dimension. -/
theorem no_decreasing_transitiveTriangle :
    ¬ ∃ T : TransitiveTriangle σ,
      OpConjecture.RepresentationDirected.groundFinrank
          (K := K) (σ.obj T.b) <
        OpConjecture.RepresentationDirected.groundFinrank
          (K := K) (σ.obj T.a) := by
  apply OpConjecture.RepresentationDirected.not_exists_of_finite_strict_ascent
    (P := fun T : TransitiveTriangle σ ↦
      OpConjecture.RepresentationDirected.groundFinrank
          (K := K) (σ.obj T.b) <
        OpConjecture.RepresentationDirected.groundFinrank
          (K := K) (σ.obj T.a))
    (weight := fun T ↦
      OpConjecture.RepresentationDirected.groundFinrank
          (K := K) (σ.obj T.u) +
        OpConjecture.RepresentationDirected.groundFinrank
          (K := K) (σ.obj T.b))
  intro T hdim
  obtain ⟨c, hca, hcu, hdim'⟩ :=
    exists_backward_rotated_transitiveTriangle (K := K) σ AR T hdim
  let T' : TransitiveTriangle σ :=
    { a := c
      u := T.a
      b := T.u
      a_to_u := hca
      u_to_b := T.a_to_u
      a_to_b := hcu }
  refine ⟨T', hdim', ?_⟩
  dsimp [T']
  omega

include K AR in
/-- No irreducible arrow in a finite AR quiver has a bypass of length two.
This is the exact special case of no sectional bypass used to separate the
fourth-vertex channels. -/
theorem no_irreducible_transitiveTriangle
    {a u b : ι}
    (hau : HasIrreducibleMorphism (σ.obj a) (σ.obj u))
    (hub : HasIrreducibleMorphism (σ.obj u) (σ.obj b)) :
    ¬ HasIrreducibleMorphism (σ.obj a) (σ.obj b) := by
  intro hab
  let T : TransitiveTriangle σ :=
    { a := a, u := u, b := b
      a_to_u := hau, u_to_b := hub, a_to_b := hab }
  rcases groundFinrank_orientation_of_hasIrreducibleMorphism
      (K := K) σ hab with hlt | hgt
  · exact no_increasing_transitiveTriangle (K := K) σ AR ⟨T, hlt⟩
  · exact no_decreasing_transitiveTriangle (K := K) σ AR ⟨T, hgt⟩

end FiniteARTranslationData

end OpConjecture.IndecomposableSkeleton
