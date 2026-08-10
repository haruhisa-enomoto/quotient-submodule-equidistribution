import QuotientSubmoduleEquidistribution.RepresentationDirected.ARCoordinateRecurrence
import QuotientSubmoduleEquidistribution.RepresentationDirected.SimpleGraphTits
import Mathlib.Data.List.FinRange

/-!
# First-negative-root cancellation infrastructure

This file separates the paper's argument into a purely linear operator
telescope and the word-specific modified-coordinate process.  It contains no
concrete algebra or module example.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace QuotientSubmoduleEquidistribution.RepresentationDirected.FirstCancellation

/-! ## A list-indexed operator telescope -/

universe uR uM uP

section Telescope

variable {S : Type uR} [CommRing S]
  {M : Type uM} [AddCommGroup M] [Module S M]
  {P : Type uP}

/-- Apply a list of linear updates from left to right.  Thus the head update
acts first and the tail product acts afterwards. -/
def updateProduct (U : P → M →ₗ[S] M) : List P → M →ₗ[S] M
  | [] => LinearMap.id
  | p :: ps => (updateProduct U ps).comp (U p)

@[simp]
theorem updateProduct_nil (U : P → M →ₗ[S] M) :
    updateProduct U [] = LinearMap.id := rfl

@[simp]
theorem updateProduct_cons (U : P → M →ₗ[S] M) (p : P) (ps : List P) :
    updateProduct U (p :: ps) = (updateProduct U ps).comp (U p) := rfl

theorem updateProduct_append (U : P → M →ₗ[S] M)
    (ps qs : List P) :
    updateProduct U (ps ++ qs) =
      (updateProduct U qs).comp (updateProduct U ps) := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      rw [List.cons_append, updateProduct_cons, ih, updateProduct_cons]
      rfl

/-- The recursively arranged right-hand side of the operator telescope.
At the head position the defect is propagated through all later `U` updates;
the second summand contains the defects at later positions after the head
`V` update has acted. -/
def operatorDefect (U V : P → M →ₗ[S] M) : List P → M →ₗ[S] M
  | [] => 0
  | p :: ps =>
      (updateProduct U ps).comp (U p - V p) +
        (operatorDefect U V ps).comp (V p)

/-- Equation `eq:directed-operator-telescope`, in recursive list form. -/
theorem updateProduct_sub_updateProduct
    (U V : P → M →ₗ[S] M) (ps : List P) :
    updateProduct U ps - updateProduct V ps = operatorDefect U V ps := by
  induction ps with
  | nil => simp [operatorDefect]
  | cons p ps ih =>
      ext z
      have h := LinearMap.congr_fun ih (V p z)
      simp only [LinearMap.sub_apply] at h
      simp only [updateProduct_cons, operatorDefect, LinearMap.sub_apply,
        LinearMap.add_apply, LinearMap.comp_apply]
      calc
        updateProduct U ps (U p z) - updateProduct V ps (V p z) =
            (updateProduct U ps (U p z) - updateProduct U ps (V p z)) +
              (updateProduct U ps (V p z) - updateProduct V ps (V p z)) := by
                abel
        _ = updateProduct U ps ((U p - V p) z) +
              operatorDefect U V ps (V p z) := by
                rw [LinearMap.sub_apply, map_sub, h]

/-- The same telescope evaluated on one initial vector. -/
theorem updateProduct_apply_sub_updateProduct_apply
    (U V : P → M →ₗ[S] M) (ps : List P) (z : M) :
    updateProduct U ps z - updateProduct V ps z =
      operatorDefect U V ps z := by
  exact LinearMap.congr_fun (updateProduct_sub_updateProduct U V ps) z

/-- Local defects along the successive states of the `V` process. -/
def HasLocalDefects (U V : P → M →ₗ[S] M)
    (impulse : P → M) : List P → M → Prop
  | [], _ => True
  | p :: ps, z =>
      (U p - V p) z = impulse p ∧
        HasLocalDefects U V impulse ps (V p z)

/-- Sum of the local impulses after propagation by all later `U` updates. -/
def propagatedImpulseSum (U : P → M →ₗ[S] M)
    (impulse : P → M) : List P → M
  | [] => 0
  | p :: ps =>
      updateProduct U ps (impulse p) + propagatedImpulseSum U impulse ps

/-- Vector form of the telescope after identifying every local defect. -/
theorem operatorDefect_apply_eq_propagatedImpulseSum
    (U V : P → M →ₗ[S] M) (impulse : P → M)
    (ps : List P) (z : M)
    (hlocal : HasLocalDefects U V impulse ps z) :
    operatorDefect U V ps z = propagatedImpulseSum U impulse ps := by
  induction ps generalizing z with
  | nil => simp [operatorDefect, propagatedImpulseSum]
  | cons p ps ih =>
      rcases hlocal with ⟨hp, hps⟩
      simp only [operatorDefect, LinearMap.add_apply, LinearMap.comp_apply,
        propagatedImpulseSum, hp]
      rw [ih (V p z) hps]

/-- Evaluated telescope with prescribed local impulses. -/
theorem updateProduct_apply_sub_eq_propagatedImpulseSum
    (U V : P → M →ₗ[S] M) (impulse : P → M)
    (ps : List P) (z : M)
    (hlocal : HasLocalDefects U V impulse ps z) :
    updateProduct U ps z - updateProduct V ps z =
      propagatedImpulseSum U impulse ps := by
  rw [updateProduct_apply_sub_updateProduct_apply,
    operatorDefect_apply_eq_propagatedImpulseSum U V impulse ps z hlocal]

end Telescope

/-! ## The scalar cancellation consequence -/

section ScalarCancellation

open SimpleGraphCoxeter WordRootProcess

universe uL uP'

variable {L : Type uL}
  {P : Type uP'} [DecidableEq P]

/-- The impulse created at an unselected position: killing a coordinate
instead of leaving it unchanged contributes `-c_p α_{i_p}`. -/
def omissionImpulse (D : Finset P) (c : P → ℤ) (label : P → L) (p : P) :
    RootLattice L :=
  if p ∈ D then 0 else -(c p) • simpleRoot (label p)

/-- Recursive assertion that a unit inserted at each position and propagated
through all later modified updates has the prescribed final coordinate. -/
def HasTransportCoordinates
    (U : P → RootLattice L →ₗ[ℤ] RootLattice L)
    (label : P → L) (target : L) (mu : P → ℤ) : List P → Prop
  | [] => True
  | p :: ps =>
      updateProduct U ps (simpleRoot (label p)) target = mu p ∧
        HasTransportCoordinates U label target mu ps

/-- The scalar sum occurring in the paper, with zero coefficients retained
harmlessly. -/
def unselectedContributionSum
    (D : Finset P) (c mu : P → ℤ) (ps : List P) : ℤ :=
  ((ps.filter fun p ↦ p ∉ D).map fun p ↦ c p * mu p).sum

/-- After taking the target coordinate, the propagated impulse sum is the
negative of the paper's sum over unselected positions. -/
theorem propagatedImpulseSum_omissionImpulse_apply
    (U : P → RootLattice L →ₗ[ℤ] RootLattice L)
    (D : Finset P) (c : P → ℤ) (label : P → L)
    (target : L) (mu : P → ℤ) (ps : List P)
    (htransport : HasTransportCoordinates U label target mu ps) :
    propagatedImpulseSum U (omissionImpulse D c label) ps target =
      -unselectedContributionSum D c mu ps := by
  induction ps with
  | nil => simp [propagatedImpulseSum, unselectedContributionSum]
  | cons p ps ih =>
      rcases htransport with ⟨hp, hps⟩
      by_cases hpD : p ∈ D
      · simp [propagatedImpulseSum, omissionImpulse, unselectedContributionSum,
          hpD, ih hps]
      · have hpropagated :
            updateProduct U ps (-(c p) • simpleRoot (label p)) target =
              -(c p * mu p) := by
            rw [map_smul, Pi.smul_apply, hp]
            simp
        rw [propagatedImpulseSum, omissionImpulse, if_neg hpD,
          Pi.add_apply, hpropagated, ih hps]
        simp [unselectedContributionSum, hpD]
        abel

/-- Exact abstract telescope form of the cancellation identity.  All
word-specific work is isolated in `hlocal` (selected updates agree and
unselected updates kill one coordinate) and `htransport` (the modified
process computes `mu`). -/
theorem cancellation_identity_of_telescope
    (U V : P → RootLattice L →ₗ[ℤ] RootLattice L)
    (D : Finset P) (c : P → ℤ) (label : P → L)
    (target : L) (mu : P → ℤ) (ps : List P)
    (z : RootLattice L)
    (muModified : ℤ)
    (hlocal : HasLocalDefects U V (omissionImpulse D c label) ps z)
    (htransport : HasTransportCoordinates U label target mu ps)
    (hmodified : updateProduct U ps z target = muModified)
    (horiginal : updateProduct V ps z target = -1) :
    muModified = -1 - unselectedContributionSum D c mu ps := by
  have htelescope :=
    updateProduct_apply_sub_eq_propagatedImpulseSum
      U V (omissionImpulse D c label) ps z hlocal
  have hcoordinate :
      updateProduct U ps z target - updateProduct V ps z target =
        propagatedImpulseSum U (omissionImpulse D c label) ps target := by
    simpa only [Pi.sub_apply] using congrFun htelescope target
  rw [propagatedImpulseSum_omissionImpulse_apply
    U D c label target mu ps htransport] at hcoordinate
  rw [hmodified, horiginal] at hcoordinate
  omega

end ScalarCancellation

/-! ## The modified coordinate process attached to a labelled word -/

section WordUpdates

open SimpleGraphCoxeter WordRootProcess

universe uL'

variable {L : Type uL'} [Fintype L]

/-- Set the `i`-coordinate to zero and leave all other coordinates fixed. -/
def killCoordinate (i : L) : RootLattice L →ₗ[ℤ] RootLattice L := by
  classical
  refine
    { toFun := fun z j ↦ if j = i then 0 else z j
      map_add' := ?_
      map_smul' := ?_ }
  · intro z w
    funext j
    by_cases hji : j = i <;> simp [hji]
  · intro c z
    funext j
    by_cases hji : j = i <;> simp [hji]

/-- The sum over the middle positions into `p`, evaluated using the current
coordinate of their labels.  `IsMiddle` ensures that at most one position
of any fixed label occurs in this sum. -/
def middleCoordinateSum (G : SimpleGraph L) (Q : List L)
    (p : Fin Q.length) (z : RootLattice L) : ℤ := by
  classical
  exact ∑ y : {y : Fin Q.length // ARWord.IsMiddle G Q y p},
    z (ARWord.label Q y.1)

/-- The selected update of the modified process.  It differs from the full
simple reflection only in replacing the sum over all graph neighbors by the
sum over recorded middle positions. -/
def middleReflection (G : SimpleGraph L) (Q : List L)
    (p : Fin Q.length) : RootLattice L →ₗ[ℤ] RootLattice L := by
  classical
  refine
    { toFun := fun z j ↦
        if j = ARWord.label Q p then
          -z (ARWord.label Q p) + middleCoordinateSum G Q p z
        else z j
      map_add' := ?_
      map_smul' := ?_ }
  · intro z w
    funext j
    by_cases hj : j = ARWord.label Q p
    · subst j
      simp only [if_pos, Pi.add_apply, middleCoordinateSum,
        Finset.sum_add_distrib, neg_add_rev]
      ring
    · have hget : j ≠ Q[p.1] := by
        simpa only [← List.get_eq_getElem] using hj
      simp_all only [List.get_eq_getElem, Pi.add_apply, if_false]
  · intro c z
    funext j
    by_cases hj : j = ARWord.label Q p
    · subst j
      simp only [if_pos, Pi.smul_apply, smul_eq_mul, middleCoordinateSum]
      rw [← Finset.mul_sum]
      simp only [RingHom.id_apply]
      ring
    · have hget : j ≠ Q[p.1] := by
        simpa only [← List.get_eq_getElem] using hj
      simp_all only [List.get_eq_getElem, Pi.smul_apply, if_false,
        RingHom.id_apply]

/-- One update of the paper's modified process. -/
def modifiedWordUpdate (G : SimpleGraph L) (Q : List L)
    (D : Finset (Fin Q.length)) (p : Fin Q.length) :
    RootLattice L →ₗ[ℤ] RootLattice L :=
  if p ∈ D then middleReflection G Q p
  else killCoordinate (ARWord.label Q p)

/-- One update of the original process: reflect at selected positions and
do nothing at unselected positions. -/
def originalWordUpdate (G : SimpleGraph L) (Q : List L)
    (D : Finset (Fin Q.length)) (p : Fin Q.length) :
    RootLattice L →ₗ[ℤ] RootLattice L :=
  if p ∈ D then simpleReflection G (ARWord.label Q p)
  else LinearMap.id

/-- Labels of the selected positions in an operational position list. -/
def selectedLabels (Q : List L) (D : Finset (Fin Q.length))
    (ps : List (Fin Q.length)) : List L :=
  (ps.filter fun p ↦ p ∈ D).map (ARWord.label Q)

/-- The original root state after processing `ps` from left to right,
starting with the unit at position `a`. -/
def selectedOperationalRootState (G : SimpleGraph L) (Q : List L)
    (D : Finset (Fin Q.length)) (a : Fin Q.length)
    (ps : List (Fin Q.length)) : RootLattice L :=
  updateProduct (originalWordUpdate G Q D) ps
    (simpleRoot (ARWord.label Q a))

/-- Processing all positions and using identity at unselected positions is
the same as processing only the selected label subword. -/
theorem updateProduct_originalWordUpdate_eq_reflectInIncreasingOrder
    (G : SimpleGraph L) (Q : List L)
    (D : Finset (Fin Q.length)) (ps : List (Fin Q.length))
    (z : RootLattice L) :
    updateProduct (originalWordUpdate G Q D) ps z =
      reflectInIncreasingOrder G (selectedLabels Q D ps) z := by
  induction ps generalizing z with
  | nil => simp [selectedLabels]
  | cons p ps ih =>
      by_cases hp : p ∈ D
      · simp [updateProduct, originalWordUpdate, selectedLabels, hp, ih]
      · simp [updateProduct, originalWordUpdate, selectedLabels, hp, ih]

/-- The selected operational state is a real root, expressed as the action
of the inverse selected-word product on its initial simple root. -/
theorem selectedOperationalRootState_eq_inverse_word_action
    (G : SimpleGraph L) (Q : List L)
    (D : Finset (Fin Q.length)) (a : Fin Q.length)
    (ps : List (Fin Q.length)) :
    selectedOperationalRootState G Q D a ps =
      geometricRepresentation G
        ((system G).wordProd (selectedLabels Q D ps))⁻¹
        (simpleRoot (ARWord.label Q a)) := by
  rw [selectedOperationalRootState,
    updateProduct_originalWordUpdate_eq_reflectInIncreasingOrder,
    reflectInIncreasingOrder_eq_inverse_word_action]

/-- Every selected operational state is nonzero, since it is the image of a
simple root under a linear equivalence. -/
theorem selectedOperationalRootState_ne_zero
    (G : SimpleGraph L) (Q : List L)
    (D : Finset (Fin Q.length)) (a : Fin Q.length)
    (ps : List (Fin Q.length)) :
    selectedOperationalRootState G Q D a ps ≠ 0 := by
  rw [selectedOperationalRootState_eq_inverse_word_action]
  intro hzero
  apply simpleRoot_ne_zero (ARWord.label Q a)
  apply (geometricRepresentation G
    (((system G).wordProd (selectedLabels Q D ps))⁻¹)).injective
  simpa using hzero

/-- Exact local first-negative-step API.  If a selected update sends the
positive operational real root to a negative root, the pre-root is the
reflecting simple root and the post-root is its negative. -/
theorem firstNegativeSelectedStep
    (G : SimpleGraph L) (Q : List L)
    (D : Finset (Fin Q.length)) (a x : Fin Q.length)
    (ps : List (Fin Q.length)) (hx : x ∈ D)
    (hpositive : IsPositive (selectedOperationalRootState G Q D a ps))
    (hnegative : IsNegative
      (originalWordUpdate G Q D x
        (selectedOperationalRootState G Q D a ps))) :
    selectedOperationalRootState G Q D a ps =
        simpleRoot (ARWord.label Q x) ∧
      originalWordUpdate G Q D x
          (selectedOperationalRootState G Q D a ps) =
        -simpleRoot (ARWord.label Q x) := by
  let w : Group G :=
    ((system G).wordProd (selectedLabels Q D ps))⁻¹
  have hstate := selectedOperationalRootState_eq_inverse_word_action
    G Q D a ps
  have hpos : IsPositive
      (geometricRepresentation G w (simpleRoot (ARWord.label Q a))) := by
    rw [← hstate]
    exact hpositive
  have hneg : IsNegative
      (simpleReflection G (ARWord.label Q x)
        (geometricRepresentation G w (simpleRoot (ARWord.label Q a)))) := by
    rw [← hstate]
    simpa [originalWordUpdate, hx] using hnegative
  have hroot :=
    RootSignStrategy.eq_simpleRoot_of_positive_of_simpleReflection_negative
      G w (ARWord.label Q a) (ARWord.label Q x) hpos hneg
  have hbefore : selectedOperationalRootState G Q D a ps =
      simpleRoot (ARWord.label Q x) := by
    rw [hstate]
    exact hroot
  refine ⟨hbefore, ?_⟩
  rw [originalWordUpdate, if_pos hx, hbefore,
    simpleReflection_simpleRoot_self]

/-- An original word update can change only the coordinate carrying the
current position's label. -/
theorem originalWordUpdate_apply_of_ne
    (G : SimpleGraph L) (Q : List L)
    (D : Finset (Fin Q.length)) (p : Fin Q.length)
    (z : RootLattice L) {h : L} (hhp : h ≠ ARWord.label Q p) :
    originalWordUpdate G Q D p z h = z h := by
  by_cases hpD : p ∈ D
  · rw [originalWordUpdate, if_pos hpD,
      simpleReflection_apply_of_ne G hhp]
  · simp [originalWordUpdate, hpD]

/-- A coordinate is preserved through a list of original updates when its
label never occurs in that list. -/
theorem updateProduct_originalWordUpdate_apply_of_forall_ne
    (G : SimpleGraph L) (Q : List L)
    (D : Finset (Fin Q.length)) (ps : List (Fin Q.length))
    (z : RootLattice L) (h : L)
    (hne : ∀ p, p ∈ ps → h ≠ ARWord.label Q p) :
    updateProduct (originalWordUpdate G Q D) ps z h = z h := by
  induction ps generalizing z with
  | nil => rfl
  | cons p ps ih =>
      rw [updateProduct_cons, LinearMap.comp_apply,
        ih (originalWordUpdate G Q D p z)]
      · exact originalWordUpdate_apply_of_ne G Q D p z
          (hne p (by simp))
      · intro q hq
        exact hne q (by simp [hq])

omit [Fintype L] in
@[simp]
theorem modifiedWordUpdate_apply_label
    (G : SimpleGraph L) (Q : List L)
    (D : Finset (Fin Q.length)) (p : Fin Q.length)
    (z : RootLattice L) :
    modifiedWordUpdate G Q D p z (ARWord.label Q p) =
      if p ∈ D then
        -z (ARWord.label Q p) + middleCoordinateSum G Q p z
      else 0 := by
  classical
  by_cases hp : p ∈ D
  · simp [modifiedWordUpdate, middleReflection, hp]
  · simp [modifiedWordUpdate, killCoordinate, hp]

/-- The value at the immediately preceding occurrence is the term subtracted
by a selected modified update.  This sum is either empty or a singleton. -/
def previousValueSum (Q : List L) (x : Fin Q.length)
    (f : Fin Q.length → ℤ) : ℤ := by
  classical
  exact ∑ p ∈ Finset.univ.filter (fun p ↦ ARWord.IsPrevious Q p x), f p

omit [Fintype L] in
theorem previousValueSum_eq_of_isPrevious
    (Q : List L) {p x : Fin Q.length} (hp : ARWord.IsPrevious Q p x)
    (f : Fin Q.length → ℤ) :
    previousValueSum Q x f = f p := by
  classical
  unfold previousValueSum
  apply Finset.sum_eq_single p
  · intro q hq hqp
    have hqPrevious : ARWord.IsPrevious Q q x := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hq
    exact False.elim (hqp (ARWord.isPrevious_unique hqPrevious hp))
  · intro hpnot
    exact False.elim (hpnot (by simp [hp]))

omit [Fintype L] in
theorem previousValueSum_eq_zero_of_no_previous
    (Q : List L) (x : Fin Q.length)
    (hprevious : ¬ ∃ p, ARWord.IsPrevious Q p x)
    (f : Fin Q.length → ℤ) :
    previousValueSum Q x f = 0 := by
  classical
  unfold previousValueSum
  apply Finset.sum_eq_zero
  intro p hp
  have hpPrevious : ARWord.IsPrevious Q p x := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hp
  exact False.elim (hprevious ⟨p, hpPrevious⟩)

/-- Values at the middle positions into `x`.  Packaging the classical finite
subtype instance behind a definition keeps later theorem statements free of
elaboration-only decidability assumptions. -/
def middleValueSum (G : SimpleGraph L) (Q : List L) (x : Fin Q.length)
    (f : Fin Q.length → ℤ) : ℤ := by
  classical
  exact ∑ y ∈ Finset.univ.filter (fun y ↦ ARWord.IsMiddle G Q y x), f y

/-- At an unselected position the local operator defect is exactly the
negative of that coordinate times the corresponding simple root. -/
theorem modifiedWordUpdate_sub_originalWordUpdate_of_not_mem
    (G : SimpleGraph L) (Q : List L)
    (D : Finset (Fin Q.length)) (p : Fin Q.length) (hp : p ∉ D)
    (z : RootLattice L) :
    (modifiedWordUpdate G Q D p - originalWordUpdate G Q D p) z =
      -z (ARWord.label Q p) • simpleRoot (ARWord.label Q p) := by
  classical
  ext j
  by_cases hj : j = ARWord.label Q p
  · subst j
    simp [modifiedWordUpdate, originalWordUpdate, killCoordinate, hp,
      simpleRoot]
  · have hget : j ≠ Q[p.1] := by
      simpa only [← List.get_eq_getElem] using hj
    simp [modifiedWordUpdate, originalWordUpdate, killCoordinate, hp,
      simpleRoot, List.get_eq_getElem, hget]

/-- A selected modified update agrees with the full reflection precisely
once the omitted neighboring coordinates contribute zero.  The displayed
equality is the exact local hypothesis needed by the telescope. -/
theorem modifiedWordUpdate_eq_originalWordUpdate_of_mem
    (G : SimpleGraph L) (Q : List L)
    (D : Finset (Fin Q.length)) (p : Fin Q.length) (hp : p ∈ D)
    (z : RootLattice L)
    (hsum : middleCoordinateSum G Q p z =
      neighborSum G (ARWord.label Q p) z) :
    modifiedWordUpdate G Q D p z = originalWordUpdate G Q D p z := by
  classical
  ext j
  by_cases hj : j = ARWord.label Q p
  · subst j
    simp [modifiedWordUpdate, originalWordUpdate, middleReflection,
      simpleReflection, hp, hsum]
  · have hget : j ≠ Q[p.1] := by
      simpa only [← List.get_eq_getElem] using hj
    simp [modifiedWordUpdate, originalWordUpdate, middleReflection,
      simpleReflection, hp, List.get_eq_getElem, hget]

/-- Along the successive states of the original process, every selected
position has the neighbor-sum equality needed for selected-update agreement. -/
def HasSelectedNeighborSums (G : SimpleGraph L) (Q : List L)
    (D : Finset (Fin Q.length)) :
    List (Fin Q.length) → RootLattice L → Prop
  | [], _ => True
  | p :: ps, z =>
      (p ∈ D → middleCoordinateSum G Q p z =
        neighborSum G (ARWord.label Q p) z) ∧
      HasSelectedNeighborSums G Q D ps (originalWordUpdate G Q D p z)

/-- `c p` is the coordinate seen immediately before processing `p` in the
original process. -/
def HasOriginalCoefficients (G : SimpleGraph L) (Q : List L)
    (D : Finset (Fin Q.length)) (c : Fin Q.length → ℤ) :
    List (Fin Q.length) → RootLattice L → Prop
  | [], _ => True
  | p :: ps, z =>
      c p = z (ARWord.label Q p) ∧
      HasOriginalCoefficients G Q D c ps (originalWordUpdate G Q D p z)

/-- Every state immediately before a listed update is coordinatewise
nonnegative.  The terminal state after the final update is deliberately not
constrained, so this is exactly what a first-negative-root hypothesis gives. -/
def HasNonnegativeOriginalStates (G : SimpleGraph L) (Q : List L)
    (D : Finset (Fin Q.length)) :
    List (Fin Q.length) → RootLattice L → Prop
  | [], _ => True
  | p :: ps, z =>
      IsNonnegative z ∧
      HasNonnegativeOriginalStates G Q D ps
        (originalWordUpdate G Q D p z)

/-- Discarding an initial part of a nonnegative original process leaves the
same predicate on the remaining suffix at the advanced state. -/
theorem hasNonnegativeOriginalStates_dropPrefix
    (G : SimpleGraph L) (Q : List L)
    (D : Finset (Fin Q.length))
    (ps qs : List (Fin Q.length)) (z : RootLattice L)
    (hnonnegative : HasNonnegativeOriginalStates G Q D (ps ++ qs) z) :
    HasNonnegativeOriginalStates G Q D qs
      (updateProduct (originalWordUpdate G Q D) ps z) := by
  induction ps generalizing z with
  | nil => simpa using hnonnegative
  | cons p ps ih =>
      change IsNonnegative z ∧
        HasNonnegativeOriginalStates G Q D (ps ++ qs)
          (originalWordUpdate G Q D p z) at hnonnegative
      exact ih (originalWordUpdate G Q D p z) hnonnegative.2

/-- The two word-process hypotheses imply the local-defect predicate used
by the abstract operator telescope. -/
theorem hasLocalDefects_modifiedWordUpdate
    (G : SimpleGraph L) (Q : List L)
    (D : Finset (Fin Q.length)) (c : Fin Q.length → ℤ)
    (ps : List (Fin Q.length)) (z : RootLattice L)
    (hsums : HasSelectedNeighborSums G Q D ps z)
    (hcoeff : HasOriginalCoefficients G Q D c ps z) :
    HasLocalDefects (modifiedWordUpdate G Q D) (originalWordUpdate G Q D)
      (omissionImpulse D c (ARWord.label Q)) ps z := by
  induction ps generalizing z with
  | nil => trivial
  | cons p ps ih =>
      rcases hsums with ⟨hsum, hsums⟩
      rcases hcoeff with ⟨hcoord, hcoeff⟩
      constructor
      · by_cases hp : p ∈ D
        · rw [LinearMap.sub_apply,
            modifiedWordUpdate_eq_originalWordUpdate_of_mem
              G Q D p hp z (hsum hp)]
          simp [omissionImpulse, hp]
        · rw [modifiedWordUpdate_sub_originalWordUpdate_of_not_mem
            G Q D p hp z, ← hcoord]
          simp [omissionImpulse, hp]
      · exact ih (originalWordUpdate G Q D p z) hsums hcoeff

/-- Nonzero coefficients in a nonnegative preterminal process are positive.
No Coxeter reducedness hypothesis is used here. -/
theorem originalCoefficient_pos_of_nonzero
    (G : SimpleGraph L) (Q : List L)
    (D : Finset (Fin Q.length)) (c : Fin Q.length → ℤ)
    (ps : List (Fin Q.length)) (z : RootLattice L)
    (hcoeff : HasOriginalCoefficients G Q D c ps z)
    (hnonnegative : HasNonnegativeOriginalStates G Q D ps z)
    {p : Fin Q.length} (hp : p ∈ ps) (hcp : c p ≠ 0) :
    0 < c p := by
  induction ps generalizing z with
  | nil => simp at hp
  | cons q ps ih =>
      rcases hcoeff with ⟨hq, hcoeff⟩
      rcases hnonnegative with ⟨hz, hnonnegative⟩
      rcases List.mem_cons.mp hp with hpq | hp
      · subst q
        have hnonneg := hz (ARWord.label Q p)
        rw [← hq] at hnonneg
        omega
      · exact ih (originalWordUpdate G Q D q z)
          hcoeff hnonnegative hp

/-! ### Boundary-run control of omitted neighbors -/

omit [Fintype L] in
/-- The direct boundary-run consequence used in the manuscript.  If two
consecutive occurrences of one label have no `h` between them but an `h`
occurs before the first, then no `h` occurs after the second. -/
theorem no_later_neighbor_of_previous_of_no_between
    (G : SimpleGraph L) (Q : List L)
    (hRuns : ARWord.HasOnlyBoundaryRepeatedRuns G Q)
    {r p : Fin Q.length} (hrp : ARWord.IsPrevious Q r p)
    {h : L} (hhp : G.Adj h (ARWord.label Q p))
    (hbefore : ∃ b : Fin Q.length,
      b < r ∧ ARWord.label Q b = h)
    (hbetween : ∀ z : Fin Q.length, r < z → z < p →
      ARWord.label Q z ≠ h) :
    ∀ z : Fin Q.length, p < z → ARWord.label Q z ≠ h := by
  have hboundary := (ARWord.hasOnlyBoundaryRepeatedRuns_iff.mp hRuns)
    hhp.symm hrp.1 hrp.2.1 rfl hbetween
  rcases hboundary with hnoneBefore | hnoneAfter
  · obtain ⟨b, hbr, hb⟩ := hbefore
    exact False.elim (hnoneBefore b hbr hb)
  · exact hnoneAfter

omit [Fintype L] in
/-- If a neighboring label occurs in the predecessor window, its last such
occurrence is an `IsMiddle` position. -/
theorem exists_isMiddle_with_label_of_exists_in_window
    (G : SimpleGraph L) (Q : List L)
    {p : Fin Q.length} {h : L}
    (hhp : G.Adj h (ARWord.label Q p))
    (hwindow : ∃ y : Fin Q.length,
      y < p ∧ ARWord.label Q y = h ∧
        ∀ r : Fin Q.length, ARWord.IsPrevious Q r p → r < y) :
    ∃ y : Fin Q.length,
      ARWord.IsMiddle G Q y p ∧ ARWord.label Q y = h := by
  classical
  let S : Finset (Fin Q.length) := Finset.univ.filter fun y ↦
    y < p ∧ ARWord.label Q y = h ∧
      ∀ r : Fin Q.length, ARWord.IsPrevious Q r p → r < y
  have hS : S.Nonempty := by
    obtain ⟨y, hyp, hyh, hafter⟩ := hwindow
    refine ⟨y, ?_⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ y, hyp, hyh, hafter⟩
  let y : Fin Q.length := S.max' hS
  have hyS : y ∈ S := S.max'_mem hS
  have hyData : y < p ∧ ARWord.label Q y = h ∧
      ∀ r : Fin Q.length, ARWord.IsPrevious Q r p → r < y := by
    simpa [S] using hyS
  have hadjY : G.Adj (ARWord.label Q y) (ARWord.label Q p) := by
    rw [hyData.2.1]
    exact hhp
  refine ⟨y, ⟨hadjY, hyData.1, hyData.2.2, ?_⟩, hyData.2.1⟩
  intro z hyz hzp hzLabel
  have hzS : z ∈ S := by
    have hzh : ARWord.label Q z = h := hzLabel.trans hyData.2.1
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ z, hzp, hzh, ?_⟩
    intro r hrp'
    exact (hyData.2.2 r hrp').trans hyz
  exact (not_le_of_gt hyz) (S.le_max' z hzS)

omit [Fintype L] in
/-- Smallest omitted-neighbor lemma.  Under the boundary-run hypothesis, a
neighboring label which has occurred before `p` but has no middle-position
representative at `p` can never occur after `p`. -/
theorem no_later_occurrence_of_neighbor_not_middle
    (G : SimpleGraph L) (Q : List L)
    (hRuns : ARWord.HasOnlyBoundaryRepeatedRuns G Q)
    {p : Fin Q.length} {h : L}
    (hhp : G.Adj h (ARWord.label Q p))
    (hseen : ∃ b : Fin Q.length, b < p ∧ ARWord.label Q b = h)
    (hnotMiddle : ¬ ∃ y : Fin Q.length,
      ARWord.IsMiddle G Q y p ∧ ARWord.label Q y = h) :
    ∀ z : Fin Q.length, p < z → ARWord.label Q z ≠ h := by
  by_cases hprevious : ∃ r : Fin Q.length, ARWord.IsPrevious Q r p
  · obtain ⟨r, hrp⟩ := hprevious
    by_cases hbetweenExists : ∃ y : Fin Q.length,
        r < y ∧ y < p ∧ ARWord.label Q y = h
    · apply False.elim
      apply hnotMiddle
      apply exists_isMiddle_with_label_of_exists_in_window G Q hhp
      obtain ⟨y, hry, hyp, hyh⟩ := hbetweenExists
      refine ⟨y, hyp, hyh, ?_⟩
      intro r' hr'p
      rw [ARWord.isPrevious_unique hr'p hrp]
      exact hry
    · have hbetween : ∀ z : Fin Q.length, r < z → z < p →
          ARWord.label Q z ≠ h := by
        intro z hrz hzp hzh
        exact hbetweenExists ⟨z, hrz, hzp, hzh⟩
      obtain ⟨b, hbp, hbh⟩ := hseen
      have hbr : b < r := by
        rcases lt_trichotomy b r with hbr | hbr | hrb
        · exact hbr
        · subst b
          exact False.elim
            (hhp.ne (hbh.symm.trans hrp.2.1))
        · exact False.elim (hbetweenExists ⟨b, hrb, hbp, hbh⟩)
      exact no_later_neighbor_of_previous_of_no_between
        G Q hRuns hrp hhp ⟨b, hbr, hbh⟩ hbetween
  · apply False.elim
    apply hnotMiddle
    apply exists_isMiddle_with_label_of_exists_in_window G Q hhp
    obtain ⟨y, hyp, hyh⟩ := hseen
    refine ⟨y, hyp, hyh, ?_⟩
    intro r hrp
    exact False.elim (hprevious ⟨r, hrp⟩)

/-- Coordinate form of selected-update agreement: every neighboring label
not represented by an `IsMiddle` position has zero current coordinate. -/
def HasZeroOmittedNeighborCoordinates (G : SimpleGraph L) (Q : List L)
    (p : Fin Q.length) (z : RootLattice L) : Prop :=
  ∀ h : L, G.Adj h (ARWord.label Q p) →
    (¬ ∃ y : Fin Q.length,
      ARWord.IsMiddle G Q y p ∧ ARWord.label Q y = h) →
    z h = 0

/-- Zero omitted-neighbor coordinates identify the modified middle sum with
the full graph-neighbor sum. -/
theorem middleCoordinateSum_eq_neighborSum_of_zero_omitted
    (G : SimpleGraph L) (Q : List L) (p : Fin Q.length)
    (z : RootLattice L)
    (hzero : HasZeroOmittedNeighborCoordinates G Q p z) :
    middleCoordinateSum G Q p z =
      neighborSum G (ARWord.label Q p) z := by
  classical
  let E : {y : Fin Q.length // ARWord.IsMiddle G Q y p} ↪ L :=
    { toFun := fun y ↦ ARWord.label Q y.1
      inj' := by
        intro y y' hlabel
        apply Subtype.ext
        exact ARWord.isMiddle_unique_of_label_eq y.2 y'.2 hlabel }
  let S : Finset L := Finset.univ.map E
  have hsub : S ⊆ G.neighborFinset (ARWord.label Q p) := by
    intro h hh
    obtain ⟨y, _, rfl⟩ := Finset.mem_map.mp hh
    exact (G.mem_neighborFinset (ARWord.label Q p)
      (ARWord.label Q y.1)).mpr y.2.1.symm
  have houtside : ∀ h ∈ G.neighborFinset (ARWord.label Q p),
      h ∉ S → z h = 0 := by
    intro h hh hnot
    apply hzero h
    · exact ((G.mem_neighborFinset (ARWord.label Q p) h).mp hh).symm
    · rintro ⟨y, hy, hlabel⟩
      apply hnot
      apply Finset.mem_map.mpr
      refine ⟨⟨y, hy⟩, Finset.mem_univ _, ?_⟩
      exact hlabel
  have hsum := Finset.sum_subset hsub houtside
  calc
    middleCoordinateSum G Q p z = ∑ h ∈ S, z h := by
      unfold middleCoordinateSum
      symm
      exact Finset.sum_map Finset.univ E z
    _ = neighborSum G (ARWord.label Q p) z := by
      simpa only [neighborSum] using hsum

/-- Recursive zero-omitted-neighbor condition along the original process. -/
def HasSelectedZeroOmittedNeighbors (G : SimpleGraph L) (Q : List L)
    (D : Finset (Fin Q.length)) :
    List (Fin Q.length) → RootLattice L → Prop
  | [], _ => True
  | p :: ps, z =>
      (p ∈ D → HasZeroOmittedNeighborCoordinates G Q p z) ∧
      HasSelectedZeroOmittedNeighbors G Q D ps
        (originalWordUpdate G Q D p z)

/-- The coordinate-zero condition discharges `HasSelectedNeighborSums`. -/
theorem hasSelectedNeighborSums_of_zero_omitted
    (G : SimpleGraph L) (Q : List L)
    (D : Finset (Fin Q.length)) (ps : List (Fin Q.length))
    (z : RootLattice L)
    (hzero : HasSelectedZeroOmittedNeighbors G Q D ps z) :
    HasSelectedNeighborSums G Q D ps z := by
  induction ps generalizing z with
  | nil => trivial
  | cons p ps ih =>
      rcases hzero with ⟨hp, hzero⟩
      constructor
      · intro hpD
        exact middleCoordinateSum_eq_neighborSum_of_zero_omitted
          G Q p z (hp hpD)
      · exact ih (originalWordUpdate G Q D p z) hzero

/-! ### Recurrence-to-process transport -/

/-- The expected bookkeeping update: record `mu p` at the label of `p` and
leave every other recorded label value unchanged. -/
noncomputable def overwriteRowCoordinate (Q : List L) (mu : Fin Q.length → ℤ)
    (z : RootLattice L) (p : Fin Q.length) : RootLattice L := by
  classical
  exact fun h ↦ if h = ARWord.label Q p then mu p else z h

/-- Apply a list of expected bookkeeping overwrites from left to right. -/
def overwriteRowCoordinates (Q : List L) (mu : Fin Q.length → ℤ)
    (z : RootLattice L) (ps : List (Fin Q.length)) : RootLattice L :=
  ps.foldl (overwriteRowCoordinate Q mu) z

omit [Fintype L] in
@[simp]
theorem overwriteRowCoordinates_nil
    (Q : List L) (mu : Fin Q.length → ℤ) (z : RootLattice L) :
    overwriteRowCoordinates Q mu z [] = z := rfl

omit [Fintype L] in
@[simp]
theorem overwriteRowCoordinates_cons
    (Q : List L) (mu : Fin Q.length → ℤ) (z : RootLattice L)
    (p : Fin Q.length) (ps : List (Fin Q.length)) :
    overwriteRowCoordinates Q mu z (p :: ps) =
      overwriteRowCoordinates Q mu (overwriteRowCoordinate Q mu z p) ps := rfl

omit [Fintype L] in
theorem overwriteRowCoordinates_append
    (Q : List L) (mu : Fin Q.length → ℤ) (z : RootLattice L)
    (ps qs : List (Fin Q.length)) :
    overwriteRowCoordinates Q mu z (ps ++ qs) =
      overwriteRowCoordinates Q mu (overwriteRowCoordinates Q mu z ps) qs := by
  exact List.foldl_append

omit [Fintype L] in
@[simp]
theorem overwriteRowCoordinate_apply_label
    (Q : List L) (mu : Fin Q.length → ℤ) (z : RootLattice L)
    (p : Fin Q.length) :
    overwriteRowCoordinate Q mu z p (ARWord.label Q p) = mu p := by
  classical
  simp [overwriteRowCoordinate]

omit [Fintype L] in
theorem overwriteRowCoordinate_apply_of_ne
    (Q : List L) (mu : Fin Q.length → ℤ) (z : RootLattice L)
    (p : Fin Q.length) {h : L} (hhp : h ≠ ARWord.label Q p) :
    overwriteRowCoordinate Q mu z p h = z h := by
  classical
  change (if h = ARWord.label Q p then mu p else z h) = z h
  rw [if_neg hhp]

omit [Fintype L] in
/-- If no listed position has label `h`, the overwrite process preserves the
`h` coordinate. -/
theorem overwriteRowCoordinates_apply_of_forall_ne
    (Q : List L) (mu : Fin Q.length → ℤ) (z : RootLattice L)
    (ps : List (Fin Q.length)) (h : L)
    (hne : ∀ p, p ∈ ps → h ≠ ARWord.label Q p) :
    overwriteRowCoordinates Q mu z ps h = z h := by
  induction ps generalizing z with
  | nil => rfl
  | cons p ps ih =>
      rw [overwriteRowCoordinates_cons,
        ih (overwriteRowCoordinate Q mu z p)]
      · exact overwriteRowCoordinate_apply_of_ne Q mu z p
          (hne p (by simp))
      · intro q hq
        exact hne q (by simp [hq])

omit [Fintype L] in
/-- A recorded value at the last occurrence of its label survives all later
overwrites. -/
theorem overwriteRowCoordinates_apply_eq_of_last
    (Q : List L) (mu : Fin Q.length → ℤ) (z : RootLattice L)
    (ps : List (Fin Q.length)) (r : Fin Q.length)
    (hr : r ∈ ps)
    (hsorted : ps.Pairwise (· < ·))
    (hlast : ∀ q, q ∈ ps → r < q →
      ARWord.label Q q ≠ ARWord.label Q r) :
    overwriteRowCoordinates Q mu z ps (ARWord.label Q r) = mu r := by
  obtain ⟨before, after, hps⟩ := List.mem_iff_append.mp hr
  subst ps
  rw [overwriteRowCoordinates_append, overwriteRowCoordinates_cons]
  have hsorted' := hsorted
  rw [List.pairwise_append, List.pairwise_cons] at hsorted'
  rw [overwriteRowCoordinates_apply_of_forall_ne]
  · exact overwriteRowCoordinate_apply_label Q mu
      (overwriteRowCoordinates Q mu z before) r
  · intro q hq
    exact (hlast q (by simp [hq]) (hsorted'.2.1.1 q hq)).symm

/-- The scalar recurrence written in exactly the form of one modified update
at a position strictly after the row source. -/
def ModifiedRowRecurrenceAt (G : SimpleGraph L) (Q : List L)
    (D : Finset (Fin Q.length)) (mu : Fin Q.length → ℤ)
    (p : Fin Q.length) : Prop :=
  mu p = if p ∈ D then
    middleValueSum G Q p mu - previousValueSum Q p mu
  else 0

omit [Fintype L] in
/-- Convert the literal subtype sum used by `middleCoordinateSum` to the
position-filtered sum used by `middleValueSum`, once the recorded coordinate
at every middle label is known. -/
theorem middleCoordinateSum_eq_middleValueSum_of_recorded
    (G : SimpleGraph L) (Q : List L) (p : Fin Q.length)
    (z : RootLattice L) (mu : Fin Q.length → ℤ)
    (hmiddle : ∀ y : Fin Q.length, ARWord.IsMiddle G Q y p →
      z (ARWord.label Q y) = mu y) :
    middleCoordinateSum G Q p z = middleValueSum G Q p mu := by
  classical
  unfold middleCoordinateSum middleValueSum
  rw [← Finset.sum_subtype
    (Finset.univ.filter (fun y ↦ ARWord.IsMiddle G Q y p))
    (by intro y; simp)
    (fun y ↦ z (ARWord.label Q y))]
  apply Finset.sum_congr rfl
  intro y hy
  apply hmiddle y
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hy

omit [Fintype L] in
/-- One modified update writes the prescribed row value at its own label.
This is the algebraic core of `htransport`; the only state information used
is the previous-occurrence coordinate and the middle-position coordinates. -/
theorem modifiedWordUpdate_apply_label_eq_of_recorded
    (G : SimpleGraph L) (Q : List L)
    (D : Finset (Fin Q.length)) (mu : Fin Q.length → ℤ)
    (p : Fin Q.length) (z : RootLattice L)
    (hrecurrence : ModifiedRowRecurrenceAt G Q D mu p)
    (hprevious : z (ARWord.label Q p) = previousValueSum Q p mu)
    (hmiddle : ∀ y : Fin Q.length, ARWord.IsMiddle G Q y p →
      z (ARWord.label Q y) = mu y) :
    modifiedWordUpdate G Q D p z (ARWord.label Q p) = mu p := by
  have hmiddleSum :=
    middleCoordinateSum_eq_middleValueSum_of_recorded G Q p z mu hmiddle
  by_cases hp : p ∈ D
  · rw [modifiedWordUpdate_apply_label, if_pos hp,
      hrecurrence, if_pos hp, hprevious, hmiddleSum]
    ring
  · rw [modifiedWordUpdate_apply_label, if_neg hp,
      hrecurrence, if_neg hp]

omit [Fintype L] in
/-- Once the predecessor and middle lookups are correct, the actual modified
linear update is exactly the expected overwrite vector. -/
theorem modifiedWordUpdate_eq_overwriteRowCoordinate_of_recorded
    (G : SimpleGraph L) (Q : List L)
    (D : Finset (Fin Q.length)) (mu : Fin Q.length → ℤ)
    (p : Fin Q.length) (z : RootLattice L)
    (hrecurrence : ModifiedRowRecurrenceAt G Q D mu p)
    (hprevious : z (ARWord.label Q p) = previousValueSum Q p mu)
    (hmiddle : ∀ y : Fin Q.length, ARWord.IsMiddle G Q y p →
      z (ARWord.label Q y) = mu y) :
    modifiedWordUpdate G Q D p z = overwriteRowCoordinate Q mu z p := by
  classical
  funext h
  by_cases hhp : h = ARWord.label Q p
  · subst h
    rw [overwriteRowCoordinate_apply_label]
    exact modifiedWordUpdate_apply_label_eq_of_recorded
      G Q D mu p z hrecurrence hprevious hmiddle
  · rw [overwriteRowCoordinate_apply_of_ne Q mu z p hhp]
    by_cases hpD : p ∈ D
    · rw [modifiedWordUpdate, if_pos hpD]
      change (if h = ARWord.label Q p then
          -z (ARWord.label Q p) + middleCoordinateSum G Q p z
        else z h) = z h
      rw [if_neg hhp]
    · rw [modifiedWordUpdate, if_neg hpD]
      change (if h = ARWord.label Q p then 0 else z h) = z h
      rw [if_neg hhp]

/-- The last-occurrence invariant for one row of the modified process.
It states exactly what must be checked combinatorially before each update. -/
def HasRecordedRowCoordinates (G : SimpleGraph L) (Q : List L)
    (D : Finset (Fin Q.length)) (mu : Fin Q.length → ℤ) :
    List (Fin Q.length) → RootLattice L → Prop
  | [], _ => True
  | p :: ps, z =>
      z (ARWord.label Q p) = previousValueSum Q p mu ∧
      (∀ y : Fin Q.length, ARWord.IsMiddle G Q y p →
        z (ARWord.label Q y) = mu y) ∧
      HasRecordedRowCoordinates G Q D mu ps (modifiedWordUpdate G Q D p z)

omit [Fintype L] in
/-- Under the row recurrence and the last-occurrence invariant, the final
coordinate at the label of the last processed position is the row value at
that position. -/
theorem updateProduct_modifiedWordUpdate_apply_last
    (G : SimpleGraph L) (Q : List L)
    (D : Finset (Fin Q.length)) (mu : Fin Q.length → ℤ)
    (ps : List (Fin Q.length)) (z : RootLattice L)
    (hrecorded : HasRecordedRowCoordinates G Q D mu ps z)
    (hrecurrence : ∀ p, p ∈ ps → ModifiedRowRecurrenceAt G Q D mu p)
    (hps : ps ≠ []) :
    updateProduct (modifiedWordUpdate G Q D) ps z
        (ARWord.label Q (ps.getLast hps)) =
      mu (ps.getLast hps) := by
  induction ps generalizing z with
  | nil => contradiction
  | cons p ps ih =>
      rcases hrecorded with ⟨hprevious, hmiddle, hrecorded⟩
      cases ps with
      | nil =>
          have hpRecurrence := hrecurrence p (by simp)
          simpa [updateProduct] using
            modifiedWordUpdate_apply_label_eq_of_recorded
              G Q D mu p z hpRecurrence hprevious hmiddle
      | cons q qs =>
          have htailRecurrence : ∀ r, r ∈ q :: qs →
              ModifiedRowRecurrenceAt G Q D mu r := by
            intro r hr
            exact hrecurrence r (by simp [hr])
          have htail := ih (modifiedWordUpdate G Q D p z)
            hrecorded htailRecurrence (by simp)
          simpa [updateProduct] using htail

/-- Every head of a common position list carries the row-recording and
recurrence data for its tail.  This is the exact invariant needed to build
`HasTransportCoordinates`. -/
def HasTailRowTransportData (G : SimpleGraph L) (Q : List L)
    (D : Finset (Fin Q.length))
    (mu : Fin Q.length → Fin Q.length → ℤ) :
    List (Fin Q.length) → Prop
  | [] => True
  | e :: ps =>
      HasRecordedRowCoordinates G Q D (mu e) ps
          (simpleRoot (ARWord.label Q e)) ∧
      (∀ p, p ∈ ps → ModifiedRowRecurrenceAt G Q D (mu e) p) ∧
      HasTailRowTransportData G Q D mu ps

/-- The genuinely state-theoretic part of tail transport, with recurrence
data omitted. -/
def HasTailRowRecordings (G : SimpleGraph L) (Q : List L)
    (D : Finset (Fin Q.length))
    (mu : Fin Q.length → Fin Q.length → ℤ) :
    List (Fin Q.length) → Prop
  | [] => True
  | e :: ps =>
      HasRecordedRowCoordinates G Q D (mu e) ps
          (simpleRoot (ARWord.label Q e)) ∧
      HasTailRowRecordings G Q D mu ps

omit [Fintype L] in
/-- Increasing tail lists turn a pointwise strict-upper recurrence into the
full recurrence component of `HasTailRowTransportData`. -/
theorem hasTailRowTransportData_of_recordings_of_pairwise
    (G : SimpleGraph L) (Q : List L)
    (D : Finset (Fin Q.length))
    (mu : Fin Q.length → Fin Q.length → ℤ)
    (es : List (Fin Q.length))
    (hrecordings : HasTailRowRecordings G Q D mu es)
    (hsorted : es.Pairwise (· < ·))
    (hrecurrence : ∀ e p, e < p →
      ModifiedRowRecurrenceAt G Q D (mu e) p) :
    HasTailRowTransportData G Q D mu es := by
  induction es with
  | nil => trivial
  | cons e es ih =>
      rcases hrecordings with ⟨hrecorded, hrecordings⟩
      rw [List.pairwise_cons] at hsorted
      refine ⟨hrecorded, ?_, ih hrecordings hsorted.2⟩
      intro p hp
      exact hrecurrence e p (hsorted.1 p hp)

omit [Fintype L] in
/-- The row-recording invariant implies the transport predicate used by the
operator telescope.  Diagonal entries handle the final singleton tail. -/
theorem hasTransportCoordinates_of_tailRowTransportData
    (G : SimpleGraph L) (Q : List L)
    (D : Finset (Fin Q.length))
    (mu : Fin Q.length → Fin Q.length → ℤ)
    (es : List (Fin Q.length)) (x : Fin Q.length)
    (hdata : HasTailRowTransportData G Q D mu es)
    (hdiag : ∀ e, e ∈ es → mu e e = 1)
    (hlast : es.getLast? = some x) :
    HasTransportCoordinates (modifiedWordUpdate G Q D)
      (ARWord.label Q) (ARWord.label Q x) (fun e ↦ mu e x) es := by
  induction es with
  | nil => trivial
  | cons e es ih =>
      rcases hdata with ⟨hrecorded, hrecurrence, hdata⟩
      cases es with
      | nil =>
          constructor
          · have hex : e = x := by simpa using Option.some.inj hlast
            subst x
            simp [hdiag e (by simp)]
          · trivial
      | cons p ps =>
          constructor
          · have hnonempty : p :: ps ≠ [] := by simp
            have hlastPosition : (p :: ps).getLast hnonempty = x := by
              have hlastSome : (p :: ps).getLast? = some x := by
                simpa using hlast
              simpa [List.getLast?_eq_some_getLast hnonempty] using hlastSome
            have hfinal := updateProduct_modifiedWordUpdate_apply_last
              G Q D (mu e) (p :: ps) (simpleRoot (ARWord.label Q e))
              hrecorded hrecurrence hnonempty
            simpa [hlastPosition] using hfinal
          · apply ih hdata
            · intro r hr
              exact hdiag r (by simp [hr])
            · simpa using hlast

end WordUpdates

/-! ## Exact paper-facing wrapper with `wordMixedMultiplicity` -/

section WordMixedMultiplicityWrapper

open SimpleGraphCoxeter WordRootProcess DirectedAROrbit
open CategoryTheory

universe uK uI

/-- Positions strictly after `a` and at most `x`, in increasing order. -/
def positionsIoc {n : ℕ} (a x : Fin n) : List (Fin n) :=
  (Finset.Ioc a x).sort (· ≤ ·)

/-- Positions strictly between two endpoints, in increasing order. -/
def positionsIoo {n : ℕ} (a x : Fin n) : List (Fin n) :=
  (Finset.Ioo a x).sort (· ≤ ·)

@[simp]
theorem mem_positionsIoc {n : ℕ} {a x p : Fin n} :
    p ∈ positionsIoc a x ↔ a < p ∧ p ≤ x := by
  simp [positionsIoc, Finset.mem_Ioc]

@[simp]
theorem mem_positionsIoo {n : ℕ} {a x p : Fin n} :
    p ∈ positionsIoo a x ↔ a < p ∧ p < x := by
  simp [positionsIoo, Finset.mem_Ioo]

theorem positionsIoc_pairwise {n : ℕ} (a x : Fin n) :
    (positionsIoc a x).Pairwise (· < ·) := by
  exact (Finset.sortedLT_sort (Finset.Ioc a x)).pairwise

theorem positionsIoo_pairwise {n : ℕ} (a x : Fin n) :
    (positionsIoo a x).Pairwise (· < ·) := by
  exact (Finset.sortedLT_sort (Finset.Ioo a x)).pairwise

theorem cons_positionsIoc_pairwise {n : ℕ} (a x : Fin n) :
    (a :: positionsIoc a x).Pairwise (· < ·) := by
  rw [List.pairwise_cons]
  constructor
  · intro p hp
    have hpIoc : p ∈ Finset.Ioc a x := by
      simpa only [positionsIoc, Finset.mem_sort] using hp
    exact (Finset.mem_Ioc.mp hpIoc).1
  · exact positionsIoc_pairwise a x

/-- Splitting a discrete interval immediately after its lower endpoint. -/
theorem positionsIoc_eq_cons_of_succ {n : ℕ} {c q x : Fin n}
    (hcq : q.val = c.val + 1) (hqx : q ≤ x) :
    positionsIoc c x = q :: positionsIoc q x := by
  apply List.Pairwise.eq_of_mem_iff
    (positionsIoc_pairwise c x) (cons_positionsIoc_pairwise q x)
  intro p
  simp only [mem_positionsIoc, List.mem_cons]
  omega

/-- Extending the upper endpoint by one appends that endpoint. -/
theorem positionsIoc_eq_append_of_succ {n : ℕ} {e c q : Fin n}
    (hec : e ≤ c) (hcq : q.val = c.val + 1) :
    positionsIoc e q = positionsIoc e c ++ [q] := by
  apply List.Pairwise.eq_of_mem_iff (positionsIoc_pairwise e q)
  · rw [List.pairwise_append]
    refine ⟨positionsIoc_pairwise e c, by simp, ?_⟩
    intro p hp r hr
    simp only [List.mem_singleton] at hr
    subst r
    have hpData := (mem_positionsIoc.mp hp)
    omega
  · intro p
    simp only [mem_positionsIoc, List.mem_append, List.mem_singleton]
    omega

/-- Immediately before the successor of `c`, the open interval is exactly
the already processed half-open interval through `c`. -/
theorem positionsIoo_eq_positionsIoc_of_succ
    {n : ℕ} {a c q : Fin n}
    (hcq : q.val = c.val + 1) :
    positionsIoo a q = positionsIoc a c := by
  apply List.Pairwise.eq_of_mem_iff
    (positionsIoo_pairwise a q) (positionsIoc_pairwise a c)
  intro p
  simp only [mem_positionsIoo, mem_positionsIoc]
  omega

/-- Splitting a complete discrete interval at an intermediate cutoff. -/
theorem positionsIoc_eq_append {n : ℕ} {e c x : Fin n}
    (hec : e ≤ c) (hcx : c ≤ x) :
    positionsIoc e x = positionsIoc e c ++ positionsIoc c x := by
  apply List.Pairwise.eq_of_mem_iff (positionsIoc_pairwise e x)
  · rw [List.pairwise_append]
    refine ⟨positionsIoc_pairwise e c, positionsIoc_pairwise c x, ?_⟩
    intro p hp q hq
    have hpData := mem_positionsIoc.mp hp
    have hqData := mem_positionsIoc.mp hq
    omega
  · intro p
    simp only [mem_positionsIoc, List.mem_append]
    omega

/-- Original-process state after processing the complete interval `(a,c]`. -/
def originalIntervalState {L : Type*} [Fintype L]
    (G : SimpleGraph L) (Q : List L)
    (D : Finset (Fin Q.length)) (a c : Fin Q.length) : RootLattice L :=
  updateProduct (originalWordUpdate G Q D) (positionsIoc a c)
    (simpleRoot (ARWord.label Q a))

/-- Original-process state immediately before position `p`, starting from
the simple root at `a`. -/
def originalPreIntervalState {L : Type*} [Fintype L]
    (G : SimpleGraph L) (Q : List L)
    (D : Finset (Fin Q.length)) (a p : Fin Q.length) : RootLattice L :=
  updateProduct (originalWordUpdate G Q D) (positionsIoo a p)
    (simpleRoot (ARWord.label Q a))

/-- The actual coefficient seen at position `p`: its own label-coordinate in
the original process immediately before processing `p`. -/
def originalIntervalCoefficient {L : Type*} [Fintype L]
    (G : SimpleGraph L) (Q : List L)
    (D : Finset (Fin Q.length)) (a p : Fin Q.length) : ℤ :=
  originalPreIntervalState G Q D a p (ARWord.label Q p)

/-- One original update advances the interval state across the next discrete
position. -/
theorem originalWordUpdate_originalIntervalState_of_succ
    {L : Type*} [Fintype L]
    (G : SimpleGraph L) (Q : List L)
    (D : Finset (Fin Q.length)) {a c q : Fin Q.length}
    (hac : a ≤ c) (hcq : q.val = c.val + 1) :
    originalWordUpdate G Q D q (originalIntervalState G Q D a c) =
      originalIntervalState G Q D a q := by
  unfold originalIntervalState
  rw [positionsIoc_eq_append_of_succ hac hcq, updateProduct_append]
  rfl

/-- The state immediately before the successor of `c` is the interval state
after processing through `c`. -/
theorem originalPreIntervalState_eq_originalIntervalState_of_succ
    {L : Type*} [Fintype L]
    (G : SimpleGraph L) (Q : List L)
    (D : Finset (Fin Q.length)) {a c q : Fin Q.length}
    (hcq : q.val = c.val + 1) :
    originalPreIntervalState G Q D a q =
      originalIntervalState G Q D a c := by
  unfold originalPreIntervalState originalIntervalState
  rw [positionsIoo_eq_positionsIoc_of_succ hcq]

/-- The definitional coefficient function automatically records every
coordinate encountered along an interval tail. -/
theorem hasOriginalCoefficients_originalIntervalState
    {L : Type*} [Fintype L]
    (G : SimpleGraph L) (Q : List L)
    (D : Finset (Fin Q.length))
    (a c x : Fin Q.length) (hac : a ≤ c) (hcx : c ≤ x) :
    HasOriginalCoefficients G Q D
      (originalIntervalCoefficient G Q D a) (positionsIoc c x)
      (originalIntervalState G Q D a c) := by
  by_cases hcxEq : c = x
  · subst x
    simp [positionsIoc, HasOriginalCoefficients]
  · have hcxlt : c < x := lt_of_le_of_ne hcx hcxEq
    let q : Fin Q.length := ⟨c.val + 1, by omega⟩
    have hcq : q.val = c.val + 1 := rfl
    have hqx : q ≤ x := by omega
    have haq : a ≤ q := by omega
    rw [positionsIoc_eq_cons_of_succ hcq hqx]
    change originalIntervalCoefficient G Q D a q =
          originalIntervalState G Q D a c (ARWord.label Q q) ∧
        HasOriginalCoefficients G Q D
          (originalIntervalCoefficient G Q D a) (positionsIoc q x)
          (originalWordUpdate G Q D q
            (originalIntervalState G Q D a c))
    constructor
    · unfold originalIntervalCoefficient
      rw [originalPreIntervalState_eq_originalIntervalState_of_succ
        G Q D hcq]
    · rw [originalWordUpdate_originalIntervalState_of_succ G Q D hac hcq]
      exact hasOriginalCoefficients_originalIntervalState
        G Q D a q x haq hqx
termination_by x.val - c.val
decreasing_by omega

/-- Initial-state specialization: `originalIntervalCoefficient` satisfies
`HasOriginalCoefficients` on every interval `(a,x]` without hypotheses. -/
theorem hasOriginalCoefficients_Ioc
    {L : Type*} [Fintype L]
    (G : SimpleGraph L) (Q : List L)
    (D : Finset (Fin Q.length)) (a x : Fin Q.length) (hax : a ≤ x) :
    HasOriginalCoefficients G Q D
      (originalIntervalCoefficient G Q D a) (positionsIoc a x)
      (simpleRoot (ARWord.label Q a)) := by
  have hcoeff := hasOriginalCoefficients_originalIntervalState
    G Q D a a x le_rfl hax
  simpa [originalIntervalState, positionsIoc] using hcoeff

/-- Along a complete interval whose terminal original state is a negative
simple root, every selected step has zero coordinate at each neighboring
label omitted from its middle positions.  Boundary-run separation supplies
the suffix preservation in the only case where that label has already been
seen. -/
theorem hasSelectedZeroOmittedNeighbors_originalIntervalState
    {L : Type*} [Fintype L]
    (G : SimpleGraph L) (Q : List L)
    (D : Finset (Fin Q.length))
    (hRuns : ARWord.HasOnlyBoundaryRepeatedRuns G Q)
    (a c x : Fin Q.length) (hac : a ≤ c) (hcx : c ≤ x)
    (hterminal :
      updateProduct (originalWordUpdate G Q D) (positionsIoc c x)
          (originalIntervalState G Q D a c) =
        -simpleRoot (ARWord.label Q x)) :
    HasSelectedZeroOmittedNeighbors G Q D (positionsIoc c x)
      (originalIntervalState G Q D a c) := by
  by_cases hcxEq : c = x
  · subst x
    simp [positionsIoc, HasSelectedZeroOmittedNeighbors]
  · have hcxlt : c < x := lt_of_le_of_ne hcx hcxEq
    let q : Fin Q.length := ⟨c.val + 1, by omega⟩
    have hcq : q.val = c.val + 1 := rfl
    have hqx : q ≤ x := by omega
    have haq : a ≤ q := by omega
    rw [positionsIoc_eq_cons_of_succ hcq hqx]
    change (q ∈ D → HasZeroOmittedNeighborCoordinates G Q q
          (originalIntervalState G Q D a c)) ∧
      HasSelectedZeroOmittedNeighbors G Q D (positionsIoc q x)
        (originalWordUpdate G Q D q
          (originalIntervalState G Q D a c))
    constructor
    · intro _ h hadj hnotMiddle
      by_cases hseen : ∃ b : Fin Q.length,
          a ≤ b ∧ b ≤ c ∧ ARWord.label Q b = h
      · obtain ⟨b, hab, hbc, hbh⟩ := hseen
        have hnoLater := no_later_occurrence_of_neighbor_not_middle
          G Q hRuns hadj ⟨b, by omega, hbh⟩ hnotMiddle
        have hpreserved :=
          updateProduct_originalWordUpdate_apply_of_forall_ne
            G Q D (positionsIoc c x)
            (originalIntervalState G Q D a c) h (by
              intro r hr
              have hrData := mem_positionsIoc.mp hr
              have hqr : q ≤ r := by omega
              by_cases hqrEq : q = r
              · subst r
                exact hadj.ne
              · exact (hnoLater r (lt_of_le_of_ne hqr hqrEq)).symm)
        have hxne : h ≠ ARWord.label Q x := by
          by_cases hqxEq : q = x
          · rw [← hqxEq]
            exact hadj.ne
          · exact (hnoLater x (lt_of_le_of_ne hqx hqxEq)).symm
        calc
          originalIntervalState G Q D a c h =
              updateProduct (originalWordUpdate G Q D) (positionsIoc c x)
                (originalIntervalState G Q D a c) h := hpreserved.symm
          _ = (-simpleRoot (ARWord.label Q x)) h := by rw [hterminal]
          _ = 0 := by
            change -simpleRoot (ARWord.label Q x) h = 0
            rw [simpleRoot_apply_of_ne hxne, neg_zero]
      · have hpreserved :=
          updateProduct_originalWordUpdate_apply_of_forall_ne
            G Q D (positionsIoc a c)
            (simpleRoot (ARWord.label Q a)) h (by
              intro r hr hhr
              apply hseen
              have hrData := mem_positionsIoc.mp hr
              exact ⟨r, hrData.1.le, hrData.2, hhr.symm⟩)
        have hane : h ≠ ARWord.label Q a := by
          intro hha
          apply hseen
          exact ⟨a, le_rfl, hac, hha.symm⟩
        exact hpreserved.trans (simpleRoot_apply_of_ne hane)
    · have hterminalTail :
          updateProduct (originalWordUpdate G Q D) (positionsIoc q x)
              (originalIntervalState G Q D a q) =
            -simpleRoot (ARWord.label Q x) := by
        have ht := hterminal
        rw [positionsIoc_eq_cons_of_succ hcq hqx,
          updateProduct_cons, LinearMap.comp_apply] at ht
        rw [← originalWordUpdate_originalIntervalState_of_succ
          G Q D hac hcq]
        exact ht
      rw [originalWordUpdate_originalIntervalState_of_succ G Q D hac hcq]
      exact hasSelectedZeroOmittedNeighbors_originalIntervalState
        G Q D hRuns a q x haq hqx hterminalTail
termination_by x.val - c.val
decreasing_by omega

/-- Initial-state specialization of the terminal negative-simple-root
criterion for selected zero omitted-neighbor coordinates. -/
theorem hasSelectedZeroOmittedNeighbors_Ioc_of_terminal
    {L : Type*} [Fintype L]
    (G : SimpleGraph L) (Q : List L)
    (D : Finset (Fin Q.length))
    (hRuns : ARWord.HasOnlyBoundaryRepeatedRuns G Q)
    (a x : Fin Q.length) (hax : a ≤ x)
    (hterminal :
      updateProduct (originalWordUpdate G Q D) (positionsIoc a x)
          (simpleRoot (ARWord.label Q a)) =
        -simpleRoot (ARWord.label Q x)) :
    HasSelectedZeroOmittedNeighbors G Q D (positionsIoc a x)
      (simpleRoot (ARWord.label Q a)) := by
  have hterminal' :
      updateProduct (originalWordUpdate G Q D) (positionsIoc a x)
          (originalIntervalState G Q D a a) =
        -simpleRoot (ARWord.label Q x) := by
    simpa [originalIntervalState, positionsIoc] using hterminal
  have hzero := hasSelectedZeroOmittedNeighbors_originalIntervalState
    G Q D hRuns a a x le_rfl hax hterminal'
  simpa [originalIntervalState, positionsIoc] using hzero

/-- The expected state of a fixed row after every position in `(e,c]` has
been processed: each encountered label stores its most recently written row
value, while labels not yet encountered retain the initial simple root. -/
noncomputable def expectedRowState {L : Type*} (Q : List L)
    (mu : Fin Q.length → ℤ) (e c : Fin Q.length) : RootLattice L :=
  overwriteRowCoordinates Q mu (simpleRoot (ARWord.label Q e))
    (positionsIoc e c)

/-- Reading a label at its last occurrence before the next discrete position
returns the corresponding row value.  Occurrences before the row source use
strict lower-triangular vanishing, the source uses the diagonal value, and
later occurrences use the overwrite invariant. -/
theorem expectedRowState_apply_of_last_before_succ
    {L : Type*} (Q : List L) (mu : Fin Q.length → ℤ)
    {e c q r : Fin Q.length}
    (hec : e ≤ c) (hcq : q.val = c.val + 1) (hrq : r < q)
    (hlast : ∀ z : Fin Q.length, r < z → z < q →
      ARWord.label Q z ≠ ARWord.label Q r)
    (hbelow : ∀ z : Fin Q.length, z < e → mu z = 0)
    (hdiag : mu e = 1) :
    expectedRowState Q mu e c (ARWord.label Q r) = mu r := by
  classical
  rcases lt_trichotomy r e with hre | hre | her
  · have hre_q : e < q := by omega
    have hbase : ARWord.label Q r ≠ ARWord.label Q e := by
      intro hlabel
      exact hlast e hre hre_q hlabel.symm
    calc
      expectedRowState Q mu e c (ARWord.label Q r) =
          simpleRoot (ARWord.label Q e) (ARWord.label Q r) := by
        apply overwriteRowCoordinates_apply_of_forall_ne
        intro p hp
        have hpData := mem_positionsIoc.mp hp
        exact (hlast p (hre.trans hpData.1) (by omega)).symm
      _ = 0 := simpleRoot_apply_of_ne hbase
      _ = mu r := (hbelow r hre).symm
  · subst r
    have heq_q : e < q := by omega
    calc
      expectedRowState Q mu e c (ARWord.label Q e) =
          simpleRoot (ARWord.label Q e) (ARWord.label Q e) := by
        apply overwriteRowCoordinates_apply_of_forall_ne
        intro p hp
        have hpData := mem_positionsIoc.mp hp
        exact (hlast p hpData.1 (by omega)).symm
      _ = 1 := simpleRoot_apply_self _
      _ = mu e := hdiag.symm
  · apply overwriteRowCoordinates_apply_eq_of_last
    · exact mem_positionsIoc.mpr ⟨her, by omega⟩
    · exact positionsIoc_pairwise e c
    · intro p hp hrp
      have hpData := mem_positionsIoc.mp hp
      exact hlast p hrp (by omega)

/-- The expected row state contains exactly the predecessor value required
by the scalar mesh recurrence. -/
theorem expectedRowState_apply_label_eq_previousValueSum_of_succ
    {L : Type*} (Q : List L) (mu : Fin Q.length → ℤ)
    {e c q : Fin Q.length}
    (hec : e ≤ c) (hcq : q.val = c.val + 1)
    (hbelow : ∀ z : Fin Q.length, z < e → mu z = 0)
    (hdiag : mu e = 1) :
    expectedRowState Q mu e c (ARWord.label Q q) =
      previousValueSum Q q mu := by
  classical
  by_cases hprevious : ∃ r : Fin Q.length, ARWord.IsPrevious Q r q
  · obtain ⟨r, hr⟩ := hprevious
    rw [previousValueSum_eq_of_isPrevious Q hr]
    rw [← hr.2.1]
    apply expectedRowState_apply_of_last_before_succ Q mu hec hcq hr.1
    · intro z hrz hzq hzr
      exact hr.2.2 z hrz hzq (hzr.trans hr.2.1)
    · exact hbelow
    · exact hdiag
  · rw [previousValueSum_eq_zero_of_no_previous Q q hprevious]
    calc
      expectedRowState Q mu e c (ARWord.label Q q) =
          simpleRoot (ARWord.label Q e) (ARWord.label Q q) := by
        apply overwriteRowCoordinates_apply_of_forall_ne
        intro p hp
        have hpData := mem_positionsIoc.mp hp
        intro hqp
        apply hprevious
        rw [ARWord.exists_isPrevious_iff_exists_lt_label_eq]
        exact ⟨p, by omega, hqp.symm⟩
      _ = 0 := by
        apply simpleRoot_apply_of_ne
        intro hqe
        apply hprevious
        rw [ARWord.exists_isPrevious_iff_exists_lt_label_eq]
        exact ⟨e, by omega, hqe.symm⟩

/-- Every middle-coordinate lookup in the expected row state returns its
row value. -/
theorem expectedRowState_apply_middle_eq_of_succ
    {L : Type*} (G : SimpleGraph L) (Q : List L)
    (mu : Fin Q.length → ℤ) {e c q : Fin Q.length}
    (hec : e ≤ c) (hcq : q.val = c.val + 1)
    (hbelow : ∀ z : Fin Q.length, z < e → mu z = 0)
    (hdiag : mu e = 1) :
    ∀ y : Fin Q.length, ARWord.IsMiddle G Q y q →
      expectedRowState Q mu e c (ARWord.label Q y) = mu y := by
  intro y hy
  apply expectedRowState_apply_of_last_before_succ Q mu hec hcq hy.2.1
  · exact hy.2.2.2
  · exact hbelow
  · exact hdiag

/-- One genuine modified update advances the expected row state across the
next discrete position. -/
theorem modifiedWordUpdate_expectedRowState_of_succ
    {L : Type*} (G : SimpleGraph L) (Q : List L)
    (D : Finset (Fin Q.length)) (mu : Fin Q.length → ℤ)
    {e c q : Fin Q.length}
    (hec : e ≤ c) (hcq : q.val = c.val + 1)
    (hbelow : ∀ z : Fin Q.length, z < e → mu z = 0)
    (hdiag : mu e = 1)
    (hrecurrence : ModifiedRowRecurrenceAt G Q D mu q) :
    modifiedWordUpdate G Q D q (expectedRowState Q mu e c) =
      expectedRowState Q mu e q := by
  rw [modifiedWordUpdate_eq_overwriteRowCoordinate_of_recorded
    G Q D mu q (expectedRowState Q mu e c) hrecurrence
    (expectedRowState_apply_label_eq_previousValueSum_of_succ
      Q mu hec hcq hbelow hdiag)
    (expectedRowState_apply_middle_eq_of_succ
      G Q mu hec hcq hbelow hdiag)]
  unfold expectedRowState
  rw [positionsIoc_eq_append_of_succ hec hcq,
    overwriteRowCoordinates_append]
  rfl

/-- Starting from the expected state at a cutoff `c`, the complete discrete
tail `(c,x]` satisfies every predecessor and middle-coordinate lookup in
`HasRecordedRowCoordinates`. -/
theorem hasRecordedRowCoordinates_expectedRowState
    {L : Type*} (G : SimpleGraph L) (Q : List L)
    (D : Finset (Fin Q.length)) (mu : Fin Q.length → ℤ)
    (e c x : Fin Q.length) (hec : e ≤ c) (hcx : c ≤ x)
    (hbelow : ∀ z : Fin Q.length, z < e → mu z = 0)
    (hdiag : mu e = 1)
    (hrecurrence : ∀ p : Fin Q.length, e < p →
      ModifiedRowRecurrenceAt G Q D mu p) :
    HasRecordedRowCoordinates G Q D mu (positionsIoc c x)
      (expectedRowState Q mu e c) := by
  by_cases hcxEq : c = x
  · subst x
    simp [positionsIoc, HasRecordedRowCoordinates]
  · have hcxlt : c < x := lt_of_le_of_ne hcx hcxEq
    let q : Fin Q.length := ⟨c.val + 1, by omega⟩
    have hcq : q.val = c.val + 1 := rfl
    have hqx : q ≤ x := by omega
    have heq : e ≤ q := by omega
    rw [positionsIoc_eq_cons_of_succ hcq hqx]
    change expectedRowState Q mu e c (ARWord.label Q q) =
          previousValueSum Q q mu ∧
        (∀ y : Fin Q.length, ARWord.IsMiddle G Q y q →
          expectedRowState Q mu e c (ARWord.label Q y) = mu y) ∧
        HasRecordedRowCoordinates G Q D mu (positionsIoc q x)
          (modifiedWordUpdate G Q D q (expectedRowState Q mu e c))
    refine ⟨expectedRowState_apply_label_eq_previousValueSum_of_succ
        Q mu hec hcq hbelow hdiag,
      expectedRowState_apply_middle_eq_of_succ
        G Q mu hec hcq hbelow hdiag, ?_⟩
    rw [modifiedWordUpdate_expectedRowState_of_succ
      G Q D mu hec hcq hbelow hdiag
      (hrecurrence q (by omega))]
    exact hasRecordedRowCoordinates_expectedRowState
      G Q D mu e q x heq hqx hbelow hdiag hrecurrence
termination_by x.val - c.val
decreasing_by omega

/-- The interval row beginning at its source has the complete recording
invariant, provided the row is lower triangular, diagonal-one, and satisfies
the modified recurrence strictly above the source. -/
theorem hasRecordedRowCoordinates_positionsIoc
    {L : Type*} (G : SimpleGraph L) (Q : List L)
    (D : Finset (Fin Q.length)) (mu : Fin Q.length → ℤ)
    (e x : Fin Q.length) (hex : e ≤ x)
    (hbelow : ∀ z : Fin Q.length, z < e → mu z = 0)
    (hdiag : mu e = 1)
    (hrecurrence : ∀ p : Fin Q.length, e < p →
      ModifiedRowRecurrenceAt G Q D mu p) :
    HasRecordedRowCoordinates G Q D mu (positionsIoc e x)
      (simpleRoot (ARWord.label Q e)) := by
  have hrecorded := hasRecordedRowCoordinates_expectedRowState
    G Q D mu e e x le_rfl hex hbelow hdiag hrecurrence
  simpa [expectedRowState, positionsIoc] using hrecorded

theorem positionsIoc_getLast?_eq_some {n : ℕ} {a x : Fin n}
    (hax : a < x) :
    (positionsIoc a x).getLast? = some x := by
  let s : Finset (Fin n) := Finset.Ioc a x
  have hxS : x ∈ s := by simp [s, hax]
  have hS : s.Nonempty := ⟨x, hxS⟩
  have hxList : x ∈ s.sort (· ≤ ·) :=
    (Finset.mem_sort (· ≤ ·)).2 hxS
  have hne : s.sort (· ≤ ·) ≠ [] := List.ne_nil_of_mem hxList
  have hmax : s.max' hS = x := by
    apply le_antisymm
    · exact (Finset.mem_Ioc.mp (s.max'_mem hS)).2
    · exact s.le_max' x hxS
  have hlast : (s.sort (· ≤ ·)).getLast hne = x := by
    rw [List.getLast_eq_getElem,
      ← Finset.max'_eq_sorted_last (s := s) (h := hS), hmax]
  change (s.sort (· ≤ ·)).getLast? = some x
  rw [List.getLast?_eq_some_getLast hne, hlast]

theorem cons_positionsIoc_getLast?_eq_some {n : ℕ} {a x : Fin n}
    (hax : a ≤ x) :
    (a :: positionsIoc a x).getLast? = some x := by
  rcases hax.eq_or_lt with hax | hax
  · subst x
    simp [positionsIoc]
  · have hlast := positionsIoc_getLast?_eq_some hax
    have hne : positionsIoc a x ≠ [] := by
      intro hnil
      simp [hnil] at hlast
    simpa [List.getLast?_cons_of_ne_nil hne] using hlast

theorem positionsIoc_eq_dropLast_append {n : ℕ} {a x : Fin n}
    (hax : a < x) :
    positionsIoc a x = (positionsIoc a x).dropLast ++ [x] := by
  have hlast := positionsIoc_getLast?_eq_some hax
  have hne : positionsIoc a x ≠ [] := by
    intro hnil
    simp [hnil] at hlast
  have hgetLast : (positionsIoc a x).getLast hne = x := by
    rw [List.getLast?_eq_some_getLast hne] at hlast
    exact Option.some.inj hlast
  calc
    positionsIoc a x =
        (positionsIoc a x).dropLast ++
          [(positionsIoc a x).getLast hne] :=
      (List.dropLast_concat_getLast hne).symm
    _ = (positionsIoc a x).dropLast ++ [x] := by rw [hgetLast]

/-- Nonnegativity of every preterminal interval state includes the state just
before its last position. -/
theorem selectedOperationalRootState_dropLast_isNonnegative
    {L : Type*} [Fintype L]
    (G : SimpleGraph L) (Q : List L)
    (D : Finset (Fin Q.length)) (a x : Fin Q.length) (hax : a < x)
    (hnonnegative : HasNonnegativeOriginalStates G Q D
      (positionsIoc a x) (simpleRoot (ARWord.label Q a))) :
    IsNonnegative (selectedOperationalRootState G Q D a
      (positionsIoc a x).dropLast) := by
  have hsplit : HasNonnegativeOriginalStates G Q D
      ((positionsIoc a x).dropLast ++ [x])
      (simpleRoot (ARWord.label Q a)) := by
    rw [← positionsIoc_eq_dropLast_append hax]
    exact hnonnegative
  have htail := hasNonnegativeOriginalStates_dropPrefix
    G Q D (positionsIoc a x).dropLast [x]
    (simpleRoot (ARWord.label Q a)) hsplit
  exact htail.1

/-- For an operational real root, the preceding nonnegativity is positivity:
nonzeroness is automatic from the geometric action. -/
theorem selectedOperationalRootState_dropLast_isPositive
    {L : Type*} [Fintype L]
    (G : SimpleGraph L) (Q : List L)
    (D : Finset (Fin Q.length)) (a x : Fin Q.length) (hax : a < x)
    (hnonnegative : HasNonnegativeOriginalStates G Q D
      (positionsIoc a x) (simpleRoot (ARWord.label Q a))) :
    IsPositive (selectedOperationalRootState G Q D a
      (positionsIoc a x).dropLast) := by
  exact ⟨selectedOperationalRootState_dropLast_isNonnegative
      G Q D a x hax hnonnegative,
    selectedOperationalRootState_ne_zero
      G Q D a (positionsIoc a x).dropLast⟩

/-- Interval form of the first-negative operational step. -/
theorem firstNegativeSelectedStep_Ioc_terminal
    {L : Type*} [Fintype L]
    (G : SimpleGraph L) (Q : List L)
    (D : Finset (Fin Q.length)) (a x : Fin Q.length)
    (hax : a < x) (hx : x ∈ D)
    (hpositive : IsPositive
      (selectedOperationalRootState G Q D a
        (positionsIoc a x).dropLast))
    (hnegative : IsNegative
      (originalWordUpdate G Q D x
        (selectedOperationalRootState G Q D a
          (positionsIoc a x).dropLast))) :
    updateProduct (originalWordUpdate G Q D) (positionsIoc a x)
        (simpleRoot (ARWord.label Q a)) =
      -simpleRoot (ARWord.label Q x) := by
  have hstep := firstNegativeSelectedStep G Q D a x
    (positionsIoc a x).dropLast hx hpositive hnegative
  rw [positionsIoc_eq_dropLast_append hax, updateProduct_append]
  simpa [selectedOperationalRootState, updateProduct] using hstep.2

variable {K R : Type uK} [Field K] [IsAlgClosed K]
  [Ring R] [Algebra K R] [FiniteDimensional K R] [IsNoetherianRing R]
  {Iota : Type uI} [Fintype Iota]
  (sigma : IndecomposableSkeleton.{uK, uI, uK} R Iota)

local instance : Finite (ProjectiveLabel sigma) :=
  Finite.of_injective Subtype.val Subtype.val_injective

local instance : Fintype (ProjectiveLabel sigma) := Fintype.ofFinite _

/-- Paper-facing coefficient `c_p` for the actual ordered AR word: the
`i_p`-coordinate of the original root immediately before position `p`. -/
def orderedARWordOriginalCoefficient
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (D : Finset (Fin (OrderedARWord.word sigma H T).length))
    (a p : Fin (OrderedARWord.word sigma H T).length) : ℤ :=
  originalIntervalCoefficient
    (OrderedARWord.orbitGraph sigma H T)
    (OrderedARWord.word sigma H T) D a p

/-- The actual coefficient function satisfies the recursive bookkeeping
predicate automatically. -/
theorem orderedARWord_hasOriginalCoefficients_Ioc
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (D : Finset (Fin (OrderedARWord.word sigma H T).length))
    (a x : Fin (OrderedARWord.word sigma H T).length) (hax : a ≤ x) :
    HasOriginalCoefficients
      (OrderedARWord.orbitGraph sigma H T)
      (OrderedARWord.word sigma H T) D
      (orderedARWordOriginalCoefficient sigma H T D a)
      (positionsIoc a x)
      (simpleRoot (ARWord.label (OrderedARWord.word sigma H T) a)) := by
  exact hasOriginalCoefficients_Ioc
    (OrderedARWord.orbitGraph sigma H T)
    (OrderedARWord.word sigma H T) D a x hax

/-- The three manuscript branches for `wordMixedMultiplicity`, combined into
one scalar update rule.  Its selected branch is exactly the coordinate rule
of `middleReflection`: subtract the value at the unique predecessor (or zero)
and add the values at all middle positions. -/
theorem wordMixedMultiplicity_modified_recurrence
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (D : Finset (Fin (OrderedARWord.word sigma H T).length))
    (a x : Fin (OrderedARWord.word sigma H T).length) :
    wordMixedMultiplicity (K := K) (R := R) sigma H T D a x =
      if x ∈ D then
        (if a = x then 1 else 0) +
          middleValueSum (OrderedARWord.orbitGraph sigma H T)
            (OrderedARWord.word sigma H T) x
            (fun y ↦ wordMixedMultiplicity (K := K) (R := R)
              sigma H T D a y) -
          previousValueSum (OrderedARWord.word sigma H T) x (fun p ↦
            wordMixedMultiplicity (K := K) (R := R)
              sigma H T D a p)
      else if a = x then 1 else 0 := by
  classical
  let Q := OrderedARWord.word sigma H T
  by_cases hxD : x ∈ D
  · rw [if_pos hxD]
    by_cases hprevious : ∃ p, ARWord.IsPrevious Q p x
    · obtain ⟨p, hp⟩ := hprevious
      rw [wordMixedMultiplicity_recurrence_of_isPrevious
          (K := K) (R := R) sigma H T D a p x hp hxD,
        previousValueSum_eq_of_isPrevious Q hp]
      unfold middleValueSum
      rw [← Finset.sum_subtype
        (Finset.univ.filter (fun y ↦
          ARWord.IsMiddle (OrderedARWord.orbitGraph sigma H T) Q y x))
        (by intro y; simp only [Finset.mem_filter, Finset.mem_univ,
          true_and, Q])
        (fun y ↦ wordMixedMultiplicity (K := K) (R := R)
          sigma H T D a y)]
    ·
      rw [wordMixedMultiplicity_recurrence_of_no_previous
          (K := K) (R := R) sigma H T D a x hprevious hxD,
        previousValueSum_eq_zero_of_no_previous Q x hprevious]
      unfold middleValueSum
      rw [← Finset.sum_subtype
        (Finset.univ.filter (fun y ↦
          ARWord.IsMiddle (OrderedARWord.orbitGraph sigma H T) Q y x))
        (by intro y; simp only [Finset.mem_filter, Finset.mem_univ,
          true_and, Q])
        (fun y ↦ wordMixedMultiplicity (K := K) (R := R)
          sigma H T D a y)]
      ring
  · rw [if_neg hxD,
      wordMixedMultiplicity_eq_delta_of_not_mem
        (K := K) (R := R) sigma H T D a x hxD]

/-- Strictly above its diagonal source, an actual
`wordMixedMultiplicity` row satisfies the delta-free modified-update
recurrence. -/
theorem wordMixedMultiplicity_modifiedRowRecurrenceAt_of_lt
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (D : Finset (Fin (OrderedARWord.word sigma H T).length))
    (e p : Fin (OrderedARWord.word sigma H T).length) (hep : e < p) :
    ModifiedRowRecurrenceAt (OrderedARWord.orbitGraph sigma H T)
      (OrderedARWord.word sigma H T) D
      (fun y ↦ wordMixedMultiplicity (K := K) (R := R)
        sigma H T D e y) p := by
  unfold ModifiedRowRecurrenceAt
  change wordMixedMultiplicity (K := K) (R := R) sigma H T D e p = _
  rw [wordMixedMultiplicity_modified_recurrence
    (K := K) (R := R) sigma H T D e p]
  simp [ne_of_lt hep]

/-- Every actual `wordMixedMultiplicity` row satisfies the recording
invariant on a complete position interval. -/
theorem wordMixedMultiplicity_hasRecordedRowCoordinates_Ioc
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (D : Finset (Fin (OrderedARWord.word sigma H T).length))
    (e x : Fin (OrderedARWord.word sigma H T).length) (hex : e ≤ x) :
    HasRecordedRowCoordinates
      (OrderedARWord.orbitGraph sigma H T)
      (OrderedARWord.word sigma H T) D
      (fun y ↦ wordMixedMultiplicity (K := K) (R := R)
        sigma H T D e y)
      (positionsIoc e x)
      (simpleRoot (ARWord.label (OrderedARWord.word sigma H T) e)) := by
  apply hasRecordedRowCoordinates_positionsIoc
    (OrderedARWord.orbitGraph sigma H T)
    (OrderedARWord.word sigma H T) D
    (fun y ↦ wordMixedMultiplicity (K := K) (R := R)
      sigma H T D e y) e x hex
  · intro z hze
    exact wordMixedMultiplicity_eq_zero_of_lt
      (K := K) (R := R) sigma H T D hze
  · exact wordMixedMultiplicity_self_eq_one
      (K := K) (R := R) sigma H T D e
  · intro p hep
    exact wordMixedMultiplicity_modifiedRowRecurrenceAt_of_lt
      (K := K) (R := R) sigma H T D e p hep

/-- The actual multiplicity matrix has the complete tail-row recording
invariant on every closed discrete interval. -/
theorem wordMixedMultiplicity_hasTailRowRecordings_Ioc
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (D : Finset (Fin (OrderedARWord.word sigma H T).length))
    (a x : Fin (OrderedARWord.word sigma H T).length) (hax : a ≤ x) :
    HasTailRowRecordings
      (OrderedARWord.orbitGraph sigma H T)
      (OrderedARWord.word sigma H T) D
      (fun e y ↦ wordMixedMultiplicity (K := K) (R := R)
        sigma H T D e y)
      (a :: positionsIoc a x) := by
  change HasRecordedRowCoordinates
        (OrderedARWord.orbitGraph sigma H T)
        (OrderedARWord.word sigma H T) D
        (fun y ↦ wordMixedMultiplicity (K := K) (R := R)
          sigma H T D a y)
        (positionsIoc a x)
        (simpleRoot (ARWord.label (OrderedARWord.word sigma H T) a)) ∧
      HasTailRowRecordings
        (OrderedARWord.orbitGraph sigma H T)
        (OrderedARWord.word sigma H T) D
        (fun e y ↦ wordMixedMultiplicity (K := K) (R := R)
          sigma H T D e y)
        (positionsIoc a x)
  refine ⟨wordMixedMultiplicity_hasRecordedRowCoordinates_Ioc
      (K := K) (R := R) sigma H T D a x hax, ?_⟩
  by_cases haxEq : a = x
  · subst x
    simp [positionsIoc, HasTailRowRecordings]
  · have haxlt : a < x := lt_of_le_of_ne hax haxEq
    let q : Fin (OrderedARWord.word sigma H T).length :=
      ⟨a.val + 1, by omega⟩
    have haq : q.val = a.val + 1 := rfl
    have hqx : q ≤ x := by omega
    rw [positionsIoc_eq_cons_of_succ haq hqx]
    exact wordMixedMultiplicity_hasTailRowRecordings_Ioc H T D q x hqx
termination_by x.val - a.val
decreasing_by omega

/-- For the actual ordered AR word, a terminal negative simple root
automatically supplies all selected zero omitted-neighbor coordinates. -/
theorem orderedARWord_hasSelectedZeroOmittedNeighbors_Ioc_of_terminal
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (D : Finset (Fin (OrderedARWord.word sigma H T).length))
    (a x : Fin (OrderedARWord.word sigma H T).length) (hax : a ≤ x)
    (hterminal :
      updateProduct
          (originalWordUpdate (OrderedARWord.orbitGraph sigma H T)
            (OrderedARWord.word sigma H T) D)
          (positionsIoc a x)
          (simpleRoot
            (ARWord.label (OrderedARWord.word sigma H T) a)) =
        -simpleRoot
          (ARWord.label (OrderedARWord.word sigma H T) x)) :
    HasSelectedZeroOmittedNeighbors
      (OrderedARWord.orbitGraph sigma H T)
      (OrderedARWord.word sigma H T) D
      (positionsIoc a x)
      (simpleRoot (ARWord.label (OrderedARWord.word sigma H T) a)) := by
  exact hasSelectedZeroOmittedNeighbors_Ioc_of_terminal
    (OrderedARWord.orbitGraph sigma H T)
    (OrderedARWord.word sigma H T) D
    (OrderedARWord.word_hasOnlyBoundaryRepeatedRuns sigma H T)
    a x hax hterminal

/-- For the actual AR word, the pure recurrence and diagonal facts discharge
all of `htransport` once the explicit last-occurrence recording invariant is
available on an increasing position list. -/
theorem wordMixedMultiplicity_hasTransportCoordinates_of_recordings
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (D : Finset (Fin (OrderedARWord.word sigma H T).length))
    (es : List (Fin (OrderedARWord.word sigma H T).length))
    (x : Fin (OrderedARWord.word sigma H T).length)
    (hrecordings : HasTailRowRecordings
      (OrderedARWord.orbitGraph sigma H T) (OrderedARWord.word sigma H T) D
      (fun e y ↦ wordMixedMultiplicity (K := K) (R := R)
        sigma H T D e y) es)
    (hsorted : es.Pairwise (· < ·))
    (hlast : es.getLast? = some x) :
    HasTransportCoordinates
      (modifiedWordUpdate (OrderedARWord.orbitGraph sigma H T)
        (OrderedARWord.word sigma H T) D)
      (ARWord.label (OrderedARWord.word sigma H T))
      (ARWord.label (OrderedARWord.word sigma H T) x)
      (fun e ↦ wordMixedMultiplicity (K := K) (R := R)
        sigma H T D e x) es := by
  apply hasTransportCoordinates_of_tailRowTransportData
    (OrderedARWord.orbitGraph sigma H T) (OrderedARWord.word sigma H T) D
    (fun e y ↦ wordMixedMultiplicity (K := K) (R := R)
      sigma H T D e y) es x
  · apply hasTailRowTransportData_of_recordings_of_pairwise
      (OrderedARWord.orbitGraph sigma H T) (OrderedARWord.word sigma H T) D
      (fun e y ↦ wordMixedMultiplicity (K := K) (R := R)
        sigma H T D e y) es hrecordings hsorted
    intro e p hep
    exact wordMixedMultiplicity_modifiedRowRecurrenceAt_of_lt
      (K := K) (R := R) sigma H T D e p hep
  · intro e he
    exact wordMixedMultiplicity_self_eq_one
      (K := K) (R := R) sigma H T D e
  · exact hlast

/-- Interval-specialized transport.  All recurrence, diagonal, ordering, and
terminal-position obligations are now automatic; only the explicit
last-occurrence recording invariant remains. -/
theorem wordMixedMultiplicity_hasTransportCoordinates_Ioc_of_recordings
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (D : Finset (Fin (OrderedARWord.word sigma H T).length))
    (a x : Fin (OrderedARWord.word sigma H T).length) (hax : a ≤ x)
    (hrecordings : HasTailRowRecordings
      (OrderedARWord.orbitGraph sigma H T) (OrderedARWord.word sigma H T) D
      (fun e y ↦ wordMixedMultiplicity (K := K) (R := R)
        sigma H T D e y) (a :: positionsIoc a x)) :
    HasTransportCoordinates
      (modifiedWordUpdate (OrderedARWord.orbitGraph sigma H T)
        (OrderedARWord.word sigma H T) D)
      (ARWord.label (OrderedARWord.word sigma H T))
      (ARWord.label (OrderedARWord.word sigma H T) x)
      (fun e ↦ wordMixedMultiplicity (K := K) (R := R)
        sigma H T D e x) (a :: positionsIoc a x) := by
  exact wordMixedMultiplicity_hasTransportCoordinates_of_recordings
    (K := K) (R := R) sigma H T D (a :: positionsIoc a x) x
    hrecordings (cons_positionsIoc_pairwise a x)
    (cons_positionsIoc_getLast?_eq_some hax)

omit [IsAlgClosed K] [FiniteDimensional K R] in
/-- A conditional paper-facing form of the cancellation identity.  The
remaining word-specific obligations are stated without abstraction loss:

* `hsums` is selected-update agreement along the original process;
* `htransport` says the modified process transports every inserted unit to
  the actual `wordMixedMultiplicity` row;
* `horiginal` is the terminal `-α_{i_x}` conclusion supplied by the
  first-negative-root argument.

The operator telescope and all scalar bookkeeping are discharged here. -/
theorem firstNegativeCancellation_wordMixedMultiplicity
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (D : Finset (Fin (OrderedARWord.word sigma H T).length))
    (a x : Fin (OrderedARWord.word sigma H T).length)
    (c : Fin (OrderedARWord.word sigma H T).length → ℤ)
    (hsums : let Q := OrderedARWord.word sigma H T
     let G := OrderedARWord.orbitGraph sigma H T
     let ps := positionsIoc a x
     HasSelectedNeighborSums G Q D ps (simpleRoot (ARWord.label Q a)))
    (hcoeff : let Q := OrderedARWord.word sigma H T
     let G := OrderedARWord.orbitGraph sigma H T
     let ps := positionsIoc a x
     HasOriginalCoefficients G Q D c ps (simpleRoot (ARWord.label Q a)))
    (htransport : let Q := OrderedARWord.word sigma H T
     let G := OrderedARWord.orbitGraph sigma H T
     let ps := positionsIoc a x
     HasTransportCoordinates (modifiedWordUpdate G Q D)
       (ARWord.label Q) (ARWord.label Q x)
       (fun e ↦ wordMixedMultiplicity (K := K) (R := R)
         sigma H T D e x) (a :: ps))
    (horiginal : let Q := OrderedARWord.word sigma H T
     let G := OrderedARWord.orbitGraph sigma H T
     let ps := positionsIoc a x
     updateProduct (originalWordUpdate G Q D) ps
       (simpleRoot (ARWord.label Q a)) =
         -simpleRoot (ARWord.label Q x)) :
    wordMixedMultiplicity (K := K) (R := R) sigma H T D a x =
      -1 - unselectedContributionSum D c
        (fun e ↦ wordMixedMultiplicity (K := K) (R := R)
          sigma H T D e x) (positionsIoc a x) := by
  let Q := OrderedARWord.word sigma H T
  let G := OrderedARWord.orbitGraph sigma H T
  let ps := positionsIoc a x
  change HasSelectedNeighborSums G Q D ps
    (simpleRoot (ARWord.label Q a)) at hsums
  change HasOriginalCoefficients G Q D c ps
    (simpleRoot (ARWord.label Q a)) at hcoeff
  change HasTransportCoordinates (modifiedWordUpdate G Q D)
    (ARWord.label Q) (ARWord.label Q x)
    (fun e ↦ wordMixedMultiplicity (K := K) (R := R)
      sigma H T D e x) (a :: ps) at htransport
  change updateProduct (originalWordUpdate G Q D) ps
    (simpleRoot (ARWord.label Q a)) =
      -simpleRoot (ARWord.label Q x) at horiginal
  have hlocal := hasLocalDefects_modifiedWordUpdate G Q D c ps
    (simpleRoot (ARWord.label Q a)) hsums hcoeff
  have hmodified := htransport.1
  have htransportTail := htransport.2
  apply cancellation_identity_of_telescope
    (modifiedWordUpdate G Q D) (originalWordUpdate G Q D)
    D c (ARWord.label Q) (ARWord.label Q x)
    (fun e ↦ wordMixedMultiplicity (K := K) (R := R)
      sigma H T D e x) ps (simpleRoot (ARWord.label Q a))
    (wordMixedMultiplicity (K := K) (R := R) sigma H T D a x)
    hlocal htransportTail hmodified
  rw [horiginal]
  simp

/-- Cancellation with both pure recurrence transport and the first-negative
terminal root discharged.  The two remaining substantive word obligations
are now visible: the last-occurrence row-recording invariant and selected
neighbor-sum agreement. -/
theorem firstNegativeCancellation_of_recordings
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (D : Finset (Fin (OrderedARWord.word sigma H T).length))
    (a x : Fin (OrderedARWord.word sigma H T).length)
    (hax : a < x) (hx : x ∈ D)
    (c : Fin (OrderedARWord.word sigma H T).length → ℤ)
    (hsums : let Q := OrderedARWord.word sigma H T
     let G := OrderedARWord.orbitGraph sigma H T
     HasSelectedNeighborSums G Q D (positionsIoc a x)
       (simpleRoot (ARWord.label Q a)))
    (hcoeff : let Q := OrderedARWord.word sigma H T
     let G := OrderedARWord.orbitGraph sigma H T
     HasOriginalCoefficients G Q D c (positionsIoc a x)
       (simpleRoot (ARWord.label Q a)))
    (hrecordings : let Q := OrderedARWord.word sigma H T
     let G := OrderedARWord.orbitGraph sigma H T
     HasTailRowRecordings G Q D
       (fun e y ↦ wordMixedMultiplicity (K := K) (R := R)
         sigma H T D e y) (a :: positionsIoc a x))
    (hpositive : let Q := OrderedARWord.word sigma H T
     let G := OrderedARWord.orbitGraph sigma H T
     IsPositive (selectedOperationalRootState G Q D a
       (positionsIoc a x).dropLast))
    (hnegative : let Q := OrderedARWord.word sigma H T
     let G := OrderedARWord.orbitGraph sigma H T
     IsNegative (originalWordUpdate G Q D x
       (selectedOperationalRootState G Q D a
         (positionsIoc a x).dropLast))) :
    wordMixedMultiplicity (K := K) (R := R) sigma H T D a x =
      -1 - unselectedContributionSum D c
        (fun e ↦ wordMixedMultiplicity (K := K) (R := R)
          sigma H T D e x) (positionsIoc a x) := by
  let Q := OrderedARWord.word sigma H T
  let G := OrderedARWord.orbitGraph sigma H T
  change HasSelectedNeighborSums G Q D (positionsIoc a x)
    (simpleRoot (ARWord.label Q a)) at hsums
  change HasOriginalCoefficients G Q D c (positionsIoc a x)
    (simpleRoot (ARWord.label Q a)) at hcoeff
  change HasTailRowRecordings G Q D
    (fun e y ↦ wordMixedMultiplicity (K := K) (R := R)
      sigma H T D e y) (a :: positionsIoc a x) at hrecordings
  change IsPositive (selectedOperationalRootState G Q D a
    (positionsIoc a x).dropLast) at hpositive
  change IsNegative (originalWordUpdate G Q D x
    (selectedOperationalRootState G Q D a
      (positionsIoc a x).dropLast)) at hnegative
  apply firstNegativeCancellation_wordMixedMultiplicity
    (K := K) (R := R) sigma H T D a x c hsums hcoeff
  · exact wordMixedMultiplicity_hasTransportCoordinates_Ioc_of_recordings
      (K := K) (R := R) sigma H T D a x hax.le hrecordings
  · exact firstNegativeSelectedStep_Ioc_terminal
      G Q D a x hax hx hpositive hnegative

/-- The strongest current cancellation assembly.  Selected-update agreement
is reduced further to the literal assertion that every neighboring label
omitted from the middle window has zero coordinate in the operational state. -/
theorem firstNegativeCancellation_of_recordings_of_zeroOmitted
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (D : Finset (Fin (OrderedARWord.word sigma H T).length))
    (a x : Fin (OrderedARWord.word sigma H T).length)
    (hax : a < x) (hx : x ∈ D)
    (c : Fin (OrderedARWord.word sigma H T).length → ℤ)
    (hzero : let Q := OrderedARWord.word sigma H T
     let G := OrderedARWord.orbitGraph sigma H T
     HasSelectedZeroOmittedNeighbors G Q D (positionsIoc a x)
       (simpleRoot (ARWord.label Q a)))
    (hcoeff : let Q := OrderedARWord.word sigma H T
     let G := OrderedARWord.orbitGraph sigma H T
     HasOriginalCoefficients G Q D c (positionsIoc a x)
       (simpleRoot (ARWord.label Q a)))
    (hrecordings : let Q := OrderedARWord.word sigma H T
     let G := OrderedARWord.orbitGraph sigma H T
     HasTailRowRecordings G Q D
       (fun e y ↦ wordMixedMultiplicity (K := K) (R := R)
         sigma H T D e y) (a :: positionsIoc a x))
    (hpositive : let Q := OrderedARWord.word sigma H T
     let G := OrderedARWord.orbitGraph sigma H T
     IsPositive (selectedOperationalRootState G Q D a
       (positionsIoc a x).dropLast))
    (hnegative : let Q := OrderedARWord.word sigma H T
     let G := OrderedARWord.orbitGraph sigma H T
     IsNegative (originalWordUpdate G Q D x
       (selectedOperationalRootState G Q D a
         (positionsIoc a x).dropLast))) :
    wordMixedMultiplicity (K := K) (R := R) sigma H T D a x =
      -1 - unselectedContributionSum D c
        (fun e ↦ wordMixedMultiplicity (K := K) (R := R)
          sigma H T D e x) (positionsIoc a x) := by
  let Q := OrderedARWord.word sigma H T
  let G := OrderedARWord.orbitGraph sigma H T
  change HasSelectedZeroOmittedNeighbors G Q D (positionsIoc a x)
    (simpleRoot (ARWord.label Q a)) at hzero
  apply firstNegativeCancellation_of_recordings
    (K := K) (R := R) sigma H T D a x hax hx c
  · exact hasSelectedNeighborSums_of_zero_omitted
      G Q D (positionsIoc a x) (simpleRoot (ARWord.label Q a)) hzero
  · exact hcoeff
  · exact hrecordings
  · exact hpositive
  · exact hnegative

/-- Fully discharged abstract word/root-state cancellation theorem.  The
row-recording invariant, selected neighbor-sum agreement, and terminal root
are all consequences of the ordered AR word and the first-negative step; the
only remaining input records the coefficients of the original process. -/
theorem firstNegativeCancellation_of_first_negative
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (D : Finset (Fin (OrderedARWord.word sigma H T).length))
    (a x : Fin (OrderedARWord.word sigma H T).length)
    (hax : a < x) (hx : x ∈ D)
    (c : Fin (OrderedARWord.word sigma H T).length → ℤ)
    (hcoeff : let Q := OrderedARWord.word sigma H T
     let G := OrderedARWord.orbitGraph sigma H T
     HasOriginalCoefficients G Q D c (positionsIoc a x)
       (simpleRoot (ARWord.label Q a)))
    (hpositive : let Q := OrderedARWord.word sigma H T
     let G := OrderedARWord.orbitGraph sigma H T
     IsPositive (selectedOperationalRootState G Q D a
       (positionsIoc a x).dropLast))
    (hnegative : let Q := OrderedARWord.word sigma H T
     let G := OrderedARWord.orbitGraph sigma H T
     IsNegative (originalWordUpdate G Q D x
       (selectedOperationalRootState G Q D a
         (positionsIoc a x).dropLast))) :
    wordMixedMultiplicity (K := K) (R := R) sigma H T D a x =
      -1 - unselectedContributionSum D c
        (fun e ↦ wordMixedMultiplicity (K := K) (R := R)
          sigma H T D e x) (positionsIoc a x) := by
  let Q := OrderedARWord.word sigma H T
  let G := OrderedARWord.orbitGraph sigma H T
  change HasOriginalCoefficients G Q D c (positionsIoc a x)
    (simpleRoot (ARWord.label Q a)) at hcoeff
  change IsPositive (selectedOperationalRootState G Q D a
    (positionsIoc a x).dropLast) at hpositive
  change IsNegative (originalWordUpdate G Q D x
    (selectedOperationalRootState G Q D a
      (positionsIoc a x).dropLast)) at hnegative
  have horiginal :
      updateProduct (originalWordUpdate G Q D) (positionsIoc a x)
          (simpleRoot (ARWord.label Q a)) =
        -simpleRoot (ARWord.label Q x) :=
    firstNegativeSelectedStep_Ioc_terminal
      G Q D a x hax hx hpositive hnegative
  have hzero : HasSelectedZeroOmittedNeighbors G Q D
      (positionsIoc a x) (simpleRoot (ARWord.label Q a)) :=
    orderedARWord_hasSelectedZeroOmittedNeighbors_Ioc_of_terminal
      sigma H T D a x hax.le horiginal
  have hsums : HasSelectedNeighborSums G Q D
      (positionsIoc a x) (simpleRoot (ARWord.label Q a)) :=
    hasSelectedNeighborSums_of_zero_omitted G Q D
      (positionsIoc a x) (simpleRoot (ARWord.label Q a)) hzero
  have hrecordings : HasTailRowRecordings G Q D
      (fun e y ↦ wordMixedMultiplicity (K := K) (R := R)
        sigma H T D e y) (a :: positionsIoc a x) :=
    wordMixedMultiplicity_hasTailRowRecordings_Ioc
      (K := K) (R := R) sigma H T D a x hax.le
  have htransport :=
    wordMixedMultiplicity_hasTransportCoordinates_Ioc_of_recordings
      (K := K) (R := R) sigma H T D a x hax.le hrecordings
  exact firstNegativeCancellation_wordMixedMultiplicity
    (K := K) (R := R) sigma H T D a x c
    hsums hcoeff htransport horiginal

/-- First cancellation with no bookkeeping hypothesis: the displayed
coefficient is definitionally the original pre-state coordinate. -/
theorem firstNegativeCancellation_actualCoefficients
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (D : Finset (Fin (OrderedARWord.word sigma H T).length))
    (a x : Fin (OrderedARWord.word sigma H T).length)
    (hax : a < x) (hx : x ∈ D)
    (hpositive : let Q := OrderedARWord.word sigma H T
     let G := OrderedARWord.orbitGraph sigma H T
     IsPositive (selectedOperationalRootState G Q D a
       (positionsIoc a x).dropLast))
    (hnegative : let Q := OrderedARWord.word sigma H T
     let G := OrderedARWord.orbitGraph sigma H T
     IsNegative (originalWordUpdate G Q D x
       (selectedOperationalRootState G Q D a
         (positionsIoc a x).dropLast))) :
    wordMixedMultiplicity (K := K) (R := R) sigma H T D a x =
      -1 - unselectedContributionSum D
        (orderedARWordOriginalCoefficient sigma H T D a)
        (fun e ↦ wordMixedMultiplicity (K := K) (R := R)
          sigma H T D e x) (positionsIoc a x) := by
  apply firstNegativeCancellation_of_first_negative
    (K := K) (R := R) sigma H T D a x hax hx
    (orderedARWordOriginalCoefficient sigma H T D a)
  · exact orderedARWord_hasOriginalCoefficients_Ioc
      sigma H T D a x hax.le
  · exact hpositive
  · exact hnegative

/-- Paper-facing first cancellation at a first negative step.  The process is
nonnegative before every listed update and becomes negative after the final
selected update.  Besides the cancellation identity, every nonzero omitted
coefficient occurring in its sum is strictly positive. -/
theorem firstNegativeCancellation_with_positive_coefficients
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (D : Finset (Fin (OrderedARWord.word sigma H T).length))
    (a x : Fin (OrderedARWord.word sigma H T).length)
    (hax : a < x) (hx : x ∈ D)
    (hnonnegative : let Q := OrderedARWord.word sigma H T
     let G := OrderedARWord.orbitGraph sigma H T
     HasNonnegativeOriginalStates G Q D (positionsIoc a x)
       (simpleRoot (ARWord.label Q a)))
    (hnegative : let Q := OrderedARWord.word sigma H T
     let G := OrderedARWord.orbitGraph sigma H T
     IsNegative (originalWordUpdate G Q D x
       (selectedOperationalRootState G Q D a
         (positionsIoc a x).dropLast))) :
    wordMixedMultiplicity (K := K) (R := R) sigma H T D a x =
        -1 - unselectedContributionSum D
          (orderedARWordOriginalCoefficient sigma H T D a)
          (fun e ↦ wordMixedMultiplicity (K := K) (R := R)
            sigma H T D e x) (positionsIoc a x) ∧
      ∀ e : Fin (OrderedARWord.word sigma H T).length,
        e ∈ positionsIoc a x → e ∉ D →
        orderedARWordOriginalCoefficient sigma H T D a e ≠ 0 →
        0 < orderedARWordOriginalCoefficient sigma H T D a e := by
  let Q := OrderedARWord.word sigma H T
  let G := OrderedARWord.orbitGraph sigma H T
  change HasNonnegativeOriginalStates G Q D (positionsIoc a x)
    (simpleRoot (ARWord.label Q a)) at hnonnegative
  change IsNegative (originalWordUpdate G Q D x
    (selectedOperationalRootState G Q D a
      (positionsIoc a x).dropLast)) at hnegative
  have hpositive : IsPositive (selectedOperationalRootState G Q D a
      (positionsIoc a x).dropLast) :=
    selectedOperationalRootState_dropLast_isPositive
      G Q D a x hax hnonnegative
  have hcancel := firstNegativeCancellation_actualCoefficients
    (K := K) (R := R) sigma H T D a x hax hx hpositive hnegative
  refine ⟨hcancel, ?_⟩
  intro e he _ hnonzero
  have hcoeff : HasOriginalCoefficients G Q D
      (orderedARWordOriginalCoefficient sigma H T D a)
      (positionsIoc a x) (simpleRoot (ARWord.label Q a)) :=
    orderedARWord_hasOriginalCoefficients_Ioc
      sigma H T D a x hax.le
  exact originalCoefficient_pos_of_nonzero
    G Q D (orderedARWordOriginalCoefficient sigma H T D a)
    (positionsIoc a x) (simpleRoot (ARWord.label Q a))
    hcoeff hnonnegative he hnonzero

/-! ## Explicit-order first cancellation -/

/-- Paper coefficient for an explicitly ordered AR word. -/
def orderedARWordOriginalCoefficientFor
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (D : Finset (Fin (OrderedARWord.wordFor sigma H T E).length))
    (a p : Fin (OrderedARWord.wordFor sigma H T E).length) : ℤ :=
  originalIntervalCoefficient
    (OrderedARWord.orbitGraph sigma H T)
    (OrderedARWord.wordFor sigma H T E) D a p

/-- The explicit-order coefficient function satisfies the generic original
coefficient bookkeeping predicate. -/
private theorem orderedARWordFor_hasOriginalCoefficients_Ioc
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (D : Finset (Fin (OrderedARWord.wordFor sigma H T E).length))
    (a x : Fin (OrderedARWord.wordFor sigma H T E).length) (hax : a ≤ x) :
    HasOriginalCoefficients
      (OrderedARWord.orbitGraph sigma H T)
      (OrderedARWord.wordFor sigma H T E) D
      (orderedARWordOriginalCoefficientFor sigma H T E D a)
      (positionsIoc a x)
      (simpleRoot
        (ARWord.label (OrderedARWord.wordFor sigma H T E) a)) := by
  exact hasOriginalCoefficients_Ioc
    (OrderedARWord.orbitGraph sigma H T)
    (OrderedARWord.wordFor sigma H T E) D a x hax

/-- The three explicit-order coordinate branches assembled into the generic
modified recurrence. -/
private theorem wordMixedMultiplicityFor_modified_recurrence
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (D : Finset (Fin (OrderedARWord.wordFor sigma H T E).length))
    (a x : Fin (OrderedARWord.wordFor sigma H T E).length) :
    wordMixedMultiplicityFor (K := K) (R := R) sigma H T E D a x =
      if x ∈ D then
        (if a = x then 1 else 0) +
          middleValueSum (OrderedARWord.orbitGraph sigma H T)
            (OrderedARWord.wordFor sigma H T E) x
            (fun y ↦ wordMixedMultiplicityFor (K := K) (R := R)
              sigma H T E D a y) -
          previousValueSum (OrderedARWord.wordFor sigma H T E) x (fun p ↦
            wordMixedMultiplicityFor (K := K) (R := R)
              sigma H T E D a p)
      else if a = x then 1 else 0 := by
  classical
  let Q := OrderedARWord.wordFor sigma H T E
  by_cases hxD : x ∈ D
  · rw [if_pos hxD]
    by_cases hprevious : ∃ p, ARWord.IsPrevious Q p x
    · obtain ⟨p, hp⟩ := hprevious
      rw [wordMixedMultiplicityFor_recurrence_of_isPrevious
          (K := K) (R := R) sigma H T E D a p x hp hxD,
        previousValueSum_eq_of_isPrevious Q hp]
      unfold middleValueSum
      rw [← Finset.sum_subtype
        (Finset.univ.filter (fun y ↦
          ARWord.IsMiddle (OrderedARWord.orbitGraph sigma H T) Q y x))
        (by intro y; simp only [Finset.mem_filter, Finset.mem_univ,
          true_and, Q])
        (fun y ↦ wordMixedMultiplicityFor (K := K) (R := R)
          sigma H T E D a y)]
    · rw [wordMixedMultiplicityFor_recurrence_of_no_previous
          (K := K) (R := R) sigma H T E D a x hprevious hxD,
        previousValueSum_eq_zero_of_no_previous Q x hprevious]
      unfold middleValueSum
      rw [← Finset.sum_subtype
        (Finset.univ.filter (fun y ↦
          ARWord.IsMiddle (OrderedARWord.orbitGraph sigma H T) Q y x))
        (by intro y; simp only [Finset.mem_filter, Finset.mem_univ,
          true_and, Q])
        (fun y ↦ wordMixedMultiplicityFor (K := K) (R := R)
          sigma H T E D a y)]
      ring
  · rw [if_neg hxD,
      wordMixedMultiplicityFor_eq_delta_of_not_mem
        (K := K) (R := R) sigma H T E D a x hxD]

/-- Delta-free modified recurrence strictly above the diagonal. -/
private theorem wordMixedMultiplicityFor_modifiedRowRecurrenceAt_of_lt
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (D : Finset (Fin (OrderedARWord.wordFor sigma H T E).length))
    (e p : Fin (OrderedARWord.wordFor sigma H T E).length) (hep : e < p) :
    ModifiedRowRecurrenceAt (OrderedARWord.orbitGraph sigma H T)
      (OrderedARWord.wordFor sigma H T E) D
      (fun y ↦ wordMixedMultiplicityFor (K := K) (R := R)
        sigma H T E D e y) p := by
  unfold ModifiedRowRecurrenceAt
  change wordMixedMultiplicityFor (K := K) (R := R)
    sigma H T E D e p = _
  rw [wordMixedMultiplicityFor_modified_recurrence
    (K := K) (R := R) sigma H T E D e p]
  simp [ne_of_lt hep]

/-- Every explicit-order coordinate row records the complete position
interval. -/
private theorem wordMixedMultiplicityFor_hasRecordedRowCoordinates_Ioc
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (D : Finset (Fin (OrderedARWord.wordFor sigma H T E).length))
    (e x : Fin (OrderedARWord.wordFor sigma H T E).length) (hex : e ≤ x) :
    HasRecordedRowCoordinates
      (OrderedARWord.orbitGraph sigma H T)
      (OrderedARWord.wordFor sigma H T E) D
      (fun y ↦ wordMixedMultiplicityFor (K := K) (R := R)
        sigma H T E D e y)
      (positionsIoc e x)
      (simpleRoot
        (ARWord.label (OrderedARWord.wordFor sigma H T E) e)) := by
  apply hasRecordedRowCoordinates_positionsIoc
    (OrderedARWord.orbitGraph sigma H T)
    (OrderedARWord.wordFor sigma H T E) D
    (fun y ↦ wordMixedMultiplicityFor (K := K) (R := R)
      sigma H T E D e y) e x hex
  · intro z hze
    exact wordMixedMultiplicityFor_eq_zero_of_lt
      (K := K) (R := R) sigma H T E D hze
  · exact wordMixedMultiplicityFor_self_eq_one
      (K := K) (R := R) sigma H T E D e
  · intro p hep
    exact wordMixedMultiplicityFor_modifiedRowRecurrenceAt_of_lt
      (K := K) (R := R) sigma H T E D e p hep

/-- Complete tail-row recordings on every explicit-order interval. -/
private theorem wordMixedMultiplicityFor_hasTailRowRecordings_Ioc
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (D : Finset (Fin (OrderedARWord.wordFor sigma H T E).length))
    (a x : Fin (OrderedARWord.wordFor sigma H T E).length) (hax : a ≤ x) :
    HasTailRowRecordings
      (OrderedARWord.orbitGraph sigma H T)
      (OrderedARWord.wordFor sigma H T E) D
      (fun e y ↦ wordMixedMultiplicityFor (K := K) (R := R)
        sigma H T E D e y)
      (a :: positionsIoc a x) := by
  change HasRecordedRowCoordinates
        (OrderedARWord.orbitGraph sigma H T)
        (OrderedARWord.wordFor sigma H T E) D
        (fun y ↦ wordMixedMultiplicityFor (K := K) (R := R)
          sigma H T E D a y)
        (positionsIoc a x)
        (simpleRoot
          (ARWord.label (OrderedARWord.wordFor sigma H T E) a)) ∧
      HasTailRowRecordings
        (OrderedARWord.orbitGraph sigma H T)
        (OrderedARWord.wordFor sigma H T E) D
        (fun e y ↦ wordMixedMultiplicityFor (K := K) (R := R)
          sigma H T E D e y)
        (positionsIoc a x)
  refine ⟨wordMixedMultiplicityFor_hasRecordedRowCoordinates_Ioc
      (K := K) (R := R) sigma H T E D a x hax, ?_⟩
  by_cases haxEq : a = x
  · subst x
    simp [positionsIoc, HasTailRowRecordings]
  · have haxlt : a < x := lt_of_le_of_ne hax haxEq
    let q : Fin (OrderedARWord.wordFor sigma H T E).length :=
      ⟨a.val + 1, by omega⟩
    have haq : q.val = a.val + 1 := rfl
    have hqx : q ≤ x := by omega
    rw [positionsIoc_eq_cons_of_succ haq hqx]
    exact wordMixedMultiplicityFor_hasTailRowRecordings_Ioc
      H T E D q x hqx
termination_by x.val - a.val
decreasing_by omega

omit [IsAlgClosed K] [FiniteDimensional K R] in
/-- Boundary-run structure discharges the omitted-neighbor condition at a
terminal negative simple root. -/
private theorem orderedARWordFor_hasSelectedZeroOmittedNeighbors_Ioc_of_terminal
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (D : Finset (Fin (OrderedARWord.wordFor sigma H T E).length))
    (a x : Fin (OrderedARWord.wordFor sigma H T E).length) (hax : a ≤ x)
    (hterminal :
      updateProduct
          (originalWordUpdate (OrderedARWord.orbitGraph sigma H T)
            (OrderedARWord.wordFor sigma H T E) D)
          (positionsIoc a x)
          (simpleRoot
            (ARWord.label (OrderedARWord.wordFor sigma H T E) a)) =
        -simpleRoot
          (ARWord.label (OrderedARWord.wordFor sigma H T E) x)) :
    HasSelectedZeroOmittedNeighbors
      (OrderedARWord.orbitGraph sigma H T)
      (OrderedARWord.wordFor sigma H T E) D
      (positionsIoc a x)
      (simpleRoot
        (ARWord.label (OrderedARWord.wordFor sigma H T E) a)) := by
  exact hasSelectedZeroOmittedNeighbors_Ioc_of_terminal
    (OrderedARWord.orbitGraph sigma H T)
    (OrderedARWord.wordFor sigma H T E) D
    (OrderedARWord.wordFor_hasOnlyBoundaryRepeatedRuns sigma H T E)
    a x hax hterminal

/-- Generic recurrence data gives transport coordinates once row recordings
are available. -/
private theorem wordMixedMultiplicityFor_hasTransportCoordinates_of_recordings
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (D : Finset (Fin (OrderedARWord.wordFor sigma H T E).length))
    (es : List (Fin (OrderedARWord.wordFor sigma H T E).length))
    (x : Fin (OrderedARWord.wordFor sigma H T E).length)
    (hrecordings : HasTailRowRecordings
      (OrderedARWord.orbitGraph sigma H T)
      (OrderedARWord.wordFor sigma H T E) D
      (fun e y ↦ wordMixedMultiplicityFor (K := K) (R := R)
        sigma H T E D e y) es)
    (hsorted : es.Pairwise (· < ·))
    (hlast : es.getLast? = some x) :
    HasTransportCoordinates
      (modifiedWordUpdate (OrderedARWord.orbitGraph sigma H T)
        (OrderedARWord.wordFor sigma H T E) D)
      (ARWord.label (OrderedARWord.wordFor sigma H T E))
      (ARWord.label (OrderedARWord.wordFor sigma H T E) x)
      (fun e ↦ wordMixedMultiplicityFor (K := K) (R := R)
        sigma H T E D e x) es := by
  apply hasTransportCoordinates_of_tailRowTransportData
    (OrderedARWord.orbitGraph sigma H T)
    (OrderedARWord.wordFor sigma H T E) D
    (fun e y ↦ wordMixedMultiplicityFor (K := K) (R := R)
      sigma H T E D e y) es x
  · apply hasTailRowTransportData_of_recordings_of_pairwise
      (OrderedARWord.orbitGraph sigma H T)
      (OrderedARWord.wordFor sigma H T E) D
      (fun e y ↦ wordMixedMultiplicityFor (K := K) (R := R)
        sigma H T E D e y) es hrecordings hsorted
    intro e p hep
    exact wordMixedMultiplicityFor_modifiedRowRecurrenceAt_of_lt
      (K := K) (R := R) sigma H T E D e p hep
  · intro e he
    exact wordMixedMultiplicityFor_self_eq_one
      (K := K) (R := R) sigma H T E D e
  · exact hlast

/-- Interval-specialized explicit-order transport. -/
private theorem wordMixedMultiplicityFor_hasTransportCoordinates_Ioc_of_recordings
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (D : Finset (Fin (OrderedARWord.wordFor sigma H T E).length))
    (a x : Fin (OrderedARWord.wordFor sigma H T E).length) (hax : a ≤ x)
    (hrecordings : HasTailRowRecordings
      (OrderedARWord.orbitGraph sigma H T)
      (OrderedARWord.wordFor sigma H T E) D
      (fun e y ↦ wordMixedMultiplicityFor (K := K) (R := R)
        sigma H T E D e y) (a :: positionsIoc a x)) :
    HasTransportCoordinates
      (modifiedWordUpdate (OrderedARWord.orbitGraph sigma H T)
        (OrderedARWord.wordFor sigma H T E) D)
      (ARWord.label (OrderedARWord.wordFor sigma H T E))
      (ARWord.label (OrderedARWord.wordFor sigma H T E) x)
      (fun e ↦ wordMixedMultiplicityFor (K := K) (R := R)
        sigma H T E D e x) (a :: positionsIoc a x) := by
  exact wordMixedMultiplicityFor_hasTransportCoordinates_of_recordings
    (K := K) (R := R) sigma H T E D
    (a :: positionsIoc a x) x hrecordings
    (cons_positionsIoc_pairwise a x)
    (cons_positionsIoc_getLast?_eq_some hax)

omit [IsAlgClosed K] [FiniteDimensional K R] in
/-- The generic telescope, instantiated with explicit-order mixed
multiplicity rows. -/
private theorem firstNegativeCancellation_wordMixedMultiplicityFor
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (D : Finset (Fin (OrderedARWord.wordFor sigma H T E).length))
    (a x : Fin (OrderedARWord.wordFor sigma H T E).length)
    (c : Fin (OrderedARWord.wordFor sigma H T E).length → ℤ)
    (hsums : let Q := OrderedARWord.wordFor sigma H T E
     let G := OrderedARWord.orbitGraph sigma H T
     let ps := positionsIoc a x
     HasSelectedNeighborSums G Q D ps
       (simpleRoot (ARWord.label Q a)))
    (hcoeff : let Q := OrderedARWord.wordFor sigma H T E
     let G := OrderedARWord.orbitGraph sigma H T
     let ps := positionsIoc a x
     HasOriginalCoefficients G Q D c ps
       (simpleRoot (ARWord.label Q a)))
    (htransport : let Q := OrderedARWord.wordFor sigma H T E
     let G := OrderedARWord.orbitGraph sigma H T
     let ps := positionsIoc a x
     HasTransportCoordinates (modifiedWordUpdate G Q D)
       (ARWord.label Q) (ARWord.label Q x)
       (fun e ↦ wordMixedMultiplicityFor (K := K) (R := R)
         sigma H T E D e x) (a :: ps))
    (horiginal : let Q := OrderedARWord.wordFor sigma H T E
     let G := OrderedARWord.orbitGraph sigma H T
     let ps := positionsIoc a x
     updateProduct (originalWordUpdate G Q D) ps
       (simpleRoot (ARWord.label Q a)) =
         -simpleRoot (ARWord.label Q x)) :
    wordMixedMultiplicityFor (K := K) (R := R)
        sigma H T E D a x =
      -1 - unselectedContributionSum D c
        (fun e ↦ wordMixedMultiplicityFor (K := K) (R := R)
          sigma H T E D e x) (positionsIoc a x) := by
  let Q := OrderedARWord.wordFor sigma H T E
  let G := OrderedARWord.orbitGraph sigma H T
  let ps := positionsIoc a x
  change HasSelectedNeighborSums G Q D ps
    (simpleRoot (ARWord.label Q a)) at hsums
  change HasOriginalCoefficients G Q D c ps
    (simpleRoot (ARWord.label Q a)) at hcoeff
  change HasTransportCoordinates (modifiedWordUpdate G Q D)
    (ARWord.label Q) (ARWord.label Q x)
    (fun e ↦ wordMixedMultiplicityFor (K := K) (R := R)
      sigma H T E D e x) (a :: ps) at htransport
  change updateProduct (originalWordUpdate G Q D) ps
    (simpleRoot (ARWord.label Q a)) =
      -simpleRoot (ARWord.label Q x) at horiginal
  have hlocal := hasLocalDefects_modifiedWordUpdate G Q D c ps
    (simpleRoot (ARWord.label Q a)) hsums hcoeff
  have hmodified := htransport.1
  have htransportTail := htransport.2
  apply cancellation_identity_of_telescope
    (modifiedWordUpdate G Q D) (originalWordUpdate G Q D)
    D c (ARWord.label Q) (ARWord.label Q x)
    (fun e ↦ wordMixedMultiplicityFor (K := K) (R := R)
      sigma H T E D e x) ps (simpleRoot (ARWord.label Q a))
    (wordMixedMultiplicityFor (K := K) (R := R)
      sigma H T E D a x)
    hlocal htransportTail hmodified
  rw [horiginal]
  simp

/-- Cancellation with recurrence transport and terminal-root calculation
discharged from explicit-order row recordings. -/
private theorem firstNegativeCancellation_of_recordingsFor
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (D : Finset (Fin (OrderedARWord.wordFor sigma H T E).length))
    (a x : Fin (OrderedARWord.wordFor sigma H T E).length)
    (hax : a < x) (hx : x ∈ D)
    (c : Fin (OrderedARWord.wordFor sigma H T E).length → ℤ)
    (hsums : let Q := OrderedARWord.wordFor sigma H T E
     let G := OrderedARWord.orbitGraph sigma H T
     HasSelectedNeighborSums G Q D (positionsIoc a x)
       (simpleRoot (ARWord.label Q a)))
    (hcoeff : let Q := OrderedARWord.wordFor sigma H T E
     let G := OrderedARWord.orbitGraph sigma H T
     HasOriginalCoefficients G Q D c (positionsIoc a x)
       (simpleRoot (ARWord.label Q a)))
    (hrecordings : let Q := OrderedARWord.wordFor sigma H T E
     let G := OrderedARWord.orbitGraph sigma H T
     HasTailRowRecordings G Q D
       (fun e y ↦ wordMixedMultiplicityFor (K := K) (R := R)
         sigma H T E D e y) (a :: positionsIoc a x))
    (hpositive : let Q := OrderedARWord.wordFor sigma H T E
     let G := OrderedARWord.orbitGraph sigma H T
     IsPositive (selectedOperationalRootState G Q D a
       (positionsIoc a x).dropLast))
    (hnegative : let Q := OrderedARWord.wordFor sigma H T E
     let G := OrderedARWord.orbitGraph sigma H T
     IsNegative (originalWordUpdate G Q D x
       (selectedOperationalRootState G Q D a
         (positionsIoc a x).dropLast))) :
    wordMixedMultiplicityFor (K := K) (R := R)
        sigma H T E D a x =
      -1 - unselectedContributionSum D c
        (fun e ↦ wordMixedMultiplicityFor (K := K) (R := R)
          sigma H T E D e x) (positionsIoc a x) := by
  let Q := OrderedARWord.wordFor sigma H T E
  let G := OrderedARWord.orbitGraph sigma H T
  change HasSelectedNeighborSums G Q D (positionsIoc a x)
    (simpleRoot (ARWord.label Q a)) at hsums
  change HasOriginalCoefficients G Q D c (positionsIoc a x)
    (simpleRoot (ARWord.label Q a)) at hcoeff
  change HasTailRowRecordings G Q D
    (fun e y ↦ wordMixedMultiplicityFor (K := K) (R := R)
      sigma H T E D e y) (a :: positionsIoc a x) at hrecordings
  change IsPositive (selectedOperationalRootState G Q D a
    (positionsIoc a x).dropLast) at hpositive
  change IsNegative (originalWordUpdate G Q D x
    (selectedOperationalRootState G Q D a
      (positionsIoc a x).dropLast)) at hnegative
  apply firstNegativeCancellation_wordMixedMultiplicityFor
    (K := K) (R := R) sigma H T E D a x c hsums hcoeff
  · exact wordMixedMultiplicityFor_hasTransportCoordinates_Ioc_of_recordings
      (K := K) (R := R) sigma H T E D a x hax.le hrecordings
  · exact firstNegativeSelectedStep_Ioc_terminal
      G Q D a x hax hx hpositive hnegative

/-- Replace selected-neighbor agreement by its zero-omitted-neighbor
criterion. -/
private theorem firstNegativeCancellation_of_recordings_of_zeroOmittedFor
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (D : Finset (Fin (OrderedARWord.wordFor sigma H T E).length))
    (a x : Fin (OrderedARWord.wordFor sigma H T E).length)
    (hax : a < x) (hx : x ∈ D)
    (c : Fin (OrderedARWord.wordFor sigma H T E).length → ℤ)
    (hzero : let Q := OrderedARWord.wordFor sigma H T E
     let G := OrderedARWord.orbitGraph sigma H T
     HasSelectedZeroOmittedNeighbors G Q D (positionsIoc a x)
       (simpleRoot (ARWord.label Q a)))
    (hcoeff : let Q := OrderedARWord.wordFor sigma H T E
     let G := OrderedARWord.orbitGraph sigma H T
     HasOriginalCoefficients G Q D c (positionsIoc a x)
       (simpleRoot (ARWord.label Q a)))
    (hrecordings : let Q := OrderedARWord.wordFor sigma H T E
     let G := OrderedARWord.orbitGraph sigma H T
     HasTailRowRecordings G Q D
       (fun e y ↦ wordMixedMultiplicityFor (K := K) (R := R)
         sigma H T E D e y) (a :: positionsIoc a x))
    (hpositive : let Q := OrderedARWord.wordFor sigma H T E
     let G := OrderedARWord.orbitGraph sigma H T
     IsPositive (selectedOperationalRootState G Q D a
       (positionsIoc a x).dropLast))
    (hnegative : let Q := OrderedARWord.wordFor sigma H T E
     let G := OrderedARWord.orbitGraph sigma H T
     IsNegative (originalWordUpdate G Q D x
       (selectedOperationalRootState G Q D a
         (positionsIoc a x).dropLast))) :
    wordMixedMultiplicityFor (K := K) (R := R)
        sigma H T E D a x =
      -1 - unselectedContributionSum D c
        (fun e ↦ wordMixedMultiplicityFor (K := K) (R := R)
          sigma H T E D e x) (positionsIoc a x) := by
  let Q := OrderedARWord.wordFor sigma H T E
  let G := OrderedARWord.orbitGraph sigma H T
  change HasSelectedZeroOmittedNeighbors G Q D (positionsIoc a x)
    (simpleRoot (ARWord.label Q a)) at hzero
  apply firstNegativeCancellation_of_recordingsFor
    (K := K) (R := R) sigma H T E D a x hax hx c
  · exact hasSelectedNeighborSums_of_zero_omitted
      G Q D (positionsIoc a x) (simpleRoot (ARWord.label Q a)) hzero
  · exact hcoeff
  · exact hrecordings
  · exact hpositive
  · exact hnegative

/-- Fully discharged explicit-order cancellation theorem, except for the
generic original coefficient bookkeeping. -/
private theorem firstNegativeCancellation_of_first_negativeFor
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (D : Finset (Fin (OrderedARWord.wordFor sigma H T E).length))
    (a x : Fin (OrderedARWord.wordFor sigma H T E).length)
    (hax : a < x) (hx : x ∈ D)
    (c : Fin (OrderedARWord.wordFor sigma H T E).length → ℤ)
    (hcoeff : let Q := OrderedARWord.wordFor sigma H T E
     let G := OrderedARWord.orbitGraph sigma H T
     HasOriginalCoefficients G Q D c (positionsIoc a x)
       (simpleRoot (ARWord.label Q a)))
    (hpositive : let Q := OrderedARWord.wordFor sigma H T E
     let G := OrderedARWord.orbitGraph sigma H T
     IsPositive (selectedOperationalRootState G Q D a
       (positionsIoc a x).dropLast))
    (hnegative : let Q := OrderedARWord.wordFor sigma H T E
     let G := OrderedARWord.orbitGraph sigma H T
     IsNegative (originalWordUpdate G Q D x
       (selectedOperationalRootState G Q D a
         (positionsIoc a x).dropLast))) :
    wordMixedMultiplicityFor (K := K) (R := R)
        sigma H T E D a x =
      -1 - unselectedContributionSum D c
        (fun e ↦ wordMixedMultiplicityFor (K := K) (R := R)
          sigma H T E D e x) (positionsIoc a x) := by
  let Q := OrderedARWord.wordFor sigma H T E
  let G := OrderedARWord.orbitGraph sigma H T
  change HasOriginalCoefficients G Q D c (positionsIoc a x)
    (simpleRoot (ARWord.label Q a)) at hcoeff
  change IsPositive (selectedOperationalRootState G Q D a
    (positionsIoc a x).dropLast) at hpositive
  change IsNegative (originalWordUpdate G Q D x
    (selectedOperationalRootState G Q D a
      (positionsIoc a x).dropLast)) at hnegative
  have horiginal :
      updateProduct (originalWordUpdate G Q D) (positionsIoc a x)
          (simpleRoot (ARWord.label Q a)) =
        -simpleRoot (ARWord.label Q x) :=
    firstNegativeSelectedStep_Ioc_terminal
      G Q D a x hax hx hpositive hnegative
  have hzero : HasSelectedZeroOmittedNeighbors G Q D
      (positionsIoc a x) (simpleRoot (ARWord.label Q a)) :=
    orderedARWordFor_hasSelectedZeroOmittedNeighbors_Ioc_of_terminal
      sigma H T E D a x hax.le horiginal
  have hsums : HasSelectedNeighborSums G Q D
      (positionsIoc a x) (simpleRoot (ARWord.label Q a)) :=
    hasSelectedNeighborSums_of_zero_omitted G Q D
      (positionsIoc a x) (simpleRoot (ARWord.label Q a)) hzero
  have hrecordings : HasTailRowRecordings G Q D
      (fun e y ↦ wordMixedMultiplicityFor (K := K) (R := R)
        sigma H T E D e y) (a :: positionsIoc a x) :=
    wordMixedMultiplicityFor_hasTailRowRecordings_Ioc
      (K := K) (R := R) sigma H T E D a x hax.le
  have htransport :=
    wordMixedMultiplicityFor_hasTransportCoordinates_Ioc_of_recordings
      (K := K) (R := R) sigma H T E D a x hax.le hrecordings
  exact firstNegativeCancellation_wordMixedMultiplicityFor
    (K := K) (R := R) sigma H T E D a x c
    hsums hcoeff htransport horiginal

/-- Cancellation using the definitionally supplied original coefficients. -/
private theorem firstNegativeCancellation_actualCoefficientsFor
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (D : Finset (Fin (OrderedARWord.wordFor sigma H T E).length))
    (a x : Fin (OrderedARWord.wordFor sigma H T E).length)
    (hax : a < x) (hx : x ∈ D)
    (hpositive : let Q := OrderedARWord.wordFor sigma H T E
     let G := OrderedARWord.orbitGraph sigma H T
     IsPositive (selectedOperationalRootState G Q D a
       (positionsIoc a x).dropLast))
    (hnegative : let Q := OrderedARWord.wordFor sigma H T E
     let G := OrderedARWord.orbitGraph sigma H T
     IsNegative (originalWordUpdate G Q D x
       (selectedOperationalRootState G Q D a
         (positionsIoc a x).dropLast))) :
    wordMixedMultiplicityFor (K := K) (R := R)
        sigma H T E D a x =
      -1 - unselectedContributionSum D
        (orderedARWordOriginalCoefficientFor sigma H T E D a)
        (fun e ↦ wordMixedMultiplicityFor (K := K) (R := R)
          sigma H T E D e x) (positionsIoc a x) := by
  apply firstNegativeCancellation_of_first_negativeFor
    (K := K) (R := R) sigma H T E D a x hax hx
    (orderedARWordOriginalCoefficientFor sigma H T E D a)
  · exact orderedARWordFor_hasOriginalCoefficients_Ioc
      sigma H T E D a x hax.le
  · exact hpositive
  · exact hnegative

/-- Explicit-order first cancellation with positivity of every nonzero
omitted coefficient. -/
theorem firstNegativeCancellation_with_positive_coefficientsFor
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (D : Finset (Fin (OrderedARWord.wordFor sigma H T E).length))
    (a x : Fin (OrderedARWord.wordFor sigma H T E).length)
    (hax : a < x) (hx : x ∈ D)
    (hnonnegative : let Q := OrderedARWord.wordFor sigma H T E
     let G := OrderedARWord.orbitGraph sigma H T
     HasNonnegativeOriginalStates G Q D (positionsIoc a x)
       (simpleRoot (ARWord.label Q a)))
    (hnegative : let Q := OrderedARWord.wordFor sigma H T E
     let G := OrderedARWord.orbitGraph sigma H T
     IsNegative (originalWordUpdate G Q D x
       (selectedOperationalRootState G Q D a
         (positionsIoc a x).dropLast))) :
    wordMixedMultiplicityFor (K := K) (R := R)
        sigma H T E D a x =
        -1 - unselectedContributionSum D
          (orderedARWordOriginalCoefficientFor sigma H T E D a)
          (fun e ↦ wordMixedMultiplicityFor (K := K) (R := R)
            sigma H T E D e x) (positionsIoc a x) ∧
      ∀ e : Fin (OrderedARWord.wordFor sigma H T E).length,
        e ∈ positionsIoc a x → e ∉ D →
        orderedARWordOriginalCoefficientFor sigma H T E D a e ≠ 0 →
        0 < orderedARWordOriginalCoefficientFor sigma H T E D a e := by
  let Q := OrderedARWord.wordFor sigma H T E
  let G := OrderedARWord.orbitGraph sigma H T
  change HasNonnegativeOriginalStates G Q D (positionsIoc a x)
    (simpleRoot (ARWord.label Q a)) at hnonnegative
  change IsNegative (originalWordUpdate G Q D x
    (selectedOperationalRootState G Q D a
      (positionsIoc a x).dropLast)) at hnegative
  have hpositive : IsPositive (selectedOperationalRootState G Q D a
      (positionsIoc a x).dropLast) :=
    selectedOperationalRootState_dropLast_isPositive
      G Q D a x hax hnonnegative
  have hcancel := firstNegativeCancellation_actualCoefficientsFor
    (K := K) (R := R) sigma H T E D a x
      hax hx hpositive hnegative
  refine ⟨hcancel, ?_⟩
  intro e he _ hnonzero
  have hcoeff : HasOriginalCoefficients G Q D
      (orderedARWordOriginalCoefficientFor sigma H T E D a)
      (positionsIoc a x) (simpleRoot (ARWord.label Q a)) :=
    orderedARWordFor_hasOriginalCoefficients_Ioc
      sigma H T E D a x hax.le
  exact originalCoefficient_pos_of_nonzero
    G Q D (orderedARWordOriginalCoefficientFor sigma H T E D a)
    (positionsIoc a x) (simpleRoot (ARWord.label Q a))
    hcoeff hnonnegative he hnonzero

end WordMixedMultiplicityWrapper

end QuotientSubmoduleEquidistribution.RepresentationDirected.FirstCancellation
