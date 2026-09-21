/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.Topology.GDelta.MetrizableSpace
public import PCError.Attr

/-!
# Squared sines of angles between lines, and from a vector to a subspace

Eigenvectors are determined only up to sign, so the angles used throughout this
development are angles between *lines*. The squared sine is the natural sign-free
invariant: `sinSqAngle u v = 1 - ⟪u, v⟫ ^ 2 / (‖u‖ ^ 2 * ‖v‖ ^ 2)` is unchanged when
either argument is rescaled by a nonzero real, in particular when it is negated.

## Main definitions

* `PCError.sinSqAngle u v`: the squared sine of the angle between the lines spanned by
  `u` and `v` in a real inner product space.
* `PCError.sinSqAngleSubspace u V`: the squared sine of the angle between `u` and a
  subspace `V` admitting an orthogonal projection.

## Main statements

* `PCError.sinSqAngle_eq_sin_angle_sq` identifies `sinSqAngle` with `sin` of Mathlib's
  unoriented `InnerProductGeometry.angle`, squared.
* `PCError.sinSqAngleSubspace_span_singleton` identifies the angle to a line with the
  angle between vectors, so the two definitions agree where both apply.
* `PCError.sinSqAngleSubspace_eq_zero_iff` and `PCError.sinSqAngle_eq_zero_iff` characterise
  a vanishing angle as membership in the subspace, respectively in the spanned line.

## Implementation notes

Both definitions are total: the division by a vanishing norm evaluates to `0`, so the
value at `u = 0` (or `v = 0`, or `V = ⊥`) is `1`. This is not merely harmless but
*correct*: Mathlib's `InnerProductGeometry.angle` is `π / 2` when an argument vanishes,
and `sinSqAngle_eq_sin_angle_sq` therefore holds with no nonvanishing hypothesis. Every
statement below that does carry `u ≠ 0` genuinely needs it.
-/

@[expose] public section

open InnerProductGeometry

open scoped RealInnerProductSpace

namespace PCError

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The angle between two lines -/

/-- The squared sine of the (acute) angle between the lines spanned by `u` and `v`,
namely `1 - ⟪u, v⟫ ^ 2 / (‖u‖ ^ 2 * ‖v‖ ^ 2)`.

It is `1` when either vector vanishes, matching `sin (angle u v) ^ 2`; see
`PCError.sinSqAngle_eq_sin_angle_sq`. -/
@[pcerror "def_sinsq"]
noncomputable def sinSqAngle (u v : E) : ℝ := 1 - ⟪u, v⟫ ^ 2 / (‖u‖ ^ 2 * ‖v‖ ^ 2)

/-- The defining formula for `sinSqAngle`, so that it can be used without unfolding the
definition. -/
theorem sinSqAngle_def (u v : E) :
    sinSqAngle u v = 1 - ⟪u, v⟫ ^ 2 / (‖u‖ ^ 2 * ‖v‖ ^ 2) :=
  rfl

/-- `sinSqAngle` is the squared sine of Mathlib's unoriented angle. Since
`sin (π - θ) = sin θ`, it is also the squared sine of the acute angle between the two
lines. -/
theorem sinSqAngle_eq_sin_angle_sq (u v : E) : sinSqAngle u v = Real.sin (angle u v) ^ 2 := by
  rw [sinSqAngle_def, Real.sin_sq, cos_angle, div_pow, mul_pow]

/-- The squared sine of the angle between two lines is symmetric in its arguments. -/
theorem sinSqAngle_comm (u v : E) : sinSqAngle u v = sinSqAngle v u := by
  simp [sinSqAngle_def, real_inner_comm u v, mul_comm]

/-- The squared sine of the angle between two lines is nonnegative. -/
theorem sinSqAngle_nonneg (u v : E) : 0 ≤ sinSqAngle u v := by
  rw [sinSqAngle_eq_sin_angle_sq]; positivity

/-- The squared sine of the angle between two lines is at most `1`. -/
theorem sinSqAngle_le_one (u v : E) : sinSqAngle u v ≤ 1 := by
  rw [sinSqAngle_eq_sin_angle_sq]
  exact Real.sin_sq_le_one _

/-- The squared sine of the angle between `0` and any vector is `1`. -/
@[simp]
theorem sinSqAngle_zero_left (v : E) : sinSqAngle 0 v = 1 := by simp [sinSqAngle_def]

/-- The squared sine of the angle between any vector and `0` is `1`. -/
@[simp]
theorem sinSqAngle_zero_right (u : E) : sinSqAngle u 0 = 1 := by simp [sinSqAngle_def]

/-- A nonzero vector makes a zero angle with itself. -/
@[simp]
theorem sinSqAngle_self {u : E} (hu : u ≠ 0) : sinSqAngle u u = 0 := by
  rw [sinSqAngle_eq_sin_angle_sq, angle_self hu]
  simp

/-- The angle is a right angle exactly when the vectors are orthogonal. -/
theorem sinSqAngle_eq_one_iff {u v : E} : sinSqAngle u v = 1 ↔ ⟪u, v⟫ = 0 := by
  rw [sinSqAngle_def, sub_eq_self, div_eq_zero_iff, pow_eq_zero_iff two_ne_zero, mul_eq_zero,
    pow_eq_zero_iff two_ne_zero, pow_eq_zero_iff two_ne_zero, norm_eq_zero, norm_eq_zero]
  refine ⟨?_, Or.inl⟩
  rintro (h | h | h) <;> simp [h]

/-- Rescaling the first argument by a nonzero scalar does not change the angle between
lines. -/
@[simp]
theorem sinSqAngle_smul_left {c : ℝ} (hc : c ≠ 0) (u v : E) :
    sinSqAngle (c • u) v = sinSqAngle u v := by
  have h : c ^ 2 * ⟪u, v⟫ ^ 2 / (c ^ 2 * ‖u‖ ^ 2 * ‖v‖ ^ 2)
      = ⟪u, v⟫ ^ 2 / (‖u‖ ^ 2 * ‖v‖ ^ 2) := by
    rw [mul_assoc, mul_div_mul_left _ _ (pow_ne_zero 2 hc)]
  simp only [sinSqAngle_def, real_inner_smul_left, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    h]

/-- Rescaling the second argument by a nonzero scalar does not change the angle between
lines. -/
@[simp]
theorem sinSqAngle_smul_right {c : ℝ} (hc : c ≠ 0) (u v : E) :
    sinSqAngle u (c • v) = sinSqAngle u v := by
  rw [sinSqAngle_comm, sinSqAngle_smul_left hc, sinSqAngle_comm]

/-- Negating the first argument does not change the angle between lines. -/
@[simp]
theorem sinSqAngle_neg_left (u v : E) : sinSqAngle (-u) v = sinSqAngle u v := by
  simp [sinSqAngle_def]

/-- Negating the second argument does not change the angle between lines. -/
@[simp]
theorem sinSqAngle_neg_right (u v : E) : sinSqAngle u (-v) = sinSqAngle u v := by
  simp [sinSqAngle_def]

/-! ### The angle from a vector to a subspace -/

/-- The squared sine of the angle from `u` to the subspace `V`, namely
`1 - ‖Π_V u‖ ^ 2 / ‖u‖ ^ 2` for `Π_V` the orthogonal projector onto `V`.

It is `1` when `u = 0` or `V = ⊥`; see `PCError.sinSqAngleSubspace_bot`. -/
@[pcerror "def_sinsq_sub"]
noncomputable def sinSqAngleSubspace (u : E) (V : Submodule ℝ E) [V.HasOrthogonalProjection] : ℝ :=
  1 - ‖V.starProjection u‖ ^ 2 / ‖u‖ ^ 2

/-- The defining formula for `sinSqAngleSubspace`, so that it can be used without
unfolding the definition. -/
theorem sinSqAngleSubspace_def (u : E) (V : Submodule ℝ E) [V.HasOrthogonalProjection] :
    sinSqAngleSubspace u V = 1 - ‖V.starProjection u‖ ^ 2 / ‖u‖ ^ 2 :=
  rfl

/-- For a nonzero `u`, the squared sine of the angle from `u` to `V` is the squared norm of
the orthogonal projection of `u` onto `Vᗮ`, divided by `‖u‖ ^ 2`. -/
theorem sinSqAngleSubspace_eq_norm_starProjection_orthogonal_sq_div {u : E} (hu : u ≠ 0)
    (V : Submodule ℝ E) [V.HasOrthogonalProjection] :
    sinSqAngleSubspace u V = ‖Vᗮ.starProjection u‖ ^ 2 / ‖u‖ ^ 2 := by
  have h := V.norm_sq_eq_add_norm_sq_starProjection u
  have h0 : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  rw [sinSqAngleSubspace_def]
  field_simp
  linarith

/-- The angle to `V` vanishes exactly on `V`. -/
theorem sinSqAngleSubspace_eq_zero_iff {u : E} (hu : u ≠ 0) (V : Submodule ℝ E)
    [V.HasOrthogonalProjection] : sinSqAngleSubspace u V = 0 ↔ u ∈ V := by
  rw [sinSqAngleSubspace_eq_norm_starProjection_orthogonal_sq_div hu V, div_eq_zero_iff,
    pow_eq_zero_iff two_ne_zero, pow_eq_zero_iff two_ne_zero, norm_eq_zero, norm_eq_zero,
    Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_orthogonal]
  simp [hu]

/-- The squared sine of the angle from a vector to a subspace is nonnegative. -/
theorem sinSqAngleSubspace_nonneg (u : E) (V : Submodule ℝ E) [V.HasOrthogonalProjection] :
    0 ≤ sinSqAngleSubspace u V := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp [sinSqAngleSubspace_def]
  · rw [sinSqAngleSubspace_eq_norm_starProjection_orthogonal_sq_div hu V]
    positivity

/-- The squared sine of the angle from a vector to a subspace is at most `1`. -/
theorem sinSqAngleSubspace_le_one (u : E) (V : Submodule ℝ E) [V.HasOrthogonalProjection] :
    sinSqAngleSubspace u V ≤ 1 := by
  rw [sinSqAngleSubspace_def]
  exact sub_le_self _ (by positivity)

/-- Rescaling by a nonzero scalar does not change the angle to a subspace. -/
@[simp]
theorem sinSqAngleSubspace_smul {c : ℝ} (hc : c ≠ 0) (u : E) (V : Submodule ℝ E)
    [V.HasOrthogonalProjection] : sinSqAngleSubspace (c • u) V = sinSqAngleSubspace u V := by
  have h : (|c| * ‖V.starProjection u‖) ^ 2 / (|c| * ‖u‖) ^ 2
      = ‖V.starProjection u‖ ^ 2 / ‖u‖ ^ 2 := by
    rw [mul_pow, mul_pow, mul_div_mul_left _ _ (pow_ne_zero 2 (abs_ne_zero.mpr hc))]
  rw [sinSqAngleSubspace_def, sinSqAngleSubspace_def, map_smul, norm_smul, norm_smul,
    Real.norm_eq_abs, h]

/-- The angle to a line is the angle to a spanning vector: the two definitions agree
wherever both apply. -/
@[simp]
theorem sinSqAngleSubspace_span_singleton (u v : E) :
    sinSqAngleSubspace u (ℝ ∙ v) = sinSqAngle u v := by
  have h : ‖(ℝ ∙ v).starProjection u‖ ^ 2 = ⟪u, v⟫ ^ 2 / ‖v‖ ^ 2 := by
    rw [Submodule.starProjection_singleton, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, div_pow,
      real_inner_comm v u]
    simp only [RCLike.ofReal_real_eq_id, id_eq]
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · field_simp
  rw [sinSqAngleSubspace_def, sinSqAngle_def, h, div_div, mul_comm (‖v‖ ^ 2)]

/-- A nonzero vector makes a zero angle with `v` exactly when it lies on the line spanned
by `v`. -/
theorem sinSqAngle_eq_zero_iff {u v : E} (hu : u ≠ 0) : sinSqAngle u v = 0 ↔ u ∈ ℝ ∙ v := by
  rw [← sinSqAngleSubspace_span_singleton, sinSqAngleSubspace_eq_zero_iff hu]

/-- The squared sine of the angle from any vector to the zero subspace is `1`. -/
@[simp]
theorem sinSqAngleSubspace_bot (u : E) : sinSqAngleSubspace u (⊥ : Submodule ℝ E) = 1 := by
  simp [sinSqAngleSubspace_def]

/-- A nonzero vector makes a zero angle with the whole space. -/
@[simp]
theorem sinSqAngleSubspace_top {u : E} (hu : u ≠ 0) :
    sinSqAngleSubspace u (⊤ : Submodule ℝ E) = 0 :=
  (sinSqAngleSubspace_eq_zero_iff hu ⊤).mpr Submodule.mem_top

end PCError
