/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import PCError.Attr
public import PCError.Defs.Angles

/-!
# Angles to a subspace, and the exact angular split

Two identities about `PCError.sinSqAngleSubspace`, both consequences of the orthogonal
decomposition `u = Π_V u + (I - Π_V) u`.

## Main statements

* `PCError.sinSqAngleSubspace_eq_norm_sub_starProjection_sq_of_norm_one`: for a unit
  vector `u`, the squared sine of the angle to `V` is the squared norm of the
  complementary projection, `‖(I - Π_V) u‖ ^ 2`.
* `PCError.sinSqAngle_eq_sinSqAngleSubspace_add_mul_sinSqAngle_starProjection`: for
  `w ∈ V`, the angle from `u` to `w` splits exactly into the angle from `u` to `V` and the
  angle from `Π_V u` to `w`,
  `sin²∠(u, w) = sin²∠(u, V) + (1 - sin²∠(u, V)) · sin²∠(Π_V u, w)`.

## Implementation notes

The split identity is stated with no hypothesis beyond `w ∈ V`: one might expect `u`
and `w` to be unit vectors with `Π_V u ≠ 0`, but both sides are invariant under rescaling
either vector, and the degenerate values `Π_V u = 0`, `u = 0` and `w = 0` come out right
under the junk-value conventions of the two definitions (both sides are then `1`). The
unit hypothesis is genuinely needed for the first statement, whose two sides have
different homogeneity degrees in `u`; the general form, with `‖u‖ ^ 2` restored in the
denominator, is `PCError.sinSqAngleSubspace_eq_norm_starProjection_orthogonal_sq_div`.
-/

@[expose] public section

open scoped RealInnerProductSpace

namespace PCError

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- For a unit vector `u`, the squared sine of the angle to `V` is the squared norm of the
complementary projection `(I - Π_V) u`. -/
@[pcerror "lem_sinsq_sub_perp"]
theorem sinSqAngleSubspace_eq_norm_sub_starProjection_sq_of_norm_one {u : E} (hu : ‖u‖ = 1)
    (V : Submodule ℝ E) [V.HasOrthogonalProjection] :
    sinSqAngleSubspace u V = ‖u - V.starProjection u‖ ^ 2 := by
  have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (by simp [hu])
  rw [sinSqAngleSubspace_eq_norm_starProjection_orthogonal_sq_div hu0 V,
    Submodule.starProjection_orthogonal_val, hu, one_pow, div_one]

/-- The exact angular split: for `w` in a subspace `V`, the angle from `u` to `w` is built
from the angle from `u` to `V` together with the angle from the projection `Π_V u` to `w`,
as `sin²∠(u, w) = sin²∠(u, V) + (1 - sin²∠(u, V)) · sin²∠(Π_V u, w)`.

Both sides are invariant under rescaling `u` or `w` by a nonzero scalar, so no
normalization is needed. -/
@[pcerror "lem_angle_split"]
theorem sinSqAngle_eq_sinSqAngleSubspace_add_mul_sinSqAngle_starProjection (u : E)
    (V : Submodule ℝ E) [V.HasOrthogonalProjection] {w : E} (hw : w ∈ V) :
    sinSqAngle u w = sinSqAngleSubspace u V +
      (1 - sinSqAngleSubspace u V) * sinSqAngle (V.starProjection u) w := by
  -- `(I - Π_V) u ∈ Vᗮ` and `w ∈ V`, so `⟪u, w⟫ = ⟪Π_V u, w⟫`.
  have key : ⟪V.starProjection u, w⟫ = ⟪u, w⟫ := by
    rw [Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr hw]
  rcases eq_or_ne (V.starProjection u) 0 with hp | hp
  · -- `Π_V u = 0`: the angle to `V` is a right angle and so is the angle to `w`.
    have hz : ⟪u, w⟫ = 0 := by rw [← key, hp, inner_zero_left]
    simp [sinSqAngle_def, sinSqAngleSubspace_def, hp, hz]
  · rcases eq_or_ne w 0 with rfl | hw0
    · simp
    have hnp : ‖V.starProjection u‖ ≠ 0 := norm_ne_zero_iff.mpr hp
    have hnu : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr fun h => hp (by rw [h, map_zero])
    have hnw : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
    simp only [sinSqAngle_def, sinSqAngleSubspace_def, ← key]
    field_simp
    ring

end PCError
