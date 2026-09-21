/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import PCError.Attr
public import PCError.ErrorInTheEstimatedPrincipalDirections

/-!
# The out-of-subspace error is estimable

The out-of-subspace error `sin²∠(h_j, 𝓑)` of the `j`-th sample principal direction is not
observable, but its limit `δ²/(nλⱼ+δ²)` is: it is the limit of the ratio `ℓ⁽ᵖ⁾/θ⁽ᵖ⁾ⱼ` of two
eigenvalue statistics of the observable dual Gram matrix `W⁽ᵖ⁾`, which is therefore a consistent
estimator of it.  Since the total error of `h_j` splits as an out-of-subspace part plus an
in-subspace rotation, that observable limit is also a *floor* for the total error, attained
exactly when the rotation vanishes.

The last two statements aggregate the `k` directions into one: the Frobenius distance between the
sample projector `Π_H = H⁽ᵖ⁾(H⁽ᵖ⁾)ᵀ` and the systematic projector `Π = b⁽ᵖ⁾(b⁽ᵖ⁾)ᵀ` measures the
total out-of-subspace error of the whole frame, and its limit is the sum of the individual ones.

## Main statements

* `PCError.frobenius_norm_frameProj_sub_sq_div_two`: *the Frobenius identity for two orthonormal
  frames* — `½‖Π_H - Π‖_F² = ∑ⱼ‖(I - Π)h_j‖²`.
* `PCError.FactorModelSeq.ae_tendsto_avgBulkEigenvalue_div_dualEigenvalues`: *a data-driven
  estimate of out-of-subspace error* — `ℓ⁽ᵖ⁾/θ⁽ᵖ⁾ⱼ → δ²/(nλⱼ+δ²)`.
* `PCError.FactorModelSeq.ae_limUnder_avgBulkEigenvalue_div_le_limUnder_sinSqAngle` and
  `PCError.FactorModelSeq.ae_limUnder_avgBulkEigenvalue_div_eq_limUnder_sinSqAngle_iff`: *the
  estimate is a floor for the total error* — `lim ℓ⁽ᵖ⁾/θ⁽ᵖ⁾ⱼ ≤ lim sin²∠(h_j, b⁽ᵖ⁾ⱼ)`, with
  equality exactly when `sin²∠(νⱼ, eⱼ) = 0`.
* `PCError.FactorModelSeq.ae_tendsto_frobenius_norm_frameProj_sub_sq_div_two`: *the aggregate
  out-of-subspace error* — `½‖Π_H - Π‖_F² → ∑ⱼ δ²/(nλⱼ+δ²)`.

## Implementation notes

The Frobenius norm is not the default norm on `Matrix`, so
`Matrix.frobeniusNormedAddCommGroup` is installed as a local instance exactly as in
`PCError.TheObservableDualGramMatrixInTheLimit`.  Half the squared distance is written
`‖Π_H - Π‖ ^ 2 / 2`, and the complementary projections `(I - Π)h_j` of the right-hand side as
`h_j - Π h_j` in `EuclideanSpace`, which is the shape
`PCError.sinSqAngleSubspace_eq_norm_sub_starProjection_sq_of_norm_one` consumes; the identity
itself is proved for an arbitrary pair of frames with orthonormal columns, the model playing
no part in it.

Both limits of the floor statement provably exist, so they are written with `limUnder`
rather than the statement being phrased in terms of two given limits.
The equality case is a separate declaration, so that the inequality can be used without it.

The frame `H⁽ᵖ⁾ = [h₁ ⋯ h_k]` of the aggregate statement is a *hypothesis*: that the `k` sample
principal directions can be collected into a frame with orthonormal columns is assumed,
not derived here, and the statement quantifies over every
frame whose columns are the chosen directions.  Both conditions are imposed only for large `p`,
as everywhere else in this development.
-/

@[expose] public section

namespace PCError

universe u

open Filter Matrix MeasureTheory
open scoped Topology RealInnerProductSpace

/-! ### The Frobenius identity for two orthonormal frames -/

section Frobenius

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

/-- The squared Frobenius norm of a real matrix is the sum of the squares of its entries. -/
private theorem frobenius_norm_sq_eq_sum_sq {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : ‖A‖ ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
  rw [Matrix.frobenius_norm_def, ← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]
  norm_num

/-- The squared Frobenius norm of a real matrix is the trace of its Gram matrix `Aᵀ A`. -/
private theorem frobenius_norm_sq_eq_trace {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : ‖A‖ ^ 2 = (Aᵀ * A).trace := by
  rw [frobenius_norm_sq_eq_sum_sq, Matrix.trace, Finset.sum_comm]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => sq _

variable {m k : Type*} [Fintype m] [Fintype k]

/-- A real orthogonal projector is a symmetric matrix. -/
private theorem transpose_eq_of_isStarProjection {Q : Matrix m m ℝ} (hQ : IsStarProjection Q) :
    Qᵀ = Q :=
  (Matrix.isHermitian_iff_isSelfAdjoint.mpr hQ.isSelfAdjoint).isSymm

/-- The squared norm of the image of a vector under an orthogonal projector is the dot
product of the vector with its image. -/
theorem norm_toEuclideanLin_sq_eq_dotProduct_of_isStarProjection [DecidableEq m]
    {Q : Matrix m m ℝ} (hQ : IsStarProjection Q) (x : m → ℝ) :
    ‖Matrix.toEuclideanLin Q (WithLp.toLp 2 x : EuclideanSpace ℝ m)‖ ^ 2 = x ⬝ᵥ (Q *ᵥ x) := by
  have hQs : Qᵀ = Q := transpose_eq_of_isStarProjection hQ
  rw [← dotProduct_self_eq_norm_sq]
  change (Q *ᵥ x) ⬝ᵥ (Q *ᵥ x) = _
  rw [← dotProduct_mulVec_eq_mulVec_dotProduct hQs, Matrix.mulVec_mulVec, hQ.isIdempotentElem.eq]

/-- The squared Frobenius distance between two orthogonal projectors, expanded in traces. -/
private theorem frobenius_norm_sub_sq_eq_trace_sub {P Q : Matrix m m ℝ} (hP : IsStarProjection P)
    (hQ : IsStarProjection Q) : ‖P - Q‖ ^ 2 = P.trace + Q.trace - 2 * (P * Q).trace := by
  have hPs : Pᵀ = P := transpose_eq_of_isStarProjection hP
  have hQs : Qᵀ = Q := transpose_eq_of_isStarProjection hQ
  rw [frobenius_norm_sq_eq_trace, Matrix.transpose_sub, hPs, hQs, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.mul_sub, trace_sub, trace_sub, trace_sub, hP.isIdempotentElem.eq,
    hQ.isIdempotentElem.eq, trace_mul_comm Q P]
  ring

/-- The trace of `Π_H Q` for a frame `H` is the sum over the columns `h_j` of `H` of the dot
products `h_j ⬝ᵥ Q h_j`. -/
theorem trace_frameProj_mul {R : Type*} [CommSemiring R] [StarRing R] [TrivialStar R]
    (H : Matrix m k R) (Q : Matrix m m R) :
    (frameProj H * Q).trace = ∑ j, Hᵀ j ⬝ᵥ (Q *ᵥ Hᵀ j) := by
  rw [frameProj_eq_mul_transpose H, Matrix.mul_assoc, trace_mul_comm, Matrix.trace]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.diag_apply, Matrix.mul_apply, dotProduct, Matrix.mulVec,
    Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => by ring

/-- **Frobenius identity for two orthonormal frames**: for frames `H` and `b` with orthonormal
columns, half the squared Frobenius distance between the projectors `Π_H = HHᵀ` and `Π = bbᵀ`
is the sum over the columns `h_j` of `H` of the squared norms of the complementary projections
`(I - Π)h_j`. -/
@[pcerror "lem_frobenius_identity"]
theorem frobenius_norm_frameProj_sub_sq_div_two [DecidableEq m] [DecidableEq k]
    {H b : Matrix m k ℝ} (hH : Hᵀ * H = 1) (hb : bᵀ * b = 1) :
    ‖frameProj H - frameProj b‖ ^ 2 / 2
      = ∑ j, ‖(WithLp.toLp 2 (Hᵀ j) : EuclideanSpace ℝ m)
          - Matrix.toEuclideanLin (frameProj b) (WithLp.toLp 2 (Hᵀ j))‖ ^ 2 := by
  have hH' : Hᴴ * H = 1 := by rwa [conjTranspose_eq_transpose_of_trivial]
  have hb' : bᴴ * b = 1 := by rwa [conjTranspose_eq_transpose_of_trivial]
  have hQ : IsStarProjection (frameProj b) := isStarProjection_frameProj hb'
  -- each column of `H` is a unit vector
  have hnorm : ∀ j, ‖(WithLp.toLp 2 (Hᵀ j) : EuclideanSpace ℝ m)‖ ^ 2 = 1 := fun j => by
    rw [← dotProduct_self_eq_norm_sq]
    have h := congrFun (congrFun hH j) j
    rw [Matrix.one_apply_eq, Matrix.mul_apply] at h
    simpa [dotProduct] using h
  have hterm : ∀ j, ‖(WithLp.toLp 2 (Hᵀ j) : EuclideanSpace ℝ m)
      - Matrix.toEuclideanLin (frameProj b) (WithLp.toLp 2 (Hᵀ j))‖ ^ 2
      = 1 - Hᵀ j ⬝ᵥ (frameProj b *ᵥ Hᵀ j) := fun j => by
    have hinner : ⟪(WithLp.toLp 2 (Hᵀ j) : EuclideanSpace ℝ m),
        Matrix.toEuclideanLin (frameProj b) (WithLp.toLp 2 (Hᵀ j))⟫
        = Hᵀ j ⬝ᵥ (frameProj b *ᵥ Hᵀ j) := inner_eq_dotProduct _ _
    rw [norm_sub_sq_real, hinner, hnorm j,
      norm_toEuclideanLin_sq_eq_dotProduct_of_isStarProjection hQ]
    ring
  rw [frobenius_norm_sub_sq_eq_trace_sub (isStarProjection_frameProj hH') hQ,
    trace_frameProj_eq_card hH', trace_frameProj_eq_card hb',
    trace_frameProj_mul H (frameProj b),
    Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one]
  ring

end Frobenius

namespace FactorModelSeq

variable {Ω : Type u} (M : FactorModelSeq Ω) [MeasurableSpace Ω] {μ : Measure Ω}
  {G : Matrix (Fin M.k) (Fin M.k) ℝ} {lam : Fin M.k → ℝ}

/-! ### A data-driven estimate of the out-of-subspace error -/

/-- **A data-driven estimate of out-of-subspace error**: almost surely
`ℓ⁽ᵖ⁾/θ⁽ᵖ⁾ⱼ → δ²/(nλⱼ+δ²)`, the out-of-subspace error of the `j`-th sample principal direction.

The average bulk eigenvalue tends to `δ²/n` and `θ⁽ᵖ⁾ⱼ` to the strictly positive
`λⱼ + δ²/n`, so the quotient tends to `(δ²/n)/(λⱼ + δ²/n) = δ²/(nλⱼ+δ²)`. -/
@[pcerror "thm_oos_estimable"]
theorem ae_tendsto_avgBulkEigenvalue_div_dualEigenvalues (hslln : KolmogorovSLLN.{u})
    (hweyl : WeylPerturbation.{0}) (hyp : StandingHypotheses μ M G lam) (j : Fin M.k) :
    ∀ᵐ ω ∂μ, Tendsto (fun p : ℕ => M.avgBulkEigenvalue p ω /
        M.dualEigenvalues p ω (Fin.castLE M.k_lt_n.le j)) atTop
      (𝓝 (M.δsq / ((M.n : ℝ) * lam j + M.δsq))) := by
  have hnR : (0 : ℝ) < M.n := by exact_mod_cast M.n_pos
  have hne : lam j + M.δsq / M.n ≠ 0 := (M.lam_add_div_pos hyp.toAsymptoticHypotheses j).ne'
  have he : M.δsq / M.n / (lam j + M.δsq / M.n) = M.δsq / ((M.n : ℝ) * lam j + M.δsq) := by
    rw [show lam j + M.δsq / M.n = ((M.n : ℝ) * lam j + M.δsq) / M.n by field_simp,
      div_div_div_cancel_right₀ (hc := hnR.ne')]
  filter_upwards [M.ae_tendsto_avgBulkEigenvalue hslln hweyl hyp,
    M.ae_tendsto_dualEigenvalues hslln hweyl hyp j] with ω hbulk hθ
  rw [← he]
  exact hbulk.div hθ hne

/-! ### The estimate is a floor for the total error -/

section Floor

variable (hslln : KolmogorovSLLN.{u}) (hweyl : WeylPerturbation.{0})
  (hyp : StandingHypotheses μ M G lam) (j : Fin M.k)
  {w : EuclideanSpace ℝ (Fin M.n)}
  (hw1 : ‖w‖ = 1) (hw : M.dualGramLim₀ G *ᵥ w = lam j • w) {ν : EuclideanSpace ℝ (Fin M.k)}
  (hν : M.scaledScoresLim *ᵥ w = Real.sqrt ((M.n : ℝ) * lam j) • ν)

include hslln hweyl hyp hw1 hw hν

/-- **The estimate is a floor for the total error**: the limit `δ²/(nλⱼ+δ²)` of the observable
ratio `ℓ⁽ᵖ⁾/θ⁽ᵖ⁾ⱼ` is at most the limit of the total error `sin²∠(h_j, b⁽ᵖ⁾ⱼ)`.

Both limits exist, and their difference is `nλⱼ/(nλⱼ+δ²) sin²∠(νⱼ, eⱼ)`, a product of a
positive number and a squared sine. -/
@[pcerror "thm_error_floor"]
theorem ae_limUnder_avgBulkEigenvalue_div_le_limUnder_sinSqAngle :
    ∀ᵐ ω ∂μ, ∀ s : M.PrincipalDirectionSeq j ω,
      limUnder atTop (fun p => M.avgBulkEigenvalue p ω /
          M.dualEigenvalues p ω (Fin.castLE M.k_lt_n.le j))
        ≤ limUnder atTop (fun p => sinSqAngle (s.sample p) (M.principalDirection p j)) := by
  have hlam : 0 < lam j := hyp.hasPosEigenvalues_dualGramLim₀.pos j
  have hδ := M.δsq_pos
  filter_upwards [M.ae_tendsto_avgBulkEigenvalue_div_dualEigenvalues hslln hweyl hyp j,
    M.ae_tendsto_sinSqAngle_principalDirection hslln hweyl hyp j hw1 hw hν]
    with ω hq hsin s
  rw [hq.limUnder_eq, (hsin s).limUnder_eq]
  exact le_add_of_nonneg_right (mul_nonneg (by positivity) (sinSqAngle_nonneg _ _))

/-- **The estimate is a floor for the total error**, the case of equality: the observable limit
`δ²/(nλⱼ+δ²)` is the whole of the total error exactly when the in-subspace rotation vanishes,
`sin²∠(νⱼ, eⱼ) = 0`, because the coefficient `nλⱼ/(nλⱼ+δ²)` of the difference is nonzero. -/
@[pcerror "thm_error_floor"]
theorem ae_limUnder_avgBulkEigenvalue_div_eq_limUnder_sinSqAngle_iff :
    ∀ᵐ ω ∂μ, ∀ s : M.PrincipalDirectionSeq j ω,
      (limUnder atTop (fun p => M.avgBulkEigenvalue p ω /
          M.dualEigenvalues p ω (Fin.castLE M.k_lt_n.le j))
        = limUnder atTop (fun p => sinSqAngle (s.sample p) (M.principalDirection p j))
        ↔ sinSqAngle ν (EuclideanSpace.single j (1 : ℝ)) = 0) := by
  have hlam : 0 < lam j := hyp.hasPosEigenvalues_dualGramLim₀.pos j
  filter_upwards [M.ae_tendsto_avgBulkEigenvalue_div_dualEigenvalues hslln hweyl hyp j,
    M.ae_tendsto_sinSqAngle_principalDirection hslln hweyl hyp j hw1 hw hν]
    with ω hq hsin s
  rw [hq.limUnder_eq, (hsin s).limUnder_eq]
  have hcoef : (0 : ℝ) < (M.n : ℝ) * lam j / ((M.n : ℝ) * lam j + M.δsq) :=
    div_pos (mul_pos (by exact_mod_cast M.n_pos) hlam) (M.n_mul_add_δsq_pos hlam)
  refine ⟨fun h => ?_, fun h => by rw [h, mul_zero, add_zero]⟩
  have hzero : (M.n : ℝ) * lam j / ((M.n : ℝ) * lam j + M.δsq) *
      sinSqAngle ν (EuclideanSpace.single j (1 : ℝ)) = 0 := by linarith
  exact (mul_eq_zero.mp hzero).resolve_left hcoef.ne'

end Floor

/-! ### The aggregate out-of-subspace error -/

section Aggregate

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable (hslln : KolmogorovSLLN.{u}) (hweyl : WeylPerturbation.{0})
  (hyp : StandingHypotheses μ M G lam)
  {w : Fin M.k → EuclideanSpace ℝ (Fin M.n)}
  (hw1 : ∀ j, ‖w j‖ = 1) (hw : ∀ j, M.dualGramLim₀ G *ᵥ w j = lam j • w j)
  {ν : Fin M.k → EuclideanSpace ℝ (Fin M.k)}
  (hν : ∀ j, M.scaledScoresLim *ᵥ w j = Real.sqrt ((M.n : ℝ) * lam j) • ν j)

include hslln hweyl hyp hw1 hw hν

/-- **Aggregate out-of-subspace error**: almost surely
`½‖Π_H - Π‖_F² → ∑ⱼ δ²/(nλⱼ+δ²)` for any frames `H⁽ᵖ⁾` with orthonormal columns collecting the
sample principal directions `h_j`.

The Frobenius identity turns the left-hand side into `∑ⱼ‖(I - Π)h_j‖²`, each summand of which is
the out-of-subspace error `sin²∠(h_j, 𝓑)` of a unit vector, and the sum of the finitely many
limits is the limit of the sum. -/
@[pcerror "thm_aggregate_oos"]
theorem ae_tendsto_frobenius_norm_frameProj_sub_sq_div_two :
    ∀ᵐ ω ∂μ, ∀ (s : ∀ j, M.PrincipalDirectionSeq j ω) (H : ∀ p : ℕ, Matrix (Fin p) (Fin M.k) ℝ),
      (∀ᶠ p in atTop, (H p)ᵀ * H p = 1) →
      (∀ᶠ p in atTop, ∀ j, WithLp.toLp 2 ((H p)ᵀ j) = (s j).sample p) →
      Tendsto (fun p => ‖frameProj (H p) - frameProj (M.b p)‖ ^ 2 / 2) atTop
        (𝓝 (∑ j, M.δsq / ((M.n : ℝ) * lam j + M.δsq))) := by
  have hoos : ∀ᵐ ω ∂μ, ∀ (j : Fin M.k) (s : M.PrincipalDirectionSeq j ω),
      Tendsto (fun p => sinSqAngleSubspace (s.sample p) (M.principalSubspace p)) atTop
        (𝓝 (M.δsq / ((M.n : ℝ) * lam j + M.δsq))) :=
    ae_all_iff.mpr fun j =>
      M.ae_tendsto_sinSqAngleSubspace hslln hweyl hyp j (hw1 j) (hw j) (hν j)
  have hunit : ∀ᵐ ω ∂μ, ∀ (j : Fin M.k) (s : M.PrincipalDirectionSeq j ω),
      ∀ᶠ p in atTop, ‖s.sample p‖ = 1 :=
    ae_all_iff.mpr (M.ae_eventually_norm_sample_eq_one hslln hweyl hyp)
  filter_upwards [hoos, hunit] with ω hoos hunit s H hHorth hcol
  have hsum : Tendsto (fun p => ∑ j, sinSqAngleSubspace ((s j).sample p) (M.principalSubspace p))
      atTop (𝓝 (∑ j, M.δsq / ((M.n : ℝ) * lam j + M.δsq))) :=
    tendsto_finsetSum _ fun j _ => hoos j (s j)
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop M.k, hHorth, hcol,
    eventually_all.mpr fun j => hunit j (s j)] with p hp hHp hcolp hnp
  rw [frobenius_norm_frameProj_sub_sq_div_two hHp (M.transpose_b_mul_b p hp)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hcolp j, ← M.starProjection_principalSubspace_eq_frameProj hp,
    sinSqAngleSubspace_eq_norm_sub_starProjection_sq_of_norm_one (hnp j)]

end Aggregate

end FactorModelSeq

end PCError

end
