/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import PCError.ErrorInTheEstimatedPrincipalDirections
public import PCError.TheOutOfSubspaceErrorIsEstimable
public import PCError.TheRotationErrorIsNotEstimable

/-! # Satisfying the formal challenge -/

@[expose] public section

universe u

open Filter Matrix MeasureTheory ProbabilityTheory

open scoped Topology MatrixOrder RealInnerProductSpace

namespace PCError

namespace Challenge

/-- **`thm_error_decomp` — Theorem 1, error decomposition.** Almost surely: the squared sine of
the angle between the `j`-th sample principal direction `h_j` and its target `b⁽ᵖ⁾ⱼ` converges
to `δ²/(nλⱼ+δ²) + nλⱼ/(nλⱼ+δ²)·sin²∠(νⱼ, eⱼ)` (17); the out-of-subspace error
`sin²∠(h_j, 𝓑⁽ᵖ⁾)` and the in-subspace mass converge to the two coefficients (18); the
in-subspace part of `h_j` is eventually nonzero; and its angle to `b⁽ᵖ⁾ⱼ` converges to
`sin²∠(νⱼ, eⱼ)` (19). -/
theorem thm_error_decomp {Ω : Type u} (M : FactorModelSeq Ω) [MeasurableSpace Ω]
    {μ : Measure Ω} {G : Matrix (Fin M.k) (Fin M.k) ℝ} {lam : Fin M.k → ℝ}
    (hslln : KolmogorovSLLN.{u}) (hweyl : WeylPerturbation.{0})
    (heigcont : EigenpairContinuity.{0}) (hyp : StandingHypotheses μ M G lam) (j : Fin M.k)
    {w : EuclideanSpace ℝ (Fin M.n)} (hw1 : ‖w‖ = 1)
    (hw : M.dualGramLim₀ G *ᵥ w = lam j • w) {ν : EuclideanSpace ℝ (Fin M.k)}
    (hν : M.scaledScoresLim *ᵥ w = Real.sqrt ((M.n : ℝ) * lam j) • ν) :
    (∀ᵐ ω ∂μ, ∀ s : M.PrincipalDirectionSeq j ω,
        Tendsto (fun p => sinSqAngle (s.sample p) (M.principalDirection p j)) atTop
          (𝓝 (M.δsq / ((M.n : ℝ) * lam j + M.δsq)
            + (M.n : ℝ) * lam j / ((M.n : ℝ) * lam j + M.δsq)
              * sinSqAngle ν (EuclideanSpace.single j (1 : ℝ))))) ∧
    (∀ᵐ ω ∂μ, ∀ s : M.PrincipalDirectionSeq j ω,
        Tendsto (fun p => sinSqAngleSubspace (s.sample p) (M.principalSubspace p)) atTop
          (𝓝 (M.δsq / ((M.n : ℝ) * lam j + M.δsq)))) ∧
    (∀ᵐ ω ∂μ, ∀ s : M.PrincipalDirectionSeq j ω,
        Tendsto (fun p => 1 - sinSqAngleSubspace (s.sample p) (M.principalSubspace p)) atTop
          (𝓝 ((M.n : ℝ) * lam j / ((M.n : ℝ) * lam j + M.δsq)))) ∧
    (∀ᵐ ω ∂μ, ∀ s : M.PrincipalDirectionSeq j ω,
        ∀ᶠ p in atTop, (M.principalSubspace p).starProjection (s.sample p) ≠ 0) ∧
    (∀ᵐ ω ∂μ, ∀ s : M.PrincipalDirectionSeq j ω,
        Tendsto (fun p => sinSqAngle ((M.principalSubspace p).starProjection (s.sample p))
          (M.principalDirection p j)) atTop
          (𝓝 (sinSqAngle ν (EuclideanSpace.single j (1 : ℝ))))) :=
  ⟨M.ae_tendsto_sinSqAngle_principalDirection hslln hweyl heigcont hyp j hw1 hw hν,
   M.ae_tendsto_sinSqAngleSubspace hslln hweyl heigcont hyp j hw1 hw hν,
   M.ae_tendsto_one_sub_sinSqAngleSubspace hslln hweyl heigcont hyp j hw1 hw hν,
   M.ae_eventually_starProjection_ne_zero hslln hweyl heigcont hyp j hw1 hw hν,
   M.ae_tendsto_sinSqAngle_starProjection hslln hweyl heigcont hyp j hw1 hw hν⟩

/-- **`thm_oos_estimable` — Theorem 2, the observable estimate (38).** Almost surely the
observable ratio `ℓ⁽ᵖ⁾/θ⁽ᵖ⁾ⱼ` of the average bulk eigenvalue to the `j`-th eigenvalue of the
dual Gram matrix converges to `δ²/(nλⱼ+δ²)`, which by `thm_error_decomp` is the limit of the
out-of-subspace error.  It needs neither eigenvector continuity nor a choice of `νⱼ`. -/
theorem thm_oos_estimable {Ω : Type u} (M : FactorModelSeq Ω) [MeasurableSpace Ω]
    {μ : Measure Ω} {G : Matrix (Fin M.k) (Fin M.k) ℝ} {lam : Fin M.k → ℝ}
    (hslln : KolmogorovSLLN.{u}) (hweyl : WeylPerturbation.{0})
    (hyp : StandingHypotheses μ M G lam) (j : Fin M.k) :
    ∀ᵐ ω ∂μ, Tendsto (fun p : ℕ => M.avgBulkEigenvalue p ω /
        M.dualEigenvalues p ω (Fin.castLE M.k_lt_n.le j)) atTop
      (𝓝 (M.δsq / ((M.n : ℝ) * lam j + M.δsq))) :=
  M.ae_tendsto_avgBulkEigenvalue_div_dualEigenvalues hslln hweyl hyp j

/-- **`thm_error_floor` — Theorem 2, the floor (39).** Almost surely the observable limit is at
most the limit of the total error, with equality exactly when the in-subspace rotation
`sin²∠(νⱼ, eⱼ)` vanishes. -/
theorem thm_error_floor {Ω : Type u} (M : FactorModelSeq Ω) [MeasurableSpace Ω]
    {μ : Measure Ω} {G : Matrix (Fin M.k) (Fin M.k) ℝ} {lam : Fin M.k → ℝ}
    (hslln : KolmogorovSLLN.{u}) (hweyl : WeylPerturbation.{0})
    (heigcont : EigenpairContinuity.{0}) (hyp : StandingHypotheses μ M G lam) (j : Fin M.k)
    {w : EuclideanSpace ℝ (Fin M.n)} (hw1 : ‖w‖ = 1)
    (hw : M.dualGramLim₀ G *ᵥ w = lam j • w) {ν : EuclideanSpace ℝ (Fin M.k)}
    (hν : M.scaledScoresLim *ᵥ w = Real.sqrt ((M.n : ℝ) * lam j) • ν) :
    (∀ᵐ ω ∂μ, ∀ s : M.PrincipalDirectionSeq j ω,
        limUnder atTop (fun p => M.avgBulkEigenvalue p ω /
            M.dualEigenvalues p ω (Fin.castLE M.k_lt_n.le j))
          ≤ limUnder atTop (fun p => sinSqAngle (s.sample p) (M.principalDirection p j))) ∧
    (∀ᵐ ω ∂μ, ∀ s : M.PrincipalDirectionSeq j ω,
        (limUnder atTop (fun p => M.avgBulkEigenvalue p ω /
            M.dualEigenvalues p ω (Fin.castLE M.k_lt_n.le j))
          = limUnder atTop (fun p => sinSqAngle (s.sample p) (M.principalDirection p j))
          ↔ sinSqAngle ν (EuclideanSpace.single j (1 : ℝ)) = 0)) :=
  ⟨M.ae_limUnder_avgBulkEigenvalue_div_le_limUnder_sinSqAngle
      hslln hweyl heigcont hyp j hw1 hw hν,
   M.ae_limUnder_avgBulkEigenvalue_div_eq_limUnder_sinSqAngle_iff
      hslln hweyl heigcont hyp j hw1 hw hν⟩

/-- **`thm_data_invariant` — Theorem 3(i), the data carry no factor covariance.** The data
matrix is `Y⁽ᵖ⁾ = B⁽ᵖ⁾F + Z⁽ᵖ⁾`, the systematic eigenvalue listing of `W₀` is unique, and the
out-of-subspace limit is determined by it — three expressions in which no candidate factor
covariance occurs. -/
theorem thm_data_invariant {Ω : Type u} (M : FactorModelSeq Ω) :
    (∀ p : ℕ, M.k ≤ p → ∀ ω : Ω,
        M.dataMatrix p ω = M.B p * M.F + M.noiseMatrix p ω) ∧
    (∀ (G : Matrix (Fin M.k) (Fin M.k) ℝ) (lam lam' : Fin M.k → ℝ),
        HasPosEigenvalues (M.dualGramLim₀ G) lam →
        HasPosEigenvalues (M.dualGramLim₀ G) lam' → lam = lam') ∧
    (∀ (G : Matrix (Fin M.k) (Fin M.k) ℝ) (lam lam' : Fin M.k → ℝ),
        HasPosEigenvalues (M.dualGramLim₀ G) lam →
        HasPosEigenvalues (M.dualGramLim₀ G) lam' → ∀ j : Fin M.k,
        M.δsq / ((M.n : ℝ) * lam j + M.δsq)
          = M.δsq / ((M.n : ℝ) * lam' j + M.δsq)) :=
  ⟨fun _ hp ω => M.dataMatrix_eq_B_mul_F_add_noiseMatrix hp ω,
   fun _ _ _ h h' => M.eq_of_hasPosEigenvalues_dualGramLim₀ h h',
   fun _ _ _ h h' j => M.δsq_div_eq_of_hasPosEigenvalues_dualGramLim₀ h h' j⟩

/-- **`thm_rotation_surjective` — Theorem 3(ii), the rotation error attains every value.** For
`k ≥ 2` and every `t ∈ [0,1]` there is an admissible factor covariance `Σ` whose systematic
dual has a unit eigenvector `ν` at `λⱼ` with `sin²∠(ν, eⱼ) = t`. -/
theorem thm_rotation_surjective {Ω : Type u} (M : FactorModelSeq Ω) (hk : 2 ≤ M.k)
    {G : Matrix (Fin M.k) (Fin M.k) ℝ} (hG : G.PosDef) {mu : Fin M.k → ℝ}
    (hmu : ∀ i, 0 < mu i) {lam : Fin M.k → ℝ}
    (hlam : HasPosEigenvalues (M.dualGramLim₀ G) lam) (j : Fin M.k) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ S, Admissible G mu S ∧ ∃ V ∈ Matrix.orthogonalGroup (Fin M.k) ℝ,
      Vᵀ * popDual G S * V = Matrix.diagonal mu ∧
      ∃ ν : EuclideanSpace ℝ (Fin M.k), ‖ν‖ = 1 ∧
        systematicDual mu M.F S V *ᵥ ν = lam j • ν ∧
        sinSqAngle ν (EuclideanSpace.single j (1 : ℝ)) = t :=
  M.exists_admissible_sinSqAngle_eq hk hG hmu hlam j ht0 ht1

/-- **`thm_error_range` — Theorem 3(iii), the total error attains every value above the
floor.** For `k ≥ 2` and every `s` between `δ²/(nλⱼ+δ²)` and `1` there is an admissible factor
covariance `Σ` whose limiting estimation error is exactly `s`. -/
theorem thm_error_range {Ω : Type u} (M : FactorModelSeq Ω) (hk : 2 ≤ M.k)
    {G : Matrix (Fin M.k) (Fin M.k) ℝ} (hG : G.PosDef) {mu : Fin M.k → ℝ}
    (hmu : ∀ i, 0 < mu i) {lam : Fin M.k → ℝ}
    (hlam : HasPosEigenvalues (M.dualGramLim₀ G) lam) (j : Fin M.k) {s : ℝ}
    (hs0 : M.δsq / ((M.n : ℝ) * lam j + M.δsq) ≤ s) (hs1 : s ≤ 1) :
    ∃ S, Admissible G mu S ∧ ∃ V ∈ Matrix.orthogonalGroup (Fin M.k) ℝ,
      Vᵀ * popDual G S * V = Matrix.diagonal mu ∧
      ∃ ν : EuclideanSpace ℝ (Fin M.k), ‖ν‖ = 1 ∧
        systematicDual mu M.F S V *ᵥ ν = lam j • ν ∧
        M.δsq / ((M.n : ℝ) * lam j + M.δsq)
          + (M.n : ℝ) * lam j / ((M.n : ℝ) * lam j + M.δsq)
            * sinSqAngle ν (EuclideanSpace.single j (1 : ℝ)) = s :=
  M.exists_admissible_errorLimit_eq hk hG hmu hlam j hs0 hs1

end Challenge

end PCError
