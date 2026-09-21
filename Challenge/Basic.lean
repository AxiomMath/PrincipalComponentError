/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Probability.Moments.Variance

/-! # The formal challenge file, written by humans

This is a human-written file certifying the formal statements that this repository proves,
on the asymptotic error of the sample principal directions in a latent factor model.

-/

@[expose] public section

universe u

open Filter Matrix MeasureTheory ProbabilityTheory

open scoped Topology MatrixOrder RealInnerProductSpace

namespace PCError

/-! ## Angles between lines -/

/-- The squared sine of the angle between the lines spanned by `u` and `v`, namely
`1 - ⟪u, v⟫ ^ 2 / (‖u‖ ^ 2 * ‖v‖ ^ 2)`.  It is `1` when either vector vanishes. -/
noncomputable def sinSqAngle {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) : ℝ :=
  1 - ⟪u, v⟫ ^ 2 / (‖u‖ ^ 2 * ‖v‖ ^ 2)

/-- The squared sine of the angle between `u` and the subspace `V`, namely
`1 - ‖Π_V u‖ ^ 2 / ‖u‖ ^ 2` for `Π_V` the orthogonal projector onto `V`.  It is `1` when
`u = 0` or `V = ⊥`. -/
noncomputable def sinSqAngleSubspace {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u : E) (V : Submodule ℝ E) [V.HasOrthogonalProjection] : ℝ :=
  1 - ‖V.starProjection u‖ ^ 2 / ‖u‖ ^ 2

/-! ## The factor model and its derived matrices -/

/-- `HasPosEigenvalues A c` says that the positive part of the spectrum of `A` is exactly the
set of values of the strictly decreasing positive family `c`. -/
structure HasPosEigenvalues {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m ℝ) {ι : Type*} [LinearOrder ι] (c : ι → ℝ) : Prop where
  /-- The eigenvalues are listed in strictly decreasing order. -/
  strictAnti : StrictAnti c
  /-- The listed eigenvalues are positive. -/
  pos : ∀ j, 0 < c j
  /-- The listed values exhaust the positive part of the spectrum. -/
  spectrum_pos_eq : {x ∈ spectrum ℝ A | 0 < x} = Set.range c

/-- A *principal-coordinate factor model sequence*: the latent factor model `y = Bf + z`
written in principal-direction coordinates, together with a cross-section size `p` tending to
infinity.  The sample size `n`, the factor count `k`, the factor covariance `Σ_f`, the factor
path `F` and the specific returns `Z` are fixed; the loadings `B⁽ᵖ⁾`, the principal frame
`b⁽ᵖ⁾` and the transformed scores `Φ⁽ᵖ⁾` vary with `p`. -/
structure FactorModelSeq (Ω : Type*) where
  /-- The number of factors `k`. -/
  k : ℕ
  /-- The sample size `n`, which stays fixed as `p → ∞`. -/
  n : ℕ
  /-- There is at least one factor. -/
  one_le_k : 1 ≤ k
  /-- There are more observation times than factors. -/
  k_lt_n : k < n
  /-- The limiting average specific variance `δ²`. -/
  δsq : ℝ
  /-- The limiting average specific variance is positive. -/
  δsq_pos : 0 < δsq
  /-- The factor covariance `Σ_f`. -/
  factorCov : Matrix (Fin k) (Fin k) ℝ
  /-- The factor covariance is symmetric positive definite. -/
  factorCov_posDef : factorCov.PosDef
  /-- The factor path `F`, whose columns are the factor realisations. -/
  F : Matrix (Fin k) (Fin n) ℝ
  /-- The loadings `B⁽ᵖ⁾` of the `p` observed variables on the `k` factors. -/
  B : ∀ p : ℕ, Matrix (Fin p) (Fin k) ℝ
  /-- The principal frame `b⁽ᵖ⁾`: an orthonormal basis of the column space of
  `B⁽ᵖ⁾` diagonalising `B⁽ᵖ⁾Σ_f(B⁽ᵖ⁾)ᵀ`. -/
  b : ∀ p : ℕ, Matrix (Fin p) (Fin k) ℝ
  /-- The transformed scores `Φ⁽ᵖ⁾`, the factor path in the coordinates of the
  principal frame. -/
  Φ : ℕ → Matrix (Fin k) (Fin n) ℝ
  /-- The specific returns: `Z i ℓ` is the specific return of the `i`th observed
  variable at time `ℓ`, a random variable on `Ω`. -/
  Z : ℕ → Fin n → Ω → ℝ
  /-- The eigenvalues `σ⁽ᵖ⁾₁ > ⋯ > σ⁽ᵖ⁾ₖ > 0` of `B⁽ᵖ⁾Σ_f(B⁽ᵖ⁾)ᵀ` on its column
  space. -/
  σ : ℕ → Fin k → ℝ
  /-- The eigenvalues `σ⁽ᵖ⁾ⱼ` are listed in strictly decreasing order. -/
  σ_strictAnti : ∀ p, StrictAnti (σ p)
  /-- The eigenvalues `σ⁽ᵖ⁾ⱼ` are positive. -/
  σ_pos : ∀ p, ∀ j, 0 < σ p j
  /-- The principal frame has orthonormal columns. -/
  transpose_b_mul_b : ∀ p, k ≤ p → (b p)ᵀ * b p = 1
  /-- The loadings have linearly independent columns. -/
  linearIndependent_B : ∀ p, k ≤ p → LinearIndependent ℝ (B p)ᵀ
  /-- The principal frame spans the column space of the loadings. -/
  range_B_eq : ∀ p, k ≤ p →
    LinearMap.range (B p).mulVecLin = LinearMap.range (b p).mulVecLin
  /-- The `j`th column of the principal frame is an eigenvector of
  `B⁽ᵖ⁾Σ_f(B⁽ᵖ⁾)ᵀ` with eigenvalue `σ⁽ᵖ⁾ⱼ`. -/
  mulVec_b_col : ∀ p, k ≤ p → ∀ j,
    (B p * factorCov * (B p)ᵀ) *ᵥ (b p)ᵀ j = σ p j • (b p)ᵀ j
  /-- The change of variables to principal coordinates: `B⁽ᵖ⁾F = b⁽ᵖ⁾Φ⁽ᵖ⁾`. -/
  B_mul_F : ∀ p, k ≤ p → B p * F = b p * Φ p

namespace FactorModelSeq

variable {Ω : Type*} (M : FactorModelSeq Ω)

noncomputable section

/-- The specific-return matrix `Z⁽ᵖ⁾ ∈ ℝ^{p×n}` at the sample point `ω`: the leading `p × n`
block of the model's array of specific returns. -/
def noiseMatrix (p : ℕ) (ω : Ω) : Matrix (Fin p) (Fin M.n) ℝ :=
  Matrix.of fun i ℓ => M.Z i ℓ ω

/-- The data matrix `Y⁽ᵖ⁾ = b⁽ᵖ⁾Φ⁽ᵖ⁾ + Z⁽ᵖ⁾ ∈ ℝ^{p×n}`: the observed returns of the `p`
variables at the `n` observation times. -/
def dataMatrix (p : ℕ) (ω : Ω) : Matrix (Fin p) (Fin M.n) ℝ :=
  M.b p * M.Φ p + M.noiseMatrix p ω

/-- The observable dual Gram matrix `W⁽ᵖ⁾ = (np)⁻¹ (Y⁽ᵖ⁾)ᵀY⁽ᵖ⁾ ∈ ℝ^{n×n}`, of fixed size
`n × n`. -/
def dualGram (p : ℕ) (ω : Ω) : Matrix (Fin M.n) (Fin M.n) ℝ :=
  ((M.n : ℝ) * p)⁻¹ • ((M.dataMatrix p ω)ᵀ * M.dataMatrix p ω)

/-- The scaled score matrix `Φ̄⁽ᵖ⁾ = p^{-1/2} Φ⁽ᵖ⁾ ∈ ℝ^{k×n}`. -/
def scaledScores (p : ℕ) : Matrix (Fin M.k) (Fin M.n) ℝ :=
  (Real.sqrt p)⁻¹ • M.Φ p

/-- The limiting scaled score matrix `Φ̄^∞ ∈ ℝ^{k×n}`, the limit of the scaled scores `Φ̄⁽ᵖ⁾`
as the cross-section grows. -/
def scaledScoresLim : Matrix (Fin M.k) (Fin M.n) ℝ :=
  limUnder atTop M.scaledScores

/-- The noiseless dual Gram limit `W₀ = n⁻¹ Fᵀ G F ∈ ℝ^{n×n}` attached to a limiting loadings
Gram `G` (the limit of `p⁻¹(B⁽ᵖ⁾)ᵀB⁽ᵖ⁾`, called `G_B` in the source). -/
def dualGramLim₀ (G : Matrix (Fin M.k) (Fin M.k) ℝ) : Matrix (Fin M.n) (Fin M.n) ℝ :=
  (M.n : ℝ)⁻¹ • (M.Fᵀ * G * M.F)

/-- The eigenvalues `θ⁽ᵖ⁾₁ ≥ ⋯ ≥ θ⁽ᵖ⁾ₙ` of the observable dual Gram matrix `W⁽ᵖ⁾`, listed in
weakly decreasing order; `W⁽ᵖ⁾` is symmetric, being a nonnegative multiple of a Gram matrix. -/
def dualEigenvalues (p : ℕ) (ω : Ω) : Fin M.n → ℝ := fun i =>
  Matrix.IsHermitian.eigenvalues₀
    (show (M.dualGram p ω).IsHermitian by
      rw [dualGram, ← Matrix.conjTranspose_eq_transpose_of_trivial]
      exact (Matrix.isHermitian_conjTranspose_mul_self _).smul (star_trivial _))
    (Fin.cast (Fintype.card_fin M.n).symm i)

/-- The average bulk eigenvalue `ℓ⁽ᵖ⁾ = (n-k)⁻¹ ∑_{i=k+1}^{n} θ⁽ᵖ⁾ᵢ`: the mean of the `n - k`
eigenvalues of `W⁽ᵖ⁾` below the `k` systematic ones. -/
def avgBulkEigenvalue (p : ℕ) (ω : Ω) : ℝ :=
  ((M.n : ℝ) - M.k)⁻¹ *
    ∑ i ∈ Finset.univ.filter fun i : Fin M.n => M.k ≤ (i : ℕ), M.dualEigenvalues p ω i

end

/-- The `j`-th *principal direction* `b⁽ᵖ⁾ⱼ ∈ ℝ^p`: the `j`-th column of the principal frame,
read in the Euclidean space `ℝ^p` so that angles to it are defined. -/
def principalDirection {Ω : Type u} (M : FactorModelSeq Ω) (p : ℕ) (j : Fin M.k) :
    EuclideanSpace ℝ (Fin p) :=
  WithLp.toLp 2 ((M.b p)ᵀ j)

/-- The *systematic subspace* `𝓑⁽ᵖ⁾ ⊆ ℝ^p`: the span of the columns of the principal frame
`b⁽ᵖ⁾`, read as a subspace of the Euclidean space `ℝ^p`. -/
noncomputable def principalSubspace {Ω : Type u} (M : FactorModelSeq Ω) (p : ℕ) :
    Submodule ℝ (EuclideanSpace ℝ (Fin p)) :=
  LinearMap.range (Matrix.toEuclideanLin (M.b p))

/-- A choice, for every `p`, of a unit eigenvector `w⁽ᵖ⁾ⱼ` of the observable dual Gram matrix
`W⁽ᵖ⁾` at its `j`-th eigenvalue `θ⁽ᵖ⁾ⱼ` together with the sample principal direction
`h_j ∈ ℝ^p` that Gram duality reconstructs from it.  Each condition is imposed only for
large `p`. -/
structure PrincipalDirectionSeq {Ω : Type u} (M : FactorModelSeq Ω) (j : Fin M.k) (ω : Ω) where
  /-- The chosen unit eigenvectors `w⁽ᵖ⁾ⱼ` of the observable dual Gram matrix. -/
  dual : ℕ → EuclideanSpace ℝ (Fin M.n)
  /-- The reconstructed sample principal directions `h_j ∈ ℝ^p`. -/
  sample : (p : ℕ) → EuclideanSpace ℝ (Fin p)
  /-- The dual eigenvectors are unit vectors. -/
  norm_dual : ∀ᶠ p in atTop, ‖dual p‖ = 1
  /-- The dual eigenvectors sit at the `j`-th eigenvalue `θ⁽ᵖ⁾ⱼ` of `W⁽ᵖ⁾`. -/
  dualGram_mulVec_dual : ∀ᶠ p in atTop, M.dualGram p ω *ᵥ dual p
    = M.dualEigenvalues p ω (Fin.castLE M.k_lt_n.le j) • dual p
  /-- `h_j` is the vector Gram duality reconstructs from `w⁽ᵖ⁾ⱼ`. -/
  sqrt_smul_sample : ∀ᶠ p in atTop,
    Real.sqrt ((M.n : ℝ) * p * M.dualEigenvalues p ω (Fin.castLE M.k_lt_n.le j)) • sample p
      = M.dataMatrix p ω *ᵥ dual p

end FactorModelSeq

/-! ## The asymptotic hypotheses -/

/-- The *asymptotic hypotheses* on a principal-coordinate factor model sequence `M`, with data
a limiting loadings Gram `G` (`G_B` in the source) and the systematic eigenvalues `lam`
(`λ₁ > ⋯ > λₖ > 0`) of the noiseless dual Gram limit. -/
structure AsymptoticHypotheses {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (M : FactorModelSeq Ω) (G : Matrix (Fin M.k) (Fin M.k) ℝ) (lam : Fin M.k → ℝ) : Prop where
  /-- The limiting loadings Gram is symmetric positive definite. -/
  G_posDef : G.PosDef
  /-- The loadings Grams `p⁻¹(B⁽ᵖ⁾)ᵀB⁽ᵖ⁾` converge to `G`. -/
  tendsto_gram_B : Tendsto (fun p : ℕ => (p : ℝ)⁻¹ • ((M.B p)ᵀ * M.B p)) atTop (𝓝 G)
  /-- `Σ_f^{1/2} G Σ_f^{1/2}` has `k` distinct positive eigenvalues. -/
  exists_hasPosEigenvalues_factorCov_conj : ∃ mu : Fin M.k → ℝ,
    HasPosEigenvalues (CFC.sqrt M.factorCov * G * CFC.sqrt M.factorCov) mu
  /-- Every specific return has a finite fourth moment. -/
  memLp_Z : ∀ i ℓ, MemLp (M.Z i ℓ) 4 μ
  /-- The specific returns are independent. -/
  iIndepFun_Z : iIndepFun (fun q : ℕ × Fin M.n => M.Z q.1 q.2) μ
  /-- The specific returns have mean zero. -/
  integral_Z : ∀ i ℓ, μ[M.Z i ℓ] = 0
  /-- The specific returns have positive variances `δ²_{i,ℓ}`. -/
  variance_Z_pos : ∀ i ℓ, 0 < Var[M.Z i ℓ; μ]
  /-- The fourth moments are bounded uniformly by some `κ₄ < ∞`. -/
  bddAbove_fourthMoment_Z :
    BddAbove (Set.range fun q : ℕ × Fin M.n => μ[fun ω => M.Z q.1 q.2 ω ^ 4])
  /-- At each observation time the average specific variance over the cross-section tends
  to `δ²`. -/
  tendsto_variance_Z : ∀ ℓ, Tendsto
    (fun p : ℕ => (p : ℝ)⁻¹ * ∑ i ∈ Finset.range p, Var[M.Z i ℓ; μ]) atTop (𝓝 M.δsq)
  /-- The noiseless dual Gram limit `W₀` has the `k` distinct positive eigenvalues
  `λ₁ > ⋯ > λₖ > 0`. -/
  hasPosEigenvalues_dualGramLim₀ : HasPosEigenvalues (M.dualGramLim₀ G) lam

/-- The *standing asymptotic hypotheses*: the asymptotic hypotheses above, together with the
convergence of the scaled scores `Φ̄⁽ᵖ⁾ → Φ̄^∞` and the Gram identity
`n⁻¹(Φ̄^∞)ᵀΦ̄^∞ = W₀` tying the limiting scores to the noiseless dual Gram limit. -/
structure StandingHypotheses {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (M : FactorModelSeq Ω) (G : Matrix (Fin M.k) (Fin M.k) ℝ) (lam : Fin M.k → ℝ) : Prop
    extends AsymptoticHypotheses μ M G lam where
  /-- The scaled scores converge to `Φ̄^∞`. -/
  tendsto_scaledScores : Tendsto M.scaledScores atTop (𝓝 M.scaledScoresLim)
  /-- The limiting scaled scores have the noiseless dual Gram limit as their Gram matrix. -/
  gram_scaledScoresLim :
    (M.n : ℝ)⁻¹ • ((M.scaledScoresLim)ᵀ * M.scaledScoresLim) = M.dualGramLim₀ G

/-! ## The candidate factor covariances -/

/-- The **population dual** `K(Σ) := Σ^{1/2} G_B Σ^{1/2}` of a candidate factor covariance
`Σ`, taken against the loading Gram limit `G_B`. -/
noncomputable def popDual {k : ℕ} (G S : Matrix (Fin k) (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  CFC.sqrt S * G * CFC.sqrt S

/-- A symmetric positive definite `Σ` is **admissible** for the population eigenvalues `μ`
when its population dual `K(Σ)` has eigenvalues `μ`, recorded as being carried to
`Λ = diagonal μ` by an orthogonal matrix. -/
structure Admissible {k : ℕ} (G : Matrix (Fin k) (Fin k) ℝ) (μ : Fin k → ℝ)
    (S : Matrix (Fin k) (Fin k) ℝ) : Prop where
  /-- An admissible candidate covariance is symmetric positive definite. -/
  posDef : S.PosDef
  /-- Its population dual is carried to `Λ = diagonal μ` by an orthogonal matrix. -/
  exists_orthogonal_conj :
    ∃ V ∈ Matrix.orthogonalGroup (Fin k) ℝ, Vᵀ * popDual G S * V = Matrix.diagonal μ

/-- The **systematic dual** `N(Σ, V) := Λ^{1/2}Vᵀ Σ^{-1/2}(FFᵀ/n)Σ^{-1/2}V Λ^{1/2}` attached
to a candidate factor covariance `Σ` together with an orthogonal `V` diagonalising `K(Σ)`,
where `Λ = diagonal μ`. -/
noncomputable def systematicDual {k n : ℕ} (μ : Fin k → ℝ) (F : Matrix (Fin k) (Fin n) ℝ)
    (S V : Matrix (Fin k) (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.diagonal (fun j => √(μ j)) * Vᵀ * (CFC.sqrt S)⁻¹ * ((n : ℝ)⁻¹ • (F * Fᵀ)) *
    ((CFC.sqrt S)⁻¹ * V * Matrix.diagonal fun j => √(μ j))

end PCError

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
    (hyp : StandingHypotheses μ M G lam) (j : Fin M.k)
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
  sorry

/-- **`thm_oos_estimable` — Theorem 2, the observable estimate (38).** Almost surely the
observable ratio `ℓ⁽ᵖ⁾/θ⁽ᵖ⁾ⱼ` of the average bulk eigenvalue to the `j`-th eigenvalue of the
dual Gram matrix converges to `δ²/(nλⱼ+δ²)`, which by `thm_error_decomp` is the limit of the
out-of-subspace error.  It needs neither eigenvector continuity nor a choice of `νⱼ`. -/
theorem thm_oos_estimable {Ω : Type u} (M : FactorModelSeq Ω) [MeasurableSpace Ω]
    {μ : Measure Ω} {G : Matrix (Fin M.k) (Fin M.k) ℝ} {lam : Fin M.k → ℝ}
    (hyp : StandingHypotheses μ M G lam) (j : Fin M.k) :
    ∀ᵐ ω ∂μ, Tendsto (fun p : ℕ => M.avgBulkEigenvalue p ω /
        M.dualEigenvalues p ω (Fin.castLE M.k_lt_n.le j)) atTop
      (𝓝 (M.δsq / ((M.n : ℝ) * lam j + M.δsq))) :=
  sorry

/-- **`thm_error_floor` — Theorem 2, the floor (39).** Almost surely the observable limit is at
most the limit of the total error, with equality exactly when the in-subspace rotation
`sin²∠(νⱼ, eⱼ)` vanishes. -/
theorem thm_error_floor {Ω : Type u} (M : FactorModelSeq Ω) [MeasurableSpace Ω]
    {μ : Measure Ω} {G : Matrix (Fin M.k) (Fin M.k) ℝ} {lam : Fin M.k → ℝ}
    (hyp : StandingHypotheses μ M G lam) (j : Fin M.k)
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
  sorry

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
  sorry

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
  sorry

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
  sorry

end Challenge

end PCError
