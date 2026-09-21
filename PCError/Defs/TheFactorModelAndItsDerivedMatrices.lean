/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Probability.Moments.Variance
public import PCError.Attr

/-!
# The factor model and its derived matrices

The latent factor model `y = Bf + z` of the source, presented in
principal-direction coordinates: the orthonormal frame `b` and the transformed
scores `Φ` are part of the data, related to the loadings `B` and the factor path
`F` by `B F = b Φ`.  All the objects the asymptotic analysis runs on are derived
from that data here.

## Main definitions

* `PCError.HasPosEigenvalues`: the predicate that the positive part of a
  matrix's spectrum is exactly the set of values of a strictly decreasing
  positive family.
* `PCError.FactorModelSeq`: a principal-coordinate factor model sequence.
* `PCError.FactorModelSeq.dataMatrix`: the data matrix `Y⁽ᵖ⁾ = b⁽ᵖ⁾Φ⁽ᵖ⁾ + Z⁽ᵖ⁾`.
* `PCError.FactorModelSeq.sampleCov`: the scaled sample covariance
  `S⁽ᵖ⁾ = (np)⁻¹ Y⁽ᵖ⁾(Y⁽ᵖ⁾)ᵀ`, a `p × p` matrix.
* `PCError.FactorModelSeq.dualGram`: the observable dual Gram matrix
  `W⁽ᵖ⁾ = (np)⁻¹ (Y⁽ᵖ⁾)ᵀY⁽ᵖ⁾`, an `n × n` matrix of fixed size.
* `PCError.FactorModelSeq.scaledScores`: `Φ̄⁽ᵖ⁾ = p^(-1/2) Φ⁽ᵖ⁾`, with limit
  `PCError.FactorModelSeq.scaledScoresLim` (`Φ̄^∞`).
* `PCError.FactorModelSeq.dualGramLim₀`, `PCError.FactorModelSeq.dualGramLim`:
  the noiseless limit `W₀ = n⁻¹ Fᵀ G_B F` and the limit `W = W₀ + (δ²/n) I`.
* `PCError.FactorModelSeq.principalDualGramLim`: the limiting systematic dual
  Gram in principal coordinates, `N = n⁻¹ Φ̄^∞ (Φ̄^∞)ᵀ`.
* `PCError.FactorModelSeq.dualEigenvalues`, `PCError.FactorModelSeq.avgBulkEigenvalue`:
  the eigenvalues `θ⁽ᵖ⁾₁ ≥ ⋯ ≥ θ⁽ᵖ⁾ₙ` of `W⁽ᵖ⁾` and the average bulk eigenvalue
  `ℓ⁽ᵖ⁾ = (n-k)⁻¹ ∑_{i>k} θ⁽ᵖ⁾ᵢ`.
* `PCError.AsymptoticHypotheses` and `PCError.StandingHypotheses`: the two
  bundles of asymptotic hypotheses every limit statement is made under.

## Implementation notes

The specific returns are the entries of a single array `Z : ℕ → Fin n → Ω → ℝ`
of random variables, and `Z⁽ᵖ⁾` (`FactorModelSeq.noiseMatrix`) is its leading
`p × n` block; this is what makes the entrywise hypotheses of
`AsymptoticHypotheses` — independence, moments, and the Cesàro limit of the
variances along the cross-section — statements about one family of random
variables rather than about an unrelated matrix for each `p`.  Everything else
in the model is deterministic, so `dataMatrix`, `sampleCov`, `dualGram` and the
bulk eigenvalue are functions of a sample point `ω`, and the limit theorems
about them are almost-sure statements.

The structural conditions of the model constrain the data only for `p ≥ k`, as
in the source: for `p < k` a `p × k` matrix `b⁽ᵖ⁾` cannot have orthonormal
columns at all.
-/

namespace PCError

open Filter Matrix MeasureTheory ProbabilityTheory
open scoped Topology MatrixOrder

@[expose] public section

/-! ### Distinct positive eigenvalues -/

/-- `HasPosEigenvalues A c` says that the positive part of the spectrum of `A` is
exactly the set of values of the strictly decreasing positive family `c`.

For an `m × m` matrix and `c` indexed by `Fin m` this is the statement that `A`
has `m` distinct positive eigenvalues `c 0 > ⋯ > c (m-1) > 0`.  For `c` indexed
by `Fin k` with `k < m` it says that `A` has `k` distinct positive eigenvalues
and no others, the remaining ones being `≤ 0`; when `A` is positive
semidefinite of rank `k` this forces each `c j` to be simple. -/
structure HasPosEigenvalues {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m ℝ) {ι : Type*} [LinearOrder ι] (c : ι → ℝ) : Prop where
  /-- The eigenvalues are listed in strictly decreasing order. -/
  strictAnti : StrictAnti c
  /-- The listed eigenvalues are positive. -/
  pos : ∀ j, 0 < c j
  /-- The listed values exhaust the positive part of the spectrum. -/
  spectrum_pos_eq : {x ∈ spectrum ℝ A | 0 < x} = Set.range c

namespace HasPosEigenvalues

variable {m : Type*} [Fintype m] [DecidableEq m] {A : Matrix m m ℝ}
  {ι : Type*} [LinearOrder ι] {c : ι → ℝ}

/-- Every listed eigenvalue lies in the spectrum of `A`. -/
theorem mem_spectrum (h : HasPosEigenvalues A c) (j : ι) : c j ∈ spectrum ℝ A :=
  Set.sep_subset _ _ (h.spectrum_pos_eq.ge (Set.mem_range_self j))

/-- The listed eigenvalues are pairwise distinct. -/
theorem injective (h : HasPosEigenvalues A c) : Function.Injective c :=
  h.strictAnti.injective

/-- A positive point of the spectrum of `A` is one of the listed eigenvalues. -/
theorem mem_range_of_mem_spectrum (h : HasPosEigenvalues A c) {x : ℝ}
    (hx : x ∈ spectrum ℝ A) (hxpos : 0 < x) : x ∈ Set.range c :=
  h.spectrum_pos_eq.le ⟨hx, hxpos⟩

end HasPosEigenvalues

/-! ### The model -/

/-- A *principal-coordinate factor model sequence*: the factor model of the
source in principal-direction coordinates, together with a cross-section size
`p` tending to infinity.  The sample size `n`, the number of factors `k`, the
factor covariance `factorCov` (`Σ_f`), the factor path `F` and the specific
returns `Z` are fixed; the loadings `B⁽ᵖ⁾`, the principal frame `b⁽ᵖ⁾` and the
transformed scores `Φ⁽ᵖ⁾` vary with `p`.

The structural conditions are the change of variables of the source's Lemma 3,
recorded here as a hypothesis rather than derived, so that no object is
introduced by an existence claim. -/
@[pcerror "def_model"]
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

/-- The specific-return matrix `Z⁽ᵖ⁾ ∈ ℝ^{p×n}` at the sample point `ω`: the
leading `p × n` block of the model's array of specific returns. -/
@[pcerror "def_model"]
def noiseMatrix (p : ℕ) (ω : Ω) : Matrix (Fin p) (Fin M.n) ℝ :=
  Matrix.of fun i ℓ => M.Z i ℓ ω

/-- The entries of `Z⁽ᵖ⁾` at the sample point `ω` are the specific returns `Z i ℓ ω`. -/
@[simp]
theorem noiseMatrix_apply (p : ℕ) (ω : Ω) (i : Fin p) (ℓ : Fin M.n) :
    M.noiseMatrix p ω i ℓ = M.Z i ℓ ω :=
  rfl

/-- The data matrix `Y⁽ᵖ⁾ = b⁽ᵖ⁾Φ⁽ᵖ⁾ + Z⁽ᵖ⁾ ∈ ℝ^{p×n}`: the observed returns of
the `p` variables at the `n` observation times. -/
@[pcerror "def_Y"]
def dataMatrix (p : ℕ) (ω : Ω) : Matrix (Fin p) (Fin M.n) ℝ :=
  M.b p * M.Φ p + M.noiseMatrix p ω

/-- The scaled sample covariance `S⁽ᵖ⁾ = (np)⁻¹ Y⁽ᵖ⁾(Y⁽ᵖ⁾)ᵀ ∈ ℝ^{p×p}`. -/
@[pcerror "def_S"]
def sampleCov (p : ℕ) (ω : Ω) : Matrix (Fin p) (Fin p) ℝ :=
  ((M.n : ℝ) * p)⁻¹ • (M.dataMatrix p ω * (M.dataMatrix p ω)ᵀ)

/-- The observable dual Gram matrix `W⁽ᵖ⁾ = (np)⁻¹ (Y⁽ᵖ⁾)ᵀY⁽ᵖ⁾ ∈ ℝ^{n×n}`.  It
has fixed size `n × n`, and shares its nonzero spectrum with `S⁽ᵖ⁾`. -/
@[pcerror "def_W"]
def dualGram (p : ℕ) (ω : Ω) : Matrix (Fin M.n) (Fin M.n) ℝ :=
  ((M.n : ℝ) * p)⁻¹ • ((M.dataMatrix p ω)ᵀ * M.dataMatrix p ω)

/-- The scaled sample covariance `S⁽ᵖ⁾` is positive semidefinite. -/
theorem sampleCov_posSemidef (p : ℕ) (ω : Ω) : (M.sampleCov p ω).PosSemidef :=
  (by simpa using posSemidef_self_mul_conjTranspose (M.dataMatrix p ω) :
    (M.dataMatrix p ω * (M.dataMatrix p ω)ᵀ).PosSemidef).smul (by positivity)

/-- The scaled sample covariance `S⁽ᵖ⁾` is symmetric. -/
theorem sampleCov_isHermitian (p : ℕ) (ω : Ω) : (M.sampleCov p ω).IsHermitian :=
  (M.sampleCov_posSemidef p ω).isHermitian

/-- The observable dual Gram matrix `W⁽ᵖ⁾` is positive semidefinite. -/
theorem dualGram_posSemidef (p : ℕ) (ω : Ω) : (M.dualGram p ω).PosSemidef :=
  (by simpa using posSemidef_conjTranspose_mul_self (M.dataMatrix p ω) :
    ((M.dataMatrix p ω)ᵀ * M.dataMatrix p ω).PosSemidef).smul (by positivity)

/-- The observable dual Gram matrix `W⁽ᵖ⁾` is symmetric. -/
theorem dualGram_isHermitian (p : ℕ) (ω : Ω) : (M.dualGram p ω).IsHermitian :=
  (M.dualGram_posSemidef p ω).isHermitian

/-- The scaled score matrix `Φ̄⁽ᵖ⁾ = p^{-1/2} Φ⁽ᵖ⁾ ∈ ℝ^{k×n}`. -/
@[pcerror "def_Phibar"]
def scaledScores (p : ℕ) : Matrix (Fin M.k) (Fin M.n) ℝ :=
  (Real.sqrt p)⁻¹ • M.Φ p

/-- For `p ≠ 0`, rescaling the scaled scores by `√p` recovers the transformed scores `Φ⁽ᵖ⁾`. -/
theorem sqrt_smul_scaledScores (p : ℕ) (hp : p ≠ 0) :
    Real.sqrt p • M.scaledScores p = M.Φ p := by
  rw [scaledScores, smul_smul, mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr (by positivity)),
    one_smul]

/-- The limiting scaled score matrix `Φ̄^∞ ∈ ℝ^{k×n}`, the limit of the scaled
scores `Φ̄⁽ᵖ⁾` as the cross-section grows.  It is meaningful exactly when that
limit exists, which is part of `PCError.StandingHypotheses`. -/
@[pcerror "def_Phibarinf"]
def scaledScoresLim : Matrix (Fin M.k) (Fin M.n) ℝ :=
  limUnder atTop M.scaledScores

/-- The defining property of `Φ̄^∞`: it is the limit of the scaled scores
whenever those converge. -/
theorem scaledScoresLim_eq_of_tendsto {A : Matrix (Fin M.k) (Fin M.n) ℝ}
    (h : Tendsto M.scaledScores atTop (𝓝 A)) : M.scaledScoresLim = A :=
  h.limUnder_eq

/-- The noiseless dual Gram limit `W₀ = n⁻¹ Fᵀ G F ∈ ℝ^{n×n}` attached to a
limiting loadings Gram `G` (the limit of `p⁻¹(B⁽ᵖ⁾)ᵀB⁽ᵖ⁾`, called `G_B` in the
source). -/
@[pcerror "def_W0"]
def dualGramLim₀ (G : Matrix (Fin M.k) (Fin M.k) ℝ) : Matrix (Fin M.n) (Fin M.n) ℝ :=
  (M.n : ℝ)⁻¹ • (M.Fᵀ * G * M.F)

/-- The noiseless dual Gram limit `W₀` is symmetric whenever the limiting loadings Gram `G` is. -/
theorem dualGramLim₀_isHermitian {G : Matrix (Fin M.k) (Fin M.k) ℝ} (hG : G.IsHermitian) :
    (M.dualGramLim₀ G).IsHermitian :=
  (by simpa using isHermitian_conjTranspose_mul_mul M.F hG :
    (M.Fᵀ * G * M.F).IsHermitian).smul (star_trivial ((M.n : ℝ)⁻¹))

/-- The limiting dual Gram matrix `W = W₀ + (δ²/n) Iₙ ∈ ℝ^{n×n}`: a rank-`k`
signal plus isotropic noise. -/
@[pcerror "def_W_limit"]
def dualGramLim (G : Matrix (Fin M.k) (Fin M.k) ℝ) : Matrix (Fin M.n) (Fin M.n) ℝ :=
  M.dualGramLim₀ G + (M.δsq / M.n) • (1 : Matrix (Fin M.n) (Fin M.n) ℝ)

/-- The limiting dual Gram matrix `W` is symmetric whenever the limiting loadings Gram `G` is. -/
theorem dualGramLim_isHermitian {G : Matrix (Fin M.k) (Fin M.k) ℝ} (hG : G.IsHermitian) :
    (M.dualGramLim G).IsHermitian :=
  (M.dualGramLim₀_isHermitian hG).add
    (isHermitian_one.smul (star_trivial (M.δsq / M.n)))

/-- The limiting systematic dual Gram in principal coordinates,
`N = n⁻¹ Φ̄^∞ (Φ̄^∞)ᵀ ∈ ℝ^{k×k}`.  Its eigenvectors live in the fixed space
`ℝ^k` and can therefore be compared with the coordinate axes. -/
@[pcerror "def_N"]
def principalDualGramLim : Matrix (Fin M.k) (Fin M.k) ℝ :=
  (M.n : ℝ)⁻¹ • (M.scaledScoresLim * M.scaledScoresLimᵀ)

/-- The limiting systematic dual Gram `N` in principal coordinates is positive semidefinite. -/
theorem principalDualGramLim_posSemidef : M.principalDualGramLim.PosSemidef :=
  (by simpa using posSemidef_self_mul_conjTranspose M.scaledScoresLim :
    (M.scaledScoresLim * M.scaledScoresLimᵀ).PosSemidef).smul (by positivity)

/-- The limiting systematic dual Gram `N` in principal coordinates is symmetric. -/
theorem principalDualGramLim_isHermitian : M.principalDualGramLim.IsHermitian :=
  M.principalDualGramLim_posSemidef.isHermitian

/-- The eigenvalues `θ⁽ᵖ⁾₁ ≥ ⋯ ≥ θ⁽ᵖ⁾ₙ` of the observable dual Gram matrix
`W⁽ᵖ⁾`, listed in weakly decreasing order. -/
@[pcerror "def_bulk"]
def dualEigenvalues (p : ℕ) (ω : Ω) : Fin M.n → ℝ := fun i =>
  Matrix.IsHermitian.eigenvalues₀
    (show (M.dualGram p ω).IsHermitian by
      rw [dualGram, ← Matrix.conjTranspose_eq_transpose_of_trivial]
      exact (Matrix.isHermitian_conjTranspose_mul_self _).smul (star_trivial _))
    (Fin.cast (Fintype.card_fin M.n).symm i)

/-- The eigenvalue list of `W⁽ᵖ⁾` is antitone: `θ⁽ᵖ⁾ᵢ ≥ θ⁽ᵖ⁾ⱼ` whenever `i ≤ j`. -/
theorem dualEigenvalues_antitone (p : ℕ) (ω : Ω) : Antitone (M.dualEigenvalues p ω) :=
  fun _ _ hij => (M.dualGram_isHermitian p ω).eigenvalues₀_antitone hij

/-- The average bulk eigenvalue `ℓ⁽ᵖ⁾ = (n-k)⁻¹ ∑_{i=k+1}^{n} θ⁽ᵖ⁾ᵢ`: the mean of
the `n - k` eigenvalues of `W⁽ᵖ⁾` below the `k` systematic ones. -/
@[pcerror "def_bulk"]
def avgBulkEigenvalue (p : ℕ) (ω : Ω) : ℝ :=
  ((M.n : ℝ) - M.k)⁻¹ *
    ∑ i : Fin M.n with M.k ≤ i.val, M.dualEigenvalues p ω i

end

end FactorModelSeq

/-! ### The asymptotic hypotheses -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The *asymptotic hypotheses* on a principal-coordinate factor model sequence
`M`, with data a limiting loadings Gram `G` (`G_B` in the source) and the
systematic eigenvalues `lam` (`λ₁ > ⋯ > λₖ > 0`) of the noiseless dual Gram
limit.

The specific returns are independent, mean zero, with positive variances, a
uniform fourth-moment bound, and average variance along the cross-section
tending to `δ²` at each observation time. -/
@[pcerror "def_assumptions"]
structure AsymptoticHypotheses (μ : Measure Ω) (M : FactorModelSeq Ω)
    (G : Matrix (Fin M.k) (Fin M.k) ℝ) (lam : Fin M.k → ℝ) : Prop where
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
  /-- At each observation time the average specific variance over the
  cross-section tends to `δ²`. -/
  tendsto_variance_Z : ∀ ℓ, Tendsto
    (fun p : ℕ => (p : ℝ)⁻¹ * ∑ i ∈ Finset.range p, Var[M.Z i ℓ; μ]) atTop (𝓝 M.δsq)
  /-- The noiseless dual Gram limit `W₀` has the `k` distinct positive
  eigenvalues `λ₁ > ⋯ > λₖ > 0`. -/
  hasPosEigenvalues_dualGramLim₀ : HasPosEigenvalues (M.dualGramLim₀ G) lam

/-- The *standing asymptotic hypotheses*: the asymptotic hypotheses of
`PCError.AsymptoticHypotheses`, together with the convergence of the scaled
scores `Φ̄⁽ᵖ⁾ → Φ̄^∞` and the Gram identity `n⁻¹(Φ̄^∞)ᵀΦ̄^∞ = W₀` tying the
limiting scores to the noiseless dual Gram limit.  Every asymptotic statement
about the model is made under this one bundle. -/
@[pcerror "def_limit_hypotheses"]
structure StandingHypotheses (μ : Measure Ω) (M : FactorModelSeq Ω)
    (G : Matrix (Fin M.k) (Fin M.k) ℝ) (lam : Fin M.k → ℝ) : Prop
    extends AsymptoticHypotheses μ M G lam where
  /-- The scaled scores converge to `Φ̄^∞`. -/
  tendsto_scaledScores : Tendsto M.scaledScores atTop (𝓝 M.scaledScoresLim)
  /-- The limiting scaled scores have the noiseless dual Gram limit as their
  Gram matrix. -/
  gram_scaledScoresLim :
    (M.n : ℝ)⁻¹ • (M.scaledScoresLimᵀ * M.scaledScoresLim) = M.dualGramLim₀ G

end

end PCError
