/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import PCError.Attr
public import PCError.Defs.TheFactorModelAndItsDerivedMatrices
public import PCError.MatrixPreliminaries

/-!
# The systematic dual Grams in the limit

The two limiting systematic Gram matrices of the model — the `k × k` matrix
`N = n⁻¹ Φ̄^∞ (Φ̄^∞)ᵀ` in principal coordinates and the `n × n` noiseless dual Gram limit
`W₀ = n⁻¹ Fᵀ G F` — are the two Gram products of one and the same matrix
`A = n^(-1/2) Φ̄^∞`, once the Gram identity `n⁻¹(Φ̄^∞)ᵀΦ̄^∞ = W₀` of
`PCError.StandingHypotheses` is assumed. Everything here is that observation fed into the
Gram duality of `PCError.MatrixPreliminaries`.

## Main statements

* `PCError.FactorModelSeq.mem_spectrum_principalDualGramLim_iff`: *the noiseless duals are
  Gram partners* — a nonzero real `λ` is an eigenvalue of `N` if and only if it is an
  eigenvalue of `W₀`.
* `PCError.FactorModelSeq.norm_eq_one_of_sqrt_smul_eq_scaledScoresLim_mulVec`,
  `PCError.FactorModelSeq.mulVec_eq_smul_of_sqrt_smul_eq_scaledScoresLim_mulVec`,
  `PCError.FactorModelSeq.exists_norm_eq_one_and_scaledScoresLim_mulVec_eq`: *the duality
  link between the two systematic eigenframes* — a vector `ν` with
  `√(nλ) ν = Φ̄^∞ w`, built from a unit eigenvector `w` of `W₀` at a nonzero `λ`, is a unit
  eigenvector of `N` at `λ`, and such a `ν` exists.

## Implementation notes

The auxiliary matrix `A = n^(-1/2) Φ̄^∞` is not given a name: it is
used only through the two identities
`PCError.FactorModelSeq.principalDualGramLim_eq_mul_transpose` and
`PCError.FactorModelSeq.dualGramLim₀_eq_transpose_mul`, which are what the Gram duality
lemmas consume.

The duality link is stated for a `ν` *characterized* by `√(nλ) ν = Φ̄^∞ w` rather than for an
explicitly constructed one, exactly as in `PCError.norm_eq_one_of_sqrt_smul_eq_transpose_mulVec`:
the characterizing equation is then the hypothesis, and what is proved is that it
forces `ν` to be the unit eigenvector of `N` at `λ`.
`PCError.FactorModelSeq.exists_norm_eq_one_and_scaledScoresLim_mulVec_eq` packages the two
conclusions together with the existence of such a `ν`, which is the form the downstream limit
statements consume.

The hypothesis is only `λ ≠ 0`, not `λ > 0`: positivity of a nonzero eigenvalue of a Gram
matrix is `PCError.pos_of_mulVec_mul_transpose_eq_smul`, so it need not be assumed.
-/

@[expose] public section

namespace PCError

namespace FactorModelSeq

open Matrix

variable {Ω : Type*} (M : FactorModelSeq Ω)

/-! ### The two limiting systematic Grams as the Gram products of one matrix -/

/-- The sample size is positive: there are more observation times than factors. -/
theorem n_pos : 0 < M.n :=
  lt_of_le_of_lt (Nat.zero_le M.k) M.k_lt_n

/-- `N = n⁻¹ Φ̄^∞ (Φ̄^∞)ᵀ` is the Gram product `AAᵀ` of `A = n^(-1/2) Φ̄^∞`. -/
theorem principalDualGramLim_eq_mul_transpose :
    M.principalDualGramLim = ((Real.sqrt M.n)⁻¹ • M.scaledScoresLim) *
      ((Real.sqrt M.n)⁻¹ • M.scaledScoresLim)ᵀ := by
  have hn : Real.sqrt M.n * Real.sqrt M.n = M.n := Real.mul_self_sqrt (by positivity)
  rw [principalDualGramLim, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    ← mul_inv, hn]

/-- The other Gram product `AᵀA` of `A = n^(-1/2) Φ̄^∞` is `n⁻¹ (Φ̄^∞)ᵀΦ̄^∞`, which the Gram
identity of `PCError.StandingHypotheses` identifies with the noiseless dual Gram limit
`W₀`. -/
theorem dualGramLim₀_eq_transpose_mul {G : Matrix (Fin M.k) (Fin M.k) ℝ}
    (hG : (M.n : ℝ)⁻¹ • (M.scaledScoresLimᵀ * M.scaledScoresLim) = M.dualGramLim₀ G) :
    M.dualGramLim₀ G = ((Real.sqrt M.n)⁻¹ • M.scaledScoresLim)ᵀ *
      ((Real.sqrt M.n)⁻¹ • M.scaledScoresLim) := by
  have hn : Real.sqrt M.n * Real.sqrt M.n = M.n := Real.mul_self_sqrt (by positivity)
  rw [← hG, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← mul_inv, hn]

/-! ### The noiseless duals are Gram partners -/

/-- **The noiseless duals are Gram partners**: if the limiting scaled scores `Φ̄^∞` have the
noiseless dual Gram limit `W₀` as their Gram matrix, `n⁻¹(Φ̄^∞)ᵀΦ̄^∞ = W₀`, then a nonzero
real `λ` is an eigenvalue of `N` if and only if it is an eigenvalue of `W₀`.

Both matrices are Gram products of `A = n^(-1/2) Φ̄^∞`, so this is
`PCError.mem_spectrum_mul_transpose_iff`. -/
@[pcerror "lem_N_W0_dual"]
theorem mem_spectrum_principalDualGramLim_iff {G : Matrix (Fin M.k) (Fin M.k) ℝ}
    (hG : (M.n : ℝ)⁻¹ • (M.scaledScoresLimᵀ * M.scaledScoresLim) = M.dualGramLim₀ G)
    {lam : ℝ} (hlam : lam ≠ 0) :
    lam ∈ spectrum ℝ M.principalDualGramLim ↔ lam ∈ spectrum ℝ (M.dualGramLim₀ G) := by
  rw [M.principalDualGramLim_eq_mul_transpose, M.dualGramLim₀_eq_transpose_mul hG]
  exact mem_spectrum_mul_transpose_iff _ hlam

/-! ### The duality link between the two systematic eigenframes -/

section DualityLink

variable {G : Matrix (Fin M.k) (Fin M.k) ℝ}
  (hG : (M.n : ℝ)⁻¹ • (M.scaledScoresLimᵀ * M.scaledScoresLim) = M.dualGramLim₀ G)
  {lam : ℝ} {w : EuclideanSpace ℝ (Fin M.n)} {ν : EuclideanSpace ℝ (Fin M.k)}

/-- Rewriting of the defining equation `√(nλ) ν = Φ̄^∞ w` of the duality link in the form
`√λ ν = Bᵀ w` with `B := Aᵀ` and `A = n^(-1/2) Φ̄^∞`. -/
theorem sqrt_smul_eq_transpose_transpose_mulVec
    (hν : Real.sqrt (M.n * lam) • ν = M.scaledScoresLim *ᵥ w) :
    Real.sqrt lam • ν = ((Real.sqrt M.n)⁻¹ • M.scaledScoresLim)ᵀᵀ *ᵥ w := by
  rw [transpose_transpose, Matrix.smul_mulVec, ← hν, smul_smul, Real.sqrt_mul (by positivity),
    inv_mul_cancel_left₀ (Real.sqrt_ne_zero'.2 (by exact_mod_cast M.n_pos))]

include hG

/-- With `A = n^(-1/2) Φ̄^∞`, a unit eigenvector `w` of `W₀ = AᵀA` at `λ` is a unit
eigenvector of `B Bᵀ` for `B := Aᵀ`: this is the form the Gram duality lemmas of
`PCError.MatrixPreliminaries` consume. -/
theorem mulVec_transpose_mul_transpose_eq_smul (hw : M.dualGramLim₀ G *ᵥ w = lam • w) :
    (((Real.sqrt M.n)⁻¹ • M.scaledScoresLim)ᵀ *
      ((Real.sqrt M.n)⁻¹ • M.scaledScoresLim)ᵀᵀ) *ᵥ w = lam • w := by
  rw [transpose_transpose, ← M.dualGramLim₀_eq_transpose_mul hG]
  exact hw

/-- **The duality link**, first part: a vector `ν` with `√(nλ) ν = Φ̄^∞ w`, built from a unit
eigenvector `w` of the noiseless dual Gram limit `W₀` at a nonzero `λ`, is a unit vector. -/
@[pcerror "lem_duality_link"]
theorem norm_eq_one_of_sqrt_smul_eq_scaledScoresLim_mulVec (hlam : lam ≠ 0) (hw1 : ‖w‖ = 1)
    (hw : M.dualGramLim₀ G *ᵥ w = lam • w)
    (hν : Real.sqrt (M.n * lam) • ν = M.scaledScoresLim *ᵥ w) : ‖ν‖ = 1 :=
  norm_eq_one_of_sqrt_smul_eq_transpose_mulVec _ hlam hw1
    (M.mulVec_transpose_mul_transpose_eq_smul hG hw)
    (M.sqrt_smul_eq_transpose_transpose_mulVec hν)

/-- **The duality link**, second part: a vector `ν` with `√(nλ) ν = Φ̄^∞ w`, built from a
unit eigenvector `w` of the noiseless dual Gram limit `W₀` at a nonzero `λ`, is an
eigenvector of the limiting systematic dual Gram `N` at the same `λ`. -/
@[pcerror "lem_duality_link"]
theorem mulVec_eq_smul_of_sqrt_smul_eq_scaledScoresLim_mulVec (hlam : lam ≠ 0) (hw1 : ‖w‖ = 1)
    (hw : M.dualGramLim₀ G *ᵥ w = lam • w)
    (hν : Real.sqrt (M.n * lam) • ν = M.scaledScoresLim *ᵥ w) :
    M.principalDualGramLim *ᵥ ν = lam • ν := by
  have hB := M.mulVec_transpose_mul_transpose_eq_smul hG hw
  have hpos : 0 < lam := pos_of_mulVec_mul_transpose_eq_smul _ hlam hw1 hB
  have h := transpose_mul_mulVec_eq_smul_of_sqrt_smul_eq_transpose_mulVec _ hpos hB
    (M.sqrt_smul_eq_transpose_transpose_mulVec hν)
  rwa [transpose_transpose, ← M.principalDualGramLim_eq_mul_transpose] at h

/-- **The duality link between the two systematic eigenframes**: if `λ ≠ 0` is an eigenvalue
of the noiseless dual Gram limit `W₀` with unit eigenvector `w`, then there is a unit
eigenvector `ν` of the limiting systematic dual Gram `N` at `λ` satisfying
`Φ̄^∞ w = √(nλ) ν`. -/
@[pcerror "lem_duality_link"]
theorem exists_norm_eq_one_and_scaledScoresLim_mulVec_eq (hlam : lam ≠ 0) (hw1 : ‖w‖ = 1)
    (hw : M.dualGramLim₀ G *ᵥ w = lam • w) :
    ∃ ν : EuclideanSpace ℝ (Fin M.k), ‖ν‖ = 1 ∧ M.principalDualGramLim *ᵥ ν = lam • ν ∧
      M.scaledScoresLim *ᵥ w = Real.sqrt (M.n * lam) • ν := by
  have hpos : 0 < lam :=
    pos_of_mulVec_mul_transpose_eq_smul _ hlam hw1 (M.mulVec_transpose_mul_transpose_eq_smul hG hw)
  have hne : Real.sqrt (M.n * lam) ≠ 0 :=
    Real.sqrt_ne_zero'.2 (mul_pos (by exact_mod_cast M.n_pos) hpos)
  set x : EuclideanSpace ℝ (Fin M.k) := WithLp.toLp 2 (M.scaledScoresLim *ᵥ w.ofLp)
  have hν : Real.sqrt (M.n * lam) • ((Real.sqrt (M.n * lam))⁻¹ • x)
      = M.scaledScoresLim *ᵥ w := by
    rw [smul_inv_smul₀ hne]
  exact ⟨(Real.sqrt (M.n * lam))⁻¹ • x,
    M.norm_eq_one_of_sqrt_smul_eq_scaledScoresLim_mulVec hG hlam hw1 hw hν,
    M.mulVec_eq_smul_of_sqrt_smul_eq_scaledScoresLim_mulVec hG hlam hw1 hw hν, hν.symm⟩

end DualityLink

end FactorModelSeq

end PCError

end
