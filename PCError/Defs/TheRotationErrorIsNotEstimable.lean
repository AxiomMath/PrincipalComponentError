/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import Mathlib.Analysis.Matrix.Order
public import PCError.Attr

/-!
# The rotation error is not estimable: the objects of the construction

The non-estimability argument fixes the factor path `F`, the loading Gram limit
`G_B` and the population eigenvalues `Λ = diagonal μ`, and lets the population
factor covariance `Σ` vary. This file introduces the four matrices and the one
predicate that the argument is phrased in.

## Main definitions

* `PCError.popDual G S` — the *population dual* `K(Σ) = Σ^{1/2} G_B Σ^{1/2}`.
* `PCError.Admissible G μ S` — `Σ` is symmetric positive definite and `K(Σ)` has
  eigenvalues `μ`.
* `PCError.candidateCov G μ O` — the candidate covariance
  `Σ_O = G_B^{-1/2} Oᵀ Λ O G_B^{-1/2}` attached to an orthogonal `O`.
* `PCError.covFreeDual G F` — the *factor-covariance-free dual*
  `M̂ = G_B^{1/2}(FFᵀ/n)G_B^{1/2}`.
* `PCError.systematicDual μ F S V` — the *systematic dual*
  `N(Σ, V) = Λ^{1/2}Vᵀ Σ^{-1/2}(FFᵀ/n)Σ^{-1/2}V Λ^{1/2}`.

## Implementation notes

The positive semidefinite square root of a matrix is Mathlib's continuous
functional calculus root `CFC.sqrt`, which needs the Loewner order and hence
`open scoped MatrixOrder`. It is defined for *every* matrix — junk (namely `0`)
off the positive semidefinite cone — so all five definitions below are
unconditional, and the hypotheses appear only on the lemmas that need them. In
particular `CFC.sqrt S` is positive semidefinite for every `S`, which is why
several of the lemmas below carry no hypothesis at all.

`Λ = diagonal μ` is diagonal with nonnegative entries in every intended
application, so its square root `Λ^{1/2}` is spelled concretely as
`diagonal fun j => √(μ j)` rather than through `CFC.sqrt`; this agrees with
`CFC.sqrt (diagonal μ)` whenever `0 ≤ μ` and needs no side condition to use.
`Σ^{-1/2}` is `(CFC.sqrt S)⁻¹`.

The index `n` of `Fin n` is the number of columns of the factor path `F`, i.e.
the `n` that `FFᵀ/n` divides by; it is determined by the type of `F`.
-/

@[expose] public section

open scoped MatrixOrder

open Matrix

namespace PCError

variable {k n : ℕ} {G S O : Matrix (Fin k) (Fin k) ℝ} {μ : Fin k → ℝ}

/-! ### Facts about `CFC.sqrt` used throughout -/

/-- The continuous-functional-calculus square root of a matrix is positive semidefinite. -/
theorem posSemidef_sqrt (S : Matrix (Fin k) (Fin k) ℝ) : (CFC.sqrt S).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg S)

private theorem conjTranspose_sqrt (S : Matrix (Fin k) (Fin k) ℝ) :
    (CFC.sqrt S)ᴴ = CFC.sqrt S :=
  (posSemidef_sqrt S).isHermitian.eq

/-- The continuous-functional-calculus square root of a real matrix is symmetric. -/
theorem transpose_sqrt (S : Matrix (Fin k) (Fin k) ℝ) : (CFC.sqrt S)ᵀ = CFC.sqrt S := by
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial, conjTranspose_sqrt]

private theorem transpose_sqrt_inv (S : Matrix (Fin k) (Fin k) ℝ) :
    ((CFC.sqrt S)⁻¹)ᵀ = (CFC.sqrt S)⁻¹ := by
  rw [Matrix.transpose_nonsing_inv, transpose_sqrt]

/-- The square root of a positive definite matrix is a unit. -/
theorem isUnit_sqrt (hS : S.PosDef) : IsUnit (CFC.sqrt S) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro h
  have hmul : CFC.sqrt S * CFC.sqrt S = S :=
    CFC.sqrt_mul_sqrt_self S (ha := Matrix.nonneg_iff_posSemidef.mpr hS.posSemidef)
  have hdet : (CFC.sqrt S).det * (CFC.sqrt S).det = S.det := by
    rw [← Matrix.det_mul, hmul]
  rw [h, mul_zero] at hdet
  exact hS.det_pos.ne' hdet.symm

/-- The square root of a positive definite matrix is positive definite. -/
theorem posDef_sqrt (hS : S.PosDef) : (CFC.sqrt S).PosDef :=
  (posSemidef_sqrt S).posDef_iff_isUnit.mpr (isUnit_sqrt hS)

/-- The scaled sample second moment `FFᵀ/n` of the factor path is positive semidefinite. -/
private theorem posSemidef_scaledGram (F : Matrix (Fin k) (Fin n) ℝ) :
    (((n : ℝ)⁻¹ • (F * Fᵀ))).PosSemidef := by
  have h := Matrix.posSemidef_self_mul_conjTranspose F
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h.smul (by positivity)

/-! ### The population dual of a candidate factor covariance -/

/-- The **population dual** `K(Σ) := Σ^{1/2} G_B Σ^{1/2}` of a candidate factor covariance
`Σ`, taken against the loading Gram limit `G_B`. -/
@[pcerror "def_K_of_Sigma"]
noncomputable def popDual (G S : Matrix (Fin k) (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  CFC.sqrt S * G * CFC.sqrt S

/-- The population dual `K(Σ)` is symmetric whenever the loading Gram limit `G_B` is. -/
theorem popDual_isHermitian (hG : G.IsHermitian) (S : Matrix (Fin k) (Fin k) ℝ) :
    (popDual G S).IsHermitian := by
  change (popDual G S)ᴴ = popDual G S
  simp only [popDual, Matrix.conjTranspose_mul, conjTranspose_sqrt, hG.eq, Matrix.mul_assoc]

/-- The population dual `K(Σ)` is positive semidefinite whenever the loading Gram limit `G_B`
is. -/
theorem popDual_posSemidef (hG : G.PosSemidef) (S : Matrix (Fin k) (Fin k) ℝ) :
    (popDual G S).PosSemidef := by
  have h := hG.conjTranspose_mul_mul_same (CFC.sqrt S)
  rwa [conjTranspose_sqrt] at h

/-- The population dual `K(Σ)` is positive definite whenever both the loading Gram limit `G_B` and
the candidate covariance `Σ` are. -/
theorem popDual_posDef (hG : G.PosDef) (hS : S.PosDef) : (popDual G S).PosDef := by
  have h := hG.conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_of_isUnit (isUnit_sqrt hS))
  rwa [conjTranspose_sqrt] at h

/-! ### Admissibility -/

/-- A symmetric positive definite `Σ` is **admissible** for the population eigenvalues `μ` when
its population dual `K(Σ)` has eigenvalues `μ`.

Having eigenvalues `μ` is recorded as being conjugate to `Λ = diagonal μ` by an orthogonal
matrix, which is what it means for a real symmetric matrix; the witness is exactly the `V` that
`PCError.systematicDual` consumes. The intended `μ` satisfies `μ 0 > ⋯ > μ (k-1) > 0`, but that
is a hypothesis on the ambient data, not part of admissibility of `Σ`. -/
@[pcerror "def_admissible"]
structure Admissible (G : Matrix (Fin k) (Fin k) ℝ) (μ : Fin k → ℝ)
    (S : Matrix (Fin k) (Fin k) ℝ) : Prop where
  /-- An admissible candidate covariance is symmetric positive definite. -/
  posDef : S.PosDef
  /-- Its population dual is carried to `Λ = diagonal μ` by an orthogonal matrix. -/
  exists_orthogonal_conj :
    ∃ V ∈ Matrix.orthogonalGroup (Fin k) ℝ, Vᵀ * popDual G S * V = Matrix.diagonal μ

/-- The spectral decomposition of the population dual of an admissible covariance. -/
theorem Admissible.exists_popDual_eq_conj (h : Admissible G μ S) :
    ∃ V ∈ Matrix.orthogonalGroup (Fin k) ℝ, popDual G S = V * Matrix.diagonal μ * Vᵀ := by
  obtain ⟨V, hV, hdiag⟩ := h.exists_orthogonal_conj
  refine ⟨V, hV, ?_⟩
  have h1 : V * Vᵀ = 1 := (Matrix.mem_orthogonalGroup_iff _ _).mp hV
  rw [← hdiag, show V * (Vᵀ * popDual G S * V) * Vᵀ = V * Vᵀ * popDual G S * (V * Vᵀ) by
    noncomm_ring, h1, one_mul, mul_one]

/-! ### The candidate covariance attached to an orthogonal matrix -/

/-- The candidate factor covariance `Σ_O := G_B^{-1/2} Oᵀ Λ O G_B^{-1/2}` attached to an
orthogonal matrix `O`, where `Λ = diagonal μ`. -/
@[pcerror "def_Sigma_O"]
noncomputable def candidateCov (G : Matrix (Fin k) (Fin k) ℝ) (μ : Fin k → ℝ)
    (O : Matrix (Fin k) (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  (CFC.sqrt G)⁻¹ * Oᵀ * Matrix.diagonal μ * O * (CFC.sqrt G)⁻¹

/-- `Σ_O` written as a congruence of `Λ` by `O G_B^{-1/2}`. -/
theorem candidateCov_eq_conj (G : Matrix (Fin k) (Fin k) ℝ) (μ : Fin k → ℝ)
    (O : Matrix (Fin k) (Fin k) ℝ) :
    candidateCov G μ O =
      (O * (CFC.sqrt G)⁻¹)ᵀ * Matrix.diagonal μ * (O * (CFC.sqrt G)⁻¹) := by
  simp only [candidateCov, Matrix.transpose_mul, transpose_sqrt_inv, Matrix.mul_assoc]

/-- The candidate covariance `Σ_O` is symmetric. -/
theorem candidateCov_isHermitian (G : Matrix (Fin k) (Fin k) ℝ) (μ : Fin k → ℝ)
    (O : Matrix (Fin k) (Fin k) ℝ) : (candidateCov G μ O).IsHermitian := by
  change (candidateCov G μ O)ᴴ = candidateCov G μ O
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  simp only [candidateCov, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.diagonal_transpose, transpose_sqrt_inv, Matrix.mul_assoc]

/-- The candidate covariance `Σ_O` is positive semidefinite whenever the eigenvalues `μ` are
nonnegative. -/
theorem candidateCov_posSemidef (G : Matrix (Fin k) (Fin k) ℝ) {μ : Fin k → ℝ}
    (hμ : ∀ j, 0 ≤ μ j) (O : Matrix (Fin k) (Fin k) ℝ) :
    (candidateCov G μ O).PosSemidef := by
  have h := (Matrix.posSemidef_diagonal_iff.mpr hμ).conjTranspose_mul_mul_same
    (O * (CFC.sqrt G)⁻¹)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  rwa [candidateCov_eq_conj]

/-- The candidate covariance `Σ_O` is positive definite whenever the loading Gram limit `G_B` is
positive definite, the eigenvalues `μ` are positive and `O` is orthogonal. -/
theorem candidateCov_posDef (hG : G.PosDef) (hμ : ∀ j, 0 < μ j)
    (hO : O ∈ Matrix.orthogonalGroup (Fin k) ℝ) : (candidateCov G μ O).PosDef := by
  have hunit : IsUnit (O * (CFC.sqrt G)⁻¹) :=
    (IsUnit.of_mul_eq_one Oᵀ ((Matrix.mem_orthogonalGroup_iff _ _).mp hO)).mul
      (Matrix.isUnit_nonsing_inv_iff.mpr (isUnit_sqrt hG))
  have h := (Matrix.PosDef.diagonal hμ).conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_of_isUnit hunit)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  rwa [candidateCov_eq_conj]

/-! ### The factor-covariance-free dual -/

/-- The **factor-covariance-free dual** `M̂ := G_B^{1/2}(FFᵀ/n)G_B^{1/2}`, where `n` is the
number of columns of the factor path `F`. -/
@[pcerror "def_Mhat"]
noncomputable def covFreeDual (G : Matrix (Fin k) (Fin k) ℝ) (F : Matrix (Fin k) (Fin n) ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  CFC.sqrt G * ((n : ℝ)⁻¹ • (F * Fᵀ)) * CFC.sqrt G

/-- The factor-covariance-free dual `M̂` is positive semidefinite. -/
theorem covFreeDual_posSemidef (G : Matrix (Fin k) (Fin k) ℝ) (F : Matrix (Fin k) (Fin n) ℝ) :
    (covFreeDual G F).PosSemidef := by
  have h := (posSemidef_scaledGram F).conjTranspose_mul_mul_same (CFC.sqrt G)
  rwa [conjTranspose_sqrt] at h

/-- The factor-covariance-free dual `M̂` is symmetric. -/
theorem covFreeDual_isHermitian (G : Matrix (Fin k) (Fin k) ℝ) (F : Matrix (Fin k) (Fin n) ℝ) :
    (covFreeDual G F).IsHermitian :=
  (covFreeDual_posSemidef G F).isHermitian

/-! ### The systematic dual attached to a candidate covariance -/

/-- The **systematic dual** `N(Σ, V) := Λ^{1/2}Vᵀ Σ^{-1/2}(FFᵀ/n)Σ^{-1/2}V Λ^{1/2}` attached to
a candidate factor covariance `Σ` together with an orthogonal `V` diagonalising `K(Σ)`, where
`Λ = diagonal μ`.

It is the intended object only when `Σ` is `PCError.Admissible` for `μ` and `V` witnesses
`PCError.Admissible.exists_orthogonal_conj`; nothing here presupposes that. -/
@[pcerror "def_N_of_Sigma"]
noncomputable def systematicDual (μ : Fin k → ℝ) (F : Matrix (Fin k) (Fin n) ℝ)
    (S V : Matrix (Fin k) (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.diagonal (fun j => √(μ j)) * Vᵀ * (CFC.sqrt S)⁻¹ * ((n : ℝ)⁻¹ • (F * Fᵀ)) *
    ((CFC.sqrt S)⁻¹ * V * Matrix.diagonal fun j => √(μ j))

/-- `N(Σ, V) = T (FFᵀ/n) Tᵀ` for `T := Λ^{1/2}Vᵀ Σ^{-1/2}`. -/
theorem systematicDual_eq_mul_mul_transpose (μ : Fin k → ℝ) (F : Matrix (Fin k) (Fin n) ℝ)
    (S V : Matrix (Fin k) (Fin k) ℝ) :
    systematicDual μ F S V =
      (Matrix.diagonal (fun j => √(μ j)) * Vᵀ * (CFC.sqrt S)⁻¹) * ((n : ℝ)⁻¹ • (F * Fᵀ)) *
        (Matrix.diagonal (fun j => √(μ j)) * Vᵀ * (CFC.sqrt S)⁻¹)ᵀ := by
  simp only [systematicDual, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.diagonal_transpose, transpose_sqrt_inv, Matrix.mul_assoc]

/-- The systematic dual `N(Σ, V)` is positive semidefinite. -/
theorem systematicDual_posSemidef (μ : Fin k → ℝ) (F : Matrix (Fin k) (Fin n) ℝ)
    (S V : Matrix (Fin k) (Fin k) ℝ) : (systematicDual μ F S V).PosSemidef := by
  have h := (posSemidef_scaledGram F).conjTranspose_mul_mul_same
    ((Matrix.diagonal (fun j => √(μ j)) * Vᵀ * (CFC.sqrt S)⁻¹)ᵀ)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] at h
  rwa [systematicDual_eq_mul_mul_transpose]

/-- The systematic dual `N(Σ, V)` is symmetric. -/
theorem systematicDual_isHermitian (μ : Fin k → ℝ) (F : Matrix (Fin k) (Fin n) ℝ)
    (S V : Matrix (Fin k) (Fin k) ℝ) : (systematicDual μ F S V).IsHermitian :=
  (systematicDual_posSemidef μ F S V).isHermitian

end PCError

end
