/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import PCError.Attr
public import PCError.Defs.Angles
public import PCError.Defs.TheFactorModelAndItsDerivedMatrices
public import PCError.Defs.TheRotationErrorIsNotEstimable
public import PCError.MatrixPreliminaries

/-!
# The rotation error is not estimable

The population spectrum `μ₁ > ⋯ > μₖ > 0` pins the candidate factor covariance `Σ` only up to
an orthogonal conjugation, and conjugation moves the eigenframe of the systematic dual over a
whole orbit.  Everything the data determine — the data matrix, the systematic eigenvalues
`λ₁ > ⋯ > λₖ`, the out-of-subspace floor — is the same for every admissible `Σ`, while the
in-subspace rotation `sin²∠(νⱼ, eⱼ)` takes *every* value in `[0,1]`.

## Main statements

* `PCError.exists_mem_orthogonalGroup_mulVec_eq`: the orthogonal group is transitive on the unit
  sphere of `ℝ^k`.
* `PCError.exists_mem_orthogonalGroup_eq_candidateCov_of_conj`,
  `PCError.admissible_iff_exists_eq_candidateCov`: *the admissible set is a single orthogonal
  orbit* — a covariance `Σ` is admissible if and only if `Σ = Σ_O` for some `O ∈ O(k)`.
* `PCError.admissible_candidateCov`,
  `PCError.exists_mem_orthogonalGroup_conj_popDual_and_systematicDual_eq`: *the systematic dual
  is an orthogonal conjugate of the covariance-free dual* — `Σ_O` is admissible, and for a
  suitable `V ∈ O(k)` diagonalising `K(Σ_O)` one has `N(Σ_O, V) = O M̂ Oᵀ`.
* `PCError.FactorModelSeq.mem_spectrum_covFreeDual_iff`,
  `PCError.FactorModelSeq.hasPosEigenvalues_covFreeDual`: *the spectrum of the
  covariance-free dual* — `M̂` and `W₀` share their nonzero spectrum, so `M̂` has the `k`
  distinct positive eigenvalues `λ₁ > ⋯ > λₖ`.
* `PCError.FactorModelSeq.dataMatrix_eq_B_mul_F_add_noiseMatrix`,
  `PCError.FactorModelSeq.eq_of_hasPosEigenvalues_dualGramLim₀`,
  `PCError.FactorModelSeq.δsq_div_eq_of_hasPosEigenvalues_dualGramLim₀`: *the data do not vary
  with the factor covariance*.
* `PCError.FactorModelSeq.exists_admissible_sinSqAngle_eq`: *the rotation error attains every
  value* in `[0,1]`.
* `PCError.FactorModelSeq.exists_admissible_errorLimit_eq`: *the limiting estimation error
  attains every value above the floor*.

## Implementation notes

The whole argument is finite-dimensional linear algebra, and it is carried out by the two Gram
products of `A := G_B^{1/2}Σ^{1/2}`: `AᵀA = K(Σ)` is the population dual and
`AAᵀ = G_B^{1/2}ΣG_B^{1/2}`.  Where the source argues through *spectra* ("a symmetric matrix has
eigenvalues `μ₁,…,μₖ` if and only if it is orthogonally similar to `Λ`", "`AAᵀ` and `AᵀA` have
the same nonzero eigenvalues, and both are positive definite, so their spectra coincide"), the
formalisation carries the same two steps out as explicit congruences, which is what
`PCError.Admissible` records:

* from a `V ∈ O(k)` with `VᵀK(Σ)V = Λ` the matrix `O := (A V Λ^{-1/2})ᵀ` is orthogonal and
  `G_B^{1/2}ΣG_B^{1/2} = Oᵀ Λ O`, whence `Σ = Σ_O`;
* from `G_B^{1/2}Σ_O G_B^{1/2} = Oᵀ Λ O` the matrix `V := Aᵀ Oᵀ Λ^{-1/2}` — the one whose
  columns Gram duality attaches to the eigenvectors `Oᵀeⱼ` of `AAᵀ` — is orthogonal and
  `VᵀK(Σ_O)V = Λ`.

Both are the source's constructions, with the eigenvector bookkeeping replaced by the matrix
identity it amounts to; in particular no distinctness of the `μⱼ` is needed, only `μⱼ > 0`.

The hypotheses are the minimal ones the algebra uses — `G_B` positive definite, `μⱼ > 0`, and
for the spectrum of `M̂` the eigenvalue listing of `W₀` — rather than the whole of
`PCError.AsymptoticHypotheses`, which supplies them.

`PCError.FactorModelSeq.dataMatrix_eq_B_mul_F_add_noiseMatrix`,
`PCError.FactorModelSeq.eq_of_hasPosEigenvalues_dualGramLim₀` and
`PCError.FactorModelSeq.δsq_div_eq_of_hasPosEigenvalues_dualGramLim₀` are the three clauses of
the source's invariance theorem: they exhibit each of the three quantities as a function of data
in which no factor covariance occurs.  The factor covariance is *not* an argument of any of
them, which is exactly the content: the second clause needs the observation that
`HasPosEigenvalues` determines its eigenvalue family uniquely, since otherwise "the eigenvalues
are the same" would say nothing.
-/

@[expose] public section

namespace PCError

open Matrix

open scoped MatrixOrder RealInnerProductSpace

variable {k n : ℕ} {G S V O : Matrix (Fin k) (Fin k) ℝ} {μ : Fin k → ℝ}

/-! ### Facts about `CFC.sqrt` and about diagonal square roots

These repeat, for the present file, the private facts of
`PCError.Defs.TheRotationErrorIsNotEstimable`: that `Σ^{1/2}` is symmetric, squares to
`Σ`, and is invertible when `Σ` is. -/

private theorem sqrt_mul_sqrt_self (hS : S.PosSemidef) : CFC.sqrt S * CFC.sqrt S = S :=
  CFC.sqrt_mul_sqrt_self S (ha := Matrix.nonneg_iff_posSemidef.2 hS)

private theorem isUnit_det_sqrt (hS : S.PosDef) : IsUnit (CFC.sqrt S).det :=
  (Matrix.isUnit_iff_isUnit_det _).1 (isUnit_sqrt hS)

private theorem inv_sqrt_mul_sqrt (hS : S.PosDef) : (CFC.sqrt S)⁻¹ * CFC.sqrt S = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_det_sqrt hS)

private theorem sqrt_mul_inv_sqrt (hS : S.PosDef) : CFC.sqrt S * (CFC.sqrt S)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (isUnit_det_sqrt hS)

private theorem diagonal_sqrt_mul_diagonal_sqrt (hμ : ∀ j, 0 ≤ μ j) :
    (Matrix.diagonal fun j => √(μ j)) * (Matrix.diagonal fun j => √(μ j))
      = Matrix.diagonal μ := by
  simp [Matrix.diagonal_mul_diagonal, Real.mul_self_sqrt (hμ _)]

private theorem diagonal_inv_sqrt_mul_diagonal_sqrt (hμ : ∀ j, 0 < μ j) :
    (Matrix.diagonal fun j => (√(μ j))⁻¹) * (Matrix.diagonal fun j => √(μ j)) = 1 := by
  simp [Matrix.diagonal_mul_diagonal, inv_mul_cancel₀ (Real.sqrt_ne_zero'.2 (hμ _))]

private theorem diagonal_sqrt_mul_diagonal_inv_sqrt (hμ : ∀ j, 0 < μ j) :
    (Matrix.diagonal fun j => √(μ j)) * (Matrix.diagonal fun j => (√(μ j))⁻¹) = 1 := by
  simp [Matrix.diagonal_mul_diagonal, mul_inv_cancel₀ (Real.sqrt_ne_zero'.2 (hμ _))]

/-! ### The orthogonal group is transitive on the unit sphere -/

/-- A unit vector `y` of `ℝ^k` is carried to the `i₀`-th coordinate axis by the transpose of an
orthogonal matrix: extend `y` to an orthonormal basis and take the matrix of its columns. -/
private theorem exists_mem_orthogonalGroup_transpose_mulVec_eq_single (i₀ : Fin k)
    {y : EuclideanSpace ℝ (Fin k)} (hy : ‖y‖ = 1) :
    ∃ P ∈ Matrix.orthogonalGroup (Fin k) ℝ,
      Pᵀ *ᵥ y = (EuclideanSpace.single i₀ (1 : ℝ)).ofLp := by
  have hone : Orthonormal ℝ (Set.domRestrict ({i₀} : Set (Fin k)) (fun _ : Fin k => y)) := by
    rw [orthonormal_iff_ite]
    intro i j
    obtain rfl : i = j := Subtype.ext (i.2.trans j.2.symm)
    simp [Set.domRestrict_apply, hy]
  obtain ⟨b, hb⟩ :=
    Orthonormal.exists_orthonormalBasis_extension_of_card_eq (by simp) hone
  refine ⟨Matrix.of fun i j => (b j).ofLp i, ?_, ?_⟩
  · have hmat : (Matrix.of fun i j => (b j).ofLp i)
        = (EuclideanSpace.basisFun (Fin k) ℝ).toBasis.toMatrix b := by
      ext i j
      simp [Module.Basis.toMatrix_apply]
    rw [hmat]
    exact (EuclideanSpace.basisFun (Fin k) ℝ).toMatrix_orthonormalBasis_mem_orthogonal b
  · funext i
    have h : ((Matrix.of fun i j => (b j).ofLp i)ᵀ *ᵥ y.ofLp) i = ⟪b i, y⟫ := by
      simp [inner_eq_dotProduct, Matrix.mulVec, dotProduct]
    rw [h, ← hb i₀ rfl, (orthonormal_iff_ite.1 b.orthonormal) i i₀]
    simp

/-- **The orthogonal group is transitive on the unit sphere**: for unit vectors `ω, x ∈ ℝ^k`
there is an `O ∈ O(k)` with `Oω = x`.

Both vectors are extended to orthonormal bases; the matrices `P` and `Q` of those bases are
orthogonal, `Pᵀω` and `Qᵀx` are the same coordinate axis, and `O := QPᵀ` does it. -/
@[pcerror "lem_orbit_sphere"]
theorem exists_mem_orthogonalGroup_mulVec_eq {ω x : EuclideanSpace ℝ (Fin k)} (hω : ‖ω‖ = 1)
    (hx : ‖x‖ = 1) : ∃ O ∈ Matrix.orthogonalGroup (Fin k) ℝ, O *ᵥ ω = x := by
  obtain ⟨i₀⟩ : Nonempty (Fin k) := not_isEmpty_iff.1 fun _ => by
    simp [EuclideanSpace.norm_eq] at hω
  obtain ⟨P, hP, hPω⟩ := exists_mem_orthogonalGroup_transpose_mulVec_eq_single i₀ hω
  obtain ⟨Q, hQ, hQx⟩ := exists_mem_orthogonalGroup_transpose_mulVec_eq_single i₀ hx
  have hQQt : Q * Qᵀ = 1 := (Matrix.mem_orthogonalGroup_iff _ _).1 hQ
  refine ⟨Q * Pᵀ, ?_, ?_⟩
  · rw [Matrix.mem_orthogonalGroup_iff, Matrix.transpose_mul, Matrix.transpose_transpose,
      show Q * Pᵀ * (P * Qᵀ) = Q * (Pᵀ * P) * Qᵀ by simp only [Matrix.mul_assoc],
      (Matrix.mem_orthogonalGroup_iff' _ _).1 hP, Matrix.mul_one, hQQt]
  · rw [← Matrix.mulVec_mulVec, hPω, ← hQx, Matrix.mulVec_mulVec, hQQt, Matrix.one_mulVec]

/-! ### The two congruences behind the orbit description

Both directions of `PCError.admissible_iff_exists_eq_candidateCov` are one algebraic
identity about an invertible `A` and the square root `Λ^{1/2}` of `Λ`, stated here for abstract
matrices `L = Λ`, `Lh = Λ^{1/2}` and `Li = Λ^{-1/2}`. -/

/-- From an orthogonal `O` with `AAᵀ = Oᵀ L O`, the matrix `V := Aᵀ Oᵀ Li` is orthogonal, carries
`AᵀA` to `L`, and satisfies `Lh Vᵀ = O A`. -/
private theorem orthogonal_conj_of_mul_transpose_eq {A L Lh Li O : Matrix (Fin k) (Fin k) ℝ}
    (hLh : Lh * Lh = L) (hiL : Li * Lh = 1) (hiR : Lh * Li = 1) (hLit : Liᵀ = Li)
    (hOOt : O * Oᵀ = 1) (hAAt : A * Aᵀ = Oᵀ * L * O) :
    (Aᵀ * Oᵀ * Li)ᵀ * (Aᵀ * Oᵀ * Li) = 1 ∧
      (Aᵀ * Oᵀ * Li)ᵀ * (Aᵀ * A) * (Aᵀ * Oᵀ * Li) = L ∧
      Lh * (Aᵀ * Oᵀ * Li)ᵀ = O * A := by
  have hVt : (Aᵀ * Oᵀ * Li)ᵀ = Li * O * A := by
    simp only [Matrix.transpose_mul, hLit, Matrix.transpose_transpose, Matrix.mul_assoc]
  grind

/-- From an orthogonal `V` carrying `AᵀA` to `L`, the matrix `B := A V Li` has orthogonal
transpose and satisfies `B L Bᵀ = AAᵀ`. -/
private theorem orthogonal_conj_of_transpose_mul_eq {A L Lh Li V : Matrix (Fin k) (Fin k) ℝ}
    (hLh : Lh * Lh = L) (hiL : Li * Lh = 1) (hiR : Lh * Li = 1) (hLit : Liᵀ = Li)
    (hVVt : V * Vᵀ = 1) (hconj : Vᵀ * (Aᵀ * A) * V = L) :
    (A * V * Li)ᵀ * (A * V * Li) = 1 ∧ (A * V * Li) * L * (A * V * Li)ᵀ = A * Aᵀ := by
  have hLiL : Li * L * Li = 1 := by grind
  have hBt : (A * V * Li)ᵀ = Li * Vᵀ * Aᵀ := by
    simp only [Matrix.transpose_mul, hLit, Matrix.mul_assoc]
  rw [hBt]
  grind

/-! ### The two Gram products of `A = G_B^{1/2}Σ^{1/2}` -/

/-- `AᵀA = K(Σ)` for `A := G_B^{1/2}Σ^{1/2}`. -/
private theorem transpose_mul_self_eq_popDual (hG : G.PosSemidef) :
    (CFC.sqrt G * CFC.sqrt S)ᵀ * (CFC.sqrt G * CFC.sqrt S) = popDual G S := by
  have hGG := sqrt_mul_sqrt_self hG
  rw [Matrix.transpose_mul, transpose_sqrt, transpose_sqrt, popDual]
  grind

/-- `AAᵀ = G_B^{1/2}ΣG_B^{1/2}` for `A := G_B^{1/2}Σ^{1/2}`. -/
private theorem mul_transpose_self_eq_sqrt_mul_mul_sqrt (hS : S.PosSemidef) :
    (CFC.sqrt G * CFC.sqrt S) * (CFC.sqrt G * CFC.sqrt S)ᵀ = CFC.sqrt G * S * CFC.sqrt G := by
  have hSS := sqrt_mul_sqrt_self hS
  rw [Matrix.transpose_mul, transpose_sqrt, transpose_sqrt]
  grind

/-- `G_B^{1/2}Σ_O G_B^{1/2} = OᵀΛO`: the candidate covariance attached to `O` is the one whose
congruence by `G_B^{1/2}` is `OᵀΛO`. -/
private theorem sqrt_mul_candidateCov_mul_sqrt (hG : G.PosDef) :
    CFC.sqrt G * candidateCov G μ O * CFC.sqrt G = Oᵀ * Matrix.diagonal μ * O := by
  have hGi := sqrt_mul_inv_sqrt hG
  have hiG := inv_sqrt_mul_sqrt hG
  rw [candidateCov]
  grind

/-! ### The systematic dual attached to `Σ_O` -/

/-- The whole content of `PCError.admissible_candidateCov` and of
`PCError.exists_mem_orthogonalGroup_conj_popDual_and_systematicDual_eq`: the `V` of the source,
namely `V := (G_B^{1/2}Σ_O^{1/2})ᵀ Oᵀ Λ^{-1/2}`, is orthogonal, carries `K(Σ_O)` to `Λ`, and
turns the prefactor `Λ^{1/2}VᵀΣ_O^{-1/2}` of the systematic dual into `O G_B^{1/2}`. -/
private theorem exists_mem_orthogonalGroup_conj_popDual_and_prefactor_eq (hG : G.PosDef)
    (hμ : ∀ j, 0 < μ j) (hO : O ∈ Matrix.orthogonalGroup (Fin k) ℝ) :
    ∃ V ∈ Matrix.orthogonalGroup (Fin k) ℝ,
      Vᵀ * popDual G (candidateCov G μ O) * V = Matrix.diagonal μ ∧
      Matrix.diagonal (fun j => √(μ j)) * Vᵀ * (CFC.sqrt (candidateCov G μ O))⁻¹
        = O * CFC.sqrt G := by
  have hS : (candidateCov G μ O).PosDef := candidateCov_posDef hG hμ hO
  have hAAt : (CFC.sqrt G * CFC.sqrt (candidateCov G μ O))
      * (CFC.sqrt G * CFC.sqrt (candidateCov G μ O))ᵀ = Oᵀ * Matrix.diagonal μ * O := by
    rw [mul_transpose_self_eq_sqrt_mul_mul_sqrt hS.posSemidef, sqrt_mul_candidateCov_mul_sqrt hG]
  obtain ⟨h1, h2, h3⟩ := orthogonal_conj_of_mul_transpose_eq
    (diagonal_sqrt_mul_diagonal_sqrt fun j => (hμ j).le)
    (diagonal_inv_sqrt_mul_diagonal_sqrt hμ) (diagonal_sqrt_mul_diagonal_inv_sqrt hμ)
    (Matrix.diagonal_transpose _) ((Matrix.mem_orthogonalGroup_iff _ _).1 hO) hAAt
  refine ⟨_, (Matrix.mem_orthogonalGroup_iff' _ _).2 h1, ?_, ?_⟩
  · rwa [← transpose_mul_self_eq_popDual hG.posSemidef]
  · have hSi := sqrt_mul_inv_sqrt hS
    rw [h3]
    grind

/-- **The candidate covariance attached to an orthogonal matrix is admissible**: `Σ_O` is
symmetric positive definite and `K(Σ_O)` is carried to `Λ` by an orthogonal matrix. -/
@[pcerror "lem_N_conjugate"]
theorem admissible_candidateCov (hG : G.PosDef) (hμ : ∀ j, 0 < μ j)
    (hO : O ∈ Matrix.orthogonalGroup (Fin k) ℝ) : Admissible G μ (candidateCov G μ O) where
  posDef := candidateCov_posDef hG hμ hO
  exists_orthogonal_conj := by
    obtain ⟨V, hV, hVK, -⟩ := exists_mem_orthogonalGroup_conj_popDual_and_prefactor_eq hG hμ hO
    exact ⟨V, hV, hVK⟩

/-- **The systematic dual is an orthogonal conjugate of the covariance-free dual**: for
`O ∈ O(k)` there is a `V ∈ O(k)` with `VᵀK(Σ_O)V = Λ` and `N(Σ_O, V) = O M̂ Oᵀ`.

With `A := G_B^{1/2}Σ_O^{1/2}` and `V := AᵀOᵀΛ^{-1/2}` the prefactor of the systematic dual is
`Λ^{1/2}VᵀΣ_O^{-1/2} = O A Σ_O^{-1/2} = O G_B^{1/2}`, and `N(Σ_O, V)` is the congruence of
`FFᵀ/n` by it. -/
@[pcerror "lem_N_conjugate"]
theorem exists_mem_orthogonalGroup_conj_popDual_and_systematicDual_eq (hG : G.PosDef)
    (hμ : ∀ j, 0 < μ j) (hO : O ∈ Matrix.orthogonalGroup (Fin k) ℝ)
    (F : Matrix (Fin k) (Fin n) ℝ) :
    ∃ V ∈ Matrix.orthogonalGroup (Fin k) ℝ,
      Vᵀ * popDual G (candidateCov G μ O) * V = Matrix.diagonal μ ∧
      systematicDual μ F (candidateCov G μ O) V = O * covFreeDual G F * Oᵀ := by
  obtain ⟨V, hV, hVK, hT⟩ := exists_mem_orthogonalGroup_conj_popDual_and_prefactor_eq hG hμ hO
  refine ⟨V, hV, hVK, ?_⟩
  rw [systematicDual_eq_mul_mul_transpose, hT, covFreeDual, Matrix.transpose_mul, transpose_sqrt]
  simp only [Matrix.mul_assoc]

/-! ### The admissible set is a single orthogonal orbit -/

/-- **A diagonalisable covariance lies on the orthogonal orbit**: if `V ∈ O(k)` carries the
population dual `K(Σ)` of a positive semidefinite `Σ` to `Λ`, then `Σ = Σ_O` for an orthogonal
`O`.

With `A := G_B^{1/2}Σ^{1/2}`, so that `K(Σ) = AᵀA`, the matrix `B := A V Λ^{-1/2}` has orthogonal
transpose and `B Λ Bᵀ = AAᵀ = G_B^{1/2}ΣG_B^{1/2}`, whence `Σ = Σ_{Bᵀ}`. -/
theorem exists_mem_orthogonalGroup_eq_candidateCov_of_conj (hG : G.PosDef) (hμ : ∀ j, 0 < μ j)
    (hS : S.PosSemidef) (hV : V ∈ Matrix.orthogonalGroup (Fin k) ℝ)
    (hVK : Vᵀ * popDual G S * V = Matrix.diagonal μ) :
    ∃ O ∈ Matrix.orthogonalGroup (Fin k) ℝ, S = candidateCov G μ O := by
  have hconj : Vᵀ * ((CFC.sqrt G * CFC.sqrt S)ᵀ * (CFC.sqrt G * CFC.sqrt S)) * V
      = Matrix.diagonal μ := by
    rwa [transpose_mul_self_eq_popDual hG.posSemidef]
  obtain ⟨h1, h2⟩ := orthogonal_conj_of_transpose_mul_eq
    (diagonal_sqrt_mul_diagonal_sqrt fun j => (hμ j).le)
    (diagonal_inv_sqrt_mul_diagonal_sqrt hμ) (diagonal_sqrt_mul_diagonal_inv_sqrt hμ)
    (Matrix.diagonal_transpose _) ((Matrix.mem_orthogonalGroup_iff _ _).1 hV) hconj
  refine ⟨_, (Matrix.mem_orthogonalGroup_iff _ _).2 (by rwa [Matrix.transpose_transpose]), ?_⟩
  have hcancel : (CFC.sqrt G)⁻¹ * (CFC.sqrt G * S * CFC.sqrt G) * (CFC.sqrt G)⁻¹ = S := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, sqrt_mul_inv_sqrt hG, Matrix.mul_one,
      ← Matrix.mul_assoc, inv_sqrt_mul_sqrt hG, Matrix.one_mul]
  rw [candidateCov, Matrix.transpose_transpose]
  refine hcancel.symm.trans ?_
  rw [← mul_transpose_self_eq_sqrt_mul_mul_sqrt hS, ← h2]
  simp only [Matrix.mul_assoc]

/-- **The admissible set is a single orthogonal orbit**: a covariance `Σ` is admissible if and
only if `Σ = Σ_O` for some `O ∈ O(k)`.

If `V ∈ O(k)` carries `K(Σ) = AᵀA` to `Λ`, then `B := A V Λ^{-1/2}` has orthogonal transpose
and `B Λ Bᵀ = AAᵀ = G_B^{1/2}ΣG_B^{1/2}`, so `Σ = Σ_{Bᵀ}`; the converse is
`PCError.admissible_candidateCov`. -/
@[pcerror "lem_admissible_orbit"]
theorem admissible_iff_exists_eq_candidateCov (hG : G.PosDef) (hμ : ∀ j, 0 < μ j) :
    Admissible G μ S ↔ ∃ O ∈ Matrix.orthogonalGroup (Fin k) ℝ, S = candidateCov G μ O := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨V, hV, hVK⟩ := h.exists_orthogonal_conj
    exact exists_mem_orthogonalGroup_eq_candidateCov_of_conj hG hμ h.posDef.posSemidef hV hVK
  · rintro ⟨O, hO, rfl⟩
    exact admissible_candidateCov hG hμ hO

/-! ### A unit vector at a prescribed angle to a coordinate axis -/

/-- For `k ≥ 2` and `t ∈ [0,1]` the vector `√(1-t) eⱼ + √t eₘ`, for any `m ≠ j`, is a unit
vector at squared sine `t` from `eⱼ`. -/
private theorem exists_norm_eq_one_sinSqAngle_eq (hk : 2 ≤ k) (j : Fin k) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : ∃ x : EuclideanSpace ℝ (Fin k), ‖x‖ = 1 ∧
      sinSqAngle x (EuclideanSpace.single j (1 : ℝ)) = t := by
  have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.2 hk
  obtain ⟨m, hm⟩ := exists_ne j
  set x : EuclideanSpace ℝ (Fin k) :=
    EuclideanSpace.single j (√(1 - t)) + EuclideanSpace.single m (√t) with hx
  have h1t : (0 : ℝ) ≤ 1 - t := by linarith
  have hinner : ⟪x, EuclideanSpace.single j (1 : ℝ)⟫ = √(1 - t) := by
    simp [hx, inner_add_left, EuclideanSpace.inner_single_left, hm]
  have hsq : ‖x‖ ^ 2 = 1 := by
    rw [hx, norm_add_sq_real]
    simp [EuclideanSpace.inner_single_left, Ne.symm hm, sq_abs, Real.sq_sqrt, h1t, ht0]
  have hnorm : ‖x‖ = 1 := by nlinarith [norm_nonneg x, hsq]
  exact ⟨x, hnorm, by simp [sinSqAngle, hinner, hnorm, Real.sq_sqrt h1t]⟩

/-- A real number in the spectrum of a square real matrix has a *unit* eigenvector at it. -/
theorem exists_norm_eq_one_mulVec_eq_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} {c : ℝ} (h : c ∈ spectrum ℝ A) :
    ∃ v : EuclideanSpace ℝ ι, ‖v‖ = 1 ∧ A *ᵥ v = c • v := by
  obtain ⟨w, hw0, hw⟩ := mem_spectrum_iff_exists_mulVec_eq_smul.1 h
  have hu0 : ‖(WithLp.toLp 2 w : EuclideanSpace ℝ ι)‖ ≠ 0 :=
    norm_ne_zero_iff.2 fun h0 => hw0 (by simpa using congrArg WithLp.ofLp h0)
  refine ⟨‖(WithLp.toLp 2 w : EuclideanSpace ℝ ι)‖⁻¹ • WithLp.toLp 2 w, ?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hu0]
  · change A *ᵥ (‖(WithLp.toLp 2 w : EuclideanSpace ℝ ι)‖⁻¹ • w)
      = c • ‖(WithLp.toLp 2 w : EuclideanSpace ℝ ι)‖⁻¹ • w
    rw [Matrix.mulVec_smul, hw]
    exact smul_comm _ _ _

/-! ### The spectrum of the covariance-free dual, and the invariance of the data -/

namespace FactorModelSeq

variable {Ω : Type*} (M : FactorModelSeq Ω)

/-- `M̂ = AAᵀ` for `A := n^{-1/2}G_B^{1/2}F`. -/
private theorem covFreeDual_eq_mul_transpose {G : Matrix (Fin M.k) (Fin M.k) ℝ} :
    covFreeDual G M.F = ((Real.sqrt M.n)⁻¹ • (CFC.sqrt G * M.F)) *
      ((Real.sqrt M.n)⁻¹ • (CFC.sqrt G * M.F))ᵀ := by
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← mul_inv,
    Real.mul_self_sqrt (show (0 : ℝ) ≤ (M.n : ℝ) by positivity), Matrix.transpose_mul,
    transpose_sqrt, covFreeDual, Matrix.mul_smul, Matrix.smul_mul]
  simp only [Matrix.mul_assoc]

/-- `W₀ = AᵀA` for `A := n^{-1/2}G_B^{1/2}F`, using `G_B^{1/2}G_B^{1/2} = G_B`. -/
private theorem dualGramLim₀_eq_transpose_mul {G : Matrix (Fin M.k) (Fin M.k) ℝ}
    (hG : G.PosSemidef) :
    M.dualGramLim₀ G = ((Real.sqrt M.n)⁻¹ • (CFC.sqrt G * M.F))ᵀ *
      ((Real.sqrt M.n)⁻¹ • (CFC.sqrt G * M.F)) := by
  rw [dualGramLim₀, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← mul_inv,
    Real.mul_self_sqrt (show (0 : ℝ) ≤ (M.n : ℝ) by positivity), Matrix.transpose_mul,
    transpose_sqrt,
    show M.Fᵀ * CFC.sqrt G * (CFC.sqrt G * M.F) = M.Fᵀ * (CFC.sqrt G * CFC.sqrt G) * M.F by
      simp only [Matrix.mul_assoc], sqrt_mul_sqrt_self hG]

/-- **The spectrum of the covariance-free dual**: a nonzero real `λ` is an eigenvalue of
`M̂` if and only if it is an eigenvalue of `W₀`.

Both are the Gram products of `A = n^{-1/2}G_B^{1/2}F`, so this is
`PCError.mem_spectrum_mul_transpose_iff`. -/
@[pcerror "lem_Mhat_spectrum"]
theorem mem_spectrum_covFreeDual_iff {G : Matrix (Fin M.k) (Fin M.k) ℝ} (hG : G.PosSemidef)
    {lam : ℝ} (hlam : lam ≠ 0) :
    lam ∈ spectrum ℝ (covFreeDual G M.F) ↔ lam ∈ spectrum ℝ (M.dualGramLim₀ G) := by
  rw [M.covFreeDual_eq_mul_transpose, M.dualGramLim₀_eq_transpose_mul hG]
  exact mem_spectrum_mul_transpose_iff _ hlam

/-- **The covariance-free dual has the systematic eigenvalues**: `M̂` has the `k` distinct
positive eigenvalues `λ₁ > ⋯ > λₖ > 0` of the noiseless dual Gram limit `W₀`. -/
@[pcerror "lem_Mhat_spectrum"]
theorem hasPosEigenvalues_covFreeDual {G : Matrix (Fin M.k) (Fin M.k) ℝ} (hG : G.PosSemidef)
    {lam : Fin M.k → ℝ} (h : HasPosEigenvalues (M.dualGramLim₀ G) lam) :
    HasPosEigenvalues (covFreeDual G M.F) lam where
  strictAnti := h.strictAnti
  pos := h.pos
  spectrum_pos_eq := by
    rw [← h.spectrum_pos_eq]
    exact Set.ext fun x => and_congr_left fun hx => M.mem_spectrum_covFreeDual_iff hG hx.ne'

/-- **The data do not vary with the factor covariance**, first clause: the data matrix is
`Y⁽ᵖ⁾ = B⁽ᵖ⁾F + Z⁽ᵖ⁾`, an expression in the loadings, the factor path and the specific returns,
in which no factor covariance occurs. -/
@[pcerror "thm_data_invariant"]
theorem dataMatrix_eq_B_mul_F_add_noiseMatrix {p : ℕ} (hp : M.k ≤ p) (ω : Ω) :
    M.dataMatrix p ω = M.B p * M.F + M.noiseMatrix p ω := by
  rw [dataMatrix, M.B_mul_F p hp]

/-- **The data do not vary with the factor covariance**, second clause: the systematic
eigenvalues are determined by `W₀ = n⁻¹FᵀG_BF`, an expression in the factor path and the
loadings Gram limit, in which no factor covariance occurs.

Two strictly antitone families with the same range are equal, so the eigenvalue listing of `W₀`
is unique. -/
@[pcerror "thm_data_invariant"]
theorem eq_of_hasPosEigenvalues_dualGramLim₀ {G : Matrix (Fin M.k) (Fin M.k) ℝ}
    {lam lam' : Fin M.k → ℝ} (h : HasPosEigenvalues (M.dualGramLim₀ G) lam)
    (h' : HasPosEigenvalues (M.dualGramLim₀ G) lam') : lam = lam' :=
  funext fun j => OrderDual.toDual_inj.1 <| congrFun
    ((StrictMono.range_inj_of_wellFoundedLT h.strictAnti.dual_right h'.strictAnti.dual_right).1
      (by rw [Set.range_comp, Set.range_comp, ← h.spectrum_pos_eq, h'.spectrum_pos_eq])) j

/-- **The data do not vary with the factor covariance**, third clause: the out-of-subspace limit
`δ²/(nλⱼ+δ²)` is a function of `n`, `δ²` and `λⱼ` alone, hence also determined by `W₀`. -/
@[pcerror "thm_data_invariant"]
theorem δsq_div_eq_of_hasPosEigenvalues_dualGramLim₀ {G : Matrix (Fin M.k) (Fin M.k) ℝ}
    {lam lam' : Fin M.k → ℝ}
    (h : HasPosEigenvalues (M.dualGramLim₀ G) lam)
    (h' : HasPosEigenvalues (M.dualGramLim₀ G) lam') (j : Fin M.k) :
    M.δsq / ((M.n : ℝ) * lam j + M.δsq) = M.δsq / ((M.n : ℝ) * lam' j + M.δsq) := by
  rw [M.eq_of_hasPosEigenvalues_dualGramLim₀ h h']

/-! ### The rotation error attains every value -/

/-- **The rotation error attains every value**: for `k ≥ 2` and every `t ∈ [0,1]` there are an
admissible `Σ`, a `V ∈ O(k)` with `VᵀK(Σ)V = Λ`, and a unit eigenvector `ν` of `N(Σ, V)` at
`λⱼ` with `sin²∠(ν, eⱼ) = t`.

Let `ωⱼ` be a unit eigenvector of `M̂` at `λⱼ`, which exists by
`PCError.FactorModelSeq.hasPosEigenvalues_covFreeDual`, and let `x` be a unit vector with
`sin²∠(x, eⱼ) = t`.  An `O ∈ O(k)` carries `ωⱼ` to `x`, and then `Σ := Σ_O` and the `V` of
`PCError.exists_mem_orthogonalGroup_conj_popDual_and_systematicDual_eq` have
`N(Σ, V) = O M̂ Oᵀ`, for which `x = Oωⱼ` is a unit eigenvector at `λⱼ`. -/
@[pcerror "thm_rotation_surjective"]
theorem exists_admissible_sinSqAngle_eq (hk : 2 ≤ M.k) {G : Matrix (Fin M.k) (Fin M.k) ℝ}
    (hG : G.PosDef) {μ : Fin M.k → ℝ} (hμ : ∀ i, 0 < μ i) {lam : Fin M.k → ℝ}
    (hlam : HasPosEigenvalues (M.dualGramLim₀ G) lam) (j : Fin M.k) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    ∃ S, Admissible G μ S ∧ ∃ V ∈ Matrix.orthogonalGroup (Fin M.k) ℝ,
      Vᵀ * popDual G S * V = Matrix.diagonal μ ∧
      ∃ ν : EuclideanSpace ℝ (Fin M.k), ‖ν‖ = 1 ∧
        systematicDual μ M.F S V *ᵥ ν = lam j • ν ∧
        sinSqAngle ν (EuclideanSpace.single j (1 : ℝ)) = t := by
  obtain ⟨w, hw1, hw⟩ := exists_norm_eq_one_mulVec_eq_smul
    ((M.hasPosEigenvalues_covFreeDual hG.posSemidef hlam).mem_spectrum j)
  obtain ⟨x, hx1, hxangle⟩ := exists_norm_eq_one_sinSqAngle_eq hk j ht0 ht1
  obtain ⟨O, hO, hOw⟩ := exists_mem_orthogonalGroup_mulVec_eq hw1 hx1
  obtain ⟨V, hV, hVK, hN⟩ :=
    exists_mem_orthogonalGroup_conj_popDual_and_systematicDual_eq hG hμ hO M.F
  refine ⟨candidateCov G μ O, admissible_candidateCov hG hμ hO, V, hV, hVK, x, hx1, ?_, hxangle⟩
  have hcancel : Oᵀ *ᵥ (O *ᵥ w.ofLp) = w.ofLp := by
    rw [Matrix.mulVec_mulVec, (Matrix.mem_orthogonalGroup_iff' _ _).1 hO, Matrix.one_mulVec]
  rw [hN, ← hOw, ← Matrix.mulVec_mulVec, hcancel, ← Matrix.mulVec_mulVec, hw,
    Matrix.mulVec_smul]

/-! ### The limiting estimation error attains every value above the floor -/

/-- **The limiting estimation error attains every value above the floor**: for `k ≥ 2` and every
`s` with `δ²/(nλⱼ+δ²) ≤ s ≤ 1` there is an admissible `Σ` for which the limit of the error
decomposition, `δ²/(nλⱼ+δ²) + nλⱼ/(nλⱼ+δ²)·sin²∠(νⱼ, eⱼ)`, equals `s`.

The floor `α := δ²/(nλⱼ+δ²)` is the same for every admissible `Σ` by
`PCError.FactorModelSeq.δsq_div_eq_of_hasPosEigenvalues_dualGramLim₀`, and lies in `(0,1)`
because `λⱼ > 0` and `δ² > 0`; so `ρ ↦ α + (1-α)ρ` is a bijection of `[0,1]` onto `[α,1]`, and
the rotation `ρ` attains `(s-α)/(1-α)` by
`PCError.FactorModelSeq.exists_admissible_sinSqAngle_eq`. -/
@[pcerror "thm_error_range"]
theorem exists_admissible_errorLimit_eq (hk : 2 ≤ M.k) {G : Matrix (Fin M.k) (Fin M.k) ℝ}
    (hG : G.PosDef) {μ : Fin M.k → ℝ} (hμ : ∀ i, 0 < μ i) {lam : Fin M.k → ℝ}
    (hlam : HasPosEigenvalues (M.dualGramLim₀ G) lam) (j : Fin M.k) {s : ℝ}
    (hs0 : M.δsq / ((M.n : ℝ) * lam j + M.δsq) ≤ s) (hs1 : s ≤ 1) :
    ∃ S, Admissible G μ S ∧ ∃ V ∈ Matrix.orthogonalGroup (Fin M.k) ℝ,
      Vᵀ * popDual G S * V = Matrix.diagonal μ ∧
      ∃ ν : EuclideanSpace ℝ (Fin M.k), ‖ν‖ = 1 ∧
        systematicDual μ M.F S V *ᵥ ν = lam j • ν ∧
        M.δsq / ((M.n : ℝ) * lam j + M.δsq)
          + (M.n : ℝ) * lam j / ((M.n : ℝ) * lam j + M.δsq)
            * sinSqAngle ν (EuclideanSpace.single j (1 : ℝ)) = s := by
  have hnum : (0 : ℝ) < (M.n : ℝ) * lam j :=
    mul_pos (Nat.cast_pos.2 (M.k.zero_le.trans_lt M.k_lt_n)) (hlam.pos j)
  have hden : (0 : ℝ) < (M.n : ℝ) * lam j + M.δsq := by linarith [M.δsq_pos]
  have hβ : (0 : ℝ) < (M.n : ℝ) * lam j / ((M.n : ℝ) * lam j + M.δsq) := div_pos hnum hden
  have hαβ : M.δsq / ((M.n : ℝ) * lam j + M.δsq)
      + (M.n : ℝ) * lam j / ((M.n : ℝ) * lam j + M.δsq) = 1 := by
    rw [← add_div, add_comm, div_self hden.ne']
  set α := M.δsq / ((M.n : ℝ) * lam j + M.δsq)
  set β := (M.n : ℝ) * lam j / ((M.n : ℝ) * lam j + M.δsq)
  obtain ⟨S, hS, V, hV, hVK, ν, hν1, hνeig, hνangle⟩ :=
    M.exists_admissible_sinSqAngle_eq hk hG hμ hlam j (t := (s - α) / β)
      (div_nonneg (by linarith) hβ.le) ((div_le_one hβ).2 (by linarith))
  refine ⟨S, hS, V, hV, hVK, ν, hν1, hνeig, ?_⟩
  rw [hνangle, mul_div_cancel₀ _ hβ.ne']
  ring

end FactorModelSeq

end PCError

end
